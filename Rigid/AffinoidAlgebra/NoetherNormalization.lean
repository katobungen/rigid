import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.NoetherNormalization
import Rigid.AffinoidAlgebra.Basic
import Rigid.TateAlgebra.Division
import Rigid.TateAlgebra.UniversalProperty

set_option linter.style.header false

/-!
# Noether normalization for affinoid algebras

This file proves Noether normalization for a nonzero affinoid algebra: it is finite over an
injectively embedded Tate algebra in finitely many variables.  The proof follows Kato,
*Introduction to Rigid Geometry*, Theorem 1.4.5, and Corollary 4.3.14 of the cited draft notes.
As a consequence it proves the affinoid Nullstellensatz: an affinoid algebra which is a field is
finite-dimensional over its ground field (Kato, Corollary 1.4.9).

The normalization argument is organized as an induction on the number of variables in a
surjective Tate-algebra presentation.  A triangular change of coordinates makes a nonzero
relation distinguished in the first variable.  The Tate-algebra division theorem then shows that
the target is finite over the image of the Tate algebra in the remaining variables.  Applying the
induction hypothesis to that image and composing the resulting finite injective maps gives the
normalization.
-/

open Filter
open scoped MonomialOrder Topology

universe u v

namespace Rigid

namespace TateAlgebra

section Slices

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

section CoordinateChange

open MvPolynomial

variable {n : ℕ}

local notation3 "up(" p ")" => 2 + MvPolynomial.totalDegree p
local notation3 "weight(" p ")" =>
  fun (i : Fin (n + 1)) ↦ up(p) ^ i.1

/-- The polynomial triangular coordinate change used in Noether normalization. -/
private noncomputable abbrev polynomialShear (p : MvPolynomial (Fin (n + 1)) K) (c : K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then MvPolynomial.X 0
    else MvPolynomial.X i + c • MvPolynomial.X 0 ^ weight(p) i

variable {p : MvPolynomial (Fin (n + 1)) K} {v w : Fin (n + 1) →₀ ℕ}

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma lt_up (hv : ∀ i, v i < up(p)) : ∀ l ∈ List.ofFn v, l < up(p) := by
  intro l hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  exact hv i

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma sum_weight_mul_ne (hv : ∀ i, v i < up(p)) (hw : ∀ i, w i < up(p))
    (hvw : v ≠ w) :
    ∑ i : Fin (n + 1), weight(p) i * v i ≠ ∑ i : Fin (n + 1), weight(p) i * w i := by
  intro h
  refine hvw (Finsupp.ext (congrFun (List.ofFn_inj.mp ?_)))
  apply Nat.ofDigits_inj_of_len_eq (Nat.lt_add_right p.totalDegree one_lt_two)
    (by simp) (lt_up (K := K) (p := p) (v := v) hv)
      (lt_up (K := K) (p := p) (v := w) hw)
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
    List.length_ofFn, Fin.val_cast, mul_comm, Fin.sum_ofFn] using! h

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma degreeOf_zero_polynomialShear_monomial {a : K} (ha : a ≠ 0) :
    ((polynomialShear K p 1) (MvPolynomial.monomial v a)).degreeOf 0 =
      ∑ i : Fin (n + 1), weight(p) i * v i := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, MvPolynomial.monomial_eq,
    Finsupp.prod_pow v fun a ↦ MvPolynomial.X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero, ite_false,
    one_smul, map_add, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.algebraMap_eq]
  have hne (i : Fin n) :
      ((Polynomial.C (MvPolynomial.X i) + Polynomial.X ^ weight(p) i.succ :
        Polynomial (MvPolynomial (Fin n) K)) ^ v i.succ) ≠ 0 := by
    letI : NeZero (weight(p) i.succ) := ⟨pow_ne_zero _ (by omega)⟩
    exact pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mp (by
      simp [add_comm, Polynomial.leadingCoeff_X_pow_add_C]))
  rw [Polynomial.natDegree_mul (by simp [ha])
      (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hne i)),
    Polynomial.natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hne i),
    Polynomial.natDegree_prod _ _ (fun i _ ↦ hne i),
    MvPolynomial.natDegree_finSuccEquiv, MvPolynomial.degreeOf_C]
  simpa only [Polynomial.natDegree_pow, zero_add, Polynomial.natDegree_X, mul_one,
    Fin.val_zero, pow_zero, one_mul, add_right_inj] using
      Finset.sum_congr rfl (fun i _ ↦ by
        rw [add_comm (Polynomial.C _), Polynomial.natDegree_X_pow_add_C, mul_comm])

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma degreeOf_polynomialShear_monomial_ne (hv : v ∈ p.support) (hw : w ∈ p.support)
    (hvw : v ≠ w) :
    ((polynomialShear K p 1) (MvPolynomial.monomial v (MvPolynomial.coeff v p))).degreeOf 0 ≠
      ((polynomialShear K p 1) (MvPolynomial.monomial w (MvPolynomial.coeff w p))).degreeOf 0 := by
  rw [degreeOf_zero_polynomialShear_monomial (K := K) (p := p)
      (MvPolynomial.mem_support_iff.mp hv),
    degreeOf_zero_polynomialShear_monomial (K := K) (p := p)
      (MvPolynomial.mem_support_iff.mp hw)]
  refine sum_weight_mul_ne (K := K) (p := p) (v := v) (w := w)
    (fun i ↦ ?_) (fun i ↦ ?_) hvw <;>
    exact lt_of_le_of_lt
      ((MvPolynomial.monomial_le_degreeOf i ‹_›).trans (MvPolynomial.degreeOf_le_totalDegree p i))
      (by omega)

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma leadingCoeff_finSuccEquiv_polynomialShear_monomial :
    (MvPolynomial.finSuccEquiv K n
      ((polynomialShear K p 1) (MvPolynomial.monomial v (MvPolynomial.coeff v p)))).leadingCoeff =
        algebraMap K _ (MvPolynomial.coeff v p) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod]
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, MvPolynomial.finSuccEquiv_apply,
      MvPolynomial.eval₂Hom_C, RingHom.coe_comp]
    simp only [Function.comp_apply, Polynomial.leadingCoeff_C, map_pow,
      Polynomial.leadingCoeff_pow, MvPolynomial.algebraMap_eq]
    have hlead : ∀ j,
        (MvPolynomial.finSuccEquiv K n
          ((polynomialShear K p 1) (MvPolynomial.X j))).leadingCoeff = 1 := by
      intro j
      by_cases hj : j = 0
      · simp [hj, MvPolynomial.finSuccEquiv_apply]
      · simp only [MvPolynomial.aeval_eq_bind₁, MvPolynomial.bind₁_X_right, if_neg hj,
          one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hj
        simp [MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_zero, add_comm]
    simp only [hlead, one_pow, Finset.prod_const_one, mul_one]
  · exact fun i ↦ pow_zero _

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- After the triangular coordinate change, the leading coefficient in the first variable is one
of the original coefficients. -/
private lemma exists_leadingCoeff_polynomialShear_eq (hp : p ≠ 0) :
    ∃ v ∈ p.support,
      (MvPolynomial.finSuccEquiv K n ((polynomialShear K p 1) p)).leadingCoeff =
        algebraMap K _ (MvPolynomial.coeff v p) := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image p.support
    (fun v ↦ ((polynomialShear K p 1)
      (MvPolynomial.monomial v (MvPolynomial.coeff v p))).degreeOf 0)
    (MvPolynomial.support_nonempty.mpr hp)
  refine ⟨v, hv, ?_⟩
  let mon := fun w ↦ MvPolynomial.monomial w (MvPolynomial.coeff w p)
  simp only [← MvPolynomial.natDegree_finSuccEquiv] at hmax
  have hlt : ∀ w ∈ p.support \ {v},
      (MvPolynomial.finSuccEquiv K n ((polynomialShear K p 1) (mon w))).degree <
        (MvPolynomial.finSuccEquiv K n ((polynomialShear K p 1) (mon v))).degree := by
    intro w hw
    obtain ⟨hwp, hwv⟩ := Finset.mem_sdiff.mp hw
    apply Polynomial.degree_lt_degree <| lt_of_le_of_ne (hmax w hwp) ?_
    simpa only [MvPolynomial.natDegree_finSuccEquiv] using
      (degreeOf_polynomialShear_monomial_ne (K := K) (p := p) hwp hv
        (by simpa using hwv))
  have hcoeff :
      (MvPolynomial.finSuccEquiv K n ((polynomialShear K p 1)
        (mon v + ∑ w ∈ p.support \ {v}, mon w))).leadingCoeff =
      (MvPolynomial.finSuccEquiv K n ((polynomialShear K p 1) (mon v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply Polynomial.leadingCoeff_add_of_degree_lt
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    have hv0 : MvPolynomial.finSuccEquiv K n ((polynomialShear K p 1) (mon v)) ≠ 0 := by
      intro hzero
      have hlead := leadingCoeff_finSuccEquiv_polynomialShear_monomial
        (K := K) (p := p) (v := v)
      rw [hzero, Polynomial.leadingCoeff_zero] at hlead
      exact (MvPolynomial.mem_support_iff.mp hv)
        (by simpa [MvPolynomial.algebraMap_eq] using hlead.symm)
    exact (Finset.sup_lt_iff (WithBot.bot_lt_iff_ne_bot.mpr
      (fun h ↦ hv0 (Polynomial.degree_eq_bot.mp h)))).mpr hlt
  nth_rw 2 [← p.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hv mon]
  rw [hcoeff]
  simpa [mon] using
    (leadingCoeff_finSuccEquiv_polynomialShear_monomial (K := K) (p := p) (v := v))

/-! The same triangular coordinate change on the Tate algebra. -/

private noncomputable def tateShearPoint (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (i : Fin (n + 1)) : TateAlgebra K (Fin (n + 1)) :=
  if i = 0 then tateVariable K _ 0
  else tateVariable K _ i + c • tateVariable K _ 0 ^ weight(p) i

omit [CompleteSpace K] in
private theorem norm_tateShearPoint_le (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) (i : Fin (n + 1)) : ‖tateShearPoint K p c i‖ ≤ 1 := by
  by_cases hi : i = 0
  · simp [tateShearPoint, hi, norm_tateVariable]
  · rw [tateShearPoint, if_neg hi]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (norm_tateVariable K _ i).le
    · calc
        ‖c • tateVariable K (Fin (n + 1)) 0 ^ weight(p) i‖
            ≤ ‖c‖ * ‖tateVariable K (Fin (n + 1)) 0 ^ weight(p) i‖ := norm_smul_le _ _
        _ ≤ 1 * 1 := mul_le_mul hc
          ((norm_pow_le _ _).trans_eq (by rw [norm_tateVariable, one_pow]))
          (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- The bounded Tate-algebra endomorphism induced by the triangular coordinate change. -/
private noncomputable def tateShear (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) :
    ContinuousAlgHom K (TateAlgebra K (Fin (n + 1))) (TateAlgebra K (Fin (n + 1))) :=
  TateAlgebra.eval K _ (tateShearPoint K p c) (norm_tateShearPoint_le K p c hc)

@[simp]
private theorem tateShear_tateVariable (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) (i : Fin (n + 1)) :
    tateShear K p c hc (tateVariable K _ i) = tateShearPoint K p c i :=
  TateAlgebra.eval_tateVariable K _ (norm_tateShearPoint_le K p c hc) i

private theorem norm_tateShear_le (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) (f : TateAlgebra K (Fin (n + 1))) :
    ‖tateShear K p c hc f‖ ≤ ‖f‖ := by
  change ‖TateAlgebra.evalFun K _ (tateShearPoint K p c) f‖ ≤ ‖f‖
  simpa only [norm_one, max_self, one_mul] using
    (TateAlgebra.norm_evalFun_le K _ (norm_tateShearPoint_le K p c hc) f)

private theorem tateShear_ofPolynomial (p q : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) :
    tateShear K p c hc (TateAlgebra.ofPolynomial K _ q) =
      TateAlgebra.ofPolynomial K _ ((polynomialShear K p c) q) := by
  rw [show tateShear K p c hc (TateAlgebra.ofPolynomial K _ q) =
      MvPolynomial.aeval (tateShearPoint K p c) q from
    TateAlgebra.evalFun_ofPolynomial K _ (tateShearPoint K p c) q]
  let lhs : MvPolynomial (Fin (n + 1)) K →ₐ[K] TateAlgebra K (Fin (n + 1)) :=
    MvPolynomial.aeval (tateShearPoint K p c)
  let rhs : MvPolynomial (Fin (n + 1)) K →ₐ[K] TateAlgebra K (Fin (n + 1)) :=
    (TateAlgebra.ofPolynomial K _).comp (polynomialShear K p c)
  have hhom : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = 0 <;>
      simp [lhs, rhs, tateShearPoint, polynomialShear, hi, ofPolynomial_X]
  exact AlgHom.congr_fun hhom q

private theorem tateShear_comp_neg (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) (hnc : ‖-c‖ ≤ 1) (f : TateAlgebra K (Fin (n + 1))) :
    tateShear K p c hc (tateShear K p (-c) hnc f) = f := by
  let ψ : ContinuousAlgHom K (TateAlgebra K (Fin (n + 1)))
      (TateAlgebra K (Fin (n + 1))) :=
    (tateShear K p c hc).comp (tateShear K p (-c) hnc)
  have hψ : ψ = ContinuousAlgHom.id K (TateAlgebra K (Fin (n + 1))) := by
    apply (existsUnique_continuousAlgHom_of_norm_le_one K _
      (fun i ↦ tateVariable K (Fin (n + 1)) i)
      (fun i ↦ (norm_tateVariable K _ i).le)).unique
    · intro i
      cases i using Fin.cases with
      | zero => simp [ψ, tateShearPoint]
      | succ i =>
          simp [ψ, tateShearPoint, map_add, map_pow, map_smul, add_assoc]
    · intro i
      rfl
  exact congrArg (fun θ : ContinuousAlgHom K _ _ ↦ θ f) hψ

private theorem norm_tateShear_eq (p : MvPolynomial (Fin (n + 1)) K) (c : K)
    (hc : ‖c‖ ≤ 1) (hnc : ‖-c‖ ≤ 1) (f : TateAlgebra K (Fin (n + 1))) :
    ‖tateShear K p c hc f‖ = ‖f‖ := by
  apply le_antisymm (norm_tateShear_le K p c hc f)
  calc
    ‖f‖ = ‖tateShear K p (-c) hnc (tateShear K p c hc f)‖ := by
      have hinv := tateShear_comp_neg K p (-c) hnc (by simpa using hc) f
      simpa only [neg_neg] using congrArg norm hinv.symm
    _ ≤ ‖tateShear K p c hc f‖ := norm_tateShear_le K p (-c) hnc _

open Classical in
/-- The polynomial consisting of the terms at which a Tate series attains its Gauss norm. -/
private noncomputable def leadingPolynomial (f : TateAlgebra K (Fin (n + 1))) :
    MvPolynomial (Fin (n + 1)) K :=
  ∑ ν ∈ leadingSupport f, MvPolynomial.monomial ν (MvPowerSeries.coeff ν f.1)

omit [CompleteSpace K] in
private theorem coeff_leadingPolynomial (f : TateAlgebra K (Fin (n + 1)))
    (μ : Fin (n + 1) →₀ ℕ) :
    MvPolynomial.coeff μ (leadingPolynomial K f) =
      if μ ∈ leadingSupport f then MvPowerSeries.coeff μ f.1 else 0 := by
  classical
  rw [leadingPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  simpa only [eq_comm] using
    (Finset.sum_ite_eq (leadingSupport f) μ fun ν ↦ MvPowerSeries.coeff ν f.1)

omit [CompleteSpace K] in
private theorem ofPolynomial_leadingPolynomial (f : TateAlgebra K (Fin (n + 1))) :
    TateAlgebra.ofPolynomial K _ (leadingPolynomial K f) = leadingPart f := by
  classical
  rw [leadingPolynomial, leadingPart, map_sum]
  apply Finset.sum_congr rfl
  intro ν hν
  apply Subtype.ext
  rw [coe_ofPolynomial, MvPolynomial.coe_monomial, coe_monomial]

omit [CompleteSpace K] in
private theorem norm_leadingPart_eq {f : TateAlgebra K (Fin (n + 1))} (hf : f ≠ 0) :
    ‖leadingPart f‖ = ‖f‖ := by
  have htail := norm_sub_leadingPart_lt hf
  have hLPle : ‖leadingPart f‖ ≤ ‖f‖ := by
    calc
      ‖leadingPart f‖ = ‖f - (f - leadingPart f)‖ := by ring_nf
      _ ≤ max ‖f‖ ‖-(f - leadingPart f)‖ := by
        simpa only [sub_eq_add_neg] using
          (IsUltrametricDist.norm_add_le_max f (-(f - leadingPart f)))
      _ ≤ ‖f‖ := by simp only [norm_neg]; exact max_le le_rfl htail.le
  apply le_antisymm hLPle
  by_contra hnot
  have hLPlt : ‖leadingPart f‖ < ‖f‖ := lt_of_not_ge hnot
  have hbound : ‖f‖ ≤ max ‖leadingPart f‖ ‖f - leadingPart f‖ := by
    calc
      ‖f‖ = ‖leadingPart f + (f - leadingPart f)‖ := by ring_nf
      _ ≤ max ‖leadingPart f‖ ‖f - leadingPart f‖ :=
        IsUltrametricDist.norm_add_le_max _ _
  exact (hbound.trans_lt (max_lt hLPlt htail)).false

/-- A triangular automorphism makes any nonzero Tate series distinguished in the first
variable.  This is the analytic coordinate-change step in Noether normalization. -/
private theorem exists_tateShear_leadingDegree_eq_single_zero
    (f : TateAlgebra K (Fin (n + 1))) (hf : f ≠ 0) :
    ∃ (p : MvPolynomial (Fin (n + 1)) K) (d : ℕ),
      leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1)))
        (tateShear K p 1 (by simp) f) = Finsupp.single 0 d := by
  classical
  let p := leadingPolynomial K f
  have hp : p ≠ 0 := by
    intro hp0
    have hLP : leadingPart f = 0 := by
      rw [← ofPolynomial_leadingPolynomial K f]
      change TateAlgebra.ofPolynomial K _ p = 0
      rw [hp0, map_zero]
    have htail := norm_sub_leadingPart_lt hf
    rw [hLP, sub_zero] at htail
    exact htail.false
  let q := (polynomialShear K p 1) p
  obtain ⟨v, hv, hlead⟩ := exists_leadingCoeff_polynomialShear_eq (K := K) hp
  let P := MvPolynomial.finSuccEquiv K n q
  let d := P.natDegree
  let a := MvPolynomial.coeff v p
  have hva : v ∈ leadingSupport f := by
    by_contra hvlead
    have hcoeff := coeff_leadingPolynomial K f v
    rw [if_neg hvlead] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hv) hcoeff
  have hnorma : ‖a‖ = ‖f‖ := by
    change ‖MvPolynomial.coeff v p‖ = ‖f‖
    rw [coeff_leadingPolynomial K f v, if_pos hva]
    exact le_antisymm (norm_coeff_le_norm K _ f v) ((mem_leadingSupport hf).mp hva)
  have hleadP : P.leadingCoeff = MvPolynomial.C a := by
    simpa [P, q, a, MvPolynomial.algebraMap_eq] using hlead
  have hqcoeff : MvPolynomial.coeff (Finsupp.single (0 : Fin (n + 1)) d) q = a := by
    have hcons : (0 : Fin n →₀ ℕ).cons d = Finsupp.single (0 : Fin (n + 1)) d := by
      ext i
      cases i using Fin.cases <;> simp
    rw [← hcons, ← MvPolynomial.finSuccEquiv_coeff_coeff]
    change MvPolynomial.coeff 0 (P.coeff d) = a
    rw [Polynomial.coeff_natDegree, hleadP]
    simp
  have hqhigh (μ : Fin (n + 1) →₀ ℕ) (hμ : d < μ 0) :
      MvPolynomial.coeff μ q = 0 := by
    rw [← Finsupp.cons_tail μ, ← MvPolynomial.finSuccEquiv_coeff_coeff]
    change MvPolynomial.coeff μ.tail (P.coeff (μ 0)) = 0
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hμ]
    simp
  have hqatd (μ : Fin (n + 1) →₀ ℕ) (hμ : μ 0 = d)
      (hμq : MvPolynomial.coeff μ q ≠ 0) :
      μ = Finsupp.single (0 : Fin (n + 1)) d := by
    have htail : μ.tail = 0 := by
      by_contra htail0
      apply hμq
      rw [← Finsupp.cons_tail μ, hμ, ← MvPolynomial.finSuccEquiv_coeff_coeff]
      change MvPolynomial.coeff μ.tail (P.coeff d) = 0
      rw [Polynomial.coeff_natDegree, hleadP]
      rw [MvPolynomial.coeff_C]
      split_ifs with hzero
      · exact (htail0 hzero.symm).elim
      · rfl
    ext i
    cases i using Fin.cases with
    | zero => simpa using hμ
    | succ i => simpa [Finsupp.tail_apply] using DFunLike.congr_fun htail i
  let ψ := tateShear K p 1 (by simp)
  let F := ψ f
  let H : TateAlgebra K (Fin (n + 1)) := TateAlgebra.ofPolynomial K _ q
  let r := ψ (f - leadingPart f)
  have hψLP : ψ (leadingPart f) = H := by
    rw [← ofPolynomial_leadingPolynomial K f,
      tateShear_ofPolynomial K p p 1 (by simp)]
  have hF : F = H + r := by
    calc
      F = ψ (leadingPart f + (f - leadingPart f)) := by simp [F, ψ]
      _ = ψ (leadingPart f) + ψ (f - leadingPart f) := map_add ψ _ _
      _ = H + r := by rw [hψLP]
  have hFnorm : ‖F‖ = ‖f‖ := by
    exact norm_tateShear_eq K p 1 (by simp) (by simp) f
  have hrnorm : ‖r‖ < ‖f‖ :=
    (norm_tateShear_le K p 1 (by simp) (f - leadingPart f)).trans_lt
      (norm_sub_leadingPart_lt hf)
  have hHnorm : ‖H‖ = ‖f‖ := by
    rw [← hψLP]
    exact (norm_tateShear_eq K p 1 (by simp) (by simp) _).trans
      (norm_leadingPart_eq K hf)
  have hcoeffF (μ : Fin (n + 1) →₀ ℕ) :
      MvPowerSeries.coeff μ F.1 =
        MvPowerSeries.coeff μ H.1 + MvPowerSeries.coeff μ r.1 := by
    rw [hF]
    exact map_add (MvPowerSeries.coeff μ) H.1 r.1
  have hcoeffH (μ : Fin (n + 1) →₀ ℕ) :
      MvPowerSeries.coeff μ H.1 = MvPolynomial.coeff μ q := by
    change MvPowerSeries.coeff μ
      ((TateAlgebra.ofPolynomial K _ q : TateAlgebra K _) : MvPowerSeries _ K) = _
    rw [coe_ofPolynomial, MvPolynomial.coeff_coe]
  have hrcoeff (μ : Fin (n + 1) →₀ ℕ) :
      ‖MvPowerSeries.coeff μ r.1‖ < ‖f‖ :=
    (norm_coeff_le_norm K _ r μ).trans_lt hrnorm
  have hHcoeff (μ : Fin (n + 1) →₀ ℕ) :
      ‖MvPowerSeries.coeff μ H.1‖ ≤ ‖f‖ :=
    (norm_coeff_le_norm K _ H μ).trans_eq hHnorm
  have hFcoeff :
      ‖MvPowerSeries.coeff (Finsupp.single (0 : Fin (n + 1)) d) F.1‖ = ‖F‖ := by
    rw [hcoeffF, hcoeffH, hqcoeff, hFnorm]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (ne_of_gt ((hrcoeff _).trans_eq hnorma.symm))]
    rw [max_eq_left]
    · exact hnorma
    · rw [hnorma]
      exact (hrcoeff _).le
  have hF0 : F ≠ 0 := by
    rw [← norm_ne_zero_iff, hFnorm]
    exact norm_ne_zero_iff.mpr hf
  have hleadF : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) F =
      Finsupp.single 0 d := by
    apply leadingDegree_unique (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) hF0 hFcoeff
    intro μ hμF
    have hHattain : ‖MvPowerSeries.coeff μ H.1‖ = ‖f‖ := by
      apply le_antisymm (hHcoeff μ)
      by_contra hnot
      have hHlt : ‖MvPowerSeries.coeff μ H.1‖ < ‖f‖ := lt_of_not_ge hnot
      have hsumlt : ‖MvPowerSeries.coeff μ H.1 + MvPowerSeries.coeff μ r.1‖ < ‖f‖ :=
        (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hHlt (hrcoeff μ))
      exact (not_le_of_gt hsumlt) (by simpa [hcoeffF, hFnorm] using hμF)
    have hqμ : MvPolynomial.coeff μ q ≠ 0 := by
      rw [← hcoeffH]
      intro hz
      rw [hz, norm_zero] at hHattain
      exact (norm_pos_iff.mpr hf).ne' hHattain.symm
    have hμd : μ 0 ≤ d := by
      by_contra hnot
      exact hqμ (hqhigh μ (lt_of_not_ge hnot))
    rcases hμd.eq_or_lt with hμdeq | hμdlt
    · rw [hqatd μ hμdeq hqμ]
    · rw [MonomialOrder.lex_le_iff]
      apply le_of_lt
      rw [Finsupp.Lex.lt_iff]
      refine ⟨0, ?_, ?_⟩
      · intro j hj
        exact (Fin.not_lt_zero j hj).elim
      · simpa using hμdlt
  exact ⟨p, d, by simpa [F] using hleadF⟩

/-- A polynomial triangular coordinate change makes every nonzero Tate series distinguished in
the first variable, expressed without exposing the implementation of the shear. -/
theorem exists_algEquiv_leadingDegree_eq_single_zero
    (f : TateAlgebra K (Fin (n + 1))) (hf : f ≠ 0) :
    ∃ (ψ : TateAlgebra K (Fin (n + 1)) ≃ₐ[K] TateAlgebra K (Fin (n + 1))) (d : ℕ),
      leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) (ψ f) =
        Finsupp.single 0 d := by
  classical
  obtain ⟨p, d, hd⟩ := exists_tateShear_leadingDegree_eq_single_zero K f hf
  have h1 : ‖(1 : K)‖ ≤ 1 := by simp
  have hn1 : ‖(-1 : K)‖ ≤ 1 := by simp
  have hnn1 : ‖-(-1 : K)‖ ≤ 1 := by simp
  let ψ : TateAlgebra K (Fin (n + 1)) →ₐ[K] TateAlgebra K (Fin (n + 1)) :=
    (tateShear K p 1 h1).toAlgHom
  let ψinv : TateAlgebra K (Fin (n + 1)) →ₐ[K] TateAlgebra K (Fin (n + 1)) :=
    (tateShear K p (-1) hn1).toAlgHom
  have hright : ψ.comp ψinv = AlgHom.id K (TateAlgebra K (Fin (n + 1))) := by
    apply DFunLike.ext _ _
    intro x
    dsimp only [ψ, ψinv, AlgHom.comp_apply, AlgHom.id_apply]
    exact tateShear_comp_neg K p 1 h1 hn1 x
  have hleft : ψinv.comp ψ = AlgHom.id K (TateAlgebra K (Fin (n + 1))) := by
    apply DFunLike.ext _ _
    intro x
    dsimp only [ψ, ψinv, AlgHom.comp_apply, AlgHom.id_apply]
    convert tateShear_comp_neg K p (-1) hn1 hnn1 x using 1
    all_goals simp
  let e := AlgEquiv.ofAlgHom ψ ψinv hright hleft
  refine ⟨e, d, ?_⟩
  exact hd

end CoordinateChange

/-- Include the Tate algebra in variables `1, ..., n` into the one in variables `0, ..., n`. -/
private noncomputable def succMap (n : ℕ) :
    TateAlgebra K (Fin n) →ₐ[K] TateAlgebra K (Fin (n + 1)) := by
  let e : Fin n ↪ Fin (n + 1) := Fin.succEmb n
  refine
    { toFun := fun p ↦ ⟨MvPowerSeries.rename e p.1, ?_⟩
      map_one' := Subtype.ext (map_one (MvPowerSeries.rename e))
      map_mul' := fun p q ↦ Subtype.ext (map_mul (MvPowerSeries.rename e) p.1 q.1)
      map_zero' := Subtype.ext (map_zero (MvPowerSeries.rename e))
      map_add' := fun p q ↦ Subtype.ext (map_add (MvPowerSeries.rename e) p.1 q.1)
      commutes' := fun c ↦ Subtype.ext (by simp [algebraMap_apply]) }
  change MvPowerSeries.IsRestricted (fun _ : Fin (n + 1) ↦ (1 : ℝ))
    (MvPowerSeries.rename e p.1)
  have hrename : Tendsto
      (fun x : Fin (n + 1) →₀ ℕ ↦
        ‖MvPowerSeries.coeff x (MvPowerSeries.rename e p.1)‖) cofinite (nhds 0) := by
    rw [tendsto_def]
    intro s hs
    have hzero : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
    have hp : {x : Fin n →₀ ℕ | ‖MvPowerSeries.coeff x p.1‖ ∈ s} ∈ cofinite :=
      (tendsto_norm_coeff_zero K (Fin n) p).eventually hs
    rw [mem_cofinite] at hp ⊢
    refine hp.image (Finsupp.embDomain e) |>.subset ?_
    intro x hx
    simp only [Set.mem_compl_iff] at hx ⊢
    by_cases hxr : x ∈ Set.range (Finsupp.embDomain e)
    · obtain ⟨y, rfl⟩ := hxr
      refine ⟨y, ?_, rfl⟩
      simpa using hx
    · exfalso
      apply hx
      change ‖MvPowerSeries.coeff x (MvPowerSeries.rename e p.1)‖ ∈ s
      rw [MvPowerSeries.coeff_rename_eq_zero]
      · simpa using hzero
      · simpa [Finsupp.embDomain_eq_mapDomain] using hxr
  simpa [MvPowerSeries.IsRestricted, Finsupp.prod] using hrename

omit [CompleteSpace K] in
@[simp]
private theorem succMap_tateVariable (n : ℕ) (i : Fin n) :
    succMap K n (tateVariable K (Fin n) i) = tateVariable K (Fin (n + 1)) i.succ := by
  apply Subtype.ext
  change MvPowerSeries.rename (Fin.succEmb n)
      (MvPowerSeries.X i : MvPowerSeries (Fin n) K) =
    (MvPowerSeries.X i.succ : MvPowerSeries (Fin (n + 1)) K)
  simp

/-- The remaining-variable inclusion preserves the Gauss norm. -/
private theorem norm_succMap_eq (n : ℕ) (a : TateAlgebra K (Fin n)) :
    ‖succMap K n a‖ = ‖a‖ := by
  apply le_antisymm
  · rw [norm_eq_sSup_coeff]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨μ, rfl⟩
    change ‖MvPowerSeries.coeff μ
      (MvPowerSeries.rename (Fin.succEmb n) a.1)‖ ≤ ‖a‖
    by_cases hμ : μ ∈ Set.range (Finsupp.embDomain (Fin.succEmb n))
    · obtain ⟨ν, rfl⟩ := hμ
      rw [MvPowerSeries.coeff_embDomain_rename]
      exact norm_coeff_le_norm K (Fin n) a ν
    · rw [MvPowerSeries.coeff_rename_eq_zero]
      · exact norm_zero.trans_le (norm_nonneg a)
      · rintro ⟨ν, hν⟩
        apply hμ
        exact ⟨ν, by simpa [Finsupp.embDomain_eq_mapDomain] using hν⟩
  · rw [norm_eq_sSup_coeff]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨ν, rfl⟩
    change ‖MvPowerSeries.coeff ν a.1‖ ≤ ‖succMap K n a‖
    rw [← MvPowerSeries.coeff_embDomain_rename (Fin.succEmb n) a.1 ν]
    exact norm_coeff_le_norm K (Fin (n + 1)) (succMap K n a)
      (Finsupp.embDomain (Fin.succEmb n) ν)

/-- The coefficient series at a fixed exponent of the first variable. -/
private noncomputable def coeffSlice (n j : ℕ) (f : TateAlgebra K (Fin (n + 1))) :
    TateAlgebra K (Fin n) :=
  ⟨fun μ ↦ MvPowerSeries.coeff (μ.cons j) f.1, by
    change MvPowerSeries.IsRestricted (fun _ : Fin n ↦ (1 : ℝ)) _
    rw [MvPowerSeries.IsRestricted]
    simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
    change Tendsto (fun μ : Fin n →₀ ℕ ↦
      ‖MvPowerSeries.coeff (μ.cons j) f.1‖) cofinite (nhds 0)
    exact (tendsto_norm_coeff_zero K (Fin (n + 1)) f).comp
      (Finsupp.cons_right_injective j).tendsto_cofinite⟩

omit [CompleteSpace K] in
@[simp]
private theorem coeff_coeffSlice (n j : ℕ) (f : TateAlgebra K (Fin (n + 1)))
    (μ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff μ (coeffSlice K n j f).1 =
      MvPowerSeries.coeff (μ.cons j) f.1 :=
  rfl

omit [CompleteSpace K] in
private theorem monomial_single_zero_eq_tateVariable_pow (n j : ℕ) :
    monomial (Finsupp.single (0 : Fin (n + 1)) j) (1 : K) =
      tateVariable K (Fin (n + 1)) 0 ^ j := by
  apply Subtype.ext
  exact (MvPowerSeries.X_pow_eq (R := K) (0 : Fin (n + 1)) j).symm

omit [CompleteSpace K] in
private theorem coe_succMap (n : ℕ) (a : TateAlgebra K (Fin n)) :
    ((succMap K n a : TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) =
      MvPowerSeries.rename (Fin.succEmb n) a.1 :=
  rfl

omit [CompleteSpace K] in
private theorem coeff_succMap_mul_tateVariable_pow (n j : ℕ)
    (a : TateAlgebra K (Fin n)) (μ : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff μ
        ((succMap K n a * tateVariable K (Fin (n + 1)) 0 ^ j :
          TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) =
      if j = μ 0 then MvPowerSeries.coeff μ.tail a.1 else 0 := by
  rw [mul_comm, ← monomial_single_zero_eq_tateVariable_pow, coeff_monomial_mul]
  by_cases hjμ : j = μ 0
  · subst j
    rw [if_pos rfl, if_pos (by simp [Finsupp.single_le_iff])]
    have hsub : μ - Finsupp.single (0 : Fin (n + 1)) (μ 0) = μ.tail.cons 0 := by
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ i => simp [Finsupp.tail_apply]
    rw [hsub]
    simp only [one_mul]
    rw [coe_succMap]
    have hemb : Finsupp.embDomain (Fin.succEmb n) μ.tail = μ.tail.cons 0 := by
      ext i
      cases i using Fin.cases with
      | zero => simp [Finsupp.embDomain_apply]
      | succ i => simp [Finsupp.embDomain_apply]
    rw [← hemb]
    exact MvPowerSeries.coeff_embDomain_rename (Fin.succEmb n) a.1 μ.tail
  · rw [if_neg hjμ]
    split_ifs with hle
    · simp only [one_mul]
      rw [coe_succMap]
      change MvPowerSeries.coeff (μ - Finsupp.single 0 j)
        (MvPowerSeries.rename (Fin.succEmb n) a.1) = 0
      apply MvPowerSeries.coeff_rename_eq_zero
      intro hrange
      obtain ⟨ν, hν⟩ := hrange
      rw [← Finsupp.embDomain_eq_mapDomain] at hν
      have hzero := congrArg (fun x : Fin (n + 1) →₀ ℕ ↦ x 0) hν
      simp [Finsupp.embDomain_apply] at hzero
      have hμj : μ 0 ≤ j := Nat.sub_eq_zero_iff_le.mp (by simpa using hzero.symm)
      exact hjμ (Nat.le_antisymm (by simpa [Finsupp.single_le_iff] using hle) hμj)
    · rfl

omit [CompleteSpace K] in
/-- A series whose first-variable exponents are bounded by `d` is a polynomial of degree less
than `d` in that variable, with coefficients in the remaining-variable Tate algebra. -/
private theorem eq_sum_succMap_coeffSlice_mul_pow {n d : ℕ}
    (f : TateAlgebra K (Fin (n + 1)))
    (hf : ∀ μ : Fin (n + 1) →₀ ℕ, d ≤ μ 0 → MvPowerSeries.coeff μ f.1 = 0) :
    f = ∑ j ∈ Finset.range d,
      succMap K n (coeffSlice K n j f) * tateVariable K (Fin (n + 1)) 0 ^ j := by
  ext μ
  change MvPowerSeries.coeff μ f.1 = MvPowerSeries.coeff μ
    ((∑ j ∈ Finset.range d,
      succMap K n (coeffSlice K n j f) * tateVariable K (Fin (n + 1)) 0 ^ j :
        TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K)
  rw [show MvPowerSeries.coeff μ
      ((∑ j ∈ Finset.range d,
        succMap K n (coeffSlice K n j f) * tateVariable K (Fin (n + 1)) 0 ^ j :
          TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) =
      ∑ j ∈ Finset.range d, MvPowerSeries.coeff μ
        ((succMap K n (coeffSlice K n j f) *
          tateVariable K (Fin (n + 1)) 0 ^ j : TateAlgebra K (Fin (n + 1))) :
            MvPowerSeries (Fin (n + 1)) K) by simp]
  simp only [coeff_succMap_mul_tateVariable_pow]
  by_cases hμd : d ≤ μ 0
  · rw [hf μ hμd]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    exact ne_of_lt (Finset.mem_range.mp hj |>.trans_le hμd)
  · have hμlt : μ 0 < d := Nat.lt_of_not_ge hμd
    rw [Finset.sum_eq_single (μ 0)]
    · rw [if_pos rfl]
      exact congrArg (fun ν ↦ MvPowerSeries.coeff ν f.1) (Finsupp.cons_tail μ).symm
    · intro j hj hjne
      rw [if_neg hjne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hμlt)).elim

section FiniteStep

variable {A : Type v} [CommRing A] [Algebra K A]

/-- Division by a relation whose leading monomial is a pure power of the first variable makes the
target finite over the image of the remaining-variable Tate algebra. -/
private theorem finite_comp_succMap_of_leadingDegree_eq_single_zero {n d : ℕ}
    (φ : TateAlgebra K (Fin (n + 1)) →ₐ[K] A) (hφ : Function.Surjective φ)
    (g : TateAlgebra K (Fin (n + 1))) (hg : g ∈ RingHom.ker φ)
    (hg0 : g ≠ 0)
    (hgd : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g =
      Finsupp.single 0 d) :
    (φ.comp (succMap K n)).Finite := by
  let h : TateAlgebra K (Fin n) →ₐ[K] A := φ.comp (succMap K n)
  letI : Algebra (TateAlgebra K (Fin n)) A := h.toRingHom.toAlgebra
  change Module.Finite (TateAlgebra K (Fin n)) A
  rw [Module.finite_def, Submodule.fg_iff_exists_fin_generating_family]
  refine ⟨d, fun j : Fin d ↦ φ (tateVariable K (Fin (n + 1)) 0 ^ j.1), ?_⟩
  apply le_antisymm le_top
  intro y _
  obtain ⟨f, rfl⟩ := hφ y
  obtain ⟨q, hq⟩ := exists_forall_coeff_eq_zero_of_leadingDegree_le
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) (fun _ : Fin 1 ↦ g)
      (fun _ ↦ hg0) f
  let r : TateAlgebra K (Fin (n + 1)) := f - q 0 * g
  have hrcoeff : ∀ μ : Fin (n + 1) →₀ ℕ, d ≤ μ 0 →
      MvPowerSeries.coeff μ r.1 = 0 := by
    intro μ hμ
    have hdiv := hq μ (by
      refine ⟨0, ?_⟩
      rw [hgd]
      simpa [Finsupp.single_le_iff] using hμ)
    simpa [r] using hdiv
  have hrdecomp := eq_sum_succMap_coeffSlice_mul_pow K r hrcoeff
  have hφr : φ f = φ r := by
    change φ g = 0 at hg
    simp [r, hg]
  rw [hφr, hrdecomp, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_mul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨j, Finset.mem_range.mp hj⟩, rfl⟩

end FiniteStep

/-! ## Noether normalization and the affinoid Nullstellensatz -/

omit [CompleteSpace K] in
/-- The zero-variable Tate algebra is one-dimensional over the ground field. -/
private theorem finite_tateAlgebra_fin_zero : Module.Finite K (TateAlgebra K (Fin 0)) := by
  apply Module.Finite.of_surjective (Algebra.linearMap K (TateAlgebra K (Fin 0)))
  intro f
  refine ⟨MvPowerSeries.coeff 0 f.1, ?_⟩
  apply Subtype.ext
  ext μ
  have hμ : μ = 0 := Subsingleton.elim _ _
  subst μ
  simp [algebraMap_apply]

/-- Algebraic form of Noether normalization for a quotient of a finite Tate algebra. -/
private theorem exists_finite_injective_tateAlgebra_of_surjective (n : ℕ) :
    ∀ {A : Type v} [CommRing A] [Algebra K A] [Nontrivial A]
      (π : TateAlgebra K (Fin n) →ₐ[K] A), Function.Surjective π →
      ∃ (d : ℕ) (j : TateAlgebra K (Fin d) →ₐ[K] TateAlgebra K (Fin n)),
        (∀ a, ‖j a‖ = ‖a‖) ∧ Function.Injective (π.comp j) ∧ (π.comp j).Finite := by
  induction n with
  | zero =>
      intro A _ _ _ π hπ
      have hscalar (f : TateAlgebra K (Fin 0)) :
          algebraMap K (TateAlgebra K (Fin 0)) (MvPowerSeries.coeff 0 f.1) = f := by
        apply Subtype.ext
        ext μ
        have hμ : μ = 0 := Subsingleton.elim _ _
        subst μ
        simp [algebraMap_apply]
      have hπinj : Function.Injective π := by
        intro f g hfg
        have hfg' := hfg
        rw [← hscalar f, ← hscalar g] at hfg'
        rw [π.commutes, π.commutes] at hfg'
        have hcoeff := FaithfulSMul.algebraMap_injective K A hfg'
        calc
          f = algebraMap K (TateAlgebra K (Fin 0)) (MvPowerSeries.coeff 0 f.1) :=
            (hscalar f).symm
          _ = algebraMap K (TateAlgebra K (Fin 0)) (MvPowerSeries.coeff 0 g.1) :=
            congrArg _ hcoeff
          _ = g := hscalar g
      refine ⟨0, AlgHom.id K _, fun _ ↦ rfl, ?_, ?_⟩
      · simpa using hπinj
      · simpa using AlgHom.Finite.of_surjective π hπ
  | succ n ih =>
      intro A _ _ _ π hπ
      by_cases hker : RingHom.ker π = ⊥
      · refine ⟨n + 1, AlgHom.id K _, fun _ ↦ rfl, ?_, ?_⟩
        · simpa using (RingHom.injective_iff_ker_eq_bot π).mpr hker
        · simpa using AlgHom.Finite.of_surjective π hπ
      · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
          (p := RingHom.ker π) hker
        obtain ⟨p, d, hgd⟩ := exists_tateShear_leadingDegree_eq_single_zero K g hg0
        let ψ : ContinuousAlgHom K (TateAlgebra K (Fin (n + 1)))
            (TateAlgebra K (Fin (n + 1))) := tateShear K p 1 (by simp)
        let ψinv : ContinuousAlgHom K (TateAlgebra K (Fin (n + 1)))
            (TateAlgebra K (Fin (n + 1))) := tateShear K p (-1) (by simp)
        let g' := ψ g
        let π' : TateAlgebra K (Fin (n + 1)) →ₐ[K] A :=
          π.comp (ψinv : TateAlgebra K (Fin (n + 1)) →ₐ[K]
            TateAlgebra K (Fin (n + 1)))
        have hψinvψ (z : TateAlgebra K (Fin (n + 1))) : ψinv (ψ z) = z := by
          simpa [ψ, ψinv] using
            (tateShear_comp_neg K p (-1) (by simp) (by simp) z)
        have hπ' : Function.Surjective π' := by
          intro a
          obtain ⟨z, hz⟩ := hπ a
          refine ⟨ψ z, ?_⟩
          change π (ψinv (ψ z)) = a
          rw [hψinvψ]
          exact hz
        have hg' : g' ∈ RingHom.ker π' := by
          change π (ψinv (ψ g)) = 0
          rw [hψinvψ]
          exact hg
        have hg'0 : g' ≠ 0 := by
          intro hgzero
          apply hg0
          calc
            g = ψinv (ψ g) := (hψinvψ g).symm
            _ = ψinv g' := rfl
            _ = 0 := by rw [hgzero, map_zero]
        have hgd' : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g' =
            Finsupp.single 0 d := by
          simpa [g', ψ] using hgd
        let h : TateAlgebra K (Fin n) →ₐ[K] A := π'.comp (succMap K n)
        have hhfinite : h.Finite :=
          finite_comp_succMap_of_leadingDegree_eq_single_zero K π' hπ' g' hg' hg'0 hgd'
        let C : Subalgebra K A := h.range
        have hvalfinite : (Subalgebra.val C).Finite := by
          apply AlgHom.Finite.of_comp_finite (f := h.rangeRestrict)
          simpa [C] using hhfinite
        obtain ⟨e, j, hjnorm, hιinj, hιfinite⟩ :=
          ih h.rangeRestrict h.rangeRestrict_surjective
        let j' : TateAlgebra K (Fin e) →ₐ[K] TateAlgebra K (Fin (n + 1)) :=
          ψinv.toAlgHom.comp ((succMap K n).comp j)
        have hj'norm (a : TateAlgebra K (Fin e)) : ‖j' a‖ = ‖a‖ := by
          change ‖ψinv (succMap K n (j a))‖ = ‖a‖
          rw [show ‖ψinv (succMap K n (j a))‖ = ‖succMap K n (j a)‖ by
            exact norm_tateShear_eq K p (-1) (by simp) (by simp) _,
            norm_succMap_eq K n, hjnorm]
        have hcomp :
            π.comp j' = (Subalgebra.val C).comp (h.rangeRestrict.comp j) := by
          ext a
          rfl
        refine ⟨e, j', hj'norm, ?_, ?_⟩
        · rw [hcomp]
          exact Subtype.val_injective.comp hιinj
        · rw [hcomp]
          exact AlgHom.Finite.comp hvalfinite hιfinite

/-- A surjective Tate presentation contains an isometric Noether-normalizing Tate subalgebra.
Keeping the factorization through the source presentation is the coefficient-comparison input in
the minimal-prime proof of Proposition 4.5.3. -/
theorem exists_isometric_normalizationFactor_of_surjective
    {A : Type v} [CommRing A] [Algebra K A] [Nontrivial A] (n : ℕ)
    (π : TateAlgebra K (Fin n) →ₐ[K] A) (hπ : Function.Surjective π) :
    ∃ (d : ℕ) (j : TateAlgebra K (Fin d) →ₐ[K] TateAlgebra K (Fin n)),
      (∀ a, ‖j a‖ = ‖a‖) ∧ Function.Injective (π.comp j) ∧ (π.comp j).Finite :=
  exists_finite_injective_tateAlgebra_of_surjective K n π hπ

end Slices

end TateAlgebra

section AffinoidNullstellensatz

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {A : Type v} [CommRing A] [Algebra K A]

/-- Quotients of affinoid algebras are affinoid. -/
theorem IsAffinoidAlgebra.quotient (hA : IsAffinoidAlgebra K A) (I : Ideal A) :
    IsAffinoidAlgebra K (A ⧸ I) := by
  let π : A →ₐ[K] A ⧸ I := Ideal.Quotient.mkₐ K I
  let g : TateAlgebra K (Fin hA.presentation.n) →ₐ[K] A ⧸ I :=
    π.comp hA.presentation.toAlgHom
  have hg : Function.Surjective g :=
    Ideal.Quotient.mkₐ_surjective K I |>.comp hA.presentation.toAlgHom_surjective
  exact ⟨
    { n := hA.presentation.n
      ideal := RingHom.ker g
      equiv := Ideal.quotientKerAlgEquivOfSurjective hg }⟩

/-- **Noether normalization for affinoid algebras.** A nonzero affinoid algebra admits an
injective homomorphism from a Tate algebra in finitely many variables and is finite as an algebra
over that Tate algebra. -/
theorem exists_finite_injective_tateAlgebra_of_isAffinoidAlgebra [Nontrivial A]
    (hA : IsAffinoidAlgebra K A) :
    ∃ (d : ℕ) (ι : TateAlgebra K (Fin d) →ₐ[K] A), Function.Injective ι ∧ ι.Finite := by
  obtain ⟨n, π, hπ⟩ := exists_surjective_presentation_of_isAffinoidAlgebra K A hA
  obtain ⟨d, j, -, hinj, hfinite⟩ :=
    TateAlgebra.exists_isometric_normalizationFactor_of_surjective K n π hπ
  exact ⟨d, π.comp j, hinj, hfinite⟩

/-- **Affinoid Nullstellensatz.** An affinoid algebra which is a field is a finite-dimensional
algebra over the ground field. -/
theorem finite_of_isField_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A)
    (hfield : IsField A) : Module.Finite K A := by
  letI : Field A := hfield.toField
  obtain ⟨d, ι, hιinj, hιfinite⟩ :=
    exists_finite_injective_tateAlgebra_of_isAffinoidAlgebra K hA
  have hTateField : IsField (TateAlgebra K (Fin d)) := by
    letI : Algebra (TateAlgebra K (Fin d)) A := ι.toRingHom.toAlgebra
    letI : Module.Finite (TateAlgebra K (Fin d)) A := hιfinite
    exact isField_of_isIntegral_of_isField hιinj hfield
  have hd : d = 0 := by
    cases d with
    | zero => rfl
    | succ d =>
        exfalso
        letI : Field (TateAlgebra K (Fin (d + 1))) := hTateField.toField
        let X₀ := tateVariable K (Fin (d + 1)) 0
        have hX₀ : X₀ ≠ 0 := by
          rw [← norm_ne_zero_iff, norm_tateVariable]
          exact one_ne_zero
        have hX₀inv : X₀ * X₀⁻¹ = 1 := mul_inv_cancel₀ hX₀
        have hconst := congrArg
          (fun z : TateAlgebra K (Fin (d + 1)) ↦ MvPowerSeries.constantCoeff z.1) hX₀inv
        simp [X₀] at hconst
  subst d
  let κ : K →ₐ[K] TateAlgebra K (Fin 0) := Algebra.ofId K (TateAlgebra K (Fin 0))
  have hκfin : κ.Finite := by
    exact TateAlgebra.finite_tateAlgebra_fin_zero K
  have hcomp : (ι.comp κ).Finite := AlgHom.Finite.comp hιfinite hκfin
  have hcomp_eq : ι.comp κ = Algebra.ofId K A := by ext
  rw [hcomp_eq] at hcomp
  change (algebraMap K A).Finite at hcomp
  exact RingHom.finite_algebraMap.mp hcomp

end AffinoidNullstellensatz

end Rigid
