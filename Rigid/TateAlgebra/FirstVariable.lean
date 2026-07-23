import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finsupp.Fin
import Mathlib.RingTheory.MvPowerSeries.Rename
import Rigid.TateAlgebra.WeierstrassDivision

set_option linter.style.header false

open scoped MonomialOrder

/-!
# A Tate algebra as restricted series in its first variable

This file relates `TateAlgebra K (Fin (n + 1))` to polynomials in the variable indexed by zero
with coefficients in `TateAlgebra K (Fin n)`.  It supplies the polynomial remainder used in
Weierstrass division and in the Rückert quotient comparison.
-/

universe u

namespace Rigid

namespace TateAlgebra

open Filter

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Include the Tate algebra in variables `1, ..., n` into the one in variables `0, ..., n`. -/
noncomputable def succMap (n : ℕ) :
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
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx ⊢
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

@[simp]
theorem succMap_tateVariable (n : ℕ) (i : Fin n) :
    succMap K n (tateVariable K (Fin n) i) = tateVariable K (Fin (n + 1)) i.succ := by
  apply Subtype.ext
  change MvPowerSeries.rename (Fin.succEmb n)
      (MvPowerSeries.X i : MvPowerSeries (Fin n) K) =
    (MvPowerSeries.X i.succ : MvPowerSeries (Fin (n + 1)) K)
  simp

/-- The coefficient series at a fixed exponent of the first variable. -/
noncomputable def coeffSlice (n j : ℕ) (f : TateAlgebra K (Fin (n + 1))) :
    TateAlgebra K (Fin n) :=
  ⟨fun μ ↦ MvPowerSeries.coeff (μ.cons j) f.1, by
    change MvPowerSeries.IsRestricted (fun _ : Fin n ↦ (1 : ℝ)) _
    rw [MvPowerSeries.IsRestricted]
    simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
    change Tendsto (fun μ : Fin n →₀ ℕ ↦
      ‖MvPowerSeries.coeff (μ.cons j) f.1‖) cofinite (nhds 0)
    exact (tendsto_norm_coeff_zero K (Fin (n + 1)) f).comp
      (Finsupp.cons_right_injective j).tendsto_cofinite⟩

@[simp]
theorem coeff_coeffSlice (n j : ℕ) (f : TateAlgebra K (Fin (n + 1)))
    (μ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff μ (coeffSlice K n j f).1 =
      MvPowerSeries.coeff (μ.cons j) f.1 :=
  rfl

private theorem monomial_single_zero_eq_tateVariable_pow (n j : ℕ) :
    monomial (Finsupp.single (0 : Fin (n + 1)) j) (1 : K) =
      tateVariable K (Fin (n + 1)) 0 ^ j := by
  apply Subtype.ext
  exact (MvPowerSeries.X_pow_eq (R := K) (0 : Fin (n + 1)) j).symm

private theorem coe_succMap (n : ℕ) (a : TateAlgebra K (Fin n)) :
    ((succMap K n a : TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) =
      MvPowerSeries.rename (Fin.succEmb n) a.1 :=
  rfl

theorem coeff_succMap_mul_tateVariable_pow (n j : ℕ)
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

/-- A series whose first-variable exponents are bounded by `d` is a polynomial of degree less
than `d` in that variable, with coefficients in the remaining-variable Tate algebra. -/
theorem eq_sum_succMap_coeffSlice_mul_pow {n d : ℕ}
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

/-- Evaluate a polynomial in the first Tate variable, after including its coefficient algebra in
the remaining variables. -/
noncomputable def firstVariablePolynomialMap (n : ℕ) :
    Polynomial (TateAlgebra K (Fin n)) →+* TateAlgebra K (Fin (n + 1)) :=
  Polynomial.eval₂RingHom (succMap K n).toRingHom (tateVariable K (Fin (n + 1)) 0)

@[simp]
theorem firstVariablePolynomialMap_monomial (n j : ℕ) (a : TateAlgebra K (Fin n)) :
    firstVariablePolynomialMap K n (Polynomial.monomial j a) =
      succMap K n a * tateVariable K (Fin (n + 1)) 0 ^ j := by
  simp [firstVariablePolynomialMap]

theorem firstVariablePolynomialMap_eq_sum (n : ℕ)
    (p : Polynomial (TateAlgebra K (Fin n))) :
    firstVariablePolynomialMap K n p =
      ∑ j ∈ Finset.range (p.natDegree + 1),
        succMap K n (p.coeff j) * tateVariable K (Fin (n + 1)) 0 ^ j := by
  calc
    firstVariablePolynomialMap K n p =
        firstVariablePolynomialMap K n
          (∑ j ∈ Finset.range (p.natDegree + 1),
            Polynomial.C (p.coeff j) * Polynomial.X ^ j) := by
      rw [← p.as_sum_range_C_mul_X_pow]
    _ = ∑ j ∈ Finset.range (p.natDegree + 1),
        succMap K n (p.coeff j) * tateVariable K (Fin (n + 1)) 0 ^ j := by
      simp [firstVariablePolynomialMap]

/-- Coefficients of a first-variable polynomial are read by splitting an exponent into its first
coordinate and its tail. -/
theorem coeff_firstVariablePolynomialMap (n : ℕ)
    (p : Polynomial (TateAlgebra K (Fin n))) (μ : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff μ (firstVariablePolynomialMap K n p).1 =
      MvPowerSeries.coeff μ.tail (p.coeff (μ 0)).1 := by
  rw [firstVariablePolynomialMap_eq_sum]
  change MvPowerSeries.coeff μ
      ((∑ j ∈ Finset.range (p.natDegree + 1),
        succMap K n (p.coeff j) * tateVariable K (Fin (n + 1)) 0 ^ j :
          TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) =
    MvPowerSeries.coeff μ.tail (p.coeff (μ 0)).1
  rw [show MvPowerSeries.coeff μ
      ((∑ j ∈ Finset.range (p.natDegree + 1),
        succMap K n (p.coeff j) * tateVariable K (Fin (n + 1)) 0 ^ j :
          TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) =
      ∑ j ∈ Finset.range (p.natDegree + 1), MvPowerSeries.coeff μ
        ((succMap K n (p.coeff j) * tateVariable K (Fin (n + 1)) 0 ^ j :
          TateAlgebra K (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) K) by simp]
  simp only [coeff_succMap_mul_tateVariable_pow]
  by_cases hμ : μ 0 < p.natDegree + 1
  · rw [Finset.sum_eq_single (μ 0)]
    · rw [if_pos rfl]
    · intro j hj hjne
      rw [if_neg hjne]
    · exact fun h ↦ (h (Finset.mem_range.mpr hμ)).elim
  · have hpμ : p.coeff (μ 0) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    rw [hpμ]
    change (∑ j ∈ Finset.range (p.natDegree + 1),
      if j = μ 0 then MvPowerSeries.coeff μ.tail (p.coeff j).1 else 0) = 0
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hjμ
    subst j
    exact hμ (Finset.mem_range.mp hj)

/-- Evaluation in the first Tate variable is injective. -/
theorem firstVariablePolynomialMap_injective (n : ℕ) :
    Function.Injective (firstVariablePolynomialMap K n) := by
  intro p q hpq
  apply Polynomial.ext
  intro j
  apply Subtype.ext
  ext μ
  have hcoeff := congrArg
    (fun f : TateAlgebra K (Fin (n + 1)) ↦ MvPowerSeries.coeff (μ.cons j) f.1) hpq
  simpa [coeff_firstVariablePolynomialMap] using hcoeff

/-- The polynomial in the first variable obtained from a series known to vanish from exponent
`d` onward. -/
noncomputable def toFirstVariablePolynomial (n d : ℕ)
    (f : TateAlgebra K (Fin (n + 1))) : Polynomial (TateAlgebra K (Fin n)) :=
  ∑ j ∈ Finset.range d, Polynomial.monomial j (coeffSlice K n j f)

@[simp]
theorem coeff_toFirstVariablePolynomial (n d j : ℕ)
    (f : TateAlgebra K (Fin (n + 1))) :
    (toFirstVariablePolynomial K n d f).coeff j =
      if j < d then coeffSlice K n j f else 0 := by
  classical
  simp [toFirstVariablePolynomial, Polynomial.coeff_monomial, eq_comm]

theorem firstVariablePolynomialMap_toFirstVariablePolynomial {n d : ℕ}
    (f : TateAlgebra K (Fin (n + 1)))
    (hf : ∀ μ : Fin (n + 1) →₀ ℕ, d ≤ μ 0 → MvPowerSeries.coeff μ f.1 = 0) :
    firstVariablePolynomialMap K n (toFirstVariablePolynomial K n d f) = f := by
  calc
    firstVariablePolynomialMap K n (toFirstVariablePolynomial K n d f) =
        ∑ j ∈ Finset.range d,
          succMap K n (coeffSlice K n j f) * tateVariable K (Fin (n + 1)) 0 ^ j := by
      simp [toFirstVariablePolynomial]
    _ = f := (eq_sum_succMap_coeffSlice_mul_pow K f hf).symm

/-- The monic polynomial represented by a Weierstrass series. -/
noncomputable def weierstrassPolynomial {n d : ℕ} (w : TateAlgebra K (Fin (n + 1))) :
    Polynomial (TateAlgebra K (Fin n)) :=
  toFirstVariablePolynomial K n (d + 1) w

theorem firstVariablePolynomialMap_weierstrassPolynomial {n d : ℕ}
    {w : TateAlgebra K (Fin (n + 1))} (hw : IsWeierstrassOfDegree d w) :
    firstVariablePolynomialMap K n (weierstrassPolynomial K (d := d) w) = w := by
  apply firstVariablePolynomialMap_toFirstVariablePolynomial
  intro μ hμ
  apply hw.2.2 μ
  · intro heq
    subst μ
    simp at hμ
  · omega

theorem isMonicOfDegree_weierstrassPolynomial {n d : ℕ}
    {w : TateAlgebra K (Fin (n + 1))} (hw : IsWeierstrassOfDegree d w) :
    Polynomial.IsMonicOfDegree (weierstrassPolynomial K (d := d) w) d := by
  rw [Polynomial.isMonicOfDegree_iff]
  constructor
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    simp only [weierstrassPolynomial, coeff_toFirstVariablePolynomial]
    rw [if_neg (by omega)]
  · simp only [weierstrassPolynomial, coeff_toFirstVariablePolynomial, Nat.lt_add_one, if_true]
    apply Subtype.ext
    ext μ
    by_cases hμ : μ = 0
    · subst μ
      rw [coeff_coeffSlice, Finsupp.cons_zero_eq_single_zero, hw.2.1]
      change TateAlgebra.coeff K (Fin n) 0 (1 : TateAlgebra K (Fin n)) = 1
      rw [← map_one (algebraMap K (TateAlgebra K (Fin n))), algebraMap_apply,
        TateAlgebra.coeff_zero_C]
    · have hconsne : μ.cons d ≠ Finsupp.single (0 : Fin (n + 1)) d := by
        intro h
        apply hμ
        ext i
        have hi := congrArg (fun ν : Fin (n + 1) →₀ ℕ ↦ ν i.succ) h
        simpa using hi
      rw [coeff_coeffSlice, hw.2.2 (μ.cons d) hconsne (by simp)]
      change 0 = TateAlgebra.coeff K (Fin n) μ (1 : TateAlgebra K (Fin n))
      rw [← map_one (algebraMap K (TateAlgebra K (Fin n))), algebraMap_apply,
        TateAlgebra.coeff_C, if_neg hμ]

theorem IsWeierstrassOfDegree.norm_eq_one {n d : ℕ}
    {w : TateAlgebra K (Fin (n + 1))} (hw : IsWeierstrassOfDegree d w) :
    ‖w‖ = 1 := by
  apply le_antisymm hw.1
  have hle := norm_coeff_le_norm K _ w (Finsupp.single (0 : Fin (n + 1)) d)
  rw [hw.2.1, norm_one] at hle
  exact hle

private theorem single_zero_le_of_lex_lt {n d : ℕ} {μ : Fin (n + 1) →₀ ℕ}
    (hμ : Finsupp.single 0 d ≺[(MonomialOrder.lex : MonomialOrder (Fin (n + 1)))] μ) :
    d ≤ μ 0 := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff] at hμ
  obtain ⟨j, hj, hjlt⟩ := hμ
  by_cases hj0 : j = 0
  · subst j
    simpa using hjlt.le
  · have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
    have heq := hj 0 h0j
    simpa using heq.le

theorem IsWeierstrassOfDegree.leadingDegree {n d : ℕ}
    {w : TateAlgebra K (Fin (n + 1))} (hw : IsWeierstrassOfDegree d w) :
    leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) w =
      Finsupp.single 0 d := by
  let ν : Fin (n + 1) →₀ ℕ := Finsupp.single 0 d
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp [IsWeierstrassOfDegree] at hw
  apply leadingDegree_unique MonomialOrder.lex hwne
  · rw [hw.2.1, norm_one, hw.norm_eq_one K]
  · intro μ hμ
    by_contra hnot
    have hlt : ν ≺[(MonomialOrder.lex : MonomialOrder (Fin (n + 1)))] μ :=
      lt_of_not_ge hnot
    have hne : μ ≠ ν := by
      intro h
      subst μ
      exact (lt_irrefl _ hlt)
    have hzero := hw.2.2 μ hne (single_zero_le_of_lex_lt hlt)
    rw [hzero, norm_zero, hw.norm_eq_one K] at hμ
    norm_num at hμ

/-- A monic first-variable polynomial is Weierstrass exactly when its Tate norm is at most one. -/
theorem isWeierstrassOfDegree_firstVariablePolynomialMap_iff {n d : ℕ}
    {p : Polynomial (TateAlgebra K (Fin n))}
    (hp : Polynomial.IsMonicOfDegree p d) :
    IsWeierstrassOfDegree d (firstVariablePolynomialMap K n p) ↔
      ‖firstVariablePolynomialMap K n p‖ ≤ 1 := by
  constructor
  · exact fun h ↦ h.1
  · intro hnorm
    refine ⟨hnorm, ?_, ?_⟩
    · rw [coeff_firstVariablePolynomialMap]
      have hpd : p.coeff d = 1 := by
        have := hp.monic.coeff_natDegree
        rwa [hp.natDegree_eq] at this
      simp only [Finsupp.single_eq_same]
      rw [hpd]
      have htail : (Finsupp.single (0 : Fin (n + 1)) d).tail = 0 := by
        ext i
        simp [Finsupp.tail_apply]
      rw [htail]
      change TateAlgebra.coeff K (Fin n) 0 (1 : TateAlgebra K (Fin n)) = 1
      rw [← map_one (algebraMap K (TateAlgebra K (Fin n))), algebraMap_apply,
        TateAlgebra.coeff_zero_C]
    · intro μ hμne hμd
      rw [coeff_firstVariablePolynomialMap]
      by_cases hμeq : μ 0 = d
      · have htail : μ.tail ≠ 0 := by
          intro htail
          apply hμne
          ext i
          cases i using Fin.cases with
          | zero => simpa using hμeq
          | succ i => simpa [Finsupp.tail_apply] using DFunLike.congr_fun htail i
        have hpd : p.coeff d = 1 := by
          have := hp.monic.coeff_natDegree
          rwa [hp.natDegree_eq] at this
        rw [hμeq, hpd]
        change TateAlgebra.coeff K (Fin n) μ.tail (1 : TateAlgebra K (Fin n)) = 0
        rw [← map_one (algebraMap K (TateAlgebra K (Fin n))), algebraMap_apply,
          TateAlgebra.coeff_C, if_neg htail]
      · have hdlt : d < μ 0 := lt_of_le_of_ne hμd (Ne.symm hμeq)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ hdlt)]
        simp

/-- Rückert's factor-closure property for Weierstrass polynomials (Definition 4.1.13, R1). -/
theorem isWeierstrassOfDegree_mul_iff {n d e : ℕ}
    {p q : Polynomial (TateAlgebra K (Fin n))}
    (hp : Polynomial.IsMonicOfDegree p d) (hq : Polynomial.IsMonicOfDegree q e) :
    IsWeierstrassOfDegree (d + e) (firstVariablePolynomialMap K n (p * q)) ↔
      IsWeierstrassOfDegree d (firstVariablePolynomialMap K n p) ∧
        IsWeierstrassOfDegree e (firstVariablePolynomialMap K n q) := by
  rw [isWeierstrassOfDegree_firstVariablePolynomialMap_iff K (hp.mul hq),
    isWeierstrassOfDegree_firstVariablePolynomialMap_iff K hp,
    isWeierstrassOfDegree_firstVariablePolynomialMap_iff K hq]
  rw [map_mul, norm_mul]
  constructor
  · intro hpq
    have hp1 : 1 ≤ ‖firstVariablePolynomialMap K n p‖ := by
      have hcoeff := norm_coeff_le_norm K _ (firstVariablePolynomialMap K n p)
        (Finsupp.single (0 : Fin (n + 1)) d)
      rw [coeff_firstVariablePolynomialMap] at hcoeff
      have hpd : p.coeff d = 1 := by
        have := hp.monic.coeff_natDegree
        rwa [hp.natDegree_eq] at this
      simp only [Finsupp.single_eq_same] at hcoeff
      rw [hpd] at hcoeff
      have htail : (Finsupp.single (0 : Fin (n + 1)) d).tail = 0 := by
        ext i
        simp [Finsupp.tail_apply]
      rw [htail] at hcoeff
      have hone : MvPowerSeries.coeff 0 (1 : TateAlgebra K (Fin n)).1 = 1 := by
        change TateAlgebra.coeff K (Fin n) 0 (1 : TateAlgebra K (Fin n)) = 1
        rw [← map_one (algebraMap K (TateAlgebra K (Fin n))), algebraMap_apply,
          TateAlgebra.coeff_zero_C]
      rw [hone, norm_one] at hcoeff
      exact hcoeff
    have hq1 : 1 ≤ ‖firstVariablePolynomialMap K n q‖ := by
      have hcoeff := norm_coeff_le_norm K _ (firstVariablePolynomialMap K n q)
        (Finsupp.single (0 : Fin (n + 1)) e)
      rw [coeff_firstVariablePolynomialMap] at hcoeff
      have hqe : q.coeff e = 1 := by
        have := hq.monic.coeff_natDegree
        rwa [hq.natDegree_eq] at this
      simp only [Finsupp.single_eq_same] at hcoeff
      rw [hqe] at hcoeff
      have htail : (Finsupp.single (0 : Fin (n + 1)) e).tail = 0 := by
        ext i
        simp [Finsupp.tail_apply]
      rw [htail] at hcoeff
      have hone : MvPowerSeries.coeff 0 (1 : TateAlgebra K (Fin n)).1 = 1 := by
        change TateAlgebra.coeff K (Fin n) 0 (1 : TateAlgebra K (Fin n)) = 1
        rw [← map_one (algebraMap K (TateAlgebra K (Fin n))), algebraMap_apply,
          TateAlgebra.coeff_zero_C]
      rw [hone, norm_one] at hcoeff
      exact hcoeff
    constructor
    · calc
        ‖firstVariablePolynomialMap K n p‖ =
            ‖firstVariablePolynomialMap K n p‖ * 1 := (mul_one _).symm
        _ ≤ ‖firstVariablePolynomialMap K n p‖ *
            ‖firstVariablePolynomialMap K n q‖ :=
          mul_le_mul_of_nonneg_left hq1 (norm_nonneg _)
        _ ≤ 1 := hpq
    · calc
        ‖firstVariablePolynomialMap K n q‖ =
            1 * ‖firstVariablePolynomialMap K n q‖ := (one_mul _).symm
        _ ≤ ‖firstVariablePolynomialMap K n p‖ *
            ‖firstVariablePolynomialMap K n q‖ :=
          mul_le_mul_of_nonneg_right hp1 (norm_nonneg _)
        _ ≤ 1 := hpq
  · rintro ⟨hp', hq'⟩
    calc
      ‖firstVariablePolynomialMap K n p‖ * ‖firstVariablePolynomialMap K n q‖ ≤
          1 * 1 := mul_le_mul hp' hq' (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1

end TateAlgebra

end Rigid
