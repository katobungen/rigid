import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.PowerBoundedUniversalProperty
import Mathlib.Analysis.Normed.Operator.Banach

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Relative Tate algebras

This file equips `TateAlgebra A ι` with its natural structure over a nonarchimedean ground field
`K` when `A` is a Banach `K`-algebra.  It also proves the relative universal property: a continuous
`K`-algebra map `A → B` and a finite power-bounded tuple in `B` determine a continuous map
`A⟨Tᵢ⟩ → B`.
-/

open Filter
open scoped Topology

universe u v w x

namespace Rigid

section Structures

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
variable (ι : Type w)

/-- The ground-field algebra structure on a relative Tate algebra. -/
noncomputable instance (priority := 100) relativeTateAlgebraAlgebra :
    Algebra K (TateAlgebra A ι) :=
  ((TateAlgebra.C A ι).comp (algebraMap K A)).toAlgebra

instance relativeTateAlgebraIsScalarTower : IsScalarTower K A (TateAlgebra A ι) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Scalar multiplication by the ground field is bounded for the relative Gauss norm. -/
theorem relativeTateAlgebra_norm_smul_le (c : K) (f : TateAlgebra A ι) :
    ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  rw [norm_eq_sSup_coeff]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  change ‖MvPowerSeries.coeff n
      ((c • f : TateAlgebra A ι) : MvPowerSeries ι A)‖ ≤ ‖c‖ * ‖f‖
  have hcoe : ((c • f : TateAlgebra A ι) : MvPowerSeries ι A) =
      MvPowerSeries.C (algebraMap K A c) * (f : MvPowerSeries ι A) := by
    rw [Algebra.smul_def]
    rfl
  rw [hcoe, MvPowerSeries.coeff_C_mul, ← Algebra.smul_def]
  exact (norm_smul_le c _).trans
    (mul_le_mul_of_nonneg_left (norm_coeff_le_norm A ι f n) (norm_nonneg c))

noncomputable instance (priority := 100) relativeTateAlgebraNormedAlgebra :
    NormedAlgebra K (TateAlgebra A ι) where
  norm_smul_le := relativeTateAlgebra_norm_smul_le K A ι

end Structures

namespace RelativeTateAlgebra

section Evaluation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]
variable {ι : Type w} [Finite ι]
variable {B : Type x} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [IsUltrametricDist B]

/-- A positive operator bound for the coefficient map. -/
private noncomputable def coefficientBound (φ : ContinuousAlgHom K A B) : ℝ :=
  Classical.choose φ.toContinuousLinearMap.bound

private theorem coefficientBound_pos (φ : ContinuousAlgHom K A B) :
    0 < coefficientBound K A φ :=
  (Classical.choose_spec φ.toContinuousLinearMap.bound).1

private theorem norm_apply_le (φ : ContinuousAlgHom K A B) (a : A) :
    ‖φ a‖ ≤ coefficientBound K A φ * ‖a‖ :=
  (Classical.choose_spec φ.toContinuousLinearMap.bound).2 a

/-- A finite power-bounded tuple has uniformly bounded evaluated monomials. -/
private theorem exists_bound_evalMonomial (x : ι → B) (hx : ∀ i, IsPowerBounded (x i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ι →₀ ℕ, ‖TateAlgebra.evalMonomial x n‖ ≤ C := by
  classical
  letI := Fintype.ofFinite ι
  have hx' : ∀ i, ∃ C : ℝ, ∀ m : ℕ, ‖x i ^ m‖ ≤ C := by
    intro i
    rcases hx i with ⟨C, hC⟩
    exact ⟨C, fun m ↦ hC ⟨m, rfl⟩⟩
  choose C hC using hx'
  let D : ℝ := max ‖(1 : B)‖ (∏ i, max 1 (C i))
  refine ⟨D, (norm_nonneg (1 : B)).trans (le_max_left _ _), fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [D, TateAlgebra.evalMonomial]
  · have hs : n.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
    simp only [TateAlgebra.evalMonomial, Finsupp.prod]
    calc
      ‖∏ i ∈ n.support, x i ^ n i‖ ≤ ∏ i ∈ n.support, ‖x i ^ n i‖ :=
        Finset.norm_prod_le' n.support hs _
      _ ≤ ∏ i ∈ n.support, max 1 (C i) := by
        refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg (x i ^ n i)) fun i _ ↦ ?_
        exact (hC i (n i)).trans (le_max_right _ _)
      _ ≤ ∏ i, max 1 (C i) := by
        refine Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) ?_ ?_
        · exact fun i _ ↦ zero_le_one.trans (le_max_left _ _)
        · exact fun i _ _ ↦ le_max_left _ _
      _ ≤ D := le_max_right _ _

/-- The underlying relative evaluation series. -/
noncomputable def evalFun (φ : ContinuousAlgHom K A B) (x : ι → B)
    (f : TateAlgebra A ι) : B :=
  ∑' n : ι →₀ ℕ, φ (MvPowerSeries.coeff n f.1) * TateAlgebra.evalMonomial x n

private theorem summable_eval (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) (f : TateAlgebra A ι) :
    Summable fun n : ι →₀ ℕ ↦
      φ (MvPowerSeries.coeff n f.1) * TateAlgebra.evalMonomial x n := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_evalMonomial x hx
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  refine squeeze_zero_norm
    (a := fun n : ι →₀ ℕ ↦
      ‖MvPowerSeries.coeff n f.1‖ * (coefficientBound K A φ * D)) (fun n ↦ ?_) ?_
  · calc
      ‖φ (MvPowerSeries.coeff n f.1) * TateAlgebra.evalMonomial x n‖
          ≤ ‖φ (MvPowerSeries.coeff n f.1)‖ *
              ‖TateAlgebra.evalMonomial x n‖ := norm_mul_le _ _
      _ ≤ (coefficientBound K A φ * ‖MvPowerSeries.coeff n f.1‖) * D :=
        mul_le_mul (norm_apply_le K A φ _) (hD n) (norm_nonneg _)
          (mul_nonneg (le_of_lt (coefficientBound_pos K A φ)) (norm_nonneg _))
      _ = ‖MvPowerSeries.coeff n f.1‖ * (coefficientBound K A φ * D) := by ring
  · simpa using
      (tendsto_norm_coeff_zero A ι f).mul_const (coefficientBound K A φ * D)

/-- On polynomials, relative evaluation is ordinary polynomial evaluation. -/
theorem evalFun_ofPolynomial (φ : ContinuousAlgHom K A B) (x : ι → B)
    (p : MvPolynomial ι A) :
    evalFun K A φ x (TateAlgebra.ofPolynomial A ι p) = MvPolynomial.eval₂ φ x p := by
  classical
  have hzero : ∀ n ∉ p.support,
      φ (MvPowerSeries.coeff n
          ((TateAlgebra.ofPolynomial A ι p : TateAlgebra A ι) : MvPowerSeries ι A)) *
          TateAlgebra.evalMonomial x n = 0 := by
    intro n hn
    rw [coe_ofPolynomial, MvPolynomial.coeff_coe,
      MvPolynomial.notMem_support_iff.mp hn, map_zero, zero_mul]
  rw [evalFun, tsum_eq_sum hzero, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [coe_ofPolynomial, MvPolynomial.coeff_coe]
  rfl

private theorem exists_evalBound (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TateAlgebra A ι, ‖evalFun K A φ x f‖ ≤ C * ‖f‖ := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_evalMonomial x hx
  refine ⟨coefficientBound K A φ * D,
    mul_nonneg (le_of_lt (coefficientBound_pos K A φ)) hD0, fun f ↦ ?_⟩
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg (le_of_lt (coefficientBound_pos K A φ)) hD0) (norm_nonneg f))
    fun n ↦ ?_
  calc
    ‖φ (MvPowerSeries.coeff n f.1) * TateAlgebra.evalMonomial x n‖
        ≤ ‖φ (MvPowerSeries.coeff n f.1)‖ *
            ‖TateAlgebra.evalMonomial x n‖ := norm_mul_le _ _
    _ ≤ (coefficientBound K A φ * ‖MvPowerSeries.coeff n f.1‖) * D :=
      mul_le_mul (norm_apply_le K A φ _) (hD n) (norm_nonneg _)
        (mul_nonneg (le_of_lt (coefficientBound_pos K A φ)) (norm_nonneg _))
    _ ≤ (coefficientBound K A φ * ‖f‖) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_coeff_le_norm A ι f n)
          (le_of_lt (coefficientBound_pos K A φ))) hD0
    _ = (coefficientBound K A φ * D) * ‖f‖ := by ring

private noncomputable def evalAddMonoidHom (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) : TateAlgebra A ι →+ B where
  toFun := evalFun K A φ x
  map_zero' := by simp [evalFun]
  map_add' f g := by
    have h : ∀ n : ι →₀ ℕ,
        φ (MvPowerSeries.coeff n ((f + g : TateAlgebra A ι) : MvPowerSeries ι A)) *
            TateAlgebra.evalMonomial x n =
          φ (MvPowerSeries.coeff n f.1) * TateAlgebra.evalMonomial x n +
            φ (MvPowerSeries.coeff n g.1) * TateAlgebra.evalMonomial x n := by
      intro n
      rw [show ((f + g : TateAlgebra A ι) : MvPowerSeries ι A) =
          (f : MvPowerSeries ι A) + (g : MvPowerSeries ι A) from rfl,
        map_add, map_add, add_mul]
    simp only [evalFun]
    simp_rw [h]
    exact (summable_eval K A φ x hx f).tsum_add (summable_eval K A φ x hx g)

private theorem continuous_evalFun (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) : Continuous (evalFun K A φ x) := by
  obtain ⟨C, -, hC⟩ := exists_evalBound K A φ x hx
  exact AddMonoidHomClass.continuous_of_bound (evalAddMonoidHom K A φ x hx) C hC

private theorem evalFun_mul (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) (f g : TateAlgebra A ι) :
    evalFun K A φ x (f * g) = evalFun K A φ x f * evalFun K A φ x g := by
  have h1 : Continuous fun z : TateAlgebra A ι × TateAlgebra A ι ↦
      evalFun K A φ x (z.1 * z.2) :=
    (continuous_evalFun K A φ x hx).comp continuous_mul
  have h2 : Continuous fun z : TateAlgebra A ι × TateAlgebra A ι ↦
      evalFun K A φ x z.1 * evalFun K A φ x z.2 :=
    ((continuous_evalFun K A φ x hx).comp continuous_fst).mul
      ((continuous_evalFun K A φ x hx).comp continuous_snd)
  have hd : Dense
      (Set.range (TateAlgebra.ofPolynomial A ι) ×ˢ
        Set.range (TateAlgebra.ofPolynomial A ι)) :=
    Dense.prod (denseRange_ofPolynomial A ι) (denseRange_ofPolynomial A ι)
  have key : (fun z : TateAlgebra A ι × TateAlgebra A ι ↦
      evalFun K A φ x (z.1 * z.2)) =
      fun z ↦ evalFun K A φ x z.1 * evalFun K A φ x z.2 := by
    refine h1.ext_on hd h2 ?_
    rintro ⟨u, v⟩ ⟨⟨p, rfl⟩, q, rfl⟩
    change evalFun K A φ x
        (TateAlgebra.ofPolynomial A ι p * TateAlgebra.ofPolynomial A ι q) =
      evalFun K A φ x (TateAlgebra.ofPolynomial A ι p) *
        evalFun K A φ x (TateAlgebra.ofPolynomial A ι q)
    rw [← map_mul, evalFun_ofPolynomial, evalFun_ofPolynomial,
      evalFun_ofPolynomial, MvPolynomial.eval₂_mul]
  exact congrFun key (f, g)

/-- Relative evaluation as a continuous ground-field algebra homomorphism. -/
noncomputable def eval (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) : ContinuousAlgHom K (TateAlgebra A ι) B where
  toFun := evalFun K A φ x
  map_one' := by
    have h := evalFun_ofPolynomial K A φ x (1 : MvPolynomial ι A)
    simpa using h
  map_mul' := evalFun_mul K A φ x hx
  map_zero' := by simp [evalFun]
  map_add' := map_add (evalAddMonoidHom K A φ x hx)
  commutes' := fun c ↦ by
    change evalFun K A φ x (TateAlgebra.C A ι (algebraMap K A c)) = algebraMap K B c
    rw [← ofPolynomial_C A ι, evalFun_ofPolynomial, MvPolynomial.eval₂_C]
    exact φ.commutes c
  cont := continuous_evalFun K A φ x hx

@[simp]
theorem eval_C (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) (a : A) :
    eval K A φ x hx (TateAlgebra.C A ι a) = φ a := by
  change evalFun K A φ x (TateAlgebra.C A ι a) = φ a
  rw [← ofPolynomial_C A ι a, evalFun_ofPolynomial,
    MvPolynomial.eval₂_C]
  rfl

@[simp]
theorem eval_tateVariable (φ : ContinuousAlgHom K A B) (x : ι → B)
    (hx : ∀ i, IsPowerBounded (x i)) (i : ι) :
    eval K A φ x hx (tateVariable A ι i) = x i := by
  change evalFun K A φ x (tateVariable A ι i) = x i
  rw [← ofPolynomial_X A ι i, evalFun_ofPolynomial,
    MvPolynomial.eval₂_X]

end Evaluation

section Ext

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
variable {ι : Type w}
variable {B : Type x} [NormedCommRing B] [NormedAlgebra K B]

/-- Continuous maps from a relative Tate algebra are determined by coefficients and variables. -/
@[ext]
theorem hom_ext (φ ψ : ContinuousAlgHom K (TateAlgebra A ι) B)
    (hC : ∀ a, φ (TateAlgebra.C A ι a) = ψ (TateAlgebra.C A ι a))
    (hX : ∀ i, φ (tateVariable A ι i) = ψ (tateVariable A ι i)) : φ = ψ := by
  let Φ : MvPolynomial ι A →+* B :=
    φ.toRingHom.comp (TateAlgebra.ofPolynomial A ι).toRingHom
  let Ψ : MvPolynomial ι A →+* B :=
    ψ.toRingHom.comp (TateAlgebra.ofPolynomial A ι).toRingHom
  have hpoly : Φ = Ψ := MvPolynomial.ringHom_ext
    (fun a ↦ by simpa [Φ, Ψ] using hC a)
    (fun i ↦ by simpa [Φ, Ψ] using hX i)
  have hfun : ⇑φ = ⇑ψ := by
    refine φ.continuous.ext_on (denseRange_ofPolynomial A ι) ψ.continuous ?_
    rintro _ ⟨p, rfl⟩
    exact RingHom.congr_fun hpoly p
  exact ContinuousAlgHom.ext fun f ↦ congrFun hfun f

end Ext

end RelativeTateAlgebra

end Rigid
