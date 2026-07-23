import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Cardinality
import Rigid.AffinoidAlgebra.FiniteExtensionFunctional

set_option linter.style.header false

/-!
# Bounded linear maps from finite Banach modules

The bounded-functional step in the domain proof of the sharp spectral polynomial theorem uses a
standard Banach-module argument.  A finite module is a quotient of a finite free module.  Scalar
linearity makes every map out of that free module continuous, and the Banach open mapping theorem
gives controlled preimages.  Consequently every linear map between such topological modules is
bounded.
-/

universe u v w x y z

namespace Rigid

/-- A continuous ring homomorphism makes its target a topological module over its source. -/
theorem continuousSMul_of_continuousRingHom {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    (f : R →+* S) (hf : Continuous f) :
    letI : Algebra R S := f.toAlgebra
    ContinuousSMul R S := by
  letI : Algebra R S := f.toAlgebra
  constructor
  change Continuous fun p : R × S ↦ f p.1 * p.2
  exact (hf.comp continuous_fst).mul continuous_snd

section FiniteModule

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
variable {C : Type w} [NormedAddCommGroup C] [NormedSpace K C] [CompleteSpace C]
variable {L : Type x} [NormedAddCommGroup L] [NormedSpace K L]
variable [Module A C] [Module A L] [IsScalarTower K A C] [IsScalarTower K A L]
variable [ContinuousSMul A C] [ContinuousSMul A L]

include K in
/-- A linear map from a finite Banach `A`-module is bounded, provided both scalar actions are
continuous.  The target itself need not be complete. -/
theorem LinearMap.exists_bound_of_module_finite [Module.Finite A C] (F : C →ₗ[A] L) :
    ∃ M : ℝ, 0 < M ∧ ∀ c : C, ‖F c‖ ≤ M * ‖c‖ := by
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' A C
  let qK : (Fin m → A) →L[K] C :=
    { toLinearMap := q.restrictScalars K
      cont := q.continuous_on_pi }
  let Fq : (Fin m → A) →ₗ[A] L := F.comp q
  let FqK : (Fin m → A) →L[K] L :=
    { toLinearMap := Fq.restrictScalars K
      cont := Fq.continuous_on_pi }
  obtain ⟨Q, hQpos, hQ⟩ := qK.exists_preimage_norm_le hq
  let M : ℝ := max 1 (‖FqK‖ * Q)
  refine ⟨M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun c ↦ ?_⟩
  obtain ⟨a, ha, hanorm⟩ := hQ c
  calc
    ‖F c‖ = ‖FqK a‖ := by rw [← ha]; rfl
    _ ≤ ‖FqK‖ * ‖a‖ := FqK.le_opNorm a
    _ ≤ ‖FqK‖ * (Q * ‖c‖) :=
      mul_le_mul_of_nonneg_left hanorm (norm_nonneg FqK)
    _ = (‖FqK‖ * Q) * ‖c‖ := by rw [mul_assoc]
    _ ≤ M * ‖c‖ :=
      mul_le_mul_of_nonneg_right (le_max_right 1 (‖FqK‖ * Q)) (norm_nonneg c)

end FiniteModule

section FractionFieldFunctional

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
variable {C : Type w} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
variable {F : Type x} {E : Type y} {L : Type z}
variable [Field F] [Field E]
variable [NormedField L] [NormedSpace K L]
variable [Algebra A C] [Algebra A F] [Algebra A E] [Algebra A L]
variable [Algebra C E] [Algebra F E] [Algebra F L]
variable [IsScalarTower K A C]
variable [IsScalarTower A C E] [IsScalarTower A F E] [IsScalarTower A F L]
variable [ContinuousSMul A C] [ContinuousSMul A L]

include K in
/-- The algebraic root functional on the ambient fraction field becomes bounded after restriction
to a finite Banach algebra.  This packages the linear-extension and open-mapping steps of
Proposition 4.5.7; the remaining input is the identification of the relevant minimal polynomial. -/
theorem exists_bounded_linearMap_map_algebraMap_pow_eq_of_minpoly_root
    [Module.Finite A C]
    (hKAL : IsScalarTower K A L) (c : C)
    (hc : IsIntegral F (algebraMap C E c)) (z : L)
    (hz : Polynomial.aeval z (minpoly F (algebraMap C E c)) = 0) :
    ∃ (G : C →ₗ[A] L) (M : ℝ), 0 < M ∧ (∀ m : ℕ, G (c ^ m) = z ^ m) ∧
      ∀ a : C, ‖G a‖ ≤ M * ‖a‖ := by
  letI : IsScalarTower K A L := hKAL
  obtain ⟨G, hGpow⟩ :=
    FiniteExtensionFunctional.exists_linearMap_map_algebraMap_pow_eq_of_minpoly_root
      (R := A) (F := F) (E := E) (L := L) c hc z hz
  obtain ⟨M, hM, hG⟩ := Rigid.LinearMap.exists_bound_of_module_finite (K := K) G
  exact ⟨G, M, hM, hGpow, hG⟩

include K in
/-- Fraction-field specialization of
`exists_bounded_linearMap_map_algebraMap_pow_eq_of_minpoly_root`.  The two fraction-field algebra
structures are the canonical lifts of the injective maps from `A`. -/
theorem exists_bounded_fractionRingFunctional_of_minpoly_root
    [IsDomain A] [IsDomain C] [FaithfulSMul A C] [FaithfulSMul A L] [Module.Finite A C]
    (hKAL : IsScalarTower K A L) (c : C) (z : L) :
    letI : Algebra (FractionRing A) (FractionRing C) :=
      FractionRing.liftAlgebra A (FractionRing C)
    letI : IsScalarTower A (FractionRing A) (FractionRing C) :=
      FractionRing.isScalarTower_liftAlgebra A (FractionRing C)
    letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    letI : IsScalarTower A (FractionRing A) L := FractionRing.isScalarTower_liftAlgebra A L
    IsIntegral (FractionRing A) (algebraMap C (FractionRing C) c) →
      Polynomial.aeval z (minpoly (FractionRing A) (algebraMap C (FractionRing C) c)) = 0 →
      ∃ (G : C →ₗ[A] L) (M : ℝ), 0 < M ∧ (∀ m : ℕ, G (c ^ m) = z ^ m) ∧
        ∀ a : C, ‖G a‖ ≤ M * ‖a‖ := by
  intro hc hz
  letI : Algebra (FractionRing A) (FractionRing C) :=
    FractionRing.liftAlgebra A (FractionRing C)
  letI : IsScalarTower A (FractionRing A) (FractionRing C) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing C)
  letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A (FractionRing A) L :=
    FractionRing.isScalarTower_liftAlgebra A L
  exact exists_bounded_linearMap_map_algebraMap_pow_eq_of_minpoly_root
    (K := K) (A := A) (C := C) (F := FractionRing A) (E := FractionRing C) (L := L)
    hKAL c hc z hz

include K in
/-- For a finite extension, algebraicity of the fraction-field extension supplies the integrality
hypothesis in `exists_bounded_fractionRingFunctional_of_minpoly_root` automatically. -/
theorem exists_bounded_fractionRingFunctional_of_minpoly_root_of_finite
    [IsDomain A] [IsDomain C] [FaithfulSMul A C] [FaithfulSMul A L] [Module.Finite A C]
    (hKAL : IsScalarTower K A L) (c : C) (z : L) :
    letI : Algebra (FractionRing A) (FractionRing C) :=
      FractionRing.liftAlgebra A (FractionRing C)
    Polynomial.eval₂ (IsFractionRing.lift (FaithfulSMul.algebraMap_injective A L)) z
      (minpoly (FractionRing A) (algebraMap C (FractionRing C) c)) = 0 →
      ∃ (G : C →ₗ[A] L) (M : ℝ), 0 < M ∧ (∀ m : ℕ, G (c ^ m) = z ^ m) ∧
        ∀ a : C, ‖G a‖ ≤ M * ‖a‖ := by
  intro hz
  letI : Algebra (FractionRing A) (FractionRing C) :=
    FractionRing.liftAlgebra A (FractionRing C)
  letI : IsScalarTower A (FractionRing A) (FractionRing C) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing C)
  letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  letI : IsScalarTower A (FractionRing A) L :=
    FractionRing.isScalarTower_liftAlgebra A L
  have hc : IsIntegral (FractionRing A) (algebraMap C (FractionRing C) c) :=
    (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hz' : Polynomial.aeval z
      (minpoly (FractionRing A) (algebraMap C (FractionRing C) c)) = 0 := by
    change Polynomial.eval₂ (algebraMap (FractionRing A) L) z
      (minpoly (FractionRing A) (algebraMap C (FractionRing C) c)) = 0
    exact hz
  exact exists_bounded_linearMap_map_algebraMap_pow_eq_of_minpoly_root
    (K := K) (A := A) (C := C) (F := FractionRing A) (E := FractionRing C) (L := L)
    hKAL c hc z hz'

end FractionFieldFunctional

end Rigid
