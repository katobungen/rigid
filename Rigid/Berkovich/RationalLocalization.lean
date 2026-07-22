import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import Rigid.Berkovich.AffinoidDomain
import Rigid.Berkovich.CompletedResidueFunctoriality

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Berkovich spectra of rational localizations

This file proves that an algebra satisfying the universal property of a rational localization has
relative Berkovich spectrum homeomorphic to the corresponding rational domain.  The construction
is phrased in terms of `RationalLocalizationPresentation`, so it is independent of a particular
quotient model for the localization.
-/

open scoped Topology

universe u v w

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The data and universal property needed from a rational localization of `A` at `(g, f)`.

Bundling this interface keeps the Berkovich-spectrum argument independent of the concrete quotient
construction used for the localization. -/
structure RationalLocalizationPresentation
    (L : Type v) [NormedCommRing L] [NormedAlgebra K L] [CompleteSpace L]
    [IsUltrametricDist L] (n : ℕ) (g : A) (f : Fin n → A) where
  isRationalDatum : IsRationalDatum g f
  baseMap : ContinuousAlgHom K A L
  coordinate : Fin n → L
  baseMap_denominator_mul_coordinate :
    ∀ i, baseMap g * coordinate i = baseMap (f i)
  isPowerBounded_coordinate : ∀ i, IsPowerBounded (coordinate i)
  isUnit_baseMap_denominator : IsUnit (baseMap g)
  lift : ∀ {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B], (φ : ContinuousAlgHom K A B) → (x : Fin n → B) →
      (∀ i, IsPowerBounded (x i)) → (∀ i, φ g * x i = φ (f i)) → ContinuousAlgHom K L B
  lift_comp_baseMap : ∀ {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [IsUltrametricDist B] (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)),
      (lift φ x hx hrel).comp baseMap = φ
  lift_coordinate : ∀ {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [IsUltrametricDist B] (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) (i : Fin n),
      lift φ x hx hrel (coordinate i) = x i
  hom_ext : ∀ {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
    (φ ψ : ContinuousAlgHom K L B), φ.comp baseMap = ψ.comp baseMap →
      (∀ i, φ (coordinate i) = ψ (coordinate i)) → φ = ψ

private theorem apply_le_one_of_isPowerBounded
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
    (x : Rigid.BerkovichSpectrumOver K B) {b : B} (hb : IsPowerBounded b) : x b ≤ 1 := by
  rcases hb with ⟨M, hM⟩
  by_contra h
  have hxb : 1 < x b := lt_of_not_ge h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hxb
  apply not_le_of_gt hn
  calc
    x b ^ n = x (b ^ n) := (map_pow x.toBerkovichSpectrum.seminorm b n).symm
    _ ≤ ‖b ^ n‖ := BerkovichSpectrum.le_norm B x.toBerkovichSpectrum _
    _ ≤ M := hM ⟨n, rfl⟩

private noncomputable def completedResidueContinuousAlgHom
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    (x : Rigid.BerkovichSpectrumOver K B) :
    ContinuousAlgHom K B (CompletedResidueField x) where
  toAlgHom := completedResidueAlgHom x
  cont :=
    ((completedResidueAlgHom x).toLinearMap.mkContinuous 1
      (fun b ↦ by
        change ‖completedResidueAlgHom x b‖ ≤ 1 * ‖b‖
        rw [norm_completedResidueAlgHom]
        simpa using le_norm K B x b)).continuous

@[simp]
private theorem completedResidueContinuousAlgHom_apply
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    (x : Rigid.BerkovichSpectrumOver K B) (b : B) :
    completedResidueContinuousAlgHom K x b = completedResidueAlgHom x b := rfl

@[simp]
private theorem norm_completedResidueContinuousAlgHom
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    (x : Rigid.BerkovichSpectrumOver K B) (b : B) :
    ‖completedResidueContinuousAlgHom K x b‖ = x b :=
  norm_completedResidueAlgHom x b

private noncomputable def ofContinuousAlgHom
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
    {L : Type w} [NormedField L] [NormedAlgebra K L]
    (φ : ContinuousAlgHom K B L) (halg : ∀ r : K, ‖algebraMap K L r‖ = ‖r‖) :
    Rigid.BerkovichSpectrumOver K B where
  toBerkovichSpectrum :=
    { seminorm :=
        { toFun := fun b ↦ ‖φ b‖
          map_zero' := by simp
          add_le' := by intro a b; simpa only [map_add] using norm_add_le (φ a) (φ b)
          neg' := by simp
          map_one' := by simp
          map_mul' := by simp }
      le_norm' := fun b ↦ by
        change ‖φ b‖ ≤ ‖b‖
        apply contraction_of_isPowMul (f := φ.toRingHom) (fun z n _ ↦ norm_pow z n)
        exact SemilinearMapClass.bound_of_continuous φ φ.continuous }
  map_algebraMap' := by
    intro r
    change ‖φ (algebraMap K B r)‖ = ‖r‖
    calc
      ‖φ (algebraMap K B r)‖ = ‖algebraMap K L r‖ := congrArg norm (φ.commutes r)
      _ = ‖r‖ := halg r

namespace RationalDomain

variable {L : Type v} [NormedCommRing L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] {n : ℕ} {g : A} {f : Fin n → A}

private noncomputable def localizationSpectrumMap
    (P : RationalLocalizationPresentation K A L n g f) :
    Rigid.BerkovichSpectrumOver K L → RationalDomain K A g f := fun x ↦
  ⟨comapContinuous K A P.baseMap x, by
    intro i
    change x (P.baseMap (f i)) ≤ x (P.baseMap g)
    rw [← P.baseMap_denominator_mul_coordinate i, BerkovichSpectrum.map_mul]
    exact mul_le_of_le_one_right
      (BerkovichSpectrum.nonneg _ x.toBerkovichSpectrum _)
      (apply_le_one_of_isPowerBounded K x (P.isPowerBounded_coordinate i))⟩

@[simp]
private theorem localizationSpectrumMap_apply
    (P : RationalLocalizationPresentation K A L n g f)
    (x : Rigid.BerkovichSpectrumOver K L) (a : A) :
    ((localizationSpectrumMap K A P x).1 : A → ℝ) a = x (P.baseMap a) := rfl

private theorem continuous_localizationSpectrumMap
    (P : RationalLocalizationPresentation K A L n g f) :
    Continuous (localizationSpectrumMap K A P) := by
  apply Continuous.subtype_mk
  apply (continuous_iff_eval K A).2
  intro a
  exact Rigid.BerkovichSpectrumOver.continuous_eval K L (P.baseMap a)

private noncomputable def rationalDomainCoordinate
    (x : RationalDomain K A g f) : Fin n → CompletedResidueField x.1 := fun i ↦
  completedResidueContinuousAlgHom K x.1 (f i) /
    completedResidueContinuousAlgHom K x.1 g

private theorem rationalDomainCoordinate_isPowerBounded
    (P : RationalLocalizationPresentation K A L n g f)
    (x : RationalDomain K A g f) (i : Fin n) :
    IsPowerBounded (rationalDomainCoordinate K A x i) := by
  apply isPowerBounded_of_norm_le_one
  rw [rationalDomainCoordinate, norm_div,
    norm_completedResidueContinuousAlgHom, norm_completedResidueContinuousAlgHom]
  exact (div_le_one₀ (lt_of_le_of_ne (nonneg K A x.1 g)
    (Ne.symm (denominator_ne_zero K A P.isRationalDatum x)))).2 (x.2 i)

private theorem completedResidue_denominator_ne_zero
    (P : RationalLocalizationPresentation K A L n g f)
    (x : RationalDomain K A g f) : completedResidueContinuousAlgHom K x.1 g ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_completedResidueContinuousAlgHom]
  exact denominator_ne_zero K A P.isRationalDatum x

private theorem rationalDomainCoordinate_relation
    (P : RationalLocalizationPresentation K A L n g f)
    (x : RationalDomain K A g f) (i : Fin n) :
    completedResidueContinuousAlgHom K x.1 g * rationalDomainCoordinate K A x i =
      completedResidueContinuousAlgHom K x.1 (f i) :=
  mul_div_cancel₀ _ (completedResidue_denominator_ne_zero K A P x)

private noncomputable def rationalDomainLift
    (P : RationalLocalizationPresentation K A L n g f) (x : RationalDomain K A g f) :
    ContinuousAlgHom K L (CompletedResidueField x.1) :=
  P.lift (completedResidueContinuousAlgHom K x.1) (rationalDomainCoordinate K A x)
    (rationalDomainCoordinate_isPowerBounded K A P x)
    (rationalDomainCoordinate_relation K A P x)

@[simp]
private theorem rationalDomainLift_baseMap
    (P : RationalLocalizationPresentation K A L n g f)
    (x : RationalDomain K A g f) (a : A) :
    rationalDomainLift K A P x (P.baseMap a) = completedResidueContinuousAlgHom K x.1 a := by
  exact congrArg (fun ψ : ContinuousAlgHom K A (CompletedResidueField x.1) ↦ ψ a)
    (P.lift_comp_baseMap (completedResidueContinuousAlgHom K x.1)
      (rationalDomainCoordinate K A x) (rationalDomainCoordinate_isPowerBounded K A P x)
      (rationalDomainCoordinate_relation K A P x))

@[simp]
private theorem rationalDomainLift_coordinate
    (P : RationalLocalizationPresentation K A L n g f)
    (x : RationalDomain K A g f) (i : Fin n) :
    rationalDomainLift K A P x (P.coordinate i) = rationalDomainCoordinate K A x i :=
  P.lift_coordinate (completedResidueContinuousAlgHom K x.1)
    (rationalDomainCoordinate K A x) (rationalDomainCoordinate_isPowerBounded K A P x)
    (rationalDomainCoordinate_relation K A P x) i

private noncomputable def rationalDomainSpectrumMap
    (P : RationalLocalizationPresentation K A L n g f) :
    RationalDomain K A g f → Rigid.BerkovichSpectrumOver K L := fun x ↦
  ofContinuousAlgHom K (rationalDomainLift K A P x) (norm_algebraMap_completedResidueField x.1)

private theorem localizationSpectrumMap_rightInverse
    (P : RationalLocalizationPresentation K A L n g f) :
    Function.RightInverse (rationalDomainSpectrumMap K A P) (localizationSpectrumMap K A P) := by
  intro x
  apply Subtype.ext
  apply ext K A
  intro a
  change ‖rationalDomainLift K A P x (P.baseMap a)‖ = x.1 a
  rw [rationalDomainLift_baseMap, norm_completedResidueContinuousAlgHom]

private theorem localizationSpectrumMap_leftInverse
    (P : RationalLocalizationPresentation K A L n g f) :
    Function.LeftInverse (rationalDomainSpectrumMap K A P) (localizationSpectrumMap K A P) := by
  intro y
  let x : RationalDomain K A g f := localizationSpectrumMap K A P y
  let base : A →ₐ[K] L := P.baseMap
  have hxy : ∀ a, x.1 a = y (base a) := fun _ ↦ rfl
  let jAlg := completedResidueFieldAlgHom base x.1 y hxy
  let j : ContinuousAlgHom K (CompletedResidueField x.1) (CompletedResidueField y) :=
    { toAlgHom := jAlg
      cont := (isometry_completedResidueFieldAlgHom base x.1 y hxy).continuous }
  let evalY := completedResidueContinuousAlgHom K y
  have hj : j.comp (rationalDomainLift K A P x) = evalY := by
    apply P.hom_ext
    · apply ContinuousAlgHom.ext
      intro a
      change j (rationalDomainLift K A P x (P.baseMap a)) = evalY (P.baseMap a)
      rw [rationalDomainLift_baseMap]
      change jAlg (completedResidueAlgHom x.1 a) = completedResidueAlgHom y (base a)
      exact completedResidueFieldMap_completedResidueMap base x.1 y hxy a
    · intro i
      change j (rationalDomainLift K A P x (P.coordinate i)) = evalY (P.coordinate i)
      rw [rationalDomainLift_coordinate]
      change jAlg (rationalDomainCoordinate K A x i) = completedResidueAlgHom y (P.coordinate i)
      rw [rationalDomainCoordinate]
      change jAlg (completedResidueAlgHom x.1 (f i) / completedResidueAlgHom x.1 g) =
        completedResidueAlgHom y (P.coordinate i)
      rw [map_div₀]
      change completedResidueFieldMap base x.1 y hxy (completedResidueMap x.1 (f i)) /
          completedResidueFieldMap base x.1 y hxy (completedResidueMap x.1 g) =
        completedResidueMap y (P.coordinate i)
      rw [completedResidueFieldMap_completedResidueMap,
        completedResidueFieldMap_completedResidueMap]
      have hden : completedResidueAlgHom y (P.baseMap g) ≠ 0 :=
        (P.isUnit_baseMap_denominator.map (completedResidueAlgHom y).toRingHom).ne_zero
      apply (div_eq_iff hden).2
      have hrel := congrArg (fun b : L ↦ completedResidueAlgHom y b)
        (P.baseMap_denominator_mul_coordinate i)
      simpa [base, mul_comm] using hrel.symm
  apply ext K L
  intro b
  change ‖rationalDomainLift K A P x b‖ = y b
  rw [← norm_completedResidueContinuousAlgHom K y b]
  have hjb := congrArg (fun ψ : ContinuousAlgHom K L (CompletedResidueField y) ↦ ψ b) hj
  rw [← hjb]
  change ‖rationalDomainLift K A P x b‖ = ‖jAlg (rationalDomainLift K A P x b)‖
  symm
  exact (isometry_completedResidueFieldAlgHom base x.1 y hxy).norm_map_of_map_zero
    (_root_.map_zero jAlg) _

/-- The relative spectrum of a rational-localization presentation is its rational domain. -/
noncomputable def localizationSpectrumHomeomorph
    (P : RationalLocalizationPresentation K A L n g f) :
    Rigid.BerkovichSpectrumOver K L ≃ₜ RationalDomain K A g f := by
  have hbij : Function.Bijective (localizationSpectrumMap K A P) :=
    ⟨(localizationSpectrumMap_leftInverse K A P).injective,
      (localizationSpectrumMap_rightInverse K A P).surjective⟩
  have hhome : IsHomeomorph (localizationSpectrumMap K A P) :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨continuous_localizationSpectrumMap K A P, hbij⟩
  exact hhome.homeomorph (localizationSpectrumMap K A P)

/-- Evaluation along the rational-localization homeomorphism is pullback along the base map. -/
@[simp]
theorem localizationSpectrumHomeomorph_apply_baseMap
    (P : RationalLocalizationPresentation K A L n g f)
    (x : Rigid.BerkovichSpectrumOver K L) (a : A) :
    ((localizationSpectrumHomeomorph K A P x).1 : A → ℝ) a = x (P.baseMap a) := by
  change ((localizationSpectrumMap K A P x).1 : A → ℝ) a = _
  rfl

end RationalDomain

end Rigid.BerkovichSpectrumOver
