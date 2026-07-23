import Rigid.AffinoidAlgebra.RationalRestriction
import Rigid.AffinoidAlgebra.SpectralRadius
import Rigid.AffinoidSpectrum.RationalBasis
import Rigid.Berkovich.Unit

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Restriction between rational subdomains

This file connects the concrete rational-localization algebra to its Berkovich rational domain.
The first application is the denominator part of restriction: if `U ⊆ V`, then the denominator
defining `V` becomes a unit in the algebra of functions on `U`.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain

/-- A Berkovich point of the section algebra restricts to a point of the ambient affinoid
algebra. -/
noncomputable def ambientPoint (U : AffinoidRationalSubdomain K A)
    (y : BerkovichSpectrumOver K U.Sections) : BerkovichSpectrumOver K A :=
  BerkovichSpectrumOver.comapContinuous K A
    (RationalLocalization.baseMap K A U.n U.g U.f) y

@[simp]
theorem ambientPoint_apply (U : AffinoidRationalSubdomain K A)
    (y : BerkovichSpectrumOver K U.Sections) (a : A) :
    ambientPoint K A U y a = y (RationalLocalization.baseMap K A U.n U.g U.f a) :=
  rfl

/-- The ambient point underlying a point of the section algebra lies in the rational domain. -/
theorem ambientPoint_mem_carrier (U : AffinoidRationalSubdomain K A)
    (y : BerkovichSpectrumOver K U.Sections) : ambientPoint K A U y ∈ U.carrier := by
  intro i
  change y (RationalLocalization.baseMap K A U.n U.g U.f (U.f i)) ≤
    y (RationalLocalization.baseMap K A U.n U.g U.f U.g)
  rw [← RationalLocalization.baseMap_denominator_mul_coordinate K A U.n U.g U.f i,
    BerkovichSpectrumOver.map_mul]
  exact mul_le_of_le_one_right
    (BerkovichSpectrumOver.nonneg K U.Sections y _)
    (IsPowerBounded.apply_le_one K y
      (RationalLocalization.isPowerBounded_coordinate K A U.n U.g U.f i))

/-- If `U ⊆ V`, the denominator defining `V` is invertible on the section algebra of `U`. -/
theorem isUnit_baseMap_denominator_of_subset
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier) :
    IsUnit (RationalLocalization.baseMap K A U.n U.g U.f V.g) := by
  rw [BerkovichSpectrumOver.isUnit_iff_forall_apply_ne_zero K U.Sections]
  intro y
  let x := ambientPoint K A U y
  have hxU : x ∈ U.carrier := ambientPoint_mem_carrier K A U y
  have hxV : x ∈ V.carrier := hUV hxU
  have hVg : x V.g ≠ 0 :=
    BerkovichSpectrumOver.RationalDomain.denominator_ne_zero K A V.isRational ⟨x, hxV⟩
  simpa [x] using hVg

/-- On the smaller rational domain, each quotient coordinate defining the larger domain has value
at most one at every Berkovich point.  The affinoid maximum-modulus theorem will turn this
pointwise estimate into power-boundedness. -/
theorem quotientCoordinate_apply_le_one_of_subset
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier)
    (i : Fin V.n) (y : BerkovichSpectrumOver K U.Sections) :
    y (RationalLocalization.quotientCoordinate K A
      (f := V.f)
      (RationalLocalization.baseMap K A U.n U.g U.f)
      (isUnit_baseMap_denominator_of_subset K A hUV) i) ≤ 1 := by
  let φ := RationalLocalization.baseMap K A U.n U.g U.f
  let hg := isUnit_baseMap_denominator_of_subset K A hUV
  let q := RationalLocalization.quotientCoordinate K A (f := V.f) φ hg i
  let x := ambientPoint K A U y
  have hxU : x ∈ U.carrier := ambientPoint_mem_carrier K A U y
  have hxV : x ∈ V.carrier := hUV hxU
  have hle : y (φ (V.f i)) ≤ y (φ V.g) := by
    simpa [x, φ] using hxV i
  have hne : y (φ V.g) ≠ 0 := by
    have hVg : x V.g ≠ 0 :=
      BerkovichSpectrumOver.RationalDomain.denominator_ne_zero K A V.isRational ⟨x, hxV⟩
    simpa [x, φ] using hVg
  have hpos : 0 < y (φ V.g) :=
    lt_of_le_of_ne (BerkovichSpectrumOver.nonneg K U.Sections y _) hne.symm
  have hrel : φ V.g * q = φ (V.f i) :=
    RationalLocalization.denominator_mul_quotientCoordinate K A (f := V.f) φ hg i
  change y q ≤ 1
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    y q * y (φ V.g) = y (φ V.g) * y q := mul_comm _ _
    _ = y (φ V.g * q) :=
      (BerkovichSpectrumOver.map_mul K U.Sections y _ _).symm
    _ = y (φ (V.f i)) := congrArg (fun z ↦ y z) hrel
    _ ≤ y (φ V.g) := hle
    _ = 1 * y (φ V.g) := (one_mul _).symm

/-- The quotient coordinates required for restriction have spectral radius at most one. -/
theorem quotientCoordinate_spectralRadius_le_one_of_subset
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier)
    (i : Fin V.n) :
    BerkovichSpectrum.spectralRadius U.Sections
      (RationalLocalization.quotientCoordinate K A
        (f := V.f)
        (RationalLocalization.baseMap K A U.n U.g U.f)
        (isUnit_baseMap_denominator_of_subset K A hUV) i) ≤ 1 := by
  by_cases hU : Nontrivial U.Sections
  · letI := hU
    apply (BerkovichSpectrumOver.forall_apply_le_one_iff_spectralRadius_le_one K
      U.Sections _).mp
    exact quotientCoordinate_apply_le_one_of_subset K A hUV i
  · haveI : Subsingleton U.Sections := not_nontrivial_iff_subsingleton.mp hU
    rw [Subsingleton.elim
      (RationalLocalization.quotientCoordinate K A
        (f := V.f)
        (RationalLocalization.baseMap K A U.n U.g U.f)
        (isUnit_baseMap_denominator_of_subset K A hUV) i) 0,
      BerkovichSpectrum.spectralRadius_zero]
    exact zero_le_one

/-- Once the pointwise maximum-modulus estimate is known to imply power-boundedness on the
section algebra, inclusion of rational domains produces the restriction homomorphism. -/
noncomputable def restrictionOfPointwisePowerBounded
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier)
    (hbounded : ∀ i : Fin V.n, IsPowerBounded
      (RationalLocalization.quotientCoordinate K A
        (f := V.f)
        (RationalLocalization.baseMap K A U.n U.g U.f)
        (isUnit_baseMap_denominator_of_subset K A hUV) i)) :
    ContinuousAlgHom K V.Sections U.Sections :=
  RationalLocalization.liftOfIsUnit K A
    (RationalLocalization.baseMap K A U.n U.g U.f)
    (isUnit_baseMap_denominator_of_subset K A hUV) hbounded

/-- Restriction follows once the boundary spectral-radius estimates are supplied with the
unit-ball integral certificates from Proposition 4.5.12. -/
noncomputable def restrictionOfUnitBallIntegralCertificates
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier)
    (hcertificate : ∀ i : Fin V.n,
      HasUnitBallIntegralCertificate K
        (RationalLocalization.quotientCoordinate K A
          (f := V.f)
          (RationalLocalization.baseMap K A U.n U.g U.f)
          (isUnit_baseMap_denominator_of_subset K A hUV) i)) :
    ContinuousAlgHom K V.Sections U.Sections :=
  restrictionOfPointwisePowerBounded K A hUV fun i ↦
    isPowerBounded_of_hasUnitBallIntegralCertificate K (hcertificate i)

/-- An algebra satisfying Proposition 4.5.12(ii) supports restriction from every larger rational
domain. -/
noncomputable def restrictionOfSpectralCriterion
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier)
    (hU : HasPowerBoundedSpectralCriterion U.Sections) :
    ContinuousAlgHom K V.Sections U.Sections :=
  restrictionOfPointwisePowerBounded K A hUV fun i ↦
    hU _ (quotientCoordinate_spectralRadius_le_one_of_subset K A hUV i)

@[simp]
theorem restrictionOfPointwisePowerBounded_comp_baseMap
    {U V : AffinoidRationalSubdomain K A} (hUV : U.carrier ⊆ V.carrier)
    (hbounded : ∀ i : Fin V.n, IsPowerBounded
      (RationalLocalization.quotientCoordinate K A
        (f := V.f)
        (RationalLocalization.baseMap K A U.n U.g U.f)
        (isUnit_baseMap_denominator_of_subset K A hUV) i)) :
    (restrictionOfPointwisePowerBounded K A hUV hbounded).comp
      (RationalLocalization.baseMap K A V.n V.g V.f) =
        RationalLocalization.baseMap K A U.n U.g U.f :=
  RationalLocalization.liftOfIsUnit_comp_baseMap K A _ _ _

/-- The conditional restriction construction is the identity for an equality inclusion. -/
@[simp]
theorem restrictionOfPointwisePowerBounded_id
    (U : AffinoidRationalSubdomain K A)
    (hbounded : ∀ i : Fin U.n, IsPowerBounded
      (RationalLocalization.quotientCoordinate K A
        (f := U.f)
        (RationalLocalization.baseMap K A U.n U.g U.f)
        (isUnit_baseMap_denominator_of_subset K A (U := U) (V := U) Set.Subset.rfl) i)) :
    restrictionOfPointwisePowerBounded K A (U := U) (V := U) Set.Subset.rfl hbounded =
      ContinuousAlgHom.id K U.Sections := by
  apply RationalLocalization.hom_ext_of_isUnit K A
    (restrictionOfPointwisePowerBounded K A Set.Subset.rfl hbounded)
    (ContinuousAlgHom.id K U.Sections)
  · have hbase := congrArg
      (fun q : ContinuousAlgHom K A U.Sections ↦ q U.g)
      (restrictionOfPointwisePowerBounded_comp_baseMap K A Set.Subset.rfl hbounded)
    change (restrictionOfPointwisePowerBounded K A Set.Subset.rfl hbounded)
      (RationalLocalization.baseMap K A U.n U.g U.f U.g) =
        RationalLocalization.baseMap K A U.n U.g U.f U.g at hbase
    rw [hbase]
    exact RationalLocalization.isUnit_baseMap_denominator
      K A U.n U.g U.f U.isRational
  · simp

/-- Conditional restrictions compose independently of the proofs of power-boundedness used to
construct them. -/
@[simp]
theorem restrictionOfPointwisePowerBounded_comp
    {U V W : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) (hWU : W.carrier ⊆ U.carrier)
    (hboundedUV : ∀ i : Fin V.n, IsPowerBounded
      (RationalLocalization.quotientCoordinate K A
        (f := V.f)
        (RationalLocalization.baseMap K A U.n U.g U.f)
        (isUnit_baseMap_denominator_of_subset K A hUV) i))
    (hboundedWU : ∀ i : Fin U.n, IsPowerBounded
      (RationalLocalization.quotientCoordinate K A
        (f := U.f)
        (RationalLocalization.baseMap K A W.n W.g W.f)
        (isUnit_baseMap_denominator_of_subset K A hWU) i))
    (hboundedWV : ∀ i : Fin V.n, IsPowerBounded
      (RationalLocalization.quotientCoordinate K A
        (f := V.f)
        (RationalLocalization.baseMap K A W.n W.g W.f)
        (isUnit_baseMap_denominator_of_subset K A (hWU.trans hUV)) i)) :
    (restrictionOfPointwisePowerBounded K A hWU hboundedWU).comp
        (restrictionOfPointwisePowerBounded K A hUV hboundedUV) =
      restrictionOfPointwisePowerBounded K A (hWU.trans hUV) hboundedWV := by
  apply RationalLocalization.hom_ext_of_isUnit K A
    ((restrictionOfPointwisePowerBounded K A hWU hboundedWU).comp
      (restrictionOfPointwisePowerBounded K A hUV hboundedUV))
    (restrictionOfPointwisePowerBounded K A (hWU.trans hUV) hboundedWV)
  · change IsUnit
      ((restrictionOfPointwisePowerBounded K A hWU hboundedWU)
        ((restrictionOfPointwisePowerBounded K A hUV hboundedUV)
          (RationalLocalization.baseMap K A V.n V.g V.f V.g)))
    have hUVg := congrArg (fun q : ContinuousAlgHom K A U.Sections ↦ q V.g)
      (restrictionOfPointwisePowerBounded_comp_baseMap K A hUV hboundedUV)
    have hWUg := congrArg (fun q : ContinuousAlgHom K A W.Sections ↦ q V.g)
      (restrictionOfPointwisePowerBounded_comp_baseMap K A hWU hboundedWU)
    change (restrictionOfPointwisePowerBounded K A hUV hboundedUV)
      (RationalLocalization.baseMap K A V.n V.g V.f V.g) =
        RationalLocalization.baseMap K A U.n U.g U.f V.g at hUVg
    change (restrictionOfPointwisePowerBounded K A hWU hboundedWU)
      (RationalLocalization.baseMap K A U.n U.g U.f V.g) =
        RationalLocalization.baseMap K A W.n W.g W.f V.g at hWUg
    rw [hUVg, hWUg]
    exact isUnit_baseMap_denominator_of_subset K A (hWU.trans hUV)
  · apply ContinuousAlgHom.ext
    intro a
    simp only [ContinuousAlgHom.comp_apply]
    have hUVa := congrArg (fun q : ContinuousAlgHom K A U.Sections ↦ q a)
      (restrictionOfPointwisePowerBounded_comp_baseMap K A hUV hboundedUV)
    have hWUa := congrArg (fun q : ContinuousAlgHom K A W.Sections ↦ q a)
      (restrictionOfPointwisePowerBounded_comp_baseMap K A hWU hboundedWU)
    have hWVa := congrArg (fun q : ContinuousAlgHom K A W.Sections ↦ q a)
      (restrictionOfPointwisePowerBounded_comp_baseMap K A (hWU.trans hUV) hboundedWV)
    change (restrictionOfPointwisePowerBounded K A hUV hboundedUV)
      (RationalLocalization.baseMap K A V.n V.g V.f a) =
        RationalLocalization.baseMap K A U.n U.g U.f a at hUVa
    change (restrictionOfPointwisePowerBounded K A hWU hboundedWU)
      (RationalLocalization.baseMap K A U.n U.g U.f a) =
        RationalLocalization.baseMap K A W.n W.g W.f a at hWUa
    change (restrictionOfPointwisePowerBounded K A (hWU.trans hUV) hboundedWV)
      (RationalLocalization.baseMap K A V.n V.g V.f a) =
        RationalLocalization.baseMap K A W.n W.g W.f a at hWVa
    rw [hUVa, hWUa, hWVa]

@[simp]
theorem restrictionOfSpectralCriterion_id
    (U : AffinoidRationalSubdomain K A)
    (hU : HasPowerBoundedSpectralCriterion U.Sections) :
    restrictionOfSpectralCriterion K A (U := U) (V := U) Set.Subset.rfl hU =
      ContinuousAlgHom.id K U.Sections := by
  unfold restrictionOfSpectralCriterion
  apply restrictionOfPointwisePowerBounded_id

@[simp]
theorem restrictionOfSpectralCriterion_comp
    {U V W : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) (hWU : W.carrier ⊆ U.carrier)
    (hU : HasPowerBoundedSpectralCriterion U.Sections)
    (hW : HasPowerBoundedSpectralCriterion W.Sections) :
    (restrictionOfSpectralCriterion K A hWU hW).comp
        (restrictionOfSpectralCriterion K A hUV hU) =
      restrictionOfSpectralCriterion K A (hWU.trans hUV) hW := by
  unfold restrictionOfSpectralCriterion
  apply restrictionOfPointwisePowerBounded_comp

end AffinoidRationalSubdomain

end Rigid
