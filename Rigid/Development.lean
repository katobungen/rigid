import Mathlib
import Rigid.AffinoidAlgebra.QuotientNorm
import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.UniversalProperty

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Rigid analytic geometry challenge

This declaration block is the target interface for a first formalization of rigid and Berkovich
analytic geometry. The Challenge module imports only mathlib; its Development counterpart may add
project imports while preserving the same declarations in namespace `RigidChallenge`.

We first work over a complete, nontrivially normed, nonarchimedean field and with *strict* affinoid
algebras. The intended construction order is:

1. Tate algebras and their Gauss norms;
2. affinoid algebras, rational localizations, and affinoid spectra;
3. the admissible topology and Tate acyclicity;
4. rigid spaces obtained by gluing affinoid spectra;
5. Berkovich spectra and Berkovich spaces;
6. comparison functors and an equivalence on suitable full subcategories.

The predicates defining the comparison subcategories below are provisional. Before proving the
comparison theorem, they must be matched to a precise theorem in the literature; see `PLAN.md`.
-/

open CategoryTheory
open Filter
open scoped Topology

universe u v w

namespace RigidChallenge

/-! ## Tate algebras -/

section TateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v)

/-- The underlying ring of the strict Tate algebra in variables indexed by `ι`.

Mathlib's restricted multivariate power series already give the correct underlying set: the
coefficients tend to zero along the cofinite filter. The missing work is the Gauss norm and its
analytic properties. The main development will initially assume that `ι` is finite. -/
abbrev TateAlgebra :=
  ↥(MvPowerSeries.IsRestricted.subring (R := K) (fun _ : ι ↦ (1 : ℝ)))

/-- The coordinate corresponding to a variable of the Tate algebra. -/
noncomputable def tateVariable (i : ι) : TateAlgebra K ι :=
  Rigid.tateVariable K ι i

/-- The Gauss norm, i.e. the supremum of the norms of the coefficients. -/
noncomputable def gaussNorm : TateAlgebra K ι → ℝ :=
  Rigid.gaussNorm K ι

noncomputable instance tateAlgebraNorm : Norm (TateAlgebra K ι) :=
  ⟨gaussNorm K ι⟩

noncomputable instance tateAlgebraNormedCommRing : NormedCommRing (TateAlgebra K ι) :=
  Rigid.tateAlgebraNormedCommRing K ι

noncomputable instance tateAlgebraAlgebra : Algebra K (TateAlgebra K ι) :=
  Rigid.tateAlgebraAlgebra K ι

noncomputable instance tateAlgebraNormedAlgebra : NormedAlgebra K (TateAlgebra K ι) :=
  Rigid.tateAlgebraNormedAlgebra K ι

noncomputable instance tateAlgebraIsUltrametricDist : IsUltrametricDist (TateAlgebra K ι) :=
  Rigid.tateAlgebraIsUltrametricDist K ι

variable [hι : Finite ι]

include hι

noncomputable instance tateAlgebraComplete [CompleteSpace K] : CompleteSpace (TateAlgebra K ι) :=
  Rigid.tateAlgebraComplete K ι

/-- The Gauss norm is the supremum norm on coefficients. -/
theorem norm_eq_sSup_coeff (f : TateAlgebra K ι) :
    ‖f‖ = sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) :=
  Rigid.norm_eq_sSup_coeff K ι f

/-- The Gauss norm is multiplicative over a nonarchimedean field. -/
theorem norm_mul (f g : TateAlgebra K ι) : ‖f * g‖ = ‖f‖ * ‖g‖ := sorry

/-- The universal property of the strict Tate algebra.

A tuple in the closed unit polydisc of a complete nonarchimedean Banach `K`-algebra determines a
unique continuous `K`-algebra homomorphism.

The codomain is `NormedCommRing` rather than `SeminormedCommRing`: Hausdorffness is needed for
uniqueness, since a continuous algebra homomorphism into a merely seminormed codomain is not
determined by its values on the coordinates. -/
theorem existsUnique_continuousAlgHom_of_norm_le_one [CompleteSpace K]
    {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (x : ι → A) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃! φ : ContinuousAlgHom K (TateAlgebra K ι) A,
      ∀ i, φ (tateVariable K ι i) = x i :=
  Rigid.existsUnique_continuousAlgHom_of_norm_le_one K ι x hx

end TateAlgebra

/-! ## Quotient norms -/

section QuotientNorm

variable {B : Type v} [hB : SeminormedAddCommGroup B]
variable {C : Type w}

include hB

/-- The quotient seminorm induced by a map, defined as the infimum of source norms in a fiber.
It has the expected behavior when the map is surjective. -/
noncomputable def quotientNorm (f : B → C) (y : C) : ℝ :=
  Rigid.quotientNorm f y

variable [hC : SeminormedAddCommGroup C]

include hC

/-- A map is a quotient-norm presentation when it is surjective and the given target norm is exactly
the induced quotient norm. -/
def IsQuotientNorm (f : B → C) : Prop :=
  Function.Surjective f ∧ ∀ y : C, ‖y‖ = quotientNorm f y

/-- The target norm is equivalent to the induced quotient norm when the map is surjective and the
two norms bound one another up to positive multiplicative constants. -/
def IsEquivalentQuotientNorm (f : B → C) : Prop :=
  Function.Surjective f ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ y : C, c₁ * quotientNorm f y ≤ ‖y‖ ∧ ‖y‖ ≤ c₂ * quotientNorm f y

namespace IsQuotientNorm

variable {f : B → C}

/-- A quotient-norm presentation is surjective. -/
theorem surjective (hf : IsQuotientNorm f) : Function.Surjective f :=
  Rigid.IsQuotientNorm.surjective hf

/-- The target norm equals the induced quotient norm. -/
theorem norm_eq_quotientNorm (hf : IsQuotientNorm f) (y : C) :
    ‖y‖ = quotientNorm f y :=
  Rigid.IsQuotientNorm.norm_eq_quotientNorm hf y

/-- The target norm is the infimum of the source norms in each fiber. -/
theorem norm_eq_sInf_fiber (hf : IsQuotientNorm f) (y : C) :
    ‖y‖ = sInf ((fun x : B ↦ ‖x‖) '' {x | f x = y}) :=
  Rigid.IsQuotientNorm.norm_eq_sInf_fiber hf y

/-- A quotient-norm presentation is norm-nonincreasing. -/
theorem norm_le (hf : IsQuotientNorm f) (x : B) : ‖f x‖ ≤ ‖x‖ :=
  Rigid.IsQuotientNorm.norm_le hf x

/-- Every target element has lifts with norm arbitrarily close to its quotient norm. -/
theorem exists_preimage_norm_lt (hf : IsQuotientNorm f) {ε : ℝ} (hε : 0 < ε) (y : C) :
    ∃ x : B, f x = y ∧ ‖x‖ < ‖y‖ + ε :=
  Rigid.IsQuotientNorm.exists_preimage_norm_lt hf hε y

/-- Exact equality with the quotient norm implies equivalence with it. -/
theorem isEquivalentQuotientNorm (hf : IsQuotientNorm f) :
    IsEquivalentQuotientNorm f :=
  Rigid.IsQuotientNorm.isEquivalentQuotientNorm hf

end IsQuotientNorm

namespace IsEquivalentQuotientNorm

variable {f : B → C}

/-- Equivalence with a quotient norm includes surjectivity. -/
theorem surjective (hf : IsEquivalentQuotientNorm f) : Function.Surjective f :=
  Rigid.IsEquivalentQuotientNorm.surjective hf

end IsEquivalentQuotientNorm

end QuotientNorm

section OpenMapping

variable {K : Type u} [NontriviallyNormedField K]
variable {B : Type v} [NormedAddCommGroup B] [NormedSpace K B] [CompleteSpace B]
variable {C : Type w} [NormedAddCommGroup C] [NormedSpace K C] [CompleteSpace C]

/-- A surjective continuous linear map between Banach spaces makes the given target norm equivalent
to the quotient norm. -/
theorem isEquivalentQuotientNorm_of_surjective (f : B →L[K] C) (hf : Function.Surjective f) :
    IsEquivalentQuotientNorm (f : B → C) :=
  Rigid.isEquivalentQuotientNorm_of_surjective f hf

/-- For a continuous linear map between Banach spaces, equivalence with the quotient norm is
precisely surjectivity. -/
theorem isEquivalentQuotientNorm_iff_surjective (f : B →L[K] C) :
    IsEquivalentQuotientNorm (f : B → C) ↔ Function.Surjective f :=
  Rigid.isEquivalentQuotientNorm_iff_surjective f

/-- A surjective continuous algebra homomorphism between Banach algebras gives an equivalent
quotient norm on its target. -/
theorem isEquivalentQuotientNorm_of_surjective_continuousAlgHom
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    {C : Type w} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    (f : ContinuousAlgHom K B C) (hf : Function.Surjective f) :
    IsEquivalentQuotientNorm (f : B → C) :=
  Rigid.isEquivalentQuotientNorm_of_surjective_continuousAlgHom f hf

/-- For a continuous homomorphism between Banach algebras, equivalence with the quotient norm is
precisely surjectivity. -/
theorem isEquivalentQuotientNorm_continuousAlgHom_iff_surjective
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    {C : Type w} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    (f : ContinuousAlgHom K B C) :
    IsEquivalentQuotientNorm (f : B → C) ↔ Function.Surjective f :=
  Rigid.isEquivalentQuotientNorm_continuousAlgHom_iff_surjective f

end OpenMapping

section RationalDatum

/-- An element of a seminormed ring is power-bounded if the norms of all its nonnegative powers
have a common upper bound. -/
def IsPowerBounded {B : Type v} [SeminormedRing B] (x : B) : Prop :=
  Rigid.IsPowerBounded x

/-- An element of norm at most one is power-bounded. -/
theorem isPowerBounded_of_norm_le_one {B : Type v} [SeminormedRing B] {x : B}
    (hx : ‖x‖ ≤ 1) : IsPowerBounded x :=
  Rigid.isPowerBounded_of_norm_le_one hx

@[simp]
theorem isPowerBounded_zero {B : Type v} [SeminormedRing B] :
    IsPowerBounded (0 : B) :=
  Rigid.isPowerBounded_zero

@[simp]
theorem isPowerBounded_one {B : Type v} [SeminormedRing B] :
    IsPowerBounded (1 : B) :=
  Rigid.isPowerBounded_one

/-- The numerator and denominator of a rational localization form a rational datum when together
they generate the unit ideal. -/
def IsRationalDatum {A : Type v} [CommRing A] {n : ℕ} (g : A) (f : Fin n → A) : Prop :=
  Rigid.IsRationalDatum g f

end RationalDatum

/-! ## Affinoid algebras and affinoid spectra -/

section AffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

section Algebraic

variable (A : Type v) [CommRing A] [Algebra K A]

/-- A presentation of a strict affinoid algebra as a quotient of a finite Tate algebra. -/
structure AffinoidPresentation
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [CommRing A] [Algebra K A] where
  n : ℕ
  ideal : Ideal (TateAlgebra K (Fin n))
  equiv : (TateAlgebra K (Fin n) ⧸ ideal) ≃ₐ[K] A

namespace AffinoidPresentation

/-- The surjective algebra homomorphism associated with an affinoid presentation. -/
noncomputable def toAlgHom (P : AffinoidPresentation K A) :
    TateAlgebra K (Fin P.n) →ₐ[K] A :=
  P.equiv.toAlgHom.comp (Ideal.Quotient.mkₐ K P.ideal)

/-- The algebra homomorphism associated with an affinoid presentation is surjective. -/
theorem toAlgHom_surjective (P : AffinoidPresentation K A) :
    Function.Surjective P.toAlgHom := sorry

/-- The quotient topology transported to the target of an affinoid presentation. -/
@[reducible]
noncomputable def residueTopology (P : AffinoidPresentation K A) : TopologicalSpace A :=
  TopologicalSpace.coinduced P.toAlgHom inferInstance

/-- The quotient topology of an affinoid algebra is independent of its presentation. -/
theorem residueTopology_eq (P Q : AffinoidPresentation K A) :
    P.residueTopology = Q.residueTopology := sorry

/-- The quotient topology makes the target a topological ring. -/
theorem residueIsTopologicalRing (P : AffinoidPresentation K A) :
    @IsTopologicalRing A P.residueTopology _ := sorry

/-- Scalar multiplication by the ground field is continuous for the quotient topology. -/
theorem residueContinuousSMul (P : AffinoidPresentation K A) :
    @ContinuousSMul K A _ _ P.residueTopology := sorry

/-- The residue norm associated with an affinoid presentation, bundled as a normed commutative ring
structure. Unlike the induced topology, this norm can depend on the presentation. -/
@[reducible]
noncomputable def residueNormedCommRing (P : AffinoidPresentation K A) :
    NormedCommRing A := sorry

/-- The residue norm makes the target a normed algebra over the ground field. -/
@[reducible]
noncomputable def residueNormedAlgebra (P : AffinoidPresentation K A) :
    letI := P.residueNormedCommRing
    NormedAlgebra K A := sorry

/-- The residue norm is complete. -/
theorem residueCompleteSpace (P : AffinoidPresentation K A) :
    letI := P.residueNormedCommRing
    CompleteSpace A := sorry

/-- The residue norm is nonarchimedean. -/
theorem residueIsUltrametricDist (P : AffinoidPresentation K A) :
    letI := P.residueNormedCommRing
    IsUltrametricDist A := sorry

/-- The metric topology of the residue norm is the quotient topology. -/
theorem residueNormedCommRing_topology_eq (P : AffinoidPresentation K A) :
    (letI := P.residueNormedCommRing
     inferInstance : TopologicalSpace A) = P.residueTopology := sorry

/-- The presentation map gives the target its exact quotient norm when the residue norm is used. -/
theorem isQuotientNorm_toAlgHom (P : AffinoidPresentation K A) :
    letI := P.residueNormedCommRing
    IsQuotientNorm (P.toAlgHom : TateAlgebra K (Fin P.n) → A) := sorry

end AffinoidPresentation

/-- A strict `K`-affinoid algebra is a `K`-algebra isomorphic to a quotient of a Tate algebra in
finitely many variables. No norm or topology on the algebra is part of this predicate. -/
def IsAffinoidAlgebra
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [CommRing A] [Algebra K A] : Prop :=
  Nonempty (AffinoidPresentation K A)

namespace IsAffinoidAlgebra

/-- Choose a quotient presentation of an affinoid algebra. -/
noncomputable def presentation (hA : IsAffinoidAlgebra K A) : AffinoidPresentation K A :=
  Classical.choice hA

end IsAffinoidAlgebra

/-- The canonical topology of an affinoid algebra, obtained from any quotient presentation. -/
@[reducible]
noncomputable def affinoidTopology (hA : IsAffinoidAlgebra K A) : TopologicalSpace A :=
  hA.presentation.residueTopology

/-- The canonical topology makes an affinoid algebra a topological ring. -/
theorem affinoidIsTopologicalRing (hA : IsAffinoidAlgebra K A) :
    @IsTopologicalRing A (affinoidTopology K A hA) _ := sorry

/-- Scalar multiplication by the ground field is continuous for the canonical topology. -/
theorem affinoidContinuousSMul (hA : IsAffinoidAlgebra K A) :
    @ContinuousSMul K A _ _ (affinoidTopology K A hA) := sorry

/-- The canonical topology agrees with the quotient topology from every presentation. -/
theorem affinoidTopology_eq_residueTopology (hA : IsAffinoidAlgebra K A)
    (P : AffinoidPresentation K A) : affinoidTopology K A hA = P.residueTopology := sorry

/-- Algebra homomorphisms between affinoid algebras are continuous for their canonical quotient
topologies. -/
theorem continuous_for_affinoidTopology_of_isAffinoidAlgebra
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    @Continuous A B (affinoidTopology K A hA) (affinoidTopology K B hB) f := sorry

/-- Unpack an affinoid algebra as a surjective algebraic presentation by a finite Tate algebra. -/
theorem exists_surjective_presentation_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (π : TateAlgebra K (Fin n) →ₐ[K] A), Function.Surjective π := sorry

/-- Unpack the defining quotient presentation of an affinoid algebra. -/
theorem exists_quotient_presentation_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (I : Ideal (TateAlgebra K (Fin n))),
      Nonempty ((TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) := sorry

/-- Affinoid algebras are Noetherian. -/
theorem isNoetherianRing_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing A := sorry

end Algebraic

section BanachRealization

/-- Any complete nonarchimedean normed-algebra topology on an affinoid algebra agrees with its
canonical quotient topology. -/
theorem topology_eq_affinoidTopology_of_isAffinoidAlgebra
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (hA : IsAffinoidAlgebra K A) :
    (inferInstance : TopologicalSpace A) = affinoidTopology K A hA := sorry

/-- The norm of an affinoid algebra is equivalent to the quotient norm induced by a finite Tate
algebra presentation. -/
theorem exists_equivalent_quotientNorm_presentation_of_isAffinoidAlgebra
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) A),
      IsEquivalentQuotientNorm (π : TateAlgebra K (Fin n) → A) := sorry

/-- Every algebra homomorphism between complete normed realizations of strict affinoid algebras is
continuous. -/
theorem continuous_of_isAffinoidAlgebra
    {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [IsUltrametricDist B] (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) : Continuous f := sorry

end BanachRealization

variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- A rational localization `A⟨T₁, ..., Tₙ⟩ / (gTᵢ - fᵢ)`.

The condition that `g, f₁, ..., fₙ` generate the unit ideal will be carried by rational-domain
constructors rather than by this raw algebra construction. -/
noncomputable def RationalLocalization
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (n : ℕ) (g : A) (f : Fin n → A) : Type v := sorry

noncomputable instance rationalLocalizationNormedCommRing (n : ℕ) (g : A) (f : Fin n → A) :
    NormedCommRing (RationalLocalization K A n g f) := sorry

noncomputable instance rationalLocalizationAlgebra (n : ℕ) (g : A) (f : Fin n → A) :
    Algebra A (RationalLocalization K A n g f) := sorry

noncomputable instance rationalLocalizationNormedAlgebra (n : ℕ) (g : A) (f : Fin n → A) :
    NormedAlgebra K (RationalLocalization K A n g f) := sorry

noncomputable instance rationalLocalizationCompleteSpace (n : ℕ) (g : A) (f : Fin n → A) :
    CompleteSpace (RationalLocalization K A n g f) := sorry

noncomputable instance rationalLocalizationIsUltrametricDist
    (n : ℕ) (g : A) (f : Fin n → A) :
    IsUltrametricDist (RationalLocalization K A n g f) := sorry

noncomputable instance rationalLocalizationIsScalarTower
    (n : ℕ) (g : A) (f : Fin n → A) :
    IsScalarTower K A (RationalLocalization K A n g f) := sorry

namespace RationalLocalization

/-- The canonical continuous map from the original algebra to its rational localization. -/
noncomputable def baseMap (n : ℕ) (g : A) (f : Fin n → A) :
    ContinuousAlgHom K A (RationalLocalization K A n g f) := sorry

@[simp]
theorem baseMap_apply (n : ℕ) (g : A) (f : Fin n → A) (a : A) :
    baseMap K A n g f a = algebraMap A (RationalLocalization K A n g f) a := sorry

/-- The coordinate representing the quotient `fᵢ / g` in a rational localization. -/
noncomputable def coordinate (n : ℕ) (g : A) (f : Fin n → A) (i : Fin n) :
    RationalLocalization K A n g f := sorry

/-- The defining relation `gTᵢ = fᵢ` of a rational localization. -/
@[simp]
theorem baseMap_denominator_mul_coordinate (n : ℕ) (g : A) (f : Fin n → A) (i : Fin n) :
    baseMap K A n g f g * coordinate K A n g f i = baseMap K A n g f (f i) := sorry

/-- Every coordinate of a rational localization is power-bounded. -/
theorem isPowerBounded_coordinate (n : ℕ) (g : A) (f : Fin n → A) (i : Fin n) :
    IsPowerBounded (coordinate K A n g f i) := sorry

/-- The denominator becomes a unit when the numerator and denominator generate the unit ideal. -/
theorem isUnit_baseMap_denominator (n : ℕ) (g : A) (f : Fin n → A)
    (h : IsRationalDatum g f) : IsUnit (baseMap K A n g f g) := sorry

/-- Map a rational localization to a complete nonarchimedean algebra by choosing power-bounded
images of its coordinates that satisfy the defining relations. -/
noncomputable def lift
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) :
    ContinuousAlgHom K (RationalLocalization K A n g f) B := sorry

@[simp]
theorem lift_comp_baseMap
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) :
    (lift K A n g f φ x hx hrel).comp (baseMap K A n g f) = φ := sorry

@[simp]
theorem lift_coordinate
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) (i : Fin n) :
    lift K A n g f φ x hx hrel (coordinate K A n g f i) = x i := sorry

/-- Continuous homomorphisms from a rational localization agree if they agree on the original
algebra and on every coordinate. -/
@[ext]
theorem hom_ext
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
    (n : ℕ) (g : A) (f : Fin n → A)
    (φ ψ : ContinuousAlgHom K (RationalLocalization K A n g f) B)
    (hbase : φ.comp (baseMap K A n g f) = ψ.comp (baseMap K A n g f))
    (hcoordinate : ∀ i, φ (coordinate K A n g f i) = ψ (coordinate K A n g f i)) :
    φ = ψ := sorry

/-- The lift from a rational localization is the unique continuous homomorphism with the prescribed
values on the original algebra and the coordinates. -/
theorem lift_unique
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i))
    (ψ : ContinuousAlgHom K (RationalLocalization K A n g f) B)
    (hbase : ψ.comp (baseMap K A n g f) = φ)
    (hcoordinate : ∀ i, ψ (coordinate K A n g f i) = x i) :
    ψ = lift K A n g f φ x hx hrel := by
  apply hom_ext K A n g f
  · exact hbase.trans (lift_comp_baseMap K A n g f φ x hx hrel).symm
  · intro i
    exact (hcoordinate i).trans (lift_coordinate K A n g f φ x hx hrel i).symm

/-- Universal mapping property of a rational localization. -/
theorem existsUnique_lift
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) :
    ∃! ψ : ContinuousAlgHom K (RationalLocalization K A n g f) B,
      ψ.comp (baseMap K A n g f) = φ ∧
        ∀ i, ψ (coordinate K A n g f i) = x i := by
  refine ⟨lift K A n g f φ x hx hrel, ?_, ?_⟩
  · exact ⟨lift_comp_baseMap K A n g f φ x hx hrel,
      lift_coordinate K A n g f φ x hx hrel⟩
  · intro ψ hψ
    exact lift_unique K A n g f φ x hx hrel ψ hψ.1 hψ.2

end RationalLocalization

/-- A rational localization of an affinoid algebra is affinoid. -/
theorem isAffinoidAlgebra_rationalLocalization (hA : IsAffinoidAlgebra K A)
    (n : ℕ) (g : A) (f : Fin n → A) :
    IsAffinoidAlgebra K (RationalLocalization K A n g f) := sorry

/-- A point of the Berkovich spectrum of `A`: a bounded multiplicative seminorm extending the norm
on `K`. The bound is normalized to be contractive. -/
structure BerkovichSpectrum where
  seminorm : MulRingSeminorm A
  map_algebraMap' : ∀ x : K, seminorm (algebraMap K A x) = ‖x‖
  le_norm' : ∀ a : A, seminorm a ≤ ‖a‖

instance berkovichSpectrumCoeFun : CoeFun (BerkovichSpectrum K A) (fun _ ↦ A → ℝ) :=
  ⟨fun x ↦ x.seminorm⟩

/-- The weakest topology for which evaluation at every element of `A` is continuous. -/
noncomputable instance berkovichSpectrumTopologicalSpace :
    TopologicalSpace (BerkovichSpectrum K A) := sorry

/-- Convergence in the Berkovich spectrum is pointwise convergence of seminorms. -/
theorem tendsto_iff_eval {l : Filter (BerkovichSpectrum K A)} {x : BerkovichSpectrum K A} :
    Tendsto id l (𝓝 x) ↔ ∀ a : A, Tendsto (fun y ↦ y a) l (𝓝 (x a)) := sorry

/-- The Berkovich spectrum of a nonzero affinoid algebra is nonempty. -/
theorem nonempty_berkovichSpectrum [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    Nonempty (BerkovichSpectrum K A) := sorry

/-- The Berkovich spectrum of an affinoid algebra is compact. -/
theorem isCompact_univ_berkovichSpectrum (hA : IsAffinoidAlgebra K A) :
    IsCompact (Set.univ : Set (BerkovichSpectrum K A)) := sorry

/-- The Berkovich spectrum is Hausdorff. -/
noncomputable instance berkovichSpectrumT2Space : T2Space (BerkovichSpectrum K A) := sorry

end AffinoidAlgebra

/-! ## Global rigid and Berkovich spaces

These declarations mark the intended global interfaces. Their implementations should eventually be
bundled locally ringed geometric objects, not opaque point sets. Their categories should use the
corresponding analytic morphisms.
-/

section GlobalSpaces

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A rigid analytic space over `K`, locally modeled on strict affinoid spectra in an admissible
Grothendieck topology. -/
def RigidSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) := sorry

noncomputable instance rigidSpaceCategory : Category.{u + 1} (RigidSpace K) := sorry

namespace RigidSpace

/-- Every point has an admissible affinoid neighborhood. -/
def IsLocallyAffinoid (X : RigidSpace K) : Prop := sorry

/-- Intersections of quasi-compact admissible opens are quasi-compact. -/
def IsQuasiSeparated (X : RigidSpace K) : Prop := sorry

/-- The rigid-space finiteness condition used in the comparison theorem.

This is provisionally named `IsParacompact`; its final definition should be the standard condition
in the chosen rigid/Berkovich comparison theorem (typically formulated using an affinoid cover of
finite type). -/
def IsParacompact (X : RigidSpace K) : Prop := sorry

/-- The diagonal is a closed immersion. -/
def IsSeparated (X : RigidSpace K) : Prop := sorry

end RigidSpace

/-- A Berkovich analytic space over `K`, locally modeled on Berkovich spectra of affinoid
algebras. -/
def BerkovichSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) := sorry

noncomputable instance berkovichSpaceCategory : Category.{u + 1} (BerkovichSpace K) :=
  sorry

namespace BerkovichSpace

/-- Every point has an affinoid neighborhood. -/
def IsGood (X : BerkovichSpace K) : Prop := sorry

/-- The analytic atlas uses strict affinoid algebras. -/
def IsStrict (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is paracompact. -/
def IsParacompact (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is Hausdorff. -/
def IsHausdorff (X : BerkovichSpace K) : Prop := sorry

end BerkovichSpace

/-- Provisional rigid-side domain of the comparison equivalence. -/
def rigidComparisonProperty : ObjectProperty (RigidSpace K) :=
  fun X ↦ RigidSpace.IsLocallyAffinoid K X ∧ RigidSpace.IsQuasiSeparated K X ∧
    RigidSpace.IsParacompact K X

/-- Provisional Berkovich-side codomain of the comparison equivalence. -/
def berkovichComparisonProperty : ObjectProperty (BerkovichSpace K) :=
  fun X ↦ BerkovichSpace.IsGood K X ∧ BerkovichSpace.IsStrict K X ∧
    BerkovichSpace.IsParacompact K X

/-- The full subcategory of rigid spaces in the provisional comparison range. -/
abbrev ComparisonRigidSpace := (rigidComparisonProperty K).FullSubcategory

/-- The full subcategory of Berkovich spaces in the provisional comparison range. -/
abbrev ComparisonBerkovichSpace := (berkovichComparisonProperty K).FullSubcategory

/-- The comparison functor from rigid spaces to Berkovich spaces. -/
noncomputable def rigidToBerkovich : ComparisonRigidSpace K ⥤ ComparisonBerkovichSpace K := sorry

/-- Main comparison goal: the comparison functor is an equivalence of categories.

The exact full subcategories are provisional until a reference theorem has been selected and its
hypotheses have been encoded. -/
theorem rigidToBerkovich_isEquivalence :
    (rigidToBerkovich K).IsEquivalence := sorry

/-- Data-valued form of the main comparison theorem. -/
noncomputable def rigidBerkovichEquivalence :
    ComparisonRigidSpace K ≌ ComparisonBerkovichSpace K := sorry

/-- Under comparison, separated rigid spaces correspond to Hausdorff Berkovich spaces. -/
theorem separated_iff_hausdorff (X : ComparisonRigidSpace K) :
    RigidSpace.IsSeparated K X.obj ↔
      BerkovichSpace.IsHausdorff K ((rigidToBerkovich K).obj X).obj := sorry

end GlobalSpaces

end RigidChallenge
