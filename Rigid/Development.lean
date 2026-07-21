import Mathlib
import Rigid.AffinoidAlgebra.AutomaticContinuity
import Rigid.AffinoidAlgebra.Basic
import Rigid.Berkovich.Nonempty
import Rigid.AffinoidAlgebra.QuotientNorm
import Rigid.AffinoidAlgebra.QuotientTopology
import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.Noetherian
import Rigid.TateAlgebra.Multiplicative
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
Their interfaces include geometric characterizations, affinoid examples, isomorphism invariance,
and nonvacuity conditions to constrain constant-predicate and degenerate-category shortcuts.
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
theorem norm_mul (f g : TateAlgebra K ι) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  Rigid.TateAlgebra.norm_mul f g

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
    Function.Surjective P.toAlgHom :=
  P.equiv.surjective.comp (Ideal.Quotient.mkₐ_surjective K P.ideal)

/-- The quotient topology transported to the target of an affinoid presentation. -/
@[reducible]
noncomputable def residueTopology (P : AffinoidPresentation K A) : TopologicalSpace A :=
  TopologicalSpace.coinduced P.toAlgHom inferInstance

/-- The quotient topology of an affinoid algebra is independent of its presentation. -/
theorem residueTopology_eq (P Q : AffinoidPresentation K A) :
    P.residueTopology = Q.residueTopology := sorry

/-- The quotient topology makes the target a topological ring. -/
theorem residueIsTopologicalRing (P : AffinoidPresentation K A) :
    @IsTopologicalRing A P.residueTopology _ :=
  Rigid.isTopologicalRing_coinduced P.toAlgHom (toAlgHom_surjective K A P)

/-- Scalar multiplication by the ground field is continuous for the quotient topology. -/
theorem residueContinuousSMul (P : AffinoidPresentation K A) :
    @ContinuousSMul K A _ _ P.residueTopology :=
  Rigid.continuousSMul_coinduced P.toAlgHom (toAlgHom_surjective K A P)
    fun c x ↦ map_smul P.toAlgHom c x

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
    @IsTopologicalRing A (affinoidTopology K A hA) _ :=
  AffinoidPresentation.residueIsTopologicalRing K A hA.presentation

/-- Scalar multiplication by the ground field is continuous for the canonical topology. -/
theorem affinoidContinuousSMul (hA : IsAffinoidAlgebra K A) :
    @ContinuousSMul K A _ _ (affinoidTopology K A hA) :=
  AffinoidPresentation.residueContinuousSMul K A hA.presentation

/-- The canonical topology agrees with the quotient topology from every presentation. -/
theorem affinoidTopology_eq_residueTopology (hA : IsAffinoidAlgebra K A)
    (P : AffinoidPresentation K A) : affinoidTopology K A hA = P.residueTopology :=
  AffinoidPresentation.residueTopology_eq K A hA.presentation P

/-- Algebra homomorphisms between affinoid algebras are continuous for their canonical quotient
topologies. -/
theorem continuous_for_affinoidTopology_of_isAffinoidAlgebra
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    @Continuous A B (affinoidTopology K A hA) (affinoidTopology K B hB) f :=
  Rigid.continuous_for_affinoidPresentationData K hA.presentation.ideal hA.presentation.equiv hB.presentation.ideal hB.presentation.equiv f

/-- Unpack an affinoid algebra as a surjective algebraic presentation by a finite Tate algebra. -/
theorem exists_surjective_presentation_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (π : TateAlgebra K (Fin n) →ₐ[K] A), Function.Surjective π :=
  ⟨hA.presentation.n, hA.presentation.toAlgHom,
    AffinoidPresentation.toAlgHom_surjective K A hA.presentation⟩

/-- Unpack the defining quotient presentation of an affinoid algebra. -/
theorem exists_quotient_presentation_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (I : Ideal (TateAlgebra K (Fin n))),
      Nonempty ((TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :=
  ⟨hA.presentation.n, hA.presentation.ideal, ⟨hA.presentation.equiv⟩⟩

/-- Affinoid algebras are Noetherian. -/
theorem isNoetherianRing_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing A := by
  obtain ⟨n, I, ⟨e⟩⟩ := exists_quotient_presentation_of_isAffinoidAlgebra K A hA
  haveI : IsNoetherianRing (TateAlgebra K (Fin n) ⧸ I) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact isNoetherianRing_of_ringEquiv _ e.toRingEquiv

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

section BerkovichSpectrum

variable (R : Type v) [NormedRing R]

/-- A point of the Berkovich spectrum of a normed ring: a multiplicative seminorm bounded by the
ring norm. The bound is normalized to be contractive. -/
structure BerkovichSpectrum where
  seminorm : MulRingSeminorm R
  le_norm' : ∀ a : R, seminorm a ≤ ‖a‖

instance berkovichSpectrumCoeFun : CoeFun (BerkovichSpectrum R) (fun _ ↦ R → ℝ) :=
  ⟨fun x ↦ x.seminorm⟩

namespace BerkovichSpectrum

/-- Two points of the Berkovich spectrum are equal when all their values are equal. -/
@[ext]
theorem ext {x y : BerkovichSpectrum R} (h : ∀ a, x a = y a) : x = y := by
  cases x with
  | mk px hx =>
    cases y with
    | mk py hy =>
      congr
      exact MulRingSeminorm.ext h

@[simp]
theorem map_zero (x : BerkovichSpectrum R) : x 0 = 0 :=
  _root_.map_zero x.seminorm

@[simp]
theorem map_one (x : BerkovichSpectrum R) : x 1 = 1 :=
  _root_.map_one x.seminorm

@[simp]
theorem map_neg (x : BerkovichSpectrum R) (a : R) : x (-a) = x a :=
  map_neg_eq_map x.seminorm a

@[simp]
theorem map_mul (x : BerkovichSpectrum R) (a b : R) : x (a * b) = x a * x b :=
  _root_.map_mul x.seminorm a b

/-- A point of the Berkovich spectrum is subadditive. -/
theorem map_add_le (x : BerkovichSpectrum R) (a b : R) : x (a + b) ≤ x a + x b :=
  map_add_le_add x.seminorm a b

/-- A point of the Berkovich spectrum takes nonnegative values. -/
theorem nonneg (x : BerkovichSpectrum R) (a : R) : 0 ≤ x a :=
  apply_nonneg x.seminorm a

/-- A point of the Berkovich spectrum is bounded by the given ring norm. -/
theorem le_norm (x : BerkovichSpectrum R) (a : R) : x a ≤ ‖a‖ :=
  x.le_norm' a

/-- The kernel of a point of the Berkovich spectrum. -/
def kernel (x : BerkovichSpectrum R) : Ideal R where
  carrier := {a | x a = 0}
  zero_mem' := x.map_zero
  add_mem' {a b} ha hb := by
    apply le_antisymm
    · exact (map_add_le R x a b).trans_eq (by rw [ha, hb, add_zero])
    · exact nonneg R x (a + b)
  smul_mem' r a ha := by
    change x (r * a) = 0
    rw [x.map_mul, ha, mul_zero]

@[simp]
theorem mem_kernel_iff (x : BerkovichSpectrum R) (a : R) : a ∈ x.kernel ↔ x a = 0 :=
  Iff.rfl

/-- The kernel of a multiplicative seminorm is a prime ideal. -/
theorem kernel_isPrime (x : BerkovichSpectrum R) : x.kernel.IsPrime := by
  refine Ideal.IsPrime.mk ?_ ?_
  · rw [Ideal.ne_top_iff_one]
    simp
  · intro a b hab
    rw [mem_kernel_iff R x, map_mul R x] at hab
    rcases mul_eq_zero.mp hab with ha | hb
    · exact Or.inl ((mem_kernel_iff R x a).mpr ha)
    · exact Or.inr ((mem_kernel_iff R x b).mpr hb)

/-- Pull back a Berkovich point along a norm-nonincreasing ring homomorphism. -/
def comap {S : Type w} [NormedRing S] (f : R →+* S) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (x : BerkovichSpectrum S) : BerkovichSpectrum R where
  seminorm :=
    { toFun := fun a ↦ x (f a)
      map_zero' := by simp
      add_le' := by intro a b; simpa using map_add_le S x (f a) (f b)
      neg' := by intro a; simp
      map_one' := by simp
      map_mul' := by intro a b; simp }
  le_norm' a := (le_norm S x (f a)).trans (hf a)

@[simp]
theorem comap_apply {S : Type w} [NormedRing S] (f : R →+* S) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (x : BerkovichSpectrum S) (a : R) : comap R f hf x a = x (f a) :=
  rfl

end BerkovichSpectrum

/-- The topology of pointwise convergence on the Berkovich spectrum. -/
noncomputable instance berkovichSpectrumTopologicalSpace :
    TopologicalSpace (BerkovichSpectrum R) :=
  TopologicalSpace.induced (fun x : BerkovichSpectrum R ↦ (x : R → ℝ)) inferInstance

namespace BerkovichSpectrum

/-- The map sending a point of the Berkovich spectrum to its underlying function is an embedding. -/
theorem isEmbedding_coe :
    Topology.IsEmbedding (fun x : BerkovichSpectrum R ↦ (x : R → ℝ)) := by
  refine ⟨Topology.IsInducing.induced _, ?_⟩
  intro x y h
  ext a
  exact congr_fun h a

/-- Evaluation at a ring element is continuous on the Berkovich spectrum. -/
theorem continuous_eval (a : R) : Continuous fun x : BerkovichSpectrum R ↦ x a :=
  (continuous_apply a).comp (isEmbedding_coe R).continuous

/-- A map into the Berkovich spectrum is continuous exactly when all its evaluations are
continuous. -/
theorem continuous_iff_eval {X : Type w} [TopologicalSpace X] {f : X → BerkovichSpectrum R} :
    Continuous f ↔ ∀ a : R, Continuous fun x ↦ f x a := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

/-- Pullback of Berkovich points along a norm-nonincreasing ring homomorphism is continuous. -/
theorem continuous_comap {S : Type w} [NormedRing S] (f : R →+* S) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) :
    Continuous (comap R f hf) :=
  (continuous_iff_eval R).2 fun a ↦ continuous_eval S (f a)

/-- Convergence in the Berkovich spectrum is pointwise convergence of seminorms. -/
theorem tendsto_iff_eval {l : Filter (BerkovichSpectrum R)} {x : BerkovichSpectrum R} :
    Tendsto id l (𝓝 x) ↔ ∀ a : R, Tendsto (fun y ↦ y a) l (𝓝 (x a)) := by
  rw [(isEmbedding_coe R).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- The Berkovich spectrum is Hausdorff. -/
noncomputable instance berkovichSpectrumT2Space : T2Space (BerkovichSpectrum R) :=
  (isEmbedding_coe R).t2Space

private noncomputable def homeomorphRigid :
    Rigid.BerkovichSpectrum R ≃ₜ BerkovichSpectrum R where
  toFun x := ⟨x.seminorm, x.le_norm'⟩
  invFun x := ⟨x.seminorm, x.le_norm'⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  continuous_toFun := (continuous_iff_eval R).2 fun a ↦
    Rigid.BerkovichSpectrum.continuous_eval R a
  continuous_invFun := (Rigid.BerkovichSpectrum.continuous_iff_eval R).2 fun a ↦
    continuous_eval R a

/-- The Berkovich spectrum of every normed ring is compact. -/
theorem isCompact_univ : IsCompact (Set.univ : Set (BerkovichSpectrum R)) := by
  have h := ((homeomorphRigid R).isCompact_image (s := Set.univ)).2
    (Rigid.BerkovichSpectrum.isCompact_univ R)
  simpa using h

noncomputable instance berkovichSpectrumCompactSpace : CompactSpace (BerkovichSpectrum R) :=
  isCompact_univ_iff.mp (isCompact_univ R)

end BerkovichSpectrum

end BerkovichSpectrum

namespace BerkovichSpectrum

/-- A bounded multiplicative seminorm on a nonarchimedean commutative normed ring is
nonarchimedean. -/
theorem map_add_le_max {R : Type v} [NormedCommRing R] [IsUltrametricDist R]
    (x : BerkovichSpectrum R) (a b : R) : x (a + b) ≤ max (x a) (x b) := by
  simpa [homeomorphRigid] using
    Rigid.BerkovichSpectrum.map_add_le_max ((homeomorphRigid R).symm x) a b

end BerkovichSpectrum

/-- The Berkovich spectrum of a nonzero nonarchimedean commutative normed ring is nonempty. -/
theorem nonempty_berkovichSpectrum_of_isUltrametric
    (R : Type v) [NormedCommRing R] [IsUltrametricDist R] [Nontrivial R] :
    Nonempty (BerkovichSpectrum R) :=
  (Rigid.BerkovichSpectrum.nonempty_of_isUltrametric R).map fun x ↦ ⟨x.seminorm, x.le_norm'⟩

/-- The Berkovich spectrum of a nonzero complete commutative normed ring is nonempty. -/
theorem nonempty_berkovichSpectrum_of_complete
    (R : Type v) [NormedCommRing R] [CompleteSpace R] [Nontrivial R] :
    Nonempty (BerkovichSpectrum R) :=
  (Rigid.BerkovichSpectrum.nonempty_of_nontrivial R).map fun x ↦ ⟨x.seminorm, x.le_norm'⟩

/-- The Berkovich spectrum of a nonzero affinoid algebra is nonempty. -/
theorem nonempty_berkovichSpectrum [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    Nonempty (BerkovichSpectrum A) := by
  rcases hA with ⟨_⟩
  exact nonempty_berkovichSpectrum_of_isUltrametric A

/-- The Berkovich spectrum of an affinoid algebra is compact. -/
theorem isCompact_univ_berkovichSpectrum (hA : IsAffinoidAlgebra K A) :
    IsCompact (Set.univ : Set (BerkovichSpectrum A)) := by
  rcases hA with ⟨_⟩
  exact BerkovichSpectrum.isCompact_univ A

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

noncomputable instance rigidSpaceHasBinaryProducts :
    CategoryTheory.Limits.HasBinaryProducts (RigidSpace K) := sorry

namespace RigidSpace

/-- The type of analytic points of a rigid space. -/
def Point (X : RigidSpace K) : Type (u + 1) := sorry

/-- An admissible open of a rigid space. -/
def AdmissibleOpen (X : RigidSpace K) : Type (u + 1) := sorry

namespace AdmissibleOpen

/-- The intersection of two admissible opens. -/
noncomputable def inter {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    AdmissibleOpen K X := sorry

/-- An admissible open is quasi-compact for the admissible topology. -/
def IsQuasiCompact {X : RigidSpace K} (U : AdmissibleOpen K X) : Prop := sorry

end AdmissibleOpen

/-- An affinoid domain in a rigid space. -/
def AffinoidDomain (X : RigidSpace K) : Type (u + 1) := sorry

namespace AffinoidDomain

/-- The admissible open underlying an affinoid domain. -/
noncomputable def toAdmissibleOpen {X : RigidSpace K} (U : AffinoidDomain K X) :
    AdmissibleOpen K X := sorry

/-- The points belonging to an affinoid domain. -/
noncomputable def carrier {X : RigidSpace K} (U : AffinoidDomain K X) :
    Set (Point K X) := sorry

end AffinoidDomain

/-- An affinoid cover of a rigid space. -/
def AffinoidCover (X : RigidSpace K) : Type (u + 1) := sorry

namespace AffinoidCover

/-- An affinoid cover is of finite type in the sense used in the comparison theorem. -/
def IsFiniteType {X : RigidSpace K} (𝒰 : AffinoidCover K X) : Prop := sorry

end AffinoidCover

/-- A closed immersion of rigid spaces. -/
def IsClosedImmersion {X Y : RigidSpace K} (f : X ⟶ Y) : Prop := sorry

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

/-- Local affinoidness is characterized by affinoid domains through every point. -/
theorem isLocallyAffinoid_iff (X : RigidSpace K) :
    IsLocallyAffinoid K X ↔ ∀ x : Point K X, ∃ U : AffinoidDomain K X, x ∈ U.carrier := sorry

/-- Quasi-separatedness is characterized by quasi-compact intersections of affinoid domains. -/
theorem isQuasiSeparated_iff (X : RigidSpace K) :
    IsQuasiSeparated K X ↔ ∀ U V : AffinoidDomain K X,
      AdmissibleOpen.IsQuasiCompact K
        (AdmissibleOpen.inter K U.toAdmissibleOpen V.toAdmissibleOpen) := sorry

/-- The comparison finiteness condition is witnessed by an affinoid cover of finite type. -/
theorem isParacompact_iff (X : RigidSpace K) :
    IsParacompact K X ↔ ∃ 𝒰 : AffinoidCover K X, 𝒰.IsFiniteType := sorry

/-- Separatedness is characterized by the diagonal being a closed immersion. -/
theorem isSeparated_iff (X : RigidSpace K) :
    IsSeparated K X ↔ IsClosedImmersion K
      (CategoryTheory.Limits.prod.lift (𝟙 X) (𝟙 X)) := sorry

/-- Local affinoidness is invariant under analytic isomorphism. -/
theorem isLocallyAffinoid_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    IsLocallyAffinoid K X ↔ IsLocallyAffinoid K Y := sorry

/-- Quasi-separatedness is invariant under analytic isomorphism. -/
theorem isQuasiSeparated_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    IsQuasiSeparated K X ↔ IsQuasiSeparated K Y := sorry

/-- The comparison finiteness condition is invariant under analytic isomorphism. -/
theorem isParacompact_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    IsParacompact K X ↔ IsParacompact K Y := sorry

/-- Separatedness is invariant under analytic isomorphism. -/
theorem isSeparated_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    IsSeparated K X ↔ IsSeparated K Y := sorry

/-- The rigid space associated to a strict affinoid algebra. -/
noncomputable def ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : RigidSpace K := sorry

/-- The points of an affinoid rigid space are the maximal ideals of its coordinate algebra. -/
noncomputable def pointsOfAffinoidEquiv {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : Point K (ofAffinoid K hA) ≃ MaximalSpectrum A := sorry

/-- An affinoid rigid space is locally affinoid. -/
theorem isLocallyAffinoid_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsLocallyAffinoid K (ofAffinoid K hA) := sorry

/-- An affinoid rigid space is quasi-separated. -/
theorem isQuasiSeparated_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsQuasiSeparated K (ofAffinoid K hA) := sorry

/-- An affinoid rigid space satisfies the comparison finiteness condition. -/
theorem isParacompact_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsParacompact K (ofAffinoid K hA) := sorry

/-- An affinoid rigid space is separated. -/
theorem isSeparated_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsSeparated K (ofAffinoid K hA) := sorry

end RigidSpace

/-- A Berkovich analytic space over `K`, locally modeled on Berkovich spectra of affinoid
algebras. -/
def BerkovichSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) := sorry

noncomputable instance berkovichSpaceCategory : Category.{u + 1} (BerkovichSpace K) :=
  sorry

namespace BerkovichSpace

/-- The underlying type of points of a Berkovich space. -/
def Point (X : BerkovichSpace K) : Type (u + 1) := sorry

/-- The canonical topology on the points of a Berkovich space. -/
noncomputable instance pointTopologicalSpace (X : BerkovichSpace K) :
    TopologicalSpace (Point K X) := sorry

/-- An affinoid domain in a Berkovich space. -/
def AffinoidDomain (X : BerkovichSpace K) : Type (u + 1) := sorry

namespace AffinoidDomain

/-- The set of points belonging to an affinoid domain. -/
noncomputable def carrier {X : BerkovichSpace K} (U : AffinoidDomain K X) :
    Set (Point K X) := sorry

/-- An affinoid domain is modeled on a strict affinoid algebra. -/
def IsStrict {X : BerkovichSpace K} (U : AffinoidDomain K X) : Prop := sorry

end AffinoidDomain

/-- Every point has an affinoid neighborhood. -/
def IsGood (X : BerkovichSpace K) : Prop := sorry

/-- The analytic atlas uses strict affinoid algebras. -/
def IsStrict (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is paracompact. -/
def IsParacompact (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is Hausdorff. -/
def IsHausdorff (X : BerkovichSpace K) : Prop := sorry

/-- Goodness means that every point lies in the interior of an affinoid domain. -/
theorem isGood_iff (X : BerkovichSpace K) :
    IsGood K X ↔ ∀ x : Point K X, ∃ U : AffinoidDomain K X, x ∈ interior U.carrier := sorry

/-- Strictness means that every point belongs to a strict affinoid domain. -/
theorem isStrict_iff (X : BerkovichSpace K) :
    IsStrict K X ↔ ∀ x : Point K X, ∃ U : AffinoidDomain K X,
      x ∈ U.carrier ∧ U.IsStrict := sorry

/-- Berkovich paracompactness agrees with paracompactness of the underlying point-set topology. -/
theorem isParacompact_iff (X : BerkovichSpace K) :
    IsParacompact K X ↔ ParacompactSpace (Point K X) := sorry

/-- Berkovich Hausdorffness agrees with the Hausdorff property of the point-set topology. -/
theorem isHausdorff_iff (X : BerkovichSpace K) :
    IsHausdorff K X ↔ T2Space (Point K X) := sorry

/-- Goodness is invariant under analytic isomorphism. -/
theorem isGood_iff_of_iso {X Y : BerkovichSpace K} (e : X ≅ Y) :
    IsGood K X ↔ IsGood K Y := sorry

/-- Strictness is invariant under analytic isomorphism. -/
theorem isStrict_iff_of_iso {X Y : BerkovichSpace K} (e : X ≅ Y) :
    IsStrict K X ↔ IsStrict K Y := sorry

/-- Paracompactness is invariant under analytic isomorphism. -/
theorem isParacompact_iff_of_iso {X Y : BerkovichSpace K} (e : X ≅ Y) :
    IsParacompact K X ↔ IsParacompact K Y := sorry

/-- Hausdorffness is invariant under analytic isomorphism. -/
theorem isHausdorff_iff_of_iso {X Y : BerkovichSpace K} (e : X ≅ Y) :
    IsHausdorff K X ↔ IsHausdorff K Y := sorry

/-- The Berkovich space associated to a strict affinoid algebra. -/
noncomputable def ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : BerkovichSpace K := sorry

/-- The points of an affinoid Berkovich space form its Berkovich spectrum. -/
noncomputable def pointsOfAffinoidHomeomorph {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    Point K (ofAffinoid K hA) ≃ₜ
      (letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
       BerkovichSpectrum A) := sorry

/-- An affinoid Berkovich space is good. -/
theorem isGood_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsGood K (ofAffinoid K hA) := sorry

/-- An affinoid Berkovich space is strict. -/
theorem isStrict_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsStrict K (ofAffinoid K hA) := sorry

/-- An affinoid Berkovich space is paracompact. -/
theorem isParacompact_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsParacompact K (ofAffinoid K hA) := sorry

/-- An affinoid Berkovich space is Hausdorff. -/
theorem isHausdorff_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsHausdorff K (ofAffinoid K hA) := sorry

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

/-- The rigid comparison property is invariant under analytic isomorphism. -/
theorem rigidComparisonProperty_isClosedUnderIsomorphisms :
    (rigidComparisonProperty K).IsClosedUnderIsomorphisms := sorry

/-- The Berkovich comparison property is invariant under analytic isomorphism. -/
theorem berkovichComparisonProperty_isClosedUnderIsomorphisms :
    (berkovichComparisonProperty K).IsClosedUnderIsomorphisms := sorry

/-- An affinoid algebra gives an object of the rigid comparison subcategory. -/
noncomputable def comparisonRigidSpaceOfAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : ComparisonRigidSpace K := sorry

/-- An affinoid algebra gives an object of the Berkovich comparison subcategory. -/
noncomputable def comparisonBerkovichSpaceOfAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : ComparisonBerkovichSpace K := sorry

/-- The rigid comparison subcategory is nonempty. -/
theorem nonempty_comparisonRigidSpace : Nonempty (ComparisonRigidSpace K) := sorry

/-- The Berkovich comparison subcategory is nonempty. -/
theorem nonempty_comparisonBerkovichSpace : Nonempty (ComparisonBerkovichSpace K) := sorry

/-- The rigid comparison subcategory has nonisomorphic objects. -/
theorem exists_nonisomorphic_comparisonRigidSpaces :
    ∃ X Y : ComparisonRigidSpace K, ¬ Nonempty (X ≅ Y) := sorry

/-- The Berkovich comparison subcategory has nonisomorphic objects. -/
theorem exists_nonisomorphic_comparisonBerkovichSpaces :
    ∃ X Y : ComparisonBerkovichSpace K, ¬ Nonempty (X ≅ Y) := sorry

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
