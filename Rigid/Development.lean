import Mathlib
import Rigid.AffinoidAlgebra.AutomaticContinuity
import Rigid.AffinoidAlgebra.Basic
import Rigid.Berkovich.Nonempty
import Rigid.Berkovich.RelativeSpectrum
import Rigid.Berkovich.RelativeNonempty
import Rigid.Berkovich.CompletedResidue
import Rigid.Berkovich.AffinoidDomain
import Rigid.AffinoidAlgebra.QuotientNorm
import Rigid.AffinoidAlgebra.QuotientTopology
import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.AffinoidAlgebra.RationalLocalization
import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.Noetherian
import Rigid.TateAlgebra.Multiplicative
import Rigid.TateAlgebra.PowerBoundedUniversalProperty
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

The global comparison interface follows Theorem 1.6.1 of Vladimir Berkovich, *Étale cohomology
for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78 (1993), 5–161. The canonical functor from
Hausdorff strict Berkovich spaces to quasi-separated rigid spaces is fully faithful, and restricts
to an equivalence between paracompact strict Berkovich spaces and quasi-separated rigid spaces with
an admissible affinoid cover of finite type. The interfaces include geometric characterizations,
affinoid examples, isomorphism invariance, and nonvacuity conditions to constrain shortcut models.
-/

open CategoryTheory
open Filter
open scoped Topology

universe u v w z

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

/-- The Tate variable is the corresponding monomial in the ambient multivariate power-series
ring. This characterizes `tateVariable` without finiteness or completeness assumptions. -/
@[simp]
theorem coe_tateVariable (i : ι) :
    (tateVariable K ι i : MvPowerSeries ι K) = MvPowerSeries.X i := rfl

/-- The Gauss norm, i.e. the supremum of the norms of the coefficients. -/
noncomputable def gaussNorm : TateAlgebra K ι → ℝ :=
  Rigid.gaussNorm K ι


/-- The defining coefficient formula for the Gauss norm, without a finiteness assumption on the
variable type. -/
theorem gaussNorm_eq_sSup_coeff (f : TateAlgebra K ι) :
    gaussNorm K ι f =
      sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) := rfl

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


/-- The constant coefficient of a scalar in the Tate algebra is that scalar. -/
@[simp]
theorem coeff_zero_algebraMap (r : K) :
    MvPowerSeries.coeff 0 (algebraMap K (TateAlgebra K ι) r).1 = r := rfl

/-- Every nonconstant coefficient of a scalar in the Tate algebra vanishes. -/
@[simp]
theorem coeff_algebraMap_of_ne_zero (r : K) {n : ι →₀ ℕ} (hn : n ≠ 0) :
    MvPowerSeries.coeff n (algebraMap K (TateAlgebra K ι) r).1 = 0 :=
  MvPowerSeries.coeff_C_of_ne_zero hn r

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

/-- Equivalent Banach norms need not put power-bounded elements in the closed unit ball. The strict
Tate algebra nevertheless has the expected norm-independent universal property for finite
power-bounded tuples. -/
theorem existsUnique_continuousAlgHom_of_isPowerBounded
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {ι : Type v} [Finite ι]
    {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (x : ι → A) (hx : ∀ i, IsPowerBounded (x i)) :
    ∃! φ : ContinuousAlgHom K (TateAlgebra K ι) A,
      ∀ i, φ (tateVariable K ι i) = x i :=
  Rigid.existsUnique_continuousAlgHom_of_isPowerBounded x hx

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


/-- The scalar embedding of the residue normed algebra agrees with the presentation map applied to
constant Tate series. -/
@[simp]
theorem residueNormedAlgebra_algebraMap (P : AffinoidPresentation K A) (r : K) :
    letI : NormedCommRing A := P.residueNormedCommRing
    letI : NormedAlgebra K A := P.residueNormedAlgebra
    algebraMap K A r =
      toAlgHom K A P (algebraMap K (TateAlgebra K (Fin P.n)) r) := sorry
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
    [IsUltrametricDist A] (n : ℕ) (g : A) (f : Fin n → A) : Type v :=
  Rigid.RationalLocalization K A n g f

noncomputable instance rationalLocalizationNormedCommRing (n : ℕ) (g : A) (f : Fin n → A) :
    NormedCommRing (RationalLocalization K A n g f) :=
  Rigid.rationalLocalizationNormedCommRing K A n g f

noncomputable instance rationalLocalizationAlgebra (n : ℕ) (g : A) (f : Fin n → A) :
    Algebra A (RationalLocalization K A n g f) :=
  Rigid.rationalLocalizationAlgebra K A n g f

noncomputable instance rationalLocalizationNormedAlgebra (n : ℕ) (g : A) (f : Fin n → A) :
    NormedAlgebra K (RationalLocalization K A n g f) :=
  Rigid.rationalLocalizationNormedAlgebra K A n g f

noncomputable instance rationalLocalizationCompleteSpace (n : ℕ) (g : A) (f : Fin n → A) :
    CompleteSpace (RationalLocalization K A n g f) :=
  Rigid.rationalLocalizationCompleteSpace K A n g f

noncomputable instance rationalLocalizationIsUltrametricDist
    (n : ℕ) (g : A) (f : Fin n → A) :
    IsUltrametricDist (RationalLocalization K A n g f) :=
  Rigid.rationalLocalizationIsUltrametricDist K A n g f

noncomputable instance rationalLocalizationIsScalarTower
    (n : ℕ) (g : A) (f : Fin n → A) :
    IsScalarTower K A (RationalLocalization K A n g f) :=
  Rigid.rationalLocalizationIsScalarTower K A n g f

namespace RationalLocalization

/-- The canonical continuous map from the original algebra to its rational localization. -/
noncomputable def baseMap (n : ℕ) (g : A) (f : Fin n → A) :
    ContinuousAlgHom K A (RationalLocalization K A n g f) :=
  Rigid.RationalLocalization.baseMap K A n g f

@[simp]
theorem baseMap_apply (n : ℕ) (g : A) (f : Fin n → A) (a : A) :
    baseMap K A n g f a = algebraMap A (RationalLocalization K A n g f) a :=
  Rigid.RationalLocalization.baseMap_apply K A n g f a

/-- The coordinate representing the quotient `fᵢ / g` in a rational localization. -/
noncomputable def coordinate (n : ℕ) (g : A) (f : Fin n → A) (i : Fin n) :
    RationalLocalization K A n g f :=
  Rigid.RationalLocalization.coordinate K A n g f i

/-- The defining relation `gTᵢ = fᵢ` of a rational localization. -/
@[simp]
theorem baseMap_denominator_mul_coordinate (n : ℕ) (g : A) (f : Fin n → A) (i : Fin n) :
    baseMap K A n g f g * coordinate K A n g f i = baseMap K A n g f (f i) :=
  Rigid.RationalLocalization.baseMap_denominator_mul_coordinate K A n g f i

/-- Every coordinate of a rational localization is power-bounded. -/
theorem isPowerBounded_coordinate (n : ℕ) (g : A) (f : Fin n → A) (i : Fin n) :
    IsPowerBounded (coordinate K A n g f i) :=
  Rigid.RationalLocalization.isPowerBounded_coordinate K A n g f i

/-- The denominator becomes a unit when the numerator and denominator generate the unit ideal. -/
theorem isUnit_baseMap_denominator (n : ℕ) (g : A) (f : Fin n → A)
    (h : IsRationalDatum g f) : IsUnit (baseMap K A n g f g) :=
  Rigid.RationalLocalization.isUnit_baseMap_denominator K A n g f h

/-- Map a rational localization to a complete nonarchimedean algebra by choosing power-bounded
images of its coordinates that satisfy the defining relations. -/
noncomputable def lift
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) :
    ContinuousAlgHom K (RationalLocalization K A n g f) B :=
  Rigid.RationalLocalization.lift K A n g f φ x hx hrel

@[simp]
theorem lift_comp_baseMap
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) :
    (lift K A n g f φ x hx hrel).comp (baseMap K A n g f) = φ :=
  Rigid.RationalLocalization.lift_comp_baseMap K A n g f φ x hx hrel

@[simp]
theorem lift_coordinate
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (n : ℕ) (g : A) (f : Fin n → A)
    (φ : ContinuousAlgHom K A B) (x : Fin n → B)
    (hx : ∀ i, IsPowerBounded (x i)) (hrel : ∀ i, φ g * x i = φ (f i)) (i : Fin n) :
    lift K A n g f φ x hx hrel (coordinate K A n g f i) = x i :=
  Rigid.RationalLocalization.lift_coordinate K A n g f φ x hx hrel i

/-- Continuous homomorphisms from a rational localization agree if they agree on the original
algebra and on every coordinate. -/
@[ext]
theorem hom_ext
    {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
    (n : ℕ) (g : A) (f : Fin n → A)
    (φ ψ : ContinuousAlgHom K (RationalLocalization K A n g f) B)
    (hbase : φ.comp (baseMap K A n g f) = ψ.comp (baseMap K A n g f))
    (hcoordinate : ∀ i, φ (coordinate K A n g f i) = ψ (coordinate K A n g f i)) :
    φ = ψ :=
  Rigid.RationalLocalization.hom_ext K A n g f φ ψ hbase hcoordinate

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
    IsAffinoidAlgebra K (RationalLocalization K A n g f) := by
  obtain ⟨m, π, hπ⟩ :=
    exists_equivalent_quotientNorm_presentation_of_isAffinoidAlgebra K A hA
  let hR : Rigid.IsAffinoidAlgebra K (Rigid.RationalLocalization K A n g f) :=
    Rigid.isAffinoidAlgebra_rationalLocalization_of_surjective
      K A m π hπ.surjective n g f
  let P := hR.presentation
  exact ⟨{
    n := P.n
    ideal := P.ideal
    equiv := AlgEquiv.ofRingEquiv (f := P.equiv.toRingEquiv) fun r ↦ by
      convert P.equiv.commutes r using 1 <;> rfl }⟩

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

/-- The Berkovich spectrum of a normed `K`-algebra relative to `K`: its points restrict to the given
norm on the ground field. -/
structure BerkovichSpectrumOver
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [NormedCommRing A] [Algebra K A] where
  toBerkovichSpectrum : BerkovichSpectrum A
  map_algebraMap' : ∀ r : K, toBerkovichSpectrum (algebraMap K A r) = ‖r‖

instance berkovichSpectrumOverCoeFun : CoeFun (BerkovichSpectrumOver K A) (fun _ ↦ A → ℝ) :=
  ⟨fun x ↦ x.toBerkovichSpectrum⟩

namespace BerkovichSpectrumOver

@[ext]
theorem ext {x y : BerkovichSpectrumOver K A} (h : ∀ a, x a = y a) : x = y := by
  cases x
  cases y
  congr
  exact BerkovichSpectrum.ext A h

@[simp]
theorem map_algebraMap (x : BerkovichSpectrumOver K A) (r : K) :
    x (algebraMap K A r) = ‖r‖ :=
  x.map_algebraMap' r

/-- The prime kernel of a relative Berkovich point. -/
def kernel (x : BerkovichSpectrumOver K A) : Ideal A :=
  x.toBerkovichSpectrum.kernel

@[simp]
theorem mem_kernel_iff (x : BerkovichSpectrumOver K A) (a : A) :
    a ∈ x.kernel ↔ x a = 0 :=
  Iff.rfl

theorem kernel_isPrime (x : BerkovichSpectrumOver K A) : x.kernel.IsPrime :=
  x.toBerkovichSpectrum.kernel_isPrime

/-- Pull back a relative point along a norm-nonincreasing algebra homomorphism. -/
def comap {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (f : A →ₐ[K] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (x : BerkovichSpectrumOver K B) :
    BerkovichSpectrumOver K A where
  toBerkovichSpectrum := BerkovichSpectrum.comap A f.toRingHom hf x.toBerkovichSpectrum
  map_algebraMap' r := by
    rw [BerkovichSpectrum.comap_apply]
    simp

@[simp]
theorem comap_apply {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    [IsUltrametricDist B] (f : A →ₐ[K] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (x : BerkovichSpectrumOver K B) (a : A) :
    comap K A f hf x a = x (f a) :=
  rfl

end BerkovichSpectrumOver

noncomputable instance berkovichSpectrumOverTopologicalSpace :
    TopologicalSpace (BerkovichSpectrumOver K A) :=
  TopologicalSpace.induced BerkovichSpectrumOver.toBerkovichSpectrum inferInstance

namespace BerkovichSpectrumOver

private theorem isEmbedding_toBerkovichSpectrum :
    Topology.IsEmbedding
      (toBerkovichSpectrum : BerkovichSpectrumOver K A → BerkovichSpectrum A) := by
  refine ⟨Topology.IsInducing.induced _, ?_⟩
  intro x y h
  apply ext K A
  intro a
  exact congr_arg (fun z : BerkovichSpectrum A ↦ z a) h

/-- Evaluation at an algebra element is continuous on the relative spectrum. -/
theorem continuous_eval (a : A) : Continuous fun x : BerkovichSpectrumOver K A ↦ x a :=
  (BerkovichSpectrum.continuous_eval A a).comp
    (isEmbedding_toBerkovichSpectrum K A).continuous

/-- A map into the relative spectrum is continuous exactly when all evaluations are continuous. -/
theorem continuous_iff_eval {X : Type w} [TopologicalSpace X]
    {f : X → BerkovichSpectrumOver K A} :
    Continuous f ↔ ∀ a : A, Continuous fun x ↦ f x a := by
  constructor
  · intro hf a
    exact (continuous_eval K A a).comp hf
  · intro hf
    rw [continuous_induced_rng]
    exact (BerkovichSpectrum.continuous_iff_eval A).2 hf

/-- Pullback of relative Berkovich points is continuous. -/
theorem continuous_comap {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [IsUltrametricDist B] (f : A →ₐ[K] B) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) :
    Continuous (comap K A f hf) :=
  (continuous_iff_eval K A).2 fun a ↦ continuous_eval K B (f a)

noncomputable instance berkovichSpectrumOverT2Space [CompleteSpace A] [IsUltrametricDist A] :
    T2Space (BerkovichSpectrumOver K A) :=
  (isEmbedding_toBerkovichSpectrum K A).t2Space

private theorem isClosed_range_toBerkovichSpectrum :
    IsClosed (Set.range
      (toBerkovichSpectrum : BerkovichSpectrumOver K A → BerkovichSpectrum A)) := by
  let C : Set (BerkovichSpectrum A) :=
    ⋂ r : K, {x | x (algebraMap K A r) = ‖r‖}
  have hC : IsClosed C := by
    dsimp only [C]
    exact isClosed_iInter fun r ↦
      isClosed_eq (BerkovichSpectrum.continuous_eval A _) continuous_const
  have hrange : Set.range
      (toBerkovichSpectrum : BerkovichSpectrumOver K A → BerkovichSpectrum A) = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp [C]
    · intro hx
      simp only [C, Set.mem_iInter, Set.mem_setOf_eq] at hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rwa [hrange]

/-- The relative Berkovich spectrum is compact. -/
theorem isCompact_univ : IsCompact (Set.univ : Set (BerkovichSpectrumOver K A)) := by
  rw [(isEmbedding_toBerkovichSpectrum K A).isCompact_iff, Set.image_univ]
  exact (isClosed_range_toBerkovichSpectrum K A).isCompact

noncomputable instance berkovichSpectrumOverCompactSpace [CompleteSpace A]
    [IsUltrametricDist A] : CompactSpace (BerkovichSpectrumOver K A) :=
  isCompact_univ_iff.mp (isCompact_univ K A)

/-- Relative Berkovich points over a nonarchimedean ring are nonarchimedean. -/
theorem map_add_le_max (x : BerkovichSpectrumOver K A) (a b : A) :
    x (a + b) ≤ max (x a) (x b) :=
  BerkovichSpectrum.map_add_le_max x.toBerkovichSpectrum a b

noncomputable instance kernelIsPrime (x : BerkovichSpectrumOver K A) : x.kernel.IsPrime :=
  x.kernel_isPrime

/-- The integral residue domain obtained by quotienting by the point's prime kernel. -/
abbrev ResidueDomain (x : BerkovichSpectrumOver K A) := A ⧸ x.kernel

/-- The fraction field of the integral residue domain. -/
abbrev ResidueFractionField (x : BerkovichSpectrumOver K A) :=
  FractionRing (ResidueDomain K A x)

noncomputable instance residueFractionNormedField (x : BerkovichSpectrumOver K A) :
    NormedField (ResidueFractionField K A x) := sorry

noncomputable instance residueFractionIsUltrametricDist (x : BerkovichSpectrumOver K A) :
    IsUltrametricDist (ResidueFractionField K A x) := sorry

/-- The completed residue field of a relative Berkovich point. -/
abbrev CompletedResidueField (x : BerkovichSpectrumOver K A) :=
  UniformSpace.Completion (ResidueFractionField K A x)

noncomputable instance completedResidueIsUltrametricDist (x : BerkovichSpectrumOver K A) :
    IsUltrametricDist (CompletedResidueField K A x) := sorry

/-- The canonical map from the original algebra to the residue fraction field. -/
noncomputable def residueFractionMap (x : BerkovichSpectrumOver K A) :
    A →+* ResidueFractionField K A x := sorry

/-- The residue-fraction map is the quotient map followed by the canonical embedding into the
fraction field. -/
@[simp]
theorem residueFractionMap_apply (x : BerkovichSpectrumOver K A) (a : A) :
    residueFractionMap K A x a =
      algebraMap (ResidueDomain K A x) (ResidueFractionField K A x)
        (Ideal.Quotient.mk x.kernel a) := sorry

/-- The residue-fraction map realizes the point seminorm before completion. -/
@[simp]
theorem norm_residueFractionMap (x : BerkovichSpectrumOver K A) (a : A) :
    ‖residueFractionMap K A x a‖ = x a := sorry

/-- The canonical evaluation map from the algebra to the completed residue field. -/
noncomputable def completedResidueMap (x : BerkovichSpectrumOver K A) :
    A →+* CompletedResidueField K A x := sorry

/-- Completed residue evaluation is the residue-fraction map followed by the canonical map into the
uniform completion. -/
@[simp]
theorem completedResidueMap_apply (x : BerkovichSpectrumOver K A) (a : A) :
    completedResidueMap K A x a =
      (residueFractionMap K A x a : CompletedResidueField K A x) := sorry

@[simp]
theorem norm_completedResidueMap (x : BerkovichSpectrumOver K A) (a : A) :
    ‖completedResidueMap K A x a‖ = x a := sorry

noncomputable instance completedResidueAlgebra (x : BerkovichSpectrumOver K A) :
    Algebra K (CompletedResidueField K A x) := sorry

noncomputable instance completedResidueNormedAlgebra (x : BerkovichSpectrumOver K A) :
    NormedAlgebra K (CompletedResidueField K A x) := sorry

noncomputable instance completedResidueNontriviallyNormedField
    (x : BerkovichSpectrumOver K A) :
    NontriviallyNormedField (CompletedResidueField K A x) := sorry

/-- The completed residue evaluation as a `K`-algebra homomorphism. -/
noncomputable def completedResidueAlgHom (x : BerkovichSpectrumOver K A) :
    A →ₐ[K] CompletedResidueField K A x := sorry

/-- The bundled algebra homomorphism has the canonical completed residue map as its underlying ring
homomorphism. -/
@[simp]
theorem completedResidueAlgHom_apply (x : BerkovichSpectrumOver K A) (a : A) :
    completedResidueAlgHom K A x a = completedResidueMap K A x a := sorry

/-- The scalar embedding in the completed residue field is induced by evaluation on the original
algebra. -/
@[simp]
theorem algebraMap_completedResidueField (x : BerkovichSpectrumOver K A) (r : K) :
    algebraMap K (CompletedResidueField K A x) r =
      completedResidueMap K A x (algebraMap K A r) := sorry

@[simp]
theorem norm_completedResidueAlgHom (x : BerkovichSpectrumOver K A) (a : A) :
    ‖completedResidueAlgHom K A x a‖ = x a := sorry

@[simp]
theorem ker_completedResidueMap (x : BerkovichSpectrumOver K A) :
    RingHom.ker (completedResidueMap K A x) = x.kernel := sorry

/-- The rational locus cut out by `|fᵢ(x)| ≤ |g(x)|`. -/
def rationalDomainSet {n : ℕ} (g : A) (f : Fin n → A) : Set (BerkovichSpectrumOver K A) :=
  {x | ∀ i, x (f i) ≤ x g}

/-- A rational domain as a topological subspace of the relative spectrum. -/
abbrev RationalDomain {n : ℕ} (g : A) (f : Fin n → A) :=
  ↥(rationalDomainSet K A g f)

namespace RationalDomain

/-- The inclusion of a rational domain into its ambient relative spectrum. -/
def inclusion {n : ℕ} (g : A) (f : Fin n → A) :
    RationalDomain K A g f → BerkovichSpectrumOver K A := Subtype.val

/-- Rational loci are closed in the relative Berkovich spectrum. -/
theorem isClosed_rationalDomainSet {n : ℕ} (g : A) (f : Fin n → A) :
    IsClosed (rationalDomainSet K A g f) := by
  rw [show rationalDomainSet K A g f = ⋂ i, {x | x (f i) ≤ x g} by
    ext x
    simp [rationalDomainSet]]
  exact isClosed_iInter fun i ↦ isClosed_le
    (BerkovichSpectrumOver.continuous_eval K A _)
    (BerkovichSpectrumOver.continuous_eval K A _)

noncomputable instance rationalDomainCompactSpace {n : ℕ} (g : A) (f : Fin n → A) :
    CompactSpace (RationalDomain K A g f) := sorry

/-- Rational domains are compact. -/
theorem isCompact_univ {n : ℕ} (g : A) (f : Fin n → A) :
    IsCompact (Set.univ : Set (RationalDomain K A g f)) :=
  _root_.isCompact_univ

/-- Evaluation at an ambient algebra element is continuous on a rational domain. -/
theorem continuous_eval {n : ℕ} (g : A) (f : Fin n → A) (a : A) :
    Continuous fun x : RationalDomain K A g f ↦ (x.1 : A → ℝ) a :=
  (BerkovichSpectrumOver.continuous_eval K A a).comp continuous_subtype_val

/-- The denominator of a rational datum does not vanish on its rational domain. -/
theorem denominator_ne_zero {n : ℕ} {g : A} {f : Fin n → A}
    (hgf : IsRationalDatum g f) (x : RationalDomain K A g f) : x.1 g ≠ 0 := by
  intro hg
  have hnonneg (a : A) : 0 ≤ x.1 a := BerkovichSpectrum.nonneg A x.1.toBerkovichSpectrum a
  have hfi (i : Fin n) : x.1 (f i) = 0 :=
    le_antisymm ((x.2 i).trans_eq hg) (hnonneg (f i))
  have hgenerators : Set.insert g (Set.range f) ⊆ x.1.kernel := by
    intro a ha
    change x.1 a = 0
    rcases ha with rfl | ⟨i, rfl⟩
    · exact hg
    · exact hfi i
  have htop : (⊤ : Ideal A) ≤ x.1.kernel := by
    rw [← hgf]
    exact Ideal.span_le.2 hgenerators
  exact x.1.kernel_isPrime.ne_top (top_unique htop)

/-- The relative spectrum of a rational localization is its associated rational domain. -/
noncomputable def localizationSpectrumHomeomorph {n : ℕ} {g : A} {f : Fin n → A}
    (hgf : IsRationalDatum g f) :
    BerkovichSpectrumOver K (RationalLocalization K A n g f) ≃ₜ
      RationalDomain K A g f := sorry

/-- Under the rational-localization homeomorphism, evaluation of an ambient function is pullback
along the canonical base map. -/
@[simp]
theorem localizationSpectrumHomeomorph_apply_baseMap
    {n : ℕ} {g : A} {f : Fin n → A} (hgf : IsRationalDatum g f)
    (x : BerkovichSpectrumOver K (RationalLocalization K A n g f)) (a : A) :
    ((localizationSpectrumHomeomorph K A hgf x).1 : A → ℝ) a =
      x (RationalLocalization.baseMap K A n g f a) := sorry

end RationalDomain

end BerkovichSpectrumOver


/-! ### The rational basis and its structure sheaf -/

/-- A rational subdomain of an affinoid Berkovich spectrum, bundled with the rational datum that
defines it. -/
structure AffinoidRationalSubdomain
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] where
  n : ℕ
  g : A
  f : Fin n → A
  isRational : IsRationalDatum g f

namespace AffinoidRationalSubdomain

/-- The point set of a bundled rational subdomain. -/
def carrier (U : AffinoidRationalSubdomain K A) : Set (BerkovichSpectrumOver K A) :=
  BerkovichSpectrumOver.rationalDomainSet K A U.g U.f

/-- Analytic functions on a rational subdomain are its rational localization. -/
abbrev Sections (U : AffinoidRationalSubdomain K A) :=
  RationalLocalization K A U.n U.g U.f

/-- The intersection of two rational subdomains, represented again by a rational datum. -/
noncomputable def inter (U V : AffinoidRationalSubdomain K A) :
    AffinoidRationalSubdomain K A := sorry

@[simp]
theorem carrier_inter (U V : AffinoidRationalSubdomain K A) :
    (inter K A U V).carrier = U.carrier ∩ V.carrier := sorry

/-- The intersection is contained in its left factor. -/
theorem inter_subset_left (U V : AffinoidRationalSubdomain K A) :
    (inter K A U V).carrier ⊆ U.carrier := sorry

/-- The intersection is contained in its right factor. -/
theorem inter_subset_right (U V : AffinoidRationalSubdomain K A) :
    (inter K A U V).carrier ⊆ V.carrier := sorry

/-- Restriction of analytic functions along an inclusion of rational subdomains. -/
noncomputable def restriction {U V : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) : ContinuousAlgHom K V.Sections U.Sections := sorry

@[simp]
theorem restriction_id (U : AffinoidRationalSubdomain K A) :
    restriction K A (U := U) (V := U) Set.Subset.rfl =
      ContinuousAlgHom.id K U.Sections := sorry

@[simp]
theorem restriction_comp {U V W : AffinoidRationalSubdomain K A}
    (hUV : U.carrier ⊆ V.carrier) (hWU : W.carrier ⊆ U.carrier) :
    (restriction K A hWU).comp (restriction K A hUV) =
      restriction K A (hWU.trans hUV) := sorry

/-- A finite rational cover of a rational subdomain. -/
structure Cover (U : AffinoidRationalSubdomain K A) where
  m : ℕ
  domain : Fin m → AffinoidRationalSubdomain K A
  subset : ∀ i, (domain i).carrier ⊆ U.carrier
  covers : U.carrier = ⋃ i, (domain i).carrier

namespace Cover

/-- A family of sections on a rational cover is compatible when its restrictions agree on every
pairwise intersection. -/
def IsCompatible {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U)
    (s : ∀ i, (𝒰.domain i).Sections) : Prop :=
  ∀ i j,
    restriction K A (inter_subset_left K A (𝒰.domain i) (𝒰.domain j)) (s i) =
      restriction K A (inter_subset_right K A (𝒰.domain i) (𝒰.domain j)) (s j)

/-- The rational-localization presheaf satisfies the sheaf condition on finite rational covers. -/
theorem existsUnique_glue {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U)
    (s : ∀ i, (𝒰.domain i).Sections) (hs : IsCompatible K A 𝒰 s) :
    ∃! t : U.Sections, ∀ i, restriction K A (𝒰.subset i) t = s i := sorry

/-- The augmented Čech complex of the rational-localization presheaf for a finite rational cover. -/
noncomputable def augmentedCechComplex {U : AffinoidRationalSubdomain K A}
    (𝒰 : Cover K A U) : CochainComplex (ModuleCat K) ℕ := sorry

/-- Degree zero of the augmented Čech complex is the ring of functions on the covered domain. -/
noncomputable def augmentedCechComplexDegreeZeroIso
    {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (𝒰.augmentedCechComplex K A).X 0 ≅ ModuleCat.of K U.Sections := sorry

/-- Tate acyclicity: the augmented Čech complex of every finite rational cover is exact. -/
theorem tateAcyclicity {U : AffinoidRationalSubdomain K A} (𝒰 : Cover K A U) :
    (𝒰.augmentedCechComplex K A).Acyclic := sorry

end Cover

end AffinoidRationalSubdomain
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

/-- The relative Berkovich spectrum of a nonzero affinoid algebra is nonempty. -/
theorem nonempty_berkovichSpectrumOver [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    Nonempty (BerkovichSpectrumOver K A) := by
  rcases hA with ⟨_⟩
  exact (Rigid.BerkovichSpectrumOver.nonempty_of_nontrivial K A).map fun x ↦
    ⟨⟨x.toBerkovichSpectrum.seminorm, x.toBerkovichSpectrum.le_norm'⟩, x.map_algebraMap'⟩

/-- The relative Berkovich spectrum of an affinoid algebra is compact. -/
theorem isCompact_univ_berkovichSpectrumOver (hA : IsAffinoidAlgebra K A) :
    IsCompact (Set.univ : Set (BerkovichSpectrumOver K A)) := by
  rcases hA with ⟨_⟩
  exact BerkovichSpectrumOver.isCompact_univ K A

end AffinoidAlgebra


/-- A universe-bounded strict affinoid algebra, used as explicit local-model data for global
analytic spaces. -/
structure AffinoidAlgebraModel
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  isAffinoid : IsAffinoidAlgebra K A

attribute [instance] AffinoidAlgebraModel.commRing AffinoidAlgebraModel.algebra
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

namespace Point

/-- The map on analytic points induced by a rigid-space morphism. -/
noncomputable def map {X Y : RigidSpace K} (f : X ⟶ Y) : Point K X → Point K Y := sorry

@[simp]
theorem map_id (X : RigidSpace K) : map K (𝟙 X) = id := sorry

@[simp]
theorem map_comp {X Y Z : RigidSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map K (f ≫ g) = map K g ∘ map K f := sorry

/-- An analytic isomorphism induces an equivalence on points. -/
noncomputable def equivOfIso {X Y : RigidSpace K} (e : X ≅ Y) : Point K X ≃ Point K Y where
  toFun := map K e.hom
  invFun := map K e.inv
  left_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp K e.hom e.inv).symm x
  right_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp K e.inv e.hom).symm x

end Point

/-- The functor assigning to a rigid space its type of analytic points. -/
noncomputable def pointFunctor : RigidSpace K ⥤ Type (u + 1) where
  obj X := Point K X
  map f := TypeCat.ofHom (Point.map K f)
  map_id X := by apply TypeCat.homEquiv.injective; exact Point.map_id K X
  map_comp f g := by apply TypeCat.homEquiv.injective; exact Point.map_comp K f g

/-- An admissible open of a rigid space. -/
def AdmissibleOpen (X : RigidSpace K) : Type (u + 1) := sorry

namespace AdmissibleOpen

/-- The analytic points belonging to an admissible open. -/
noncomputable def carrier {X : RigidSpace K} (U : AdmissibleOpen K X) :
    Set (Point K X) := sorry

/-- Admissible opens are determined by their point sets. -/
@[ext]
theorem ext {X : RigidSpace K} {U V : AdmissibleOpen K X}
    (h : U.carrier = V.carrier) : U = V := sorry

/-- The full admissible open. -/
noncomputable def top (X : RigidSpace K) : AdmissibleOpen K X := sorry

@[simp]
theorem carrier_top (X : RigidSpace K) :
    (top K X).carrier = Set.univ := sorry

/-- The intersection of two admissible opens. -/
noncomputable def inter {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    AdmissibleOpen K X := sorry

@[simp]
theorem carrier_inter {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    (inter K U V).carrier = U.carrier ∩ V.carrier := sorry

/-- The intersection is contained in its left factor. -/
theorem inter_subset_left {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    (inter K U V).carrier ⊆ U.carrier := sorry

/-- The intersection is contained in its right factor. -/
theorem inter_subset_right {X : RigidSpace K} (U V : AdmissibleOpen K X) :
    (inter K U V).carrier ⊆ V.carrier := sorry

/-- A family is an admissible cover of an admissible open in the rigid Grothendieck topology. -/
def IsCover {X : RigidSpace K} {ι : Type (u + 1)}
    (U : ι → AdmissibleOpen K X) (V : AdmissibleOpen K X) : Prop := sorry

namespace IsCover

/-- A one-member family covers its member. -/
theorem singleton {X : RigidSpace K} (V : AdmissibleOpen K X) :
    IsCover K (fun _ : PUnit ↦ V) V := sorry

/-- Admissible covers are stable under intersection with another admissible open. -/
theorem pullback {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (h : IsCover K U V)
    (W : AdmissibleOpen K X) :
    IsCover K (fun i ↦ inter K (U i) W) (inter K V W) := sorry

/-- Admissible coverings are transitive. -/
theorem trans {X : RigidSpace K} {ι : Type (u + 1)} {κ : ι → Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (hU : IsCover K U V)
    (W : ∀ i, κ i → AdmissibleOpen K X) (hW : ∀ i, IsCover K (W i) (U i)) :
    IsCover K (fun p : Σ i, κ i ↦ W p.1 p.2) V := sorry

/-- Every member of an admissible cover is contained in the covered open. -/
theorem subset {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (h : IsCover K U V) (i : ι) :
    (U i).carrier ⊆ V.carrier := sorry

/-- An admissible cover covers the underlying point set. -/
theorem iUnion_carrier {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X} (h : IsCover K U V) :
    V.carrier = ⋃ i, (U i).carrier := sorry

end IsCover

/-- An admissible open is quasi-compact for the admissible topology. -/
def IsQuasiCompact {X : RigidSpace K} (U : AdmissibleOpen K X) : Prop := sorry

/-- Quasi-compactness means that every admissible cover has a finite admissible subcover. -/
theorem isQuasiCompact_iff {X : RigidSpace K} (U : AdmissibleOpen K X) :
    IsQuasiCompact K U ↔
      ∀ {ι : Type (u + 1)} (V : ι → AdmissibleOpen K X), IsCover K V U →
        ∃ s : Set ι, s.Finite ∧ IsCover K (fun i : s ↦ V i.1) U := sorry

end AdmissibleOpen


namespace StructureSheaf

/-- Analytic functions on an admissible open of a rigid space. -/
noncomputable def Sections {X : RigidSpace K} (U : AdmissibleOpen K X) : Type u := sorry

noncomputable instance sectionsCommRing {X : RigidSpace K} (U : AdmissibleOpen K X) :
    CommRing (Sections K U) := sorry

noncomputable instance sectionsAlgebra {X : RigidSpace K} (U : AdmissibleOpen K X) :
    Algebra K (Sections K U) := sorry

/-- Restriction of analytic functions. -/
noncomputable def restriction {X : RigidSpace K} {U V : AdmissibleOpen K X}
    (hUV : U.carrier ⊆ V.carrier) : Sections K V →ₐ[K] Sections K U := sorry

@[simp]
theorem restriction_id {X : RigidSpace K} (U : AdmissibleOpen K X) :
    restriction K (U := U) (V := U) Set.Subset.rfl = AlgHom.id K (Sections K U) := sorry

@[simp]
theorem restriction_comp {X : RigidSpace K} {U V W : AdmissibleOpen K X}
    (hUV : U.carrier ⊆ V.carrier) (hWU : W.carrier ⊆ U.carrier) :
    (restriction K hWU).comp (restriction K hUV) = restriction K (hWU.trans hUV) := sorry

/-- Compatibility of local sections on an admissible cover. -/
def IsCompatible {X : RigidSpace K} {ι : Type (u + 1)}
    (U : ι → AdmissibleOpen K X) (s : ∀ i, Sections K (U i)) : Prop :=
  ∀ i j,
    restriction K (AdmissibleOpen.inter_subset_left K (U i) (U j)) (s i) =
      restriction K (AdmissibleOpen.inter_subset_right K (U i) (U j)) (s j)

/-- The rigid analytic structure presheaf is a sheaf for admissible covers. -/
theorem existsUnique_glue {X : RigidSpace K} {ι : Type (u + 1)}
    {U : ι → AdmissibleOpen K X} {V : AdmissibleOpen K X}
    (hU : AdmissibleOpen.IsCover K U V) (s : ∀ i, Sections K (U i))
    (hs : IsCompatible K U s) :
    ∃! t : Sections K V, ∀ i, restriction K (hU.subset K i) t = s i := sorry

/-- The local ring of germs at an analytic point. -/
noncomputable def Stalk (X : RigidSpace K) (x : Point K X) : Type u := sorry

noncomputable instance stalkCommRing (X : RigidSpace K) (x : Point K X) :
    CommRing (Stalk K X x) := sorry

noncomputable instance stalkAlgebra (X : RigidSpace K) (x : Point K X) :
    Algebra K (Stalk K X x) := sorry

noncomputable instance stalkIsLocalRing (X : RigidSpace K) (x : Point K X) :
    IsLocalRing (Stalk K X x) := sorry

/-- The germ of a section at a point of its domain. -/
noncomputable def germ {X : RigidSpace K} {U : AdmissibleOpen K X}
    {x : Point K X} (hx : x ∈ U.carrier) : Sections K U →ₐ[K] Stalk K X x := sorry

end StructureSheaf

/-- Restriction of a rigid space to an admissible open. -/
noncomputable def restrict {X : RigidSpace K} (U : AdmissibleOpen K X) : RigidSpace K := sorry

/-- The points of a restricted rigid space are the points of the corresponding admissible open. -/
noncomputable def pointsRestrictEquiv {X : RigidSpace K} (U : AdmissibleOpen K X) :
    Point K (restrict K U) ≃ ↥U.carrier := sorry

/-- Concrete data of an analytic morphism of rigid spaces: a map on points, inverse images of
admissible opens, compatible pullback maps on sections, and local maps on stalks. -/
structure AnalyticMorphismData (X Y : RigidSpace K) where
  base : Point K X → Point K Y
  preimage : AdmissibleOpen K Y → AdmissibleOpen K X
  mem_preimage : ∀ x U, x ∈ (preimage U).carrier ↔ base x ∈ U.carrier
  preimage_mono : ∀ {U V}, U.carrier ⊆ V.carrier →
    (preimage U).carrier ⊆ (preimage V).carrier
  pullback : ∀ U, StructureSheaf.Sections K U →ₐ[K]
    StructureSheaf.Sections K (preimage U)
  pullback_restriction : ∀ {U V} (hUV : U.carrier ⊆ V.carrier),
    (StructureSheaf.restriction K (preimage_mono hUV)).comp (pullback V) =
      (pullback U).comp (StructureSheaf.restriction K hUV)
  stalkMap : ∀ x, StructureSheaf.Stalk K Y (base x) →ₐ[K] StructureSheaf.Stalk K X x
  stalkMap_isLocal : ∀ x, IsLocalHom (stalkMap x)
  pullback_germ : ∀ (x) (U) (hx : base x ∈ U.carrier) (s : StructureSheaf.Sections K U),
    stalkMap x (StructureSheaf.germ K hx s) =
      StructureSheaf.germ K ((mem_preimage x U).2 hx) (pullback U s)

namespace AnalyticMorphismData

/-- Identity analytic-morphism data. -/
noncomputable def id (X : RigidSpace K) : AnalyticMorphismData K X X := sorry

/-- Composition of analytic-morphism data. -/
noncomputable def comp {X Y Z : RigidSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z) :
    AnalyticMorphismData K X Z := sorry

@[simp]
theorem id_base (X : RigidSpace K) : (id K X).base = _root_.id := sorry

@[simp]
theorem id_preimage (X : RigidSpace K) (U : AdmissibleOpen K X) :
    (id K X).preimage U = U := sorry

@[simp]
theorem comp_base {X Y Z : RigidSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z) :
    (comp K f g).base = g.base ∘ f.base := sorry

@[simp]
theorem comp_preimage {X Y Z : RigidSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z)
    (U : AdmissibleOpen K Z) :
    (comp K f g).preimage U = f.preimage (g.preimage U) := sorry

end AnalyticMorphismData

/-- Rigid-space morphisms are exactly compatible locally ringed morphism data. -/
noncomputable def analyticHomEquiv (X Y : RigidSpace K) :
    (X ⟶ Y) ≃ AnalyticMorphismData K X Y := sorry

@[simp]
theorem analyticHomEquiv_base {X Y : RigidSpace K} (f : X ⟶ Y) :
    (analyticHomEquiv K X Y f).base = Point.map K f := sorry

@[simp]
theorem analyticHomEquiv_id (X : RigidSpace K) :
    analyticHomEquiv K X X (𝟙 X) = AnalyticMorphismData.id K X := sorry

@[simp]
theorem analyticHomEquiv_comp {X Y Z : RigidSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    analyticHomEquiv K X Z (f ≫ g) =
      AnalyticMorphismData.comp K (analyticHomEquiv K X Y f)
        (analyticHomEquiv K Y Z g) := sorry
/-- An affinoid domain in a rigid space. -/
def AffinoidDomain (X : RigidSpace K) : Type (u + 1) := sorry

namespace AffinoidDomain

/-- The admissible open underlying an affinoid domain. -/
noncomputable def toAdmissibleOpen {X : RigidSpace K} (U : AffinoidDomain K X) :
    AdmissibleOpen K X := sorry

/-- The points belonging to an affinoid domain. -/
noncomputable def carrier {X : RigidSpace K} (U : AffinoidDomain K X) :
    Set (Point K X) := sorry

/-- The point set of an affinoid domain agrees with that of its underlying admissible open. -/
@[simp]
theorem carrier_toAdmissibleOpen {X : RigidSpace K} (U : AffinoidDomain K X) :
    U.toAdmissibleOpen.carrier = U.carrier := sorry

/-- Two affinoid domains meet when their point sets intersect. -/
def Meets {X : RigidSpace K} (U V : AffinoidDomain K X) : Prop :=
  (U.carrier ∩ V.carrier).Nonempty

end AffinoidDomain

/-- A family of affinoid domains is an admissible cover. -/
def IsAdmissibleAffinoidCover {X : RigidSpace K} {ι : Type (u + 1)}
    (U : ι → AffinoidDomain K X) : Prop := sorry


/-- Affinoid admissible covers are precisely admissible-open covers of the full space. -/
theorem isAdmissibleAffinoidCover_iff {X : RigidSpace K} {ι : Type (u + 1)}
    (U : ι → AffinoidDomain K X) :
    IsAdmissibleAffinoidCover K U ↔
      AdmissibleOpen.IsCover K (fun i ↦ (U i).toAdmissibleOpen) (AdmissibleOpen.top K X) := sorry
/-- An admissible affinoid cover of a rigid space. -/
structure AffinoidCover (X : RigidSpace K) : Type (u + 2) where
  /-- The indexing type of the cover. -/
  index : Type (u + 1)
  /-- The affinoid domain at an index. -/
  domain : index → AffinoidDomain K X
  /-- The domains form an admissible cover. -/
  isAdmissible : IsAdmissibleAffinoidCover K domain

namespace AffinoidCover

/-- Every point lies in some member of an admissible affinoid cover. -/
theorem exists_mem_carrier {X : RigidSpace K} (𝒰 : AffinoidCover K X) (x : Point K X) :
    ∃ i, x ∈ (𝒰.domain i).carrier := sorry

/-- A cover is of finite type when every member meets only finitely many other members.

This is the definition preceding Theorem 1.6.1 of Berkovich's *Étale cohomology for
non-Archimedean analytic spaces*. -/
def IsFiniteType {X : RigidSpace K} (𝒰 : AffinoidCover K X) : Prop :=
  ∀ i, Set.Finite {j : 𝒰.index |
    AffinoidDomain.Meets K (𝒰.domain i) (𝒰.domain j)}

end AffinoidCover

/-- A closed immersion of rigid spaces. -/
def IsClosedImmersion {X Y : RigidSpace K} (f : X ⟶ Y) : Prop := sorry

/-- Every point has an admissible affinoid neighborhood. -/
def IsLocallyAffinoid (X : RigidSpace K) : Prop := sorry

/-- Intersections of quasi-compact admissible opens are quasi-compact. -/
def IsQuasiSeparated (X : RigidSpace K) : Prop := sorry

/-- The rigid space has an admissible affinoid cover of finite type. -/
def HasAffinoidCoverOfFiniteType (X : RigidSpace K) : Prop :=
  ∃ 𝒰 : AffinoidCover K X, 𝒰.IsFiniteType

/-- Compatibility name for the rigid-side finiteness condition in the comparison theorem. -/
abbrev IsParacompact (X : RigidSpace K) : Prop := HasAffinoidCoverOfFiniteType K X

/-- The diagonal is a closed immersion. -/
def IsSeparated (X : RigidSpace K) : Prop := sorry

/-- Every rigid analytic space is locally affinoid by definition. -/
theorem isLocallyAffinoid (X : RigidSpace K) : IsLocallyAffinoid K X := sorry

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
    IsParacompact K X ↔ ∃ 𝒰 : AffinoidCover K X, 𝒰.IsFiniteType := Iff.rfl

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

/-- Having an affinoid cover of finite type is invariant under analytic isomorphism. -/
theorem hasAffinoidCoverOfFiniteType_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    HasAffinoidCoverOfFiniteType K X ↔ HasAffinoidCoverOfFiniteType K Y := sorry

/-- The compatibility finiteness predicate is invariant under analytic isomorphism. -/
theorem isParacompact_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    IsParacompact K X ↔ IsParacompact K Y := sorry

/-- Separatedness is invariant under analytic isomorphism. -/
theorem isSeparated_iff_of_iso {X Y : RigidSpace K} (e : X ≅ Y) :
    IsSeparated K X ↔ IsSeparated K Y := sorry

/-- The rigid space associated to a strict affinoid algebra. -/
noncomputable def ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : RigidSpace K := sorry

/-- Global analytic functions on an affinoid rigid space recover its coordinate algebra. -/
noncomputable def globalSectionsOfAffinoidEquiv {A : Type u} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    StructureSheaf.Sections K (AdmissibleOpen.top K (ofAffinoid K hA)) ≃ₐ[K] A := sorry

namespace AffinoidDomain

/-- The coordinate algebra chosen by an affinoid domain. -/
noncomputable def model {X : RigidSpace K} (U : AffinoidDomain K X) :
    AffinoidAlgebraModel K := sorry

/-- Restriction to an affinoid domain is analytically isomorphic to the spectrum of its coordinate
algebra. -/
noncomputable def modelIso {X : RigidSpace K} (U : AffinoidDomain K X) :
    restrict K U.toAdmissibleOpen ≅ ofAffinoid K U.model.isAffinoid := sorry

end AffinoidDomain

/-- The points of an affinoid rigid space are the maximal ideals of its coordinate algebra. -/
noncomputable def pointsOfAffinoidEquiv {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : Point K (ofAffinoid K hA) ≃ MaximalSpectrum A := sorry

/-- Pullback of maximal ideals along a morphism of affinoid algebras. -/
noncomputable def maximalSpectrumComap {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    MaximalSpectrum B → MaximalSpectrum A := sorry

/-- The underlying ideal of pullback on maximal spectra is ideal-theoretic comap. -/
@[simp]
theorem maximalSpectrumComap_asIdeal {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (x : MaximalSpectrum B) :
    (maximalSpectrumComap K hA hB f x).asIdeal = Ideal.comap f x.asIdeal := sorry

@[simp]
theorem maximalSpectrumComap_id {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    maximalSpectrumComap K hA hA (AlgHom.id K A) = id := sorry

@[simp]
theorem maximalSpectrumComap_comp {A : Type v} {B : Type w} {C : Type z}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    maximalSpectrumComap K hA hC (g.comp f) =
      maximalSpectrumComap K hA hB f ∘ maximalSpectrumComap K hB hC g := sorry

/-- The morphism of affinoid rigid spaces induced contravariantly by an algebra homomorphism. -/
noncomputable def ofAffinoidMap {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    ofAffinoid K hB ⟶ ofAffinoid K hA := sorry

@[simp]
theorem ofAffinoidMap_id {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    ofAffinoidMap K hA hA (AlgHom.id K A) = 𝟙 (ofAffinoid K hA) := sorry

@[simp]
theorem ofAffinoidMap_comp {A : Type v} {B : Type w} {C : Type*}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    ofAffinoidMap K hB hC g ≫ ofAffinoidMap K hA hB f =
      ofAffinoidMap K hA hC (g.comp f) := sorry

/-- The affinoid point equivalence is natural in the coordinate algebra. -/
theorem pointsOfAffinoidEquiv_naturality {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (x : Point K (ofAffinoid K hB)) :
    pointsOfAffinoidEquiv K hA (Point.map K (ofAffinoidMap K hA hB f) x) =
      maximalSpectrumComap K hA hB f (pointsOfAffinoidEquiv K hB x) := sorry

/-- An affinoid rigid space is locally affinoid. -/
theorem isLocallyAffinoid_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsLocallyAffinoid K (ofAffinoid K hA) := sorry

/-- An affinoid rigid space is quasi-separated. -/
theorem isQuasiSeparated_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : IsQuasiSeparated K (ofAffinoid K hA) := sorry

/-- An affinoid rigid space has an affinoid cover of finite type. -/
theorem hasAffinoidCoverOfFiniteType_ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    HasAffinoidCoverOfFiniteType K (ofAffinoid K hA) := sorry

/-- An affinoid rigid space satisfies the compatibility finiteness predicate. -/
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

namespace Point

/-- The map on points induced by a morphism of Berkovich spaces. -/
noncomputable def map {X Y : BerkovichSpace K} (f : X ⟶ Y) : Point K X → Point K Y := sorry

/-- The map on points induced by an analytic morphism is continuous. -/
theorem continuous_map {X Y : BerkovichSpace K} (f : X ⟶ Y) : Continuous (map K f) := sorry

@[simp]
theorem map_id (X : BerkovichSpace K) : map K (𝟙 X) = id := sorry

@[simp]
theorem map_comp {X Y Z : BerkovichSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map K (f ≫ g) = map K g ∘ map K f := sorry

/-- An analytic isomorphism induces a homeomorphism on underlying point spaces. -/
noncomputable def homeomorphOfIso {X Y : BerkovichSpace K} (e : X ≅ Y) :
    Point K X ≃ₜ Point K Y where
  toFun := map K e.hom
  invFun := map K e.inv
  left_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp K e.hom e.inv).symm x
  right_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp K e.inv e.hom).symm x
  continuous_toFun := continuous_map K e.hom
  continuous_invFun := continuous_map K e.inv

end Point

/-- The functor assigning to a Berkovich space its underlying topological space. -/
noncomputable def pointFunctor : BerkovichSpace K ⥤ TopCat.{u + 1} where
  obj X := TopCat.of (Point K X)
  map f := TopCat.ofHom (ContinuousMap.mk (Point.map K f) (Point.continuous_map K f))
  map_id X := by
    apply TopCat.hom_ext
    ext x
    exact congr_fun (Point.map_id K X) x
  map_comp f g := by
    apply TopCat.hom_ext
    ext x
    exact congr_fun (Point.map_comp K f g) x

namespace StructureSheaf

/-- Analytic functions on an open subset of a Berkovich space. -/
noncomputable def Sections {X : BerkovichSpace K}
    (U : TopologicalSpace.Opens (Point K X)) : Type u := sorry

noncomputable instance sectionsCommRing {X : BerkovichSpace K}
    (U : TopologicalSpace.Opens (Point K X)) : CommRing (Sections K U) := sorry

noncomputable instance sectionsAlgebra {X : BerkovichSpace K}
    (U : TopologicalSpace.Opens (Point K X)) : Algebra K (Sections K U) := sorry

/-- Restriction of Berkovich analytic functions. -/
noncomputable def restriction {X : BerkovichSpace K}
    {U V : TopologicalSpace.Opens (Point K X)} (hUV : U ≤ V) :
    Sections K V →ₐ[K] Sections K U := sorry

@[simp]
theorem restriction_id {X : BerkovichSpace K}
    (U : TopologicalSpace.Opens (Point K X)) :
    restriction K (U := U) (V := U) le_rfl = AlgHom.id K (Sections K U) := sorry

@[simp]
theorem restriction_comp {X : BerkovichSpace K}
    {U V W : TopologicalSpace.Opens (Point K X)} (hUV : U ≤ V) (hWU : W ≤ U) :
    (restriction K hWU).comp (restriction K hUV) = restriction K (hWU.trans hUV) := sorry

/-- Compatibility of analytic functions on an ordinary open cover. -/
def IsCompatible {X : BerkovichSpace K} {ι : Type (u + 1)}
    (U : ι → TopologicalSpace.Opens (Point K X)) (s : ∀ i, Sections K (U i)) : Prop :=
  ∀ i j,
    restriction K inf_le_left (s i) = restriction K inf_le_right (s j)

/-- The Berkovich analytic structure presheaf satisfies the sheaf condition. -/
theorem existsUnique_glue {X : BerkovichSpace K} {ι : Type (u + 1)}
    (U : ι → TopologicalSpace.Opens (Point K X))
    (V : TopologicalSpace.Opens (Point K X)) (hsub : ∀ i, U i ≤ V)
    (hcover : V = ⨆ i, U i) (s : ∀ i, Sections K (U i))
    (hs : IsCompatible K U s) :
    ∃! t : Sections K V, ∀ i, restriction K (hsub i) t = s i := sorry

/-- The local ring of germs at a Berkovich point. -/
noncomputable def Stalk (X : BerkovichSpace K) (x : Point K X) : Type u := sorry

noncomputable instance stalkCommRing (X : BerkovichSpace K) (x : Point K X) :
    CommRing (Stalk K X x) := sorry

noncomputable instance stalkAlgebra (X : BerkovichSpace K) (x : Point K X) :
    Algebra K (Stalk K X x) := sorry

noncomputable instance stalkIsLocalRing (X : BerkovichSpace K) (x : Point K X) :
    IsLocalRing (Stalk K X x) := sorry

/-- The germ of a Berkovich analytic function. -/
noncomputable def germ {X : BerkovichSpace K}
    {U : TopologicalSpace.Opens (Point K X)} {x : Point K X}
    (hx : x ∈ U) : Sections K U →ₐ[K] Stalk K X x := sorry

end StructureSheaf

/-- Concrete data of a morphism of Berkovich analytic spaces. -/
structure AnalyticMorphismData (X Y : BerkovichSpace K) where
  base : Point K X → Point K Y
  continuous_base : Continuous base
  preimage : TopologicalSpace.Opens (Point K Y) → TopologicalSpace.Opens (Point K X)
  mem_preimage : ∀ x U, x ∈ preimage U ↔ base x ∈ U
  preimage_mono : ∀ {U V}, U ≤ V → preimage U ≤ preimage V
  pullback : ∀ U, StructureSheaf.Sections K U →ₐ[K]
    StructureSheaf.Sections K (preimage U)
  pullback_restriction : ∀ {U V} (hUV : U ≤ V),
    (StructureSheaf.restriction K (preimage_mono hUV)).comp (pullback V) =
      (pullback U).comp (StructureSheaf.restriction K hUV)
  stalkMap : ∀ x, StructureSheaf.Stalk K Y (base x) →ₐ[K] StructureSheaf.Stalk K X x
  stalkMap_isLocal : ∀ x, IsLocalHom (stalkMap x)
  pullback_germ : ∀ (x) (U) (hx : base x ∈ U) (s : StructureSheaf.Sections K U),
    stalkMap x (StructureSheaf.germ K hx s) =
      StructureSheaf.germ K ((mem_preimage x U).2 hx) (pullback U s)

namespace AnalyticMorphismData

noncomputable def id (X : BerkovichSpace K) : AnalyticMorphismData K X X := sorry

noncomputable def comp {X Y Z : BerkovichSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z) :
    AnalyticMorphismData K X Z := sorry

@[simp]
theorem id_base (X : BerkovichSpace K) : (id K X).base = _root_.id := sorry

@[simp]
theorem id_preimage (X : BerkovichSpace K)
    (U : TopologicalSpace.Opens (Point K X)) : (id K X).preimage U = U := sorry

@[simp]
theorem comp_base {X Y Z : BerkovichSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z) :
    (comp K f g).base = g.base ∘ f.base := sorry

@[simp]
theorem comp_preimage {X Y Z : BerkovichSpace K}
    (f : AnalyticMorphismData K X Y) (g : AnalyticMorphismData K Y Z)
    (U : TopologicalSpace.Opens (Point K Z)) :
    (comp K f g).preimage U = f.preimage (g.preimage U) := sorry

end AnalyticMorphismData

/-- Berkovich-space morphisms are exactly compatible locally ringed morphism data with continuous
maps on points. -/
noncomputable def analyticHomEquiv (X Y : BerkovichSpace K) :
    (X ⟶ Y) ≃ AnalyticMorphismData K X Y := sorry

@[simp]
theorem analyticHomEquiv_base {X Y : BerkovichSpace K} (f : X ⟶ Y) :
    (analyticHomEquiv K X Y f).base = Point.map K f := sorry

@[simp]
theorem analyticHomEquiv_id (X : BerkovichSpace K) :
    analyticHomEquiv K X X (𝟙 X) = AnalyticMorphismData.id K X := sorry

@[simp]
theorem analyticHomEquiv_comp {X Y Z : BerkovichSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    analyticHomEquiv K X Z (f ≫ g) =
      AnalyticMorphismData.comp K (analyticHomEquiv K X Y f)
        (analyticHomEquiv K Y Z g) := sorry

/-- An affinoid domain in a Berkovich space. -/
def AffinoidDomain (X : BerkovichSpace K) : Type (u + 1) := sorry

namespace AffinoidDomain

/-- The set of points belonging to an affinoid domain. -/
noncomputable def carrier {X : BerkovichSpace K} (U : AffinoidDomain K X) :
    Set (Point K X) := sorry

/-- An affinoid domain is modeled on a strict affinoid algebra. -/
def IsStrict {X : BerkovichSpace K} (U : AffinoidDomain K X) : Prop := sorry

end AffinoidDomain


/-- Restriction of a Berkovich space to an affinoid domain. -/
noncomputable def restrictToAffinoidDomain {X : BerkovichSpace K}
    (U : AffinoidDomain K X) : BerkovichSpace K := sorry

/-- Restriction to an affinoid domain has the corresponding subspace of points. -/
noncomputable def pointsRestrictToAffinoidDomainHomeomorph {X : BerkovichSpace K}
    (U : AffinoidDomain K X) :
    Point K (restrictToAffinoidDomain K U) ≃ₜ ↥U.carrier := sorry
/-- Every point has an affinoid neighborhood. -/
def IsGood (X : BerkovichSpace K) : Prop := sorry

/-- The analytic atlas uses strict affinoid algebras. -/
def IsStrict (X : BerkovichSpace K) : Prop := sorry

/-- The underlying topological space is Hausdorff and paracompact.

Berkovich's convention in the source comparison theorem includes Hausdorffness in the word
`paracompact`; Mathlib's `ParacompactSpace` does not. -/
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

/-- Berkovich paracompactness agrees with Hausdorff paracompactness of the point topology. -/
theorem isParacompact_iff (X : BerkovichSpace K) :
    IsParacompact K X ↔ T2Space (Point K X) ∧ ParacompactSpace (Point K X) := sorry

/-- Berkovich Hausdorffness agrees with the Hausdorff property of the point-set topology. -/
theorem isHausdorff_iff (X : BerkovichSpace K) :
    IsHausdorff K X ↔ T2Space (Point K X) := sorry

/-- A paracompact Berkovich space is Hausdorff under the source convention. -/
theorem isHausdorff_of_isParacompact {X : BerkovichSpace K} (hX : IsParacompact K X) :
    IsHausdorff K X := sorry

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

/-- Global analytic functions on an affinoid Berkovich space recover its coordinate algebra. -/
noncomputable def globalSectionsOfAffinoidEquiv {A : Type u} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    StructureSheaf.Sections K
      (⊤ : TopologicalSpace.Opens (Point K (ofAffinoid K hA))) ≃ₐ[K] A := sorry

namespace AffinoidDomain

/-- The strict affinoid algebra modeling a strict affinoid domain. -/
noncomputable def model {X : BerkovichSpace K} (U : AffinoidDomain K X)
    (hU : U.IsStrict) : AffinoidAlgebraModel K := sorry

/-- Restriction to a strict affinoid domain is isomorphic to the Berkovich spectrum of its
coordinate algebra. -/
noncomputable def modelIso {X : BerkovichSpace K} (U : AffinoidDomain K X)
    (hU : U.IsStrict) :
    restrictToAffinoidDomain K U ≅ ofAffinoid K (model K U hU).isAffinoid := sorry

end AffinoidDomain

/-- The points of an affinoid Berkovich space form its Berkovich spectrum. -/
noncomputable def pointsOfAffinoidHomeomorph {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    Point K (ofAffinoid K hA) ≃ₜ
      (letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
       letI : NormedAlgebra K A := hA.presentation.residueNormedAlgebra K A
       BerkovichSpectrumOver K A) := sorry

/-- Pullback of Berkovich spectra along a morphism of affinoid algebras. -/
noncomputable def spectrumComap {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    (letI : NormedCommRing B := hB.presentation.residueNormedCommRing K B
     letI : NormedAlgebra K B := hB.presentation.residueNormedAlgebra K B
     BerkovichSpectrumOver K B) →
      (letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
       letI : NormedAlgebra K A := hA.presentation.residueNormedAlgebra K A
       BerkovichSpectrumOver K A) := sorry

/-- Pullback on affinoid Berkovich spectra is pointwise precomposition with the algebra map. -/
@[simp]
theorem spectrumComap_apply {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (x : letI : NormedCommRing B := hB.presentation.residueNormedCommRing K B
         letI : NormedAlgebra K B := hB.presentation.residueNormedAlgebra K B
         BerkovichSpectrumOver K B) (a : A) :
    letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
    letI : NormedAlgebra K A := hA.presentation.residueNormedAlgebra K A
    letI : NormedCommRing B := hB.presentation.residueNormedCommRing K B
    letI : NormedAlgebra K B := hB.presentation.residueNormedAlgebra K B
    spectrumComap K hA hB f x a = x (f a) := sorry

@[simp]
theorem spectrumComap_id {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
    spectrumComap K hA hA (AlgHom.id K A) = id := sorry

@[simp]
theorem spectrumComap_comp {A : Type v} {B : Type w} {C : Type z}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
    letI : NormedCommRing B := hB.presentation.residueNormedCommRing K B
    letI : NormedCommRing C := hC.presentation.residueNormedCommRing K C
    spectrumComap K hA hC (g.comp f) =
      spectrumComap K hA hB f ∘ spectrumComap K hB hC g := sorry

/-- Pullback on affinoid Berkovich spectra is continuous. -/
theorem continuous_spectrumComap {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    letI : NormedCommRing A := hA.presentation.residueNormedCommRing K A
    letI : NormedCommRing B := hB.presentation.residueNormedCommRing K B
    Continuous (spectrumComap K hA hB f) := sorry

/-- The morphism of affinoid Berkovich spaces induced contravariantly by an algebra homomorphism. -/
noncomputable def ofAffinoidMap {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    ofAffinoid K hB ⟶ ofAffinoid K hA := sorry

@[simp]
theorem ofAffinoidMap_id {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    ofAffinoidMap K hA hA (AlgHom.id K A) = 𝟙 (ofAffinoid K hA) := sorry

@[simp]
theorem ofAffinoidMap_comp {A : Type v} {B : Type w} {C : Type*}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    ofAffinoidMap K hB hC g ≫ ofAffinoidMap K hA hB f =
      ofAffinoidMap K hA hC (g.comp f) := sorry

/-- The affinoid point homeomorphism is natural in the coordinate algebra. -/
theorem pointsOfAffinoidHomeomorph_naturality {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (x : Point K (ofAffinoid K hB)) :
    pointsOfAffinoidHomeomorph K hA (Point.map K (ofAffinoidMap K hA hB f) x) =
      spectrumComap K hA hB f (pointsOfAffinoidHomeomorph K hB x) := sorry

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

/-- Quasi-separated rigid spaces, the target of the fully faithful comparison functor. -/
def quasiSeparatedRigidProperty : ObjectProperty (RigidSpace K) :=
  fun X ↦ RigidSpace.IsQuasiSeparated K X

/-- Hausdorff strict Berkovich spaces, the source of the fully faithful comparison functor. -/
def hausdorffStrictBerkovichProperty : ObjectProperty (BerkovichSpace K) :=
  fun X ↦ BerkovichSpace.IsHausdorff K X ∧ BerkovichSpace.IsStrict K X

/-- Rigid spaces in the essential image of paracompact strict Berkovich spaces. -/
def rigidComparisonProperty : ObjectProperty (RigidSpace K) :=
  fun X ↦ RigidSpace.IsQuasiSeparated K X ∧
    RigidSpace.HasAffinoidCoverOfFiniteType K X

/-- Paracompact strict Berkovich spaces. -/
def berkovichComparisonProperty : ObjectProperty (BerkovichSpace K) :=
  fun X ↦ BerkovichSpace.IsStrict K X ∧ BerkovichSpace.IsParacompact K X

/-- The full subcategory of quasi-separated rigid spaces. -/
abbrev QuasiSeparatedRigidSpace := (quasiSeparatedRigidProperty K).FullSubcategory

/-- The full subcategory of Hausdorff strict Berkovich spaces. -/
abbrev HausdorffStrictBerkovichSpace :=
  (hausdorffStrictBerkovichProperty K).FullSubcategory

/-- The rigid side of Berkovich's paracompact comparison equivalence. -/
abbrev ComparisonRigidSpace := (rigidComparisonProperty K).FullSubcategory

/-- The Berkovich side of Berkovich's paracompact comparison equivalence. -/
abbrev ComparisonBerkovichSpace := (berkovichComparisonProperty K).FullSubcategory

/-- Quasi-separatedness is invariant under analytic isomorphism. -/
theorem quasiSeparatedRigidProperty_isClosedUnderIsomorphisms :
    (quasiSeparatedRigidProperty K).IsClosedUnderIsomorphisms := sorry

/-- The Hausdorff strict property is invariant under analytic isomorphism. -/
theorem hausdorffStrictBerkovichProperty_isClosedUnderIsomorphisms :
    (hausdorffStrictBerkovichProperty K).IsClosedUnderIsomorphisms := sorry

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

/-- The morphism between rigid comparison objects induced by an affinoid algebra map. -/
noncomputable def comparisonRigidSpaceOfAffinoidMap
    {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    comparisonRigidSpaceOfAffinoid K hB ⟶ comparisonRigidSpaceOfAffinoid K hA := sorry

/-- The morphism between Berkovich comparison objects induced by an affinoid algebra map. -/
noncomputable def comparisonBerkovichSpaceOfAffinoidMap
    {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    comparisonBerkovichSpaceOfAffinoid K hB ⟶
      comparisonBerkovichSpaceOfAffinoid K hA := sorry

@[simp]
theorem comparisonRigidSpaceOfAffinoid_obj {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    (comparisonRigidSpaceOfAffinoid K hA).obj = RigidSpace.ofAffinoid K hA := sorry

@[simp]
theorem comparisonBerkovichSpaceOfAffinoid_obj {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    (comparisonBerkovichSpaceOfAffinoid K hA).obj = BerkovichSpace.ofAffinoid K hA := sorry


/-- Forgetting the comparison-subcategory structure recovers the usual affinoid rigid morphism. -/
theorem comparisonRigidSpaceOfAffinoidMap_forget
    {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    eqToHom (comparisonRigidSpaceOfAffinoid_obj K hB).symm ≫
        (rigidComparisonProperty K).ι.map
          (comparisonRigidSpaceOfAffinoidMap K hA hB f) ≫
      eqToHom (comparisonRigidSpaceOfAffinoid_obj K hA) =
        RigidSpace.ofAffinoidMap K hA hB f := sorry

/-- Forgetting the comparison-subcategory structure recovers the usual affinoid Berkovich
morphism. -/
theorem comparisonBerkovichSpaceOfAffinoidMap_forget
    {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    eqToHom (comparisonBerkovichSpaceOfAffinoid_obj K hB).symm ≫
        (berkovichComparisonProperty K).ι.map
          (comparisonBerkovichSpaceOfAffinoidMap K hA hB f) ≫
      eqToHom (comparisonBerkovichSpaceOfAffinoid_obj K hA) =
        BerkovichSpace.ofAffinoidMap K hA hB f := sorry
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

/-- Berkovich's canonical functor from Hausdorff strict analytic spaces to rigid spaces. -/
noncomputable def berkovichToRigid :
    HausdorffStrictBerkovichSpace K ⥤ QuasiSeparatedRigidSpace K := sorry

/-- The canonical Berkovich-to-rigid functor is fully faithful. -/
noncomputable def berkovichToRigid_fullyFaithful : (berkovichToRigid K).FullyFaithful := sorry

/-- Inclusion of the paracompact rigid comparison range into quasi-separated rigid spaces. -/
noncomputable def comparisonRigidToQuasiSeparated :
    ComparisonRigidSpace K ⥤ QuasiSeparatedRigidSpace K := sorry

/-- The rigid comparison inclusion has the expected underlying rigid space. -/
noncomputable def comparisonRigidToQuasiSeparatedCompιIso :
    comparisonRigidToQuasiSeparated K ⋙ (quasiSeparatedRigidProperty K).ι ≅
      (rigidComparisonProperty K).ι := sorry

/-- Inclusion of paracompact strict Berkovich spaces into Hausdorff strict Berkovich spaces. -/
noncomputable def comparisonBerkovichToHausdorffStrict :
    ComparisonBerkovichSpace K ⥤ HausdorffStrictBerkovichSpace K := sorry

/-- The Berkovich comparison inclusion has the expected underlying Berkovich space. -/
noncomputable def comparisonBerkovichToHausdorffStrictCompιIso :
    comparisonBerkovichToHausdorffStrict K ⋙ (hausdorffStrictBerkovichProperty K).ι ≅
      (berkovichComparisonProperty K).ι := sorry

/-- The restriction of the canonical functor to the paracompact comparison subcategories. -/
noncomputable def comparisonBerkovichToRigid :
    ComparisonBerkovichSpace K ⥤ ComparisonRigidSpace K := sorry

/-- The restricted functor agrees with the canonical functor after the evident inclusions. -/
noncomputable def comparisonBerkovichToRigidRestrictionIso :
    comparisonBerkovichToHausdorffStrict K ⋙ berkovichToRigid K ≅
      comparisonBerkovichToRigid K ⋙ comparisonRigidToQuasiSeparated K := sorry

/-- The restricted canonical functor is an equivalence. -/
theorem comparisonBerkovichToRigid_isEquivalence :
    (comparisonBerkovichToRigid K).IsEquivalence := sorry

/-- On affinoid spaces, the canonical comparison preserves the coordinate algebra. -/
noncomputable def comparisonBerkovichToRigid_obj_ofAffinoidIso
    {A : Type v} [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A) :
    (comparisonBerkovichToRigid K).obj (comparisonBerkovichSpaceOfAffinoid K hA) ≅
      comparisonRigidSpaceOfAffinoid K hA := sorry

/-- The affinoid comparison isomorphisms are natural in the coordinate algebra. -/
theorem comparisonBerkovichToRigid_obj_ofAffinoidIso_naturality
    {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    (comparisonBerkovichToRigid K).map
          (comparisonBerkovichSpaceOfAffinoidMap K hA hB f) ≫
        (comparisonBerkovichToRigid_obj_ofAffinoidIso K hA).hom =
      (comparisonBerkovichToRigid_obj_ofAffinoidIso K hB).hom ≫
        comparisonRigidSpaceOfAffinoidMap K hA hB f := sorry

/-- A chosen quasi-inverse from rigid spaces to Berkovich spaces. -/
noncomputable def rigidToBerkovich : ComparisonRigidSpace K ⥤ ComparisonBerkovichSpace K := sorry

/-- The rigid-to-Berkovich functor followed by the canonical functor is naturally isomorphic to the
identity. -/
noncomputable def rigidToBerkovichCompComparisonBerkovichToRigidIso :
    rigidToBerkovich K ⋙ comparisonBerkovichToRigid K ≅ 𝟭 (ComparisonRigidSpace K) := sorry

/-- The canonical functor followed by its chosen quasi-inverse is naturally isomorphic to the
identity. -/
noncomputable def comparisonBerkovichToRigidCompRigidToBerkovichIso :
    comparisonBerkovichToRigid K ⋙ rigidToBerkovich K ≅
      𝟭 (ComparisonBerkovichSpace K) := sorry

/-- Main comparison theorem: the chosen rigid-to-Berkovich quasi-inverse is an equivalence. -/
theorem rigidToBerkovich_isEquivalence :
    (rigidToBerkovich K).IsEquivalence := sorry

/-- Data-valued form of the main comparison theorem. -/
noncomputable def rigidBerkovichEquivalence :
    ComparisonRigidSpace K ≌ ComparisonBerkovichSpace K := sorry

/-- The forward functor of the packaged equivalence is the chosen rigid-to-Berkovich functor. -/
@[simp]
theorem rigidBerkovichEquivalence_functor :
    (rigidBerkovichEquivalence K).functor = rigidToBerkovich K := sorry

/-- The inverse functor of the packaged equivalence is the canonical restricted
Berkovich-to-rigid functor. -/
@[simp]
theorem rigidBerkovichEquivalence_inverse :
    (rigidBerkovichEquivalence K).inverse = comparisonBerkovichToRigid K := sorry

end GlobalSpaces

end RigidChallenge
