import Mathlib.RingTheory.Ideal.Quotient.Operations
import Rigid.AffinoidAlgebra.QuotientTopology
import Rigid.TateAlgebra.NormedRing

set_option linter.style.header false

/-!
# Affinoid algebra presentations

This file defines the algebraic notion of a strict affinoid algebra. A presentation identifies the
algebra with a quotient of a finite Tate algebra. It also supplies the quotient topology associated
with a presentation and proves the elementary facts that do not require presentation-independence
or closedness of ideals.
-/

universe u v

namespace Rigid

section AffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
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

/-- The quotient topology makes the target a topological ring. -/
theorem residueIsTopologicalRing (P : AffinoidPresentation K A) :
    @IsTopologicalRing A P.residueTopology _ :=
  isTopologicalRing_coinduced P.toAlgHom P.toAlgHom_surjective

/-- Scalar multiplication by the ground field is continuous for the quotient topology. -/
theorem residueContinuousSMul (P : AffinoidPresentation K A) :
    @ContinuousSMul K A _ _ P.residueTopology :=
  continuousSMul_coinduced P.toAlgHom P.toAlgHom_surjective fun c x ↦ map_smul P.toAlgHom c x

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

/-- The quotient topology associated with a chosen presentation of an affinoid algebra. -/
@[reducible]
noncomputable def affinoidTopology (hA : IsAffinoidAlgebra K A) : TopologicalSpace A :=
  hA.presentation.residueTopology

/-- The chosen quotient topology makes an affinoid algebra a topological ring. -/
theorem affinoidIsTopologicalRing (hA : IsAffinoidAlgebra K A) :
    @IsTopologicalRing A (affinoidTopology K A hA) _ :=
  hA.presentation.residueIsTopologicalRing

/-- Scalar multiplication by the ground field is continuous for the chosen quotient topology. -/
theorem affinoidContinuousSMul (hA : IsAffinoidAlgebra K A) :
    @ContinuousSMul K A _ _ (affinoidTopology K A hA) :=
  hA.presentation.residueContinuousSMul

/-- Unpack an affinoid algebra as a surjective algebraic presentation by a finite Tate algebra. -/
theorem exists_surjective_presentation_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (π : TateAlgebra K (Fin n) →ₐ[K] A), Function.Surjective π :=
  ⟨hA.presentation.n, hA.presentation.toAlgHom, hA.presentation.toAlgHom_surjective⟩

/-- Unpack the defining quotient presentation of an affinoid algebra. -/
theorem exists_quotient_presentation_of_isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (I : Ideal (TateAlgebra K (Fin n))),
      Nonempty ((TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :=
  ⟨hA.presentation.n, hA.presentation.ideal, ⟨hA.presentation.equiv⟩⟩

end AffinoidAlgebra

end Rigid
