import Mathlib.RingTheory.Ideal.Quotient.Operations
import Rigid.AffinoidAlgebra.AutomaticContinuity

set_option linter.style.header false

/-!
# Tate algebras as affinoid algebras

The quotient by the zero ideal gives a preferred affinoid presentation of a Tate algebra.  This
file records that its canonical affinoid topology is the Gauss-norm topology and uses automatic
continuity for canonical affinoid topologies to obtain continuity of maps from a Tate algebra into
any Banach realization whose topology is known to be canonical.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The tautological presentation of a Tate algebra as its quotient by the zero ideal. -/
noncomputable def tateAlgebraPresentation (n : ℕ) :
    AffinoidPresentation K (TateAlgebra K (Fin n)) where
  n := n
  ideal := ⊥
  equiv := AlgEquiv.quotientBot K (TateAlgebra K (Fin n))

@[simp]
theorem tateAlgebraPresentation_toAlgHom_apply (n : ℕ)
    (f : TateAlgebra K (Fin n)) :
    AffinoidPresentation.toAlgHom K (TateAlgebra K (Fin n))
      (tateAlgebraPresentation K n) f = f := by
  rfl

/-- A finite Tate algebra is an affinoid algebra. -/
theorem isAffinoidAlgebra_tateAlgebra (n : ℕ) :
    IsAffinoidAlgebra K (TateAlgebra K (Fin n)) :=
  ⟨tateAlgebraPresentation K n⟩

/-- The canonical affinoid topology of a Tate algebra is its Gauss-norm topology. -/
theorem affinoidTopology_tateAlgebra_eq (n : ℕ)
    (hT : IsAffinoidAlgebra K (TateAlgebra K (Fin n))) :
    affinoidTopology K (TateAlgebra K (Fin n)) hT =
      (inferInstance : TopologicalSpace (TateAlgebra K (Fin n))) := by
  calc
    affinoidTopology K (TateAlgebra K (Fin n)) hT =
        (tateAlgebraPresentation K n).residueTopology :=
      residueTopology_eq_for_affinoidPresentationData K
        hT.presentation.ideal hT.presentation.equiv
        (tateAlgebraPresentation K n).ideal (tateAlgebraPresentation K n).equiv
    _ = (inferInstance : TopologicalSpace (TateAlgebra K (Fin n))) := by
      change TopologicalSpace.coinduced
        (AffinoidPresentation.toAlgHom K (TateAlgebra K (Fin n))
          (tateAlgebraPresentation K n))
          (inferInstance : TopologicalSpace (TateAlgebra K (Fin n))) =
            (inferInstance : TopologicalSpace (TateAlgebra K (Fin n)))
      rw [show AffinoidPresentation.toAlgHom K (TateAlgebra K (Fin n))
          (tateAlgebraPresentation K n) =
          AlgHom.id K (TateAlgebra K (Fin n)) by
        apply DFunLike.ext _ _
        intro f
        exact tateAlgebraPresentation_toAlgHom_apply K n f]
      exact coinduced_id

variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A]

/-- Every algebra homomorphism from a Tate algebra to a Banach realization of an affinoid algebra
is continuous once the target topology is identified with its canonical affinoid topology. -/
theorem continuous_tateAlgebra_to_affinoid
    (hA : IsAffinoidAlgebra K A)
    (htop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA)
    {n : ℕ} (f : TateAlgebra K (Fin n) →ₐ[K] A) : Continuous f := by
  let hT := isAffinoidAlgebra_tateAlgebra K n
  have hf :
      @Continuous (TateAlgebra K (Fin n)) A
        (affinoidTopology K (TateAlgebra K (Fin n)) hT)
        (affinoidTopology K A hA) f :=
    continuous_for_affinoidPresentationData K
      hT.presentation.ideal hT.presentation.equiv
      hA.presentation.ideal hA.presentation.equiv f
  rw [affinoidTopology_tateAlgebra_eq K n hT, ← htop] at hf
  exact hf

end Rigid
