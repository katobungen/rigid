import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.OpenQuotient
import Rigid.AffinoidAlgebra.AutomaticContinuity

set_option linter.style.header false

/-!
# Closed ideals in a Banach realization of an affinoid algebra

Ideals in a Tate algebra are closed.  Since an affinoid presentation is a quotient map for the
canonical affinoid topology, the same is true in every normed realization whose topology agrees
with that canonical topology.  This isolates the topological input needed to form complete
minimal-prime quotients in the reduction of Proposition 4.5.3.
-/

universe u v

namespace Rigid

section Quotient

variable {R : Type v} [NormedCommRing R] [IsUltrametricDist R]

/-- A quotient by a closed ideal inherits a nonarchimedean quotient norm. -/
theorem idealQuotientIsUltrametricDist (I : Ideal R) [IsClosed (I : Set R)] :
    IsUltrametricDist (R ⧸ I) := by
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨x', hx', hxnorm⟩ :=
      Ideal.Quotient.norm_mk_lt (ε := ε / 2) x (half_pos hε)
    obtain ⟨y', hy', hynorm⟩ :=
      Ideal.Quotient.norm_mk_lt (ε := ε / 2) y (half_pos hε)
    calc
      ‖x + y‖ = ‖Ideal.Quotient.mk I x' + Ideal.Quotient.mk I y'‖ := by
        rw [hx', hy']
      _ = ‖Ideal.Quotient.mk I (x' + y')‖ := by rw [map_add]
      _ ≤ ‖x' + y'‖ := Ideal.Quotient.norm_mk_le I _
      _ ≤ max ‖x'‖ ‖y'‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (‖x‖ + ε / 2) (‖y‖ + ε / 2) :=
        max_le_max (le_of_lt hxnorm) (le_of_lt hynorm)
      _ ≤ max ‖x‖ ‖y‖ + ε := by
        apply max_le
        · linarith [le_max_left ‖x‖ ‖y‖]
        · linarith [le_max_right ‖x‖ ‖y‖]

variable (K : Type u) [NontriviallyNormedField K] [NormedAlgebra K R]

/-- The quotient map by a closed ideal, bundled as a continuous algebra homomorphism. -/
noncomputable def idealQuotientMk (I : Ideal R) [IsClosed (I : Set R)] :
    ContinuousAlgHom K R (R ⧸ I) where
  toAlgHom := Ideal.Quotient.mkₐ K I
  cont := AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mkₐ K I) 1 fun r ↦ by
    change ‖Ideal.Quotient.mk I r‖ ≤ 1 * ‖r‖
    simpa only [one_mul] using Ideal.Quotient.norm_mk_le I r

end Quotient

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A]

/-- Every ideal is closed once the given norm topology is known to be the canonical affinoid
quotient topology. -/
theorem isClosed_ideal_of_topology_eq_affinoidTopology
    (hA : IsAffinoidAlgebra K A)
    (htop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA)
    (I : Ideal A) : IsClosed (I : Set A) := by
  let P := hA.presentation
  have hcanonical :
      @IsClosed A (affinoidTopology K A hA) (I : Set A) := by
    letI : TopologicalSpace A := affinoidTopology K A hA
    have hquotient : IsOpenQuotientMap P.toAlgHom :=
      isOpenQuotientMap_coinduced P.toAlgHom P.toAlgHom_surjective
    rw [← hquotient.isQuotientMap.isClosed_preimage]
    change IsClosed
      ((I.comap P.toAlgHom.toRingHom : Ideal (TateAlgebra K (Fin P.n))) :
        Set (TateAlgebra K (Fin P.n)))
    exact isClosed_tateAlgebra_ideal K _
  rw [← isOpen_compl_iff]
  change @IsOpen A (inferInstance : TopologicalSpace A) ((I : Set A)ᶜ)
  rw [htop]
  exact hcanonical.isOpen_compl

end Rigid
