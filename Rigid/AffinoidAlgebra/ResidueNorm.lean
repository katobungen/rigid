import Rigid.AffinoidAlgebra.AutomaticContinuity

set_option linter.style.header false

/-!
# Residue norms for affinoid presentations

This module constructs the normed algebra structure transported from the quotient associated with
an affinoid presentation.  The comparator-facing declarations in `Rigid.Development` use these
production definitions and theorems directly.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [CommRing A] [Algebra K A]

/-- The residue norm associated with an affinoid presentation, bundled as a normed commutative ring
structure. Unlike the induced topology, this norm can depend on the presentation. -/
@[reducible]
noncomputable def residueNormedCommRing (n : ℕ)
    (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :
    NormedCommRing A :=
  letI : IsClosed (I : Set (TateAlgebra K (Fin n))) := Rigid.isClosed_tateAlgebra_ideal K I
  { (inferInstance : CommRing A), NormedCommRing.induced A (TateAlgebra K (Fin n) ⧸ I)
      e.symm.toRingHom e.symm.injective with }

/-- The residue norm makes the target a normed algebra over the ground field. -/
@[reducible]
noncomputable def residueNormedAlgebra (n : ℕ)
    (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :
    letI := residueNormedCommRing K A n I e
    NormedAlgebra K A :=
  letI : NormedCommRing A := residueNormedCommRing K A n I e
  { (inferInstance : Algebra K A) with
    norm_smul_le := by
      intro r x
      letI : IsClosed (I : Set (TateAlgebra K (Fin n))) :=
        Rigid.isClosed_tateAlgebra_ideal K I
      letI : NormedCommRing (TateAlgebra K (Fin n) ⧸ I) := inferInstance
      change ‖e.symm (r • x)‖ ≤ ‖r‖ * ‖e.symm x‖
      rw [map_smul]
      exact norm_smul_le _ _ }

omit [CompleteSpace K] in
/-- The scalar embedding of the residue normed algebra agrees with the presentation map applied to
constant Tate series. -/
@[simp]
theorem residueNormedAlgebra_algebraMap (n : ℕ)
    (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) (r : K) :
    letI : NormedCommRing A := residueNormedCommRing K A n I e
    letI : NormedAlgebra K A := residueNormedAlgebra K A n I e
    algebraMap K A r =
      (e.toAlgHom.comp (Ideal.Quotient.mkₐ K I))
        (algebraMap K (TateAlgebra K (Fin n)) r) := by
  change algebraMap K A r =
    e.toAlgHom (Ideal.Quotient.mkₐ K I
      (algebraMap K (TateAlgebra K (Fin n)) r))
  rw [← e.commutes]
  rfl

/-- The residue norm is complete. -/
theorem residueCompleteSpace (n : ℕ)
    (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :
    letI := residueNormedCommRing K A n I e
    CompleteSpace A := by
  letI : IsClosed (I : Set (TateAlgebra K (Fin n))) :=
    Rigid.isClosed_tateAlgebra_ideal K I
  letI : NormedCommRing (TateAlgebra K (Fin n) ⧸ I) := inferInstance
  letI : NormedCommRing A := residueNormedCommRing K A n I e
  let e' : A ≃ₗᵢ[K] (TateAlgebra K (Fin n) ⧸ I) :=
    { e.symm.toLinearEquiv with norm_map' := fun _ ↦ rfl }
  exact (completeSpace_congr (e := e'.toEquiv) e'.isometry.isUniformEmbedding).2 inferInstance

/-- The residue norm is nonarchimedean. -/
theorem residueIsUltrametricDist (n : ℕ)
    (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :
    letI := residueNormedCommRing K A n I e
    IsUltrametricDist A := by
  letI : IsClosed (I : Set (TateAlgebra K (Fin n))) :=
    Rigid.isClosed_tateAlgebra_ideal K I
  letI : NormedCommRing (TateAlgebra K (Fin n) ⧸ I) := inferInstance
  letI : IsUltrametricDist (TateAlgebra K (Fin n) ⧸ I) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
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
  letI : NormedCommRing A := residueNormedCommRing K A n I e
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    change ‖e.symm (x + y)‖ ≤ max ‖e.symm x‖ ‖e.symm y‖
    rw [map_add]
    exact IsUltrametricDist.norm_add_le_max _ _

end Rigid
