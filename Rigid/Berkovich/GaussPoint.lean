import Rigid.Berkovich.SpectralSeminorm
import Rigid.TateAlgebra.Multiplicative

set_option linter.style.header false

/-!
# The relative Gauss point of a finite Tate algebra

For a Tate algebra in finitely many variables, the Gauss norm itself is a relative Berkovich point.
This identifies the relative Berkovich spectral seminorm with the ambient Gauss norm and gives the
expected power-bounded criterion on finite Tate algebras.
-/

universe u v w

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v) [Finite ι]

/-- The relative Berkovich point on a finite Tate algebra whose evaluation is the Gauss norm. -/
noncomputable def gaussPoint : Rigid.BerkovichSpectrumOver K (Rigid.TateAlgebra K ι) where
  toBerkovichSpectrum :=
    { seminorm :=
        { toFun := fun f ↦ ‖f‖
          map_zero' := by simp
          add_le' := by intro f g; exact norm_add_le _ _
          neg' := by intro f; exact norm_neg f
          map_one' := by simp
          map_mul' := by intro f g; simpa using Rigid.TateAlgebra.norm_mul (K := K) (ι := ι) f g }
      le_norm' := fun _ ↦ le_rfl }
  map_algebraMap' r := by
    change ‖Rigid.TateAlgebra.C K ι r‖ = ‖r‖
    simp

@[simp]
theorem gaussPoint_apply (f : Rigid.TateAlgebra K ι) : gaussPoint K ι f = ‖f‖ := rfl

@[simp]
theorem gaussPoint_tateVariable (i : ι) :
    gaussPoint K ι (Rigid.tateVariable K ι i) = 1 := by
  change ‖Rigid.tateVariable K ι i‖ = 1
  simp

/-- On a finite Tate algebra, the relative Berkovich spectral seminorm is exactly the Gauss norm. -/
theorem spectralSeminorm_eq_norm (f : Rigid.TateAlgebra K ι) :
    spectralSeminorm K (Rigid.TateAlgebra K ι) f = ‖f‖ := by
  apply le_antisymm
  · exact spectralSeminorm_le_norm K (Rigid.TateAlgebra K ι) f
  · simpa [gaussPoint_apply] using
      le_spectralSeminorm K (Rigid.TateAlgebra K ι) (gaussPoint K ι) f

/-- An element of a finite Tate algebra that is bounded by `1` at every relative Berkovich point is
power-bounded. -/
theorem isPowerBounded_of_forall_apply_le_one {f : Rigid.TateAlgebra K ι}
    (hf : ∀ x : Rigid.BerkovichSpectrumOver K (Rigid.TateAlgebra K ι), x f ≤ 1) :
    Rigid.IsPowerBounded f := by
  apply Rigid.isPowerBounded_of_norm_le_one
  simpa [gaussPoint_apply] using hf (gaussPoint K ι)

end Rigid.BerkovichSpectrumOver

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable {A : Type w} [NormedCommRing A] [NormedAlgebra K A]

/-- Reduction toward the affinoid spectral power-bounded criterion: it suffices to realize the
ambient element as the image of a Tate element bounded by `1` at every relative Gauss point. -/
theorem isPowerBounded_of_exists_tateLift
    {n : ℕ} (π : ContinuousAlgHom K (Rigid.TateAlgebra K (Fin n)) A) {a : A}
    (h : ∃ y : Rigid.TateAlgebra K (Fin n),
      π y = a ∧
      ∀ x : Rigid.BerkovichSpectrumOver K (Rigid.TateAlgebra K (Fin n)), x y ≤ 1) :
    Rigid.IsPowerBounded a := by
  rcases h with ⟨y, rfl, hy⟩
  exact Rigid.IsPowerBounded.map_continuousAlgHom π
    (Rigid.BerkovichSpectrumOver.isPowerBounded_of_forall_apply_le_one K (ι := Fin n) hy)

end Rigid
