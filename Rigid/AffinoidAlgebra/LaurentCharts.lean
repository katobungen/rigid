import Rigid.AffinoidAlgebra.RationalLocalization

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The analytic maps in a two-member Laurent cover

For `f ∈ A`, the two Laurent charts are `A⟨f⟩` and `A⟨f⁻¹⟩`.  Their overlap can be obtained by
localizing the first chart once more at `f`.  This file constructs the two restriction maps into
that overlap and the first two arrows

`A ⟶ A⟨f⟩ × A⟨f⁻¹⟩ ⟶ A⟨f, f⁻¹⟩`

of Tate's Laurent-cover sequence.  It proves that these arrows form a complex.  Exactness is the
closed-ideal descent of the completed coefficient sequence in `CompletedLaurent`.
-/

universe u v

namespace Rigid

namespace LaurentCharts

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The Laurent chart on which `|f| ≤ 1`. -/
abbrev Plus (f : A) :=
  RationalLocalization K A 1 1 (fun _ ↦ f)

/-- The Laurent chart on which `1 ≤ |f|`. -/
abbrev Minus (f : A) :=
  RationalLocalization K A 1 f (fun _ ↦ 1)

/-- The overlap, obtained from the positive chart by adjoining a power-bounded inverse of `f`. -/
abbrev Overlap (f : A) :=
  RationalLocalization K (Plus K A f) 1
    (RationalLocalization.baseMap K A 1 1 (fun _ ↦ f) f) (fun _ ↦ 1)

/-- Restriction from the ambient algebra to the positive Laurent chart. -/
noncomputable def plusMap (f : A) : ContinuousAlgHom K A (Plus K A f) :=
  RationalLocalization.baseMap K A 1 1 (fun _ ↦ f)

/-- Restriction from the ambient algebra to the negative Laurent chart. -/
noncomputable def minusMap (f : A) : ContinuousAlgHom K A (Minus K A f) :=
  RationalLocalization.baseMap K A 1 f (fun _ ↦ 1)

/-- Restriction from the positive Laurent chart to the overlap. -/
noncomputable def plusToOverlap (f : A) :
    ContinuousAlgHom K (Plus K A f) (Overlap K A f) :=
  RationalLocalization.baseMap K (Plus K A f) 1 (plusMap K A f f) (fun _ ↦ 1)

/-- The ambient map from `A` to the overlap. -/
noncomputable def overlapMap (f : A) : ContinuousAlgHom K A (Overlap K A f) :=
  (plusToOverlap K A f).comp (plusMap K A f)

/-- The power-bounded inverse of `f` on the overlap. -/
noncomputable def overlapInverse (f : A) : Overlap K A f :=
  RationalLocalization.coordinate K (Plus K A f) 1 (plusMap K A f f) (fun _ ↦ 1) 0

theorem isPowerBounded_overlapInverse (f : A) :
    IsPowerBounded (overlapInverse K A f) :=
  RationalLocalization.isPowerBounded_coordinate K (Plus K A f) 1
    (plusMap K A f f) (fun _ ↦ 1) 0

@[simp]
theorem overlapMap_mul_inverse (f : A) :
    overlapMap K A f f * overlapInverse K A f = 1 := by
  change
    RationalLocalization.baseMap K (Plus K A f) 1 (plusMap K A f f) (fun _ ↦ 1)
        (plusMap K A f f) *
      RationalLocalization.coordinate K (Plus K A f) 1
        (plusMap K A f f) (fun _ ↦ 1) 0 = 1
  rw [RationalLocalization.baseMap_denominator_mul_coordinate]
  simp

/-- Restriction from the negative Laurent chart to the overlap. -/
noncomputable def minusToOverlap (f : A) :
    ContinuousAlgHom K (Minus K A f) (Overlap K A f) :=
  RationalLocalization.lift K A 1 f (fun _ ↦ 1) (overlapMap K A f)
    (fun _ ↦ overlapInverse K A f) (fun _ ↦ isPowerBounded_overlapInverse K A f)
    (fun _ ↦ by simp)

@[simp]
theorem plusToOverlap_comp_plusMap (f : A) :
    (plusToOverlap K A f).comp (plusMap K A f) = overlapMap K A f :=
  rfl

@[simp]
theorem minusToOverlap_comp_minusMap (f : A) :
    (minusToOverlap K A f).comp (minusMap K A f) = overlapMap K A f :=
  RationalLocalization.lift_comp_baseMap K A 1 f (fun _ ↦ 1)
    (overlapMap K A f) (fun _ ↦ overlapInverse K A f)
    (fun _ ↦ isPowerBounded_overlapInverse K A f) (fun _ ↦ by simp)

/-- The diagonal restriction in the Laurent-cover sequence. -/
noncomputable def diagonal (f : A) :
    A →ₗ[K] Plus K A f × Minus K A f :=
  (plusMap K A f).toLinearMap.prod (minusMap K A f).toLinearMap

/-- Difference of the two restrictions to the overlap. -/
noncomputable def difference (f : A) :
    Plus K A f × Minus K A f →ₗ[K] Overlap K A f :=
  (plusToOverlap K A f).toLinearMap.comp (LinearMap.fst K _ _) -
    (minusToOverlap K A f).toLinearMap.comp (LinearMap.snd K _ _)

@[simp]
theorem diagonal_apply (f a : A) :
    diagonal K A f a = (plusMap K A f a, minusMap K A f a) :=
  rfl

@[simp]
theorem difference_apply (f : A) (p : Plus K A f) (q : Minus K A f) :
    difference K A f (p, q) = plusToOverlap K A f p - minusToOverlap K A f q :=
  rfl

/-- The Laurent-cover arrows compose to zero. -/
@[simp]
theorem difference_diagonal (f a : A) :
    difference K A f (diagonal K A f a) = 0 := by
  rw [diagonal_apply, difference_apply]
  have hp := congrArg (fun φ : ContinuousAlgHom K A (Overlap K A f) ↦ φ a)
    (plusToOverlap_comp_plusMap K A f)
  have hm := congrArg (fun φ : ContinuousAlgHom K A (Overlap K A f) ↦ φ a)
    (minusToOverlap_comp_minusMap K A f)
  change plusToOverlap K A f (plusMap K A f a) =
    overlapMap K A f a at hp
  change minusToOverlap K A f (minusMap K A f a) =
    overlapMap K A f a at hm
  rw [hp, hm, sub_self]

theorem range_diagonal_le_ker_difference (f : A) :
    LinearMap.range (diagonal K A f) ≤ LinearMap.ker (difference K A f) := by
  rintro _ ⟨a, rfl⟩
  exact LinearMap.mem_ker.mpr (difference_diagonal K A f a)

end LaurentCharts

end Rigid
