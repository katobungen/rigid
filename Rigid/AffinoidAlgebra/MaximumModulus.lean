import Rigid.AffinoidAlgebra.PowerBounded
import Rigid.Berkovich.GaussPoint
import Rigid.Berkovich.RelativeNonempty

set_option linter.style.header false

/-!
# Maximum-modulus and unit-ball foundations

Compactness of the relative Berkovich spectrum gives maximum attainment for every element. The
Gauss point identifies power-bounded elements of a finite Tate algebra with its closed unit ball.
These facts supply the bounded-coefficient and integrality tools used in the general affinoid
maximum-modulus argument.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

namespace BerkovichSpectrumOver

variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A]

omit [IsUltrametricDist K] in
/-- On a nonzero normed algebra, every element attains its maximum on the relative Berkovich
spectrum. -/
theorem exists_maximum [Nontrivial A] (a : A) :
    ∃ x : BerkovichSpectrumOver K A, ∀ y : BerkovichSpectrumOver K A, y a ≤ x a := by
  have hne : (Set.univ : Set (BerkovichSpectrumOver K A)).Nonempty :=
    ⟨Classical.choice (nonempty_of_nontrivial K A), Set.mem_univ _⟩
  obtain ⟨x, -, hx⟩ := (isCompact_univ K A).exists_isMaxOn
    hne (continuous_eval K A a).continuousOn
  exact ⟨x, fun y ↦ hx (Set.mem_univ y)⟩

end BerkovichSpectrumOver

namespace TateAlgebra

/-- The Gauss unit ball in a finite strict Tate algebra. -/
def unitBallSubring (n : ℕ) : Subring (TateAlgebra K (Fin n)) where
  carrier := {f | ‖f‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {f g} hf hg :=
    (IsUltrametricDist.norm_add_le_max f g).trans (max_le hf hg)
  neg_mem' {f} hf := by simpa using hf
  mul_mem' {f g} hf hg :=
    (norm_mul_le f g).trans (by simpa using mul_le_mul hf hg (norm_nonneg g) zero_le_one)

/-- Compatibility alias for the finite-variable Gauss point. -/
noncomputable abbrev gaussPoint (n : ℕ) :
    BerkovichSpectrumOver K (TateAlgebra K (Fin n)) :=
  BerkovichSpectrumOver.gaussPoint K (Fin n)

@[simp]
theorem gaussPoint_apply (n : ℕ) (f : TateAlgebra K (Fin n)) :
    gaussPoint K n f = ‖f‖ :=
  BerkovichSpectrumOver.gaussPoint_apply K (Fin n) f

/-- The Gauss point realizes the maximum modulus of every function on a strict Tate algebra. -/
theorem le_gaussPoint (n : ℕ) (x : BerkovichSpectrumOver K (TateAlgebra K (Fin n)))
    (f : TateAlgebra K (Fin n)) : x f ≤ gaussPoint K n f := by
  rw [gaussPoint_apply]
  exact BerkovichSpectrumOver.le_norm K _ x f

/-- In a finite strict Tate algebra, power-boundedness is equivalent to membership in the Gauss
unit ball. -/
theorem isPowerBounded_iff_norm_le_one {n : ℕ} {f : TateAlgebra K (Fin n)} :
    IsPowerBounded f ↔ ‖f‖ ≤ 1 := by
  constructor
  · intro hf
    simpa using BerkovichSpectrumOver.apply_le_one_of_isPowerBounded K _
      (BerkovichSpectrumOver.gaussPoint K (Fin n)) hf
  · exact isPowerBounded_of_norm_le_one

@[simp]
theorem mem_unitBallSubring_iff {n : ℕ} {f : TateAlgebra K (Fin n)} :
    f ∈ unitBallSubring K n ↔ IsPowerBounded f := by
  rw [isPowerBounded_iff_norm_le_one]
  rfl

variable {B : Type v} [NormedCommRing B] [NormedAlgebra K B]

/-- The image of the Tate unit ball under a continuous homomorphism is uniformly bounded. -/
theorem bddAbove_image_unitBall (n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) B) :
    BddAbove (Set.range fun b : (unitBallSubring K n).map π.toRingHom ↦ ‖(b : B)‖) := by
  obtain ⟨M, hM, hπ⟩ := SemilinearMapClass.bound_of_continuous π π.continuous
  refine ⟨max 0 M, ?_⟩
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, ha, hab⟩ := b.2
  calc
    ‖(b : B)‖ = ‖π a‖ := congrArg norm hab |>.symm
    _ ≤ M * ‖a‖ := hπ a
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left ha hM.le
    _ ≤ max 0 M := by simp [le_max_right 0 M]

/-- An element integral over the image of a Tate unit ball is power-bounded. -/
theorem isPowerBounded_of_isIntegral_image_unitBall (n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) B) {b : B}
    (hb : IsIntegral ((unitBallSubring K n).map π.toRingHom) b) : IsPowerBounded b :=
  IsPowerBounded.of_isIntegral_over_bounded_subring _
    (bddAbove_image_unitBall K n π) hb

end TateAlgebra

end Rigid
