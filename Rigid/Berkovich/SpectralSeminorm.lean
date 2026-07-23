import Mathlib.Analysis.SpecificLimits.Normed
import Rigid.AffinoidAlgebra.PowerBounded
import Rigid.Berkovich.RelativeNonempty

set_option linter.style.header false

/-!
# Relative Berkovich spectral seminorms

This file defines the supremum seminorm of an element over the relative Berkovich spectrum and
records the elementary bounds needed for Tate-algebra and affinoid power-bounded arguments.
-/

universe u v

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NontriviallyNormedField K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A]

/-- Power-bounded elements take values at most `1` at every relative Berkovich point. -/
theorem apply_le_one_of_isPowerBounded (x : Rigid.BerkovichSpectrumOver K A) {a : A}
    (ha : Rigid.IsPowerBounded a) : x a ≤ 1 := by
  rcases ha with ⟨M, hM⟩
  by_contra h
  have hxa : 1 < x a := lt_of_not_ge h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hxa
  apply not_le_of_gt hn
  calc
    x a ^ n = x (a ^ n) := (map_pow x.toBerkovichSpectrum.seminorm a n).symm
    _ ≤ ‖a ^ n‖ := Rigid.BerkovichSpectrumOver.le_norm K A x (a ^ n)
    _ ≤ M := hM ⟨n, rfl⟩

/-- The supremum of evaluations of `a` over the relative Berkovich spectrum. -/
noncomputable def spectralSeminorm (a : A) : ℝ :=
  sSup (Set.range fun x : Rigid.BerkovichSpectrumOver K A ↦ x a)

/-- Every evaluation is bounded by the relative Berkovich spectral seminorm. -/
theorem le_spectralSeminorm (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    x a ≤ spectralSeminorm K A a := by
  unfold spectralSeminorm
  apply le_csSup
  · refine ⟨‖a‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Rigid.BerkovichSpectrumOver.le_norm K A y a
  · exact ⟨x, rfl⟩

/-- The relative Berkovich spectral seminorm is nonnegative. -/
theorem spectralSeminorm_nonneg [Nontrivial A] (a : A) : 0 ≤ spectralSeminorm K A a := by
  letI : Nonempty (Rigid.BerkovichSpectrumOver K A) :=
    Rigid.BerkovichSpectrumOver.nonempty_of_nontrivial K A
  obtain ⟨x⟩ := ‹Nonempty (Rigid.BerkovichSpectrumOver K A)›
  exact (Rigid.BerkovichSpectrumOver.nonneg K A x a).trans (le_spectralSeminorm K A x a)

/-- The relative Berkovich spectral seminorm is bounded by the ambient norm. -/
theorem spectralSeminorm_le_norm [Nontrivial A] (a : A) :
    spectralSeminorm K A a ≤ ‖a‖ := by
  letI : Nonempty (Rigid.BerkovichSpectrumOver K A) :=
    Rigid.BerkovichSpectrumOver.nonempty_of_nontrivial K A
  unfold spectralSeminorm
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨x, rfl⟩
  exact Rigid.BerkovichSpectrumOver.le_norm K A x a

/-- Power-bounded elements have relative Berkovich spectral seminorm at most `1`. -/
theorem spectralSeminorm_le_one_of_isPowerBounded [Nontrivial A] {a : A}
    (ha : Rigid.IsPowerBounded a) : spectralSeminorm K A a ≤ 1 := by
  letI : Nonempty (Rigid.BerkovichSpectrumOver K A) :=
    Rigid.BerkovichSpectrumOver.nonempty_of_nontrivial K A
  unfold spectralSeminorm
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨x, rfl⟩
  exact apply_le_one_of_isPowerBounded K A x ha

end Rigid.BerkovichSpectrumOver
