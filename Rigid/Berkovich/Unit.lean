import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Group.Quotient
import Rigid.Berkovich.RelativeNonempty

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Detecting units on the Berkovich spectrum

Maximal ideals in a Banach ring are closed.  Consequently, a nonunit survives as zero in a
nontrivial Banach-field quotient.  Pulling any Berkovich point of that quotient back to the
original algebra produces a point at which the nonunit vanishes.  Thus an element of a complete
normed algebra is a unit exactly when it is nonzero at every Berkovich point.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]

namespace BerkovichSpectrumOver

/-- A unit has nonzero value at every relative Berkovich point. -/
theorem apply_ne_zero_of_isUnit {a : A} (ha : IsUnit a)
    (x : BerkovichSpectrumOver K A) : x a ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  intro hu
  have hzero : x ((↑u : A) * (↑(u⁻¹) : A)) = 0 := by
    rw [BerkovichSpectrumOver.map_mul, hu, zero_mul]
  have hone : x ((↑u : A) * (↑(u⁻¹) : A)) = 1 := by simp
  exact zero_ne_one (hzero.symm.trans hone)

/-- **Unit detection on the Berkovich spectrum.** An element of a Banach algebra is a unit if it
does not vanish at any relative Berkovich point. -/
theorem isUnit_iff_forall_apply_ne_zero {a : A} :
    IsUnit a ↔ ∀ x : BerkovichSpectrumOver K A, x a ≠ 0 := by
  constructor
  · exact fun ha x ↦ apply_ne_zero_of_isUnit K A ha x
  · intro ha
    by_contra hunit
    have hspan : Ideal.span ({a} : Set A) ≠ ⊤ := by
      intro htop
      exact hunit (Ideal.span_singleton_eq_top.mp htop)
    obtain ⟨m, hm, ham⟩ := (Ideal.span ({a} : Set A)).exists_le_maximal hspan
    letI : m.IsMaximal := hm
    letI : IsClosed (m : Set A) := Ideal.IsMaximal.isClosed
    let q : ContinuousAlgHom K A (A ⧸ m) :=
      { toAlgHom := Ideal.Quotient.mkₐ K m
        cont := continuous_quot_mk }
    let y : BerkovichSpectrumOver K (A ⧸ m) :=
      Classical.choice (nonempty_of_nontrivial K (A ⧸ m))
    let x : BerkovichSpectrumOver K A := comapContinuous K A q y
    have haq : q a = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (ham (Ideal.subset_span (Set.mem_singleton a)))
    exact ha x (by simp [x, haq])

end BerkovichSpectrumOver

end Rigid
