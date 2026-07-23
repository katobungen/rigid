import Rigid.Berkovich.Nonempty
import Rigid.Berkovich.RelativeSpectrum

set_option linter.style.header false

/-!
# Nonemptiness of relative Berkovich spectra

Every contractive multiplicative seminorm on a normed algebra necessarily restricts to the
specified ground-field norm. For the upper bound, apply contractivity to arbitrary powers of a
scalar; the fixed factor `‖1‖` disappears asymptotically. Applying that bound to a nonzero
scalar and its inverse gives the reverse inequality. Thus the relative and unrestricted Berkovich
spectra are homeomorphic. General Berkovich nonemptiness immediately gives relative nonemptiness.
-/

universe u v

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NormedField K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A]

private theorem map_algebraMap_le (x : Rigid.BerkovichSpectrum A) (r : K) :
    x (algebraMap K A r) ≤ ‖r‖ := by
  by_cases hr : r = 0
  · simp [hr]
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  by_contra! hlt
  have hratio : 1 < x (algebraMap K A r) / ‖r‖ := (one_lt_div hn).2 hlt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖(1 : A)‖ hratio
  have hpow : x (algebraMap K A r) ^ m ≤ ‖r‖ ^ m * ‖(1 : A)‖ := by
    calc
      x (algebraMap K A r) ^ m = x ((algebraMap K A r) ^ m) :=
        (_root_.map_pow x.seminorm _ _).symm
      _ = x (algebraMap K A (r ^ m)) :=
        congr_arg x (_root_.map_pow (algebraMap K A) r m).symm
      _ ≤ ‖algebraMap K A (r ^ m)‖ := Rigid.BerkovichSpectrum.le_norm A x _
      _ = ‖r‖ ^ m * ‖(1 : A)‖ := by rw [norm_algebraMap, norm_pow]
  have hratio_le : (x (algebraMap K A r) / ‖r‖) ^ m ≤ ‖(1 : A)‖ := by
    rw [div_pow, div_le_iff₀ (pow_pos hn m)]
    simpa [mul_comm] using hpow
  exact (not_lt_of_ge hratio_le) hm

/-- Regard an unrestricted Berkovich point as a relative point on a normed algebra. -/
noncomputable def ofBerkovichSpectrum (x : Rigid.BerkovichSpectrum A) :
    Rigid.BerkovichSpectrumOver K A where
  toBerkovichSpectrum := x
  map_algebraMap' r := by
    by_cases hr : r = 0
    · simp [hr]
    have ha : 0 ≤ x (algebraMap K A r) := Rigid.BerkovichSpectrum.nonneg A x _
    have hab : x (algebraMap K A r) * x (algebraMap K A r⁻¹) = 1 := by
      calc
        _ = x (algebraMap K A r * algebraMap K A r⁻¹) :=
          (Rigid.BerkovichSpectrum.map_mul A x _ _).symm
        _ = x (algebraMap K A (r * r⁻¹)) :=
          congr_arg x (_root_.map_mul (algebraMap K A) r r⁻¹).symm
        _ = x 1 := congr_arg x (by rw [mul_inv_cancel₀ hr, _root_.map_one])
        _ = 1 := x.map_one
    have hale : x (algebraMap K A r) ≤ ‖r‖ := map_algebraMap_le K A x r
    have hble : x (algebraMap K A r⁻¹) ≤ ‖r‖⁻¹ :=
      (map_algebraMap_le K A x r⁻¹).trans_eq (norm_inv r)
    have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
    have hnb : ‖r‖ * x (algebraMap K A r⁻¹) ≤ 1 := by
      calc
        ‖r‖ * x (algebraMap K A r⁻¹) ≤ ‖r‖ * ‖r‖⁻¹ :=
          mul_le_mul_of_nonneg_left hble hn.le
        _ = 1 := mul_inv_cancel₀ hn.ne'
    apply le_antisymm hale
    calc
      ‖r‖ = ‖r‖ * (x (algebraMap K A r) * x (algebraMap K A r⁻¹)) := by
        rw [hab, mul_one]
      _ = x (algebraMap K A r) * (‖r‖ * x (algebraMap K A r⁻¹)) := by ring
      _ ≤ x (algebraMap K A r) * 1 := mul_le_mul_of_nonneg_left hnb ha
      _ = x (algebraMap K A r) := mul_one _

@[simp]
theorem ofBerkovichSpectrum_apply (x : Rigid.BerkovichSpectrum A) (a : A) :
    ofBerkovichSpectrum K A x a = x a := rfl

/-- For a normed algebra, the relative and unrestricted Berkovich spectra are homeomorphic. -/
noncomputable def homeomorphBerkovichSpectrum :
    Rigid.BerkovichSpectrumOver K A ≃ₜ Rigid.BerkovichSpectrum A where
  toFun := toBerkovichSpectrum
  invFun := ofBerkovichSpectrum K A
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  continuous_toFun := (Rigid.BerkovichSpectrumOver.isEmbedding_toBerkovichSpectrum K A).continuous
  continuous_invFun := (Rigid.BerkovichSpectrumOver.continuous_iff_eval K A).2 fun a ↦
    Rigid.BerkovichSpectrum.continuous_eval A a

/-- The relative spectrum of a nonzero normed algebra is nonempty. -/
theorem nonempty_of_nontrivial [Nontrivial A] :
    Nonempty (Rigid.BerkovichSpectrumOver K A) :=
  (Rigid.BerkovichSpectrum.nonempty_of_nontrivial A).map (ofBerkovichSpectrum K A)

end Rigid.BerkovichSpectrumOver
