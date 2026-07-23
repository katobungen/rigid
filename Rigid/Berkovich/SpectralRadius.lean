import Rigid.Berkovich.RelativeNonempty

set_option linter.style.header false

/-!
# The spectral radius and the Berkovich maximum-modulus theorem

The spectral radius is the limit of the `n`-th roots of the norms of the powers.  We use the
standard normalized seminorm associated with a possibly non-normalized ring norm; the two norms
are equivalent, so this does not change power-boundedness.  The compactness construction in
`Rigid.Berkovich.Nonempty` produces a multiplicative seminorm attaining this spectral radius.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid.BerkovichSpectrum

variable (R : Type u) [NormedCommRing R]

@[simp]
theorem spectralRadius_zero : spectralRadius R 0 = 0 := by
  change smoothingFun (normalizedNormSeminorm R) 0 = 0
  apply le_antisymm
  · simpa using (smoothingFun_le (normalizedNormSeminorm R) (0 : R) (1 : PNat))
  · exact le_ciInf fun n ↦ Real.rpow_nonneg (apply_nonneg (normalizedNormSeminorm R) _) _

/-- The normalized seminorm controls the original norm up to the fixed factor `‖1‖`. -/
theorem norm_le_norm_one_mul_normalizedNormSeminorm [Nontrivial R] (a : R) :
    ‖a‖ ≤ ‖(1 : R)‖ * normalizedNormSeminorm R a := by
  have hmul : ∀ x y : R, ‖x * y‖ ≤ (1 : ℝ) * ‖x‖ * ‖y‖ := by
    intro x y
    simpa using norm_mul_le x y
  have hbdd : BddAbove (Set.range fun y : R ↦ ‖a * y‖ / ‖y‖) :=
    seminormFromBounded_bddAbove_range norm_nonneg hmul a
  have hle : ‖a‖ / ‖(1 : R)‖ ≤ normalizedNormSeminorm R a := by
    unfold normalizedNormSeminorm
    change ‖a‖ / ‖(1 : R)‖ ≤ seminormFromBounded' (fun x : R ↦ ‖x‖) a
    have hle' := le_ciSup hbdd (1 : R)
    change ‖a * 1‖ / ‖(1 : R)‖ ≤
      seminormFromBounded' (fun x : R ↦ ‖x‖) a at hle'
    simpa only [mul_one] using hle'
  have h1 : 0 < ‖(1 : R)‖ := norm_pos_iff.mpr one_ne_zero
  calc
    ‖a‖ ≤ normalizedNormSeminorm R a * ‖(1 : R)‖ := (div_le_iff₀ h1).mp hle
    _ = ‖(1 : R)‖ * normalizedNormSeminorm R a := mul_comm _ _

/-- The spectral radius is nonnegative. -/
theorem spectralRadius_nonneg [Nontrivial R] (a : R) : 0 ≤ spectralRadius R a :=
  smoothingFun_nonneg (normalizedNormSeminorm R) (normalizedNormSeminorm_one R).le a

/-- The spectral radius is at most the given norm. -/
theorem spectralRadius_le_norm [Nontrivial R] (a : R) : spectralRadius R a ≤ ‖a‖ :=
  (smoothingFun_le_self (normalizedNormSeminorm R) a).trans
    (normalizedNormSeminorm_le_norm R a)

/-- The `n`-th roots of the normalized norms of powers converge to the spectral radius. -/
theorem tendsto_spectralRadius [Nontrivial R] (a : R) :
    Tendsto (smoothingSeminormSeq (normalizedNormSeminorm R) a) atTop
      (𝓝 (spectralRadius R a)) :=
  tendsto_smoothingFun_of_map_one_le_one (normalizedNormSeminorm R)
    (normalizedNormSeminorm_one R).le a

/-- Every bounded multiplicative seminorm is bounded above by the spectral radius. -/
theorem le_spectralRadius [Nontrivial R] (x : Rigid.BerkovichSpectrum R) (a : R) :
    x a ≤ spectralRadius R a := by
  have hroot1 : Tendsto (fun n : ℕ ↦ ‖(1 : R)‖ ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h1 : ‖(1 : R)‖ ≠ 0 := norm_ne_zero_iff.mpr one_ne_zero
    convert tendsto_const_nhds.rpow tendsto_one_div_atTop_nhds_zero_nat (Or.inl h1) using 1
    rw [Real.rpow_zero]
  have hlim : Tendsto (fun n : ℕ ↦
      smoothingSeminormSeq (normalizedNormSeminorm R) a n *
        ‖(1 : R)‖ ^ (1 / (n : ℝ))) atTop (𝓝 (spectralRadius R a)) := by
    simpa using (tendsto_spectralRadius R a).mul hroot1
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  have hexp : 0 < 1 / (n : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr (by omega))
  calc
    x a = (x a ^ n) ^ (1 / (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Rigid.BerkovichSpectrum.nonneg R x a),
        mul_one_div_cancel hn0, Real.rpow_one]
    _ = x (a ^ n) ^ (1 / (n : ℝ)) := by rw [_root_.map_pow x.seminorm]
    _ ≤ ‖a ^ n‖ ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (Rigid.BerkovichSpectrum.nonneg R x (a ^ n))
        (Rigid.BerkovichSpectrum.le_norm R x (a ^ n)) hexp.le
    _ ≤ (normalizedNormSeminorm R (a ^ n) * ‖(1 : R)‖) ^ (1 / (n : ℝ)) := by
      apply Real.rpow_le_rpow (norm_nonneg _) _ hexp.le
      simpa only [mul_comm] using norm_le_norm_one_mul_normalizedNormSeminorm R (a ^ n)
    _ = normalizedNormSeminorm R (a ^ n) ^ (1 / (n : ℝ)) *
        ‖(1 : R)‖ ^ (1 / (n : ℝ)) := by
      rw [Real.mul_rpow (apply_nonneg (normalizedNormSeminorm R) _) (norm_nonneg _)]
    _ = smoothingSeminormSeq (normalizedNormSeminorm R) a n *
        ‖(1 : R)‖ ^ (1 / (n : ℝ)) := rfl

/-- The maximum in the Berkovich maximum-modulus theorem is attained. -/
theorem exists_apply_eq_spectralRadius [Nontrivial R] (a : R) :
    ∃ x : Rigid.BerkovichSpectrum R, x a = spectralRadius R a :=
  exists_apply_eq_smoothingFun R a

end Rigid.BerkovichSpectrum

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NontriviallyNormedField K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A]

/-- Relative Berkovich points are also bounded above by the spectral radius. -/
theorem le_spectralRadius [Nontrivial A] (x : Rigid.BerkovichSpectrumOver K A) (a : A) :
    x a ≤ Rigid.BerkovichSpectrum.spectralRadius A a :=
  Rigid.BerkovichSpectrum.le_spectralRadius A x.toBerkovichSpectrum a

/-- The spectral radius is attained on the relative Berkovich spectrum. -/
theorem exists_apply_eq_spectralRadius [Nontrivial A] (a : A) :
    ∃ x : Rigid.BerkovichSpectrumOver K A,
      x a = Rigid.BerkovichSpectrum.spectralRadius A a := by
  obtain ⟨x, hx⟩ := Rigid.BerkovichSpectrum.exists_apply_eq_spectralRadius A a
  exact ⟨ofBerkovichSpectrum K A x, hx⟩

/-- **Berkovich maximum-modulus theorem.** The spectral radius is the attained maximum of the
values of an element on the relative Berkovich spectrum. -/
theorem exists_spectralRadius_maximum [Nontrivial A] (a : A) :
    ∃ x : Rigid.BerkovichSpectrumOver K A,
      x a = Rigid.BerkovichSpectrum.spectralRadius A a ∧
        ∀ y : Rigid.BerkovichSpectrumOver K A, y a ≤ x a := by
  obtain ⟨x, hx⟩ := exists_apply_eq_spectralRadius K A a
  refine ⟨x, hx, fun y ↦ ?_⟩
  rw [hx]
  exact le_spectralRadius K A y a

/-- Spectral radius does not increase under a continuous algebra homomorphism. -/
theorem spectralRadius_map_le
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [Nontrivial B]
    (f : ContinuousAlgHom K A B) (a : A) :
    Rigid.BerkovichSpectrum.spectralRadius B (f a) ≤
      Rigid.BerkovichSpectrum.spectralRadius A a := by
  letI : Nontrivial A := f.toRingHom.domain_nontrivial
  obtain ⟨y, hy⟩ := exists_apply_eq_spectralRadius K B (f a)
  rw [← hy]
  exact le_spectralRadius K A (comapContinuous K A f y) a

/-- Pointwise boundedness by one on the relative Berkovich spectrum is equivalent to spectral
radius at most one. -/
theorem forall_apply_le_one_iff_spectralRadius_le_one [Nontrivial A] (a : A) :
    (∀ x : Rigid.BerkovichSpectrumOver K A, x a ≤ 1) ↔
      Rigid.BerkovichSpectrum.spectralRadius A a ≤ 1 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_apply_eq_spectralRadius K A a
    rw [← hx]
    exact h x
  · intro h x
    exact (le_spectralRadius K A x a).trans h

end Rigid.BerkovichSpectrumOver
