import Rigid.AffinoidAlgebra.MaximumModulus
import Rigid.Berkovich.SpectralRadius

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Spectral radius and power-bounded elements

This file formalizes the analytic part of Proposition 4.5.12 from the cited draft.  In every
Banach algebra, power-bounded elements have spectral radius at most one, and spectral radius
strictly less than one implies power-boundedness.  The boundary case is reduced to the monic
unit-ball relation supplied by Noether normalization.  For a Tate algebra that relation is not
needed: the Gauss point identifies the spectral radius with the Gauss norm directly.
-/

open Filter
open scoped Topology BigOperators

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [IsUltrametricDist B]

namespace IsPowerBounded

/-- A power-bounded element has spectral radius at most one. -/
theorem spectralRadius_le_one [Nontrivial B] {b : B} (hb : IsPowerBounded b) :
    BerkovichSpectrum.spectralRadius B b ≤ 1 := by
  obtain ⟨x, hx⟩ := BerkovichSpectrum.exists_apply_eq_spectralRadius B b
  rw [← hx]
  rcases hb with ⟨C, hC⟩
  by_contra h
  have hxb : 1 < x b := lt_of_not_ge h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hxb
  apply not_le_of_gt hn
  calc
    x b ^ n = x (b ^ n) := (_root_.map_pow x.seminorm b n).symm
    _ ≤ ‖b ^ n‖ := BerkovichSpectrum.le_norm B x _
    _ ≤ C := hC ⟨n, rfl⟩

private theorem of_normalizedNorm_pow_lt_one [Nontrivial B] {b : B} {n : ℕ} (hn : 0 < n)
    (hbn : BerkovichSpectrum.normalizedNormSeminorm B (b ^ n) < 1) :
    IsPowerBounded b := by
  let μ : RingSeminorm B := BerkovichSpectrum.normalizedNormSeminorm B
  let D : ℝ := ∑ r ∈ Finset.range n, μ (b ^ r)
  have hμ1 : μ 1 ≤ 1 := (BerkovichSpectrum.normalizedNormSeminorm_one B).le
  refine ⟨‖(1 : B)‖ * D, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hmod : m % n < n := Nat.mod_lt m hn
  have hdecomp : b ^ m = (b ^ n) ^ (m / n) * b ^ (m % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hblock : μ ((b ^ n) ^ (m / n)) ≤ 1 := by
    calc
      μ ((b ^ n) ^ (m / n)) ≤ μ (b ^ n) ^ (m / n) :=
        map_pow_le_pow' hμ1 (b ^ n) (m / n)
      _ ≤ 1 := pow_le_one₀ (apply_nonneg μ _) hbn.le
  have hrem : μ (b ^ (m % n)) ≤ D := by
    dsimp only [D]
    exact Finset.single_le_sum
      (fun r _ ↦ apply_nonneg μ (b ^ r)) (Finset.mem_range.mpr hmod)
  calc
    ‖b ^ m‖ ≤ ‖(1 : B)‖ * μ (b ^ m) :=
      BerkovichSpectrum.norm_le_norm_one_mul_normalizedNormSeminorm B (b ^ m)
    _ ≤ ‖(1 : B)‖ * (μ ((b ^ n) ^ (m / n)) * μ (b ^ (m % n))) := by
      gcongr
      rw [hdecomp]
      exact map_mul_le_mul μ _ _
    _ ≤ ‖(1 : B)‖ * (1 * μ (b ^ (m % n))) := by gcongr
    _ ≤ ‖(1 : B)‖ * D := by simpa using
      mul_le_mul_of_nonneg_left hrem (norm_nonneg (1 : B))

/-- Spectral radius strictly less than one implies power-boundedness in any complete normed
algebra.  The affinoid input is needed only for the boundary case `ρ = 1`. -/
theorem of_spectralRadius_lt_one [Nontrivial B] {b : B}
    (hb : BerkovichSpectrum.spectralRadius B b < 1) : IsPowerBounded b := by
  have hev : ∀ᶠ n : ℕ in atTop,
      smoothingSeminormSeq (BerkovichSpectrum.normalizedNormSeminorm B) b n < 1 :=
    (BerkovichSpectrum.tendsto_spectralRadius B b) (Iio_mem_nhds hb)
  obtain ⟨n, hnroot, hn⟩ :=
    (hev.and (show ∀ᶠ n : ℕ in atTop, 1 ≤ n from eventually_ge_atTop 1)).exists
  have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hexp : 0 < 1 / (n : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hnpos)
  have hnorm : BerkovichSpectrum.normalizedNormSeminorm B (b ^ n) < 1 :=
    (Real.rpow_lt_one_iff'
      (apply_nonneg (BerkovichSpectrum.normalizedNormSeminorm B) (b ^ n)) hexp).mp hnroot
  exact of_normalizedNorm_pow_lt_one hnpos hnorm

end IsPowerBounded

namespace TateAlgebra

/-- On a strict Tate algebra, the spectral radius is the Gauss norm. -/
theorem spectralRadius_eq_norm (n : ℕ) (f : TateAlgebra K (Fin n)) :
    BerkovichSpectrum.spectralRadius (TateAlgebra K (Fin n)) f = ‖f‖ := by
  apply le_antisymm
  · exact BerkovichSpectrum.spectralRadius_le_norm _ f
  · simpa using BerkovichSpectrumOver.le_spectralRadius K _ (gaussPoint K n) f

/-- Proposition 4.5.12(ii) for the Tate-algebra base case. -/
theorem isPowerBounded_iff_spectralRadius_le_one {n : ℕ} {f : TateAlgebra K (Fin n)} :
    IsPowerBounded f ↔ BerkovichSpectrum.spectralRadius (TateAlgebra K (Fin n)) f ≤ 1 := by
  rw [spectralRadius_eq_norm K n f, isPowerBounded_iff_norm_le_one]

end TateAlgebra

/-- A BGR unit-ball certificate for an element: a finite Tate algebra maps continuously to the
ambient algebra and the element is integral over the image of its Gauss unit ball. -/
def HasUnitBallIntegralCertificate (b : B) : Prop :=
  ∃ (n : ℕ) (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) B),
    IsIntegral ((TateAlgebra.unitBallSubring K n).map π.toRingHom) b

/-- A unit-ball integral certificate implies power-boundedness. -/
theorem isPowerBounded_of_hasUnitBallIntegralCertificate {b : B}
    (hb : HasUnitBallIntegralCertificate K b) : IsPowerBounded b := by
  obtain ⟨n, π, hb⟩ := hb
  exact TateAlgebra.isPowerBounded_of_isIntegral_image_unitBall K n π hb

/-- The boundary property in Proposition 4.5.12(ii). -/
def HasPowerBoundedSpectralCriterion (B : Type v) [NormedCommRing B] : Prop :=
  ∀ b : B, BerkovichSpectrum.spectralRadius B b ≤ 1 → IsPowerBounded b

/-- Unit-ball integral certificates for the closed spectral unit ball imply the boundary
criterion. -/
theorem hasPowerBoundedSpectralCriterion_of_certificates
    (hcertificate : ∀ b : B, BerkovichSpectrum.spectralRadius B b ≤ 1 →
      HasUnitBallIntegralCertificate K b) : HasPowerBoundedSpectralCriterion B :=
  fun b hb ↦ isPowerBounded_of_hasUnitBallIntegralCertificate K (hcertificate b hb)

/-- The boundary step in Proposition 4.5.12(ii), isolated in the exact form supplied by its
Noether-normalization proof. -/
theorem isPowerBounded_iff_spectralRadius_le_one_of_certificate
    [Nontrivial B]
    (hcertificate : ∀ b : B, BerkovichSpectrum.spectralRadius B b ≤ 1 →
      HasUnitBallIntegralCertificate K b) (b : B) :
    IsPowerBounded b ↔ BerkovichSpectrum.spectralRadius B b ≤ 1 := by
  constructor
  · exact IsPowerBounded.spectralRadius_le_one
  · exact fun hb ↦ isPowerBounded_of_hasUnitBallIntegralCertificate K (hcertificate b hb)

/-- Once the affinoid boundary criterion is available, power-boundedness is characterized exactly
by spectral radius at most one. -/
theorem isPowerBounded_iff_spectralRadius_le_one [Nontrivial B]
    (hB : HasPowerBoundedSpectralCriterion B) (b : B) :
    IsPowerBounded b ↔ BerkovichSpectrum.spectralRadius B b ≤ 1 :=
  ⟨IsPowerBounded.spectralRadius_le_one, hB b⟩

end Rigid
