import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Algebra

set_option linter.style.header false

/-!
# Quotient norms

This file defines the quotient norm associated to a surjective map and distinguishes exact equality
with that quotient norm from equivalence up to positive multiplicative constants.
-/

universe u v w

namespace Rigid

section QuotientNorm

variable {B : Type v} [SeminormedAddCommGroup B]
variable {C : Type w} [SeminormedAddCommGroup C]

/-- The quotient seminorm induced by a map, defined as the infimum of source norms in a fiber.
It has the expected behavior when the map is surjective. -/
noncomputable def quotientNorm (f : B → C) (y : C) : ℝ :=
  sInf ((fun x : B ↦ ‖x‖) '' {x | f x = y})

/-- A map is a quotient-norm presentation when it is surjective and the given target norm is exactly
the induced quotient norm. -/
def IsQuotientNorm (f : B → C) : Prop :=
  Function.Surjective f ∧ ∀ y : C, ‖y‖ = quotientNorm f y

/-- The target norm is equivalent to the induced quotient norm when the map is surjective and the
two norms bound one another up to positive constants. -/
def IsEquivalentQuotientNorm (f : B → C) : Prop :=
  Function.Surjective f ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ y : C, c₁ * quotientNorm f y ≤ ‖y‖ ∧ ‖y‖ ≤ c₂ * quotientNorm f y

namespace IsQuotientNorm

variable {f : B → C}

/-- A quotient-norm presentation is surjective. -/
theorem surjective (hf : IsQuotientNorm f) : Function.Surjective f :=
  hf.1

/-- The target norm is the infimum of the source norms in each fiber. -/
theorem norm_eq_quotientNorm (hf : IsQuotientNorm f) (y : C) : ‖y‖ = quotientNorm f y :=
  hf.2 y

/-- The target norm is the infimum of the source norms in each fiber. -/
theorem norm_eq_sInf_fiber (hf : IsQuotientNorm f) (y : C) :
    ‖y‖ = sInf ((fun x : B ↦ ‖x‖) '' {x | f x = y}) :=
  hf.norm_eq_quotientNorm y

/-- A quotient-norm presentation is norm-nonincreasing. -/
theorem norm_le (hf : IsQuotientNorm f) (x : B) : ‖f x‖ ≤ ‖x‖ := by
  rw [hf.norm_eq_sInf_fiber]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨y, -, rfl⟩
    exact norm_nonneg y
  · exact ⟨x, rfl, rfl⟩

/-- Every target element has lifts with norm arbitrarily close to its quotient norm. -/
theorem exists_preimage_norm_lt (hf : IsQuotientNorm f) {ε : ℝ} (hε : 0 < ε) (y : C) :
    ∃ x : B, f x = y ∧ ‖x‖ < ‖y‖ + ε := by
  obtain ⟨x, hx⟩ := hf.surjective y
  have hne : ((fun x : B ↦ ‖x‖) '' {x | f x = y}).Nonempty :=
    ⟨‖x‖, x, hx, rfl⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne hε
  rw [← hf.norm_eq_sInf_fiber] at hlt
  exact ⟨x, hx, hlt⟩

/-- Exact equality with the quotient norm implies equivalence with it. -/
theorem isEquivalentQuotientNorm (hf : IsQuotientNorm f) : IsEquivalentQuotientNorm f := by
  refine ⟨hf.surjective, 1, 1, zero_lt_one, zero_lt_one, fun y ↦ ?_⟩
  rw [hf.norm_eq_quotientNorm]
  simp

end IsQuotientNorm

namespace IsEquivalentQuotientNorm

variable {f : B → C}

/-- Equivalence with a quotient norm includes surjectivity. -/
theorem surjective (hf : IsEquivalentQuotientNorm f) : Function.Surjective f :=
  hf.1

end IsEquivalentQuotientNorm

end QuotientNorm

section OpenMapping

variable {K : Type u} [NontriviallyNormedField K]
variable {B : Type v} [NormedAddCommGroup B] [NormedSpace K B] [CompleteSpace B]
variable {C : Type w} [NormedAddCommGroup C] [NormedSpace K C] [CompleteSpace C]

/-- A surjective continuous linear map between Banach spaces makes the given target norm equivalent
to the quotient norm. This is the norm-level form of the Banach open mapping theorem. -/
theorem isEquivalentQuotientNorm_of_surjective (f : B →L[K] C) (hf : Function.Surjective f) :
    IsEquivalentQuotientNorm (f : B → C) := by
  obtain ⟨M, hM, hMf⟩ := f.bound
  obtain ⟨N, hN, hNf⟩ := f.exists_preimage_norm_le hf
  refine ⟨hf, N⁻¹, M, inv_pos.mpr hN, hM, fun y ↦ ?_⟩
  obtain ⟨x, hfx, hx⟩ := hNf y
  have hbdd : BddBelow ((fun x : B ↦ ‖x‖) '' {x | f x = y}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, -, rfl⟩
    exact norm_nonneg z
  have hq_le : quotientNorm (f : B → C) y ≤ N * ‖y‖ := by
    exact (csInf_le hbdd ⟨x, hfx, rfl⟩).trans hx
  have hne : ((fun x : B ↦ ‖x‖) '' {x | f x = y}).Nonempty :=
    ⟨‖x‖, x, hfx, rfl⟩
  have hdiv_le : ‖y‖ / M ≤ quotientNorm (f : B → C) y := by
    apply le_csInf hne
    rintro _ ⟨z, hfz, rfl⟩
    apply (div_le_iff₀ hM).2
    rw [← hfz]
    simpa [mul_comm] using hMf z
  constructor
  · calc
      N⁻¹ * quotientNorm (f : B → C) y ≤ N⁻¹ * (N * ‖y‖) := by
        gcongr
      _ = ‖y‖ := by field_simp
  · calc
      ‖y‖ = M * (‖y‖ / M) := by field_simp
      _ ≤ M * quotientNorm (f : B → C) y := by gcongr

/-- A surjective continuous algebra homomorphism between Banach algebras gives an equivalent
quotient norm on its target. -/
theorem isEquivalentQuotientNorm_of_surjective_continuousAlgHom
    {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
    {C : Type w} [NormedCommRing C] [NormedAlgebra K C] [CompleteSpace C]
    (f : ContinuousAlgHom K B C) (hf : Function.Surjective f) :
    IsEquivalentQuotientNorm (f : B → C) :=
  isEquivalentQuotientNorm_of_surjective f.toContinuousLinearMap hf

end OpenMapping

end Rigid
