import Rigid.TateAlgebra.NormedRing
import Mathlib.Data.Finsupp.MonomialOrder

set_option linter.style.header false

/-!
# Leading terms of Tate series

A nonzero Tate series attains its Gauss norm at finitely many exponents. Following Appendix B of
Kato, *Introduction to Rigid Geometry* (the chapter on the division algorithm in Tate algebras),
the sum of the corresponding terms is the *leading part* of the series; given a monomial order,
the largest attaining exponent is the *leading degree* and its coefficient is the *leading
coefficient*. These notions drive the division algorithm in `Rigid.TateAlgebra.Division`.

Everything here is relative to an arbitrary `MonomialOrder`; the variable set need not be finite
and the ground field need not be complete.
-/

open Filter
open scoped MonomialOrder

universe u v

namespace Rigid

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {ι : Type v}

namespace TateAlgebra

/-! ## Monomials -/

/-- The monomial of a Tate algebra with the given exponent and coefficient. -/
noncomputable def monomial (n : ι →₀ ℕ) (a : K) : TateAlgebra K ι :=
  ⟨MvPowerSeries.monomial n a, MvPowerSeries.isRestricted_monomial _ n a⟩

@[simp]
theorem coe_monomial (n : ι →₀ ℕ) (a : K) :
    ((monomial n a : TateAlgebra K ι) : MvPowerSeries ι K) = MvPowerSeries.monomial n a :=
  rfl

@[simp]
theorem norm_monomial (n : ι →₀ ℕ) (a : K) : ‖(monomial n a : TateAlgebra K ι)‖ = ‖a‖ := by
  classical
  apply le_antisymm
  · rw [norm_eq_sSup_coeff]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨μ, rfl⟩
    dsimp only
    rw [coe_monomial, MvPowerSeries.coeff_monomial]
    split_ifs <;> simp
  · have h := norm_coeff_le_norm K ι (monomial n a) n
    rwa [coe_monomial, MvPowerSeries.coeff_monomial_same] at h

/-- The coefficients of the product of a monomial and a Tate series. -/
theorem coeff_monomial_mul (n : ι →₀ ℕ) (a : K) (f : TateAlgebra K ι) (μ : ι →₀ ℕ) :
    MvPowerSeries.coeff μ ((monomial n a * f : TateAlgebra K ι) : MvPowerSeries ι K)
      = if n ≤ μ then a * MvPowerSeries.coeff (μ - n) f.1 else 0 := by
  rw [show ((monomial n a * f : TateAlgebra K ι) : MvPowerSeries ι K)
      = MvPowerSeries.monomial n a * f.1 from rfl, MvPowerSeries.coeff_monomial_mul]

/-- Multiplication by a scalar acts on every coefficient of a Tate series. -/
theorem coeff_smul (c : K) (f : TateAlgebra K ι) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n ((c • f : TateAlgebra K ι) : MvPowerSeries ι K)
      = c * MvPowerSeries.coeff n f.1 := by
  have hcoe : ((c • f : TateAlgebra K ι) : MvPowerSeries ι K)
      = MvPowerSeries.C c * (f : MvPowerSeries ι K) := by
    rw [Algebra.smul_def, algebraMap_apply]
    rfl
  rw [hcoe, MvPowerSeries.coeff_C_mul]

/-! ## Attained coefficients -/

/-- Only finitely many coefficients of a Tate series have norm at least a positive bound. -/
theorem finite_setOf_le_norm_coeff (f : TateAlgebra K ι) {ε : ℝ} (hε : 0 < ε) :
    {n : ι →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff n f.1‖}.Finite := by
  have hev : ∀ᶠ n : ι →₀ ℕ in cofinite, ‖MvPowerSeries.coeff n f.1‖ < ε :=
    (tendsto_norm_coeff_zero K ι f).eventually (eventually_lt_nhds hε)
  simpa [Filter.eventually_cofinite, not_lt] using hev

/-- A nonzero Tate series attains its Gauss norm at some coefficient. -/
theorem exists_norm_coeff_eq_norm {f : TateAlgebra K ι} (hf : f ≠ 0) :
    ∃ n : ι →₀ ℕ, ‖MvPowerSeries.coeff n f.1‖ = ‖f‖ := by
  have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hfin := finite_setOf_le_norm_coeff f (half_pos hpos)
  have hSne : {n : ι →₀ ℕ | ‖f‖ / 2 ≤ ‖MvPowerSeries.coeff n f.1‖}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hcon
    have hle : ‖f‖ ≤ ‖f‖ / 2 := by
      rw [norm_eq_sSup_coeff]
      refine csSup_le (Set.range_nonempty _) ?_
      rintro _ ⟨n, rfl⟩
      exact (not_le.mp fun h => hcon n h).le
    linarith
  obtain ⟨n₁, hn₁⟩ := hSne
  obtain ⟨n₀, hn₀S, hmax⟩ := hfin.toFinset.exists_max_image
    (fun n => ‖MvPowerSeries.coeff n f.1‖) ⟨n₁, hfin.mem_toFinset.mpr hn₁⟩
  refine ⟨n₀, le_antisymm (norm_coeff_le_norm K ι f n₀) ?_⟩
  rw [norm_eq_sSup_coeff]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  dsimp only
  by_cases hn : ‖f‖ / 2 ≤ ‖MvPowerSeries.coeff n f.1‖
  · exact hmax n (hfin.mem_toFinset.mpr hn)
  · exact (not_le.mp hn).le.trans (hfin.mem_toFinset.mp hn₀S)

/-! ## Leading degree and leading coefficient -/

variable (m : MonomialOrder ι)

/-- Among the exponents where a nonzero Tate series attains its Gauss norm there is a largest one
for any monomial order. -/
theorem exists_leadingDegree {f : TateAlgebra K ι} (hf : f ≠ 0) :
    ∃ ν : ι →₀ ℕ, ‖MvPowerSeries.coeff ν f.1‖ = ‖f‖ ∧
      ∀ n : ι →₀ ℕ, ‖f‖ ≤ ‖MvPowerSeries.coeff n f.1‖ → n ≼[m] ν := by
  have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hfin := finite_setOf_le_norm_coeff f hpos
  obtain ⟨n₁, hn₁⟩ := exists_norm_coeff_eq_norm hf
  obtain ⟨ν, hνS, hmax⟩ := hfin.toFinset.exists_max_image (fun n => m.toSyn n)
    ⟨n₁, hfin.mem_toFinset.mpr hn₁.ge⟩
  refine ⟨ν, le_antisymm (norm_coeff_le_norm K ι f ν) (hfin.mem_toFinset.mp hνS), ?_⟩
  exact fun n hn => hmax n (hfin.mem_toFinset.mpr hn)

open Classical in
/-- The leading degree of a Tate series: the largest exponent, in the given monomial order, at
which the series attains its Gauss norm. This is Kato's `ν(F)`; the zero series is sent to `0`. -/
noncomputable def leadingDegree (f : TateAlgebra K ι) : ι →₀ ℕ :=
  if hf : f = 0 then 0 else (exists_leadingDegree m hf).choose

/-- The leading coefficient of a Tate series: the coefficient at the leading degree. This is
Kato's `LC(F)`. -/
noncomputable def leadingCoeff (f : TateAlgebra K ι) : K :=
  MvPowerSeries.coeff (leadingDegree m f) f.1

theorem norm_leadingCoeff {f : TateAlgebra K ι} (hf : f ≠ 0) :
    ‖leadingCoeff m f‖ = ‖f‖ := by
  rw [leadingCoeff, leadingDegree, dif_neg hf]
  exact (exists_leadingDegree m hf).choose_spec.1

theorem le_leadingDegree {f : TateAlgebra K ι} (hf : f ≠ 0) {n : ι →₀ ℕ}
    (hn : ‖f‖ ≤ ‖MvPowerSeries.coeff n f.1‖) : n ≼[m] leadingDegree m f := by
  rw [leadingDegree, dif_neg hf]
  exact (exists_leadingDegree m hf).choose_spec.2 n hn

theorem leadingCoeff_ne_zero {f : TateAlgebra K ι} (hf : f ≠ 0) :
    leadingCoeff m f ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_leadingCoeff m hf]
  exact (norm_pos_iff.mpr hf).ne'

theorem norm_coeff_lt_of_leadingDegree_lt {f : TateAlgebra K ι} (hf : f ≠ 0) {n : ι →₀ ℕ}
    (hn : leadingDegree m f ≺[m] n) : ‖MvPowerSeries.coeff n f.1‖ < ‖f‖ :=
  lt_of_le_of_ne (norm_coeff_le_norm K ι f n) fun h =>
    absurd (le_leadingDegree m hf h.ge) (not_le.mpr hn)

/-- The leading degree is characterized by attaining the norm and dominating all attaining
exponents. -/
theorem leadingDegree_unique {f : TateAlgebra K ι} (hf : f ≠ 0) {ν : ι →₀ ℕ}
    (h1 : ‖MvPowerSeries.coeff ν f.1‖ = ‖f‖)
    (h2 : ∀ n : ι →₀ ℕ, ‖f‖ ≤ ‖MvPowerSeries.coeff n f.1‖ → n ≼[m] ν) :
    leadingDegree m f = ν := by
  have ha : leadingDegree m f ≼[m] ν := by
    refine h2 _ ?_
    rw [← norm_leadingCoeff m hf]
    rfl
  have hb : ν ≼[m] leadingDegree m f := le_leadingDegree m hf h1.ge
  exact m.toSyn.injective (le_antisymm ha hb)

@[simp]
theorem leadingDegree_smul {c : K} (hc : c ≠ 0) (f : TateAlgebra K ι) :
    leadingDegree m (c • f) = leadingDegree m f := by
  by_cases hf : f = 0
  · rw [hf, smul_zero]
  have hcf : c • f ≠ 0 := by
    intro h
    apply hf
    have h' := congrArg (fun g : TateAlgebra K ι => c⁻¹ • g) h
    simpa [smul_smul, inv_mul_cancel₀ hc] using h'
  refine (leadingDegree_unique m hcf ?_ ?_).symm.symm
  · rw [show ((c • f : TateAlgebra K ι) : MvPowerSeries ι K).coeff (leadingDegree m f)
        = c * MvPowerSeries.coeff (leadingDegree m f) f.1 from coeff_smul c f _]
    rw [norm_mul, norm_smul, ← norm_leadingCoeff m hf]
    rfl
  · intro n hn
    apply le_leadingDegree m hf
    rw [norm_smul] at hn
    have hn' := hn.trans_eq (congrArg norm (coeff_smul c f n))
    rw [norm_mul] at hn'
    exact le_of_mul_le_mul_left hn' (norm_pos_iff.mpr hc)

theorem leadingCoeff_smul {c : K} (hc : c ≠ 0) (f : TateAlgebra K ι) :
    leadingCoeff m (c • f) = c * leadingCoeff m f := by
  rw [leadingCoeff, leadingCoeff, leadingDegree_smul m hc]
  exact coeff_smul c f _

/-! ## The leading part -/

open Classical in
/-- The exponents at which a Tate series attains its Gauss norm; empty for the zero series. -/
noncomputable def leadingSupport (f : TateAlgebra K ι) : Finset (ι →₀ ℕ) :=
  if hf : f = 0 then ∅
  else (finite_setOf_le_norm_coeff f (norm_pos_iff.mpr hf)).toFinset

theorem mem_leadingSupport {f : TateAlgebra K ι} (hf : f ≠ 0) {n : ι →₀ ℕ} :
    n ∈ leadingSupport f ↔ ‖f‖ ≤ ‖MvPowerSeries.coeff n f.1‖ := by
  rw [leadingSupport, dif_neg hf, Set.Finite.mem_toFinset]
  rfl

theorem notMem_leadingSupport_of_leadingDegree_lt {f : TateAlgebra K ι} (hf : f ≠ 0)
    {n : ι →₀ ℕ} (hn : leadingDegree m f ≺[m] n) : n ∉ leadingSupport f := fun hmem =>
  absurd (le_leadingDegree m hf ((mem_leadingSupport hf).mp hmem)) (not_le.mpr hn)

/-- Kato's *leading part* of a Tate series: the polynomial formed by the finitely many terms
whose coefficients attain the Gauss norm. -/
noncomputable def leadingPart (f : TateAlgebra K ι) : TateAlgebra K ι :=
  ∑ n ∈ leadingSupport f, monomial n (MvPowerSeries.coeff n f.1)

open Classical in
theorem coeff_leadingPart (f : TateAlgebra K ι) (μ : ι →₀ ℕ) :
    MvPowerSeries.coeff μ ((leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K)
      = if μ ∈ leadingSupport f then MvPowerSeries.coeff μ f.1 else 0 := by
  have hcoe : ((leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K)
      = ∑ n ∈ leadingSupport f, MvPowerSeries.monomial n (MvPowerSeries.coeff n f.1) := by
    rw [leadingPart, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun n _ => rfl
  rw [hcoe, map_sum]
  rw [Finset.sum_congr rfl fun n _ => MvPowerSeries.coeff_monomial μ n _]
  exact Finset.sum_ite_eq (leadingSupport f) μ fun n => MvPowerSeries.coeff n f.1

/-- Removing the leading part strictly decreases the Gauss norm. -/
theorem norm_sub_leadingPart_lt {f : TateAlgebra K ι} (hf : f ≠ 0) :
    ‖f - leadingPart f‖ < ‖f‖ := by
  by_cases h0 : f - leadingPart f = 0
  · rw [h0, norm_zero]
    exact norm_pos_iff.mpr hf
  · obtain ⟨n, hn⟩ := exists_norm_coeff_eq_norm h0
    rw [← hn]
    have hcoeff : MvPowerSeries.coeff n ((f - leadingPart f : TateAlgebra K ι)
          : MvPowerSeries ι K)
        = MvPowerSeries.coeff n f.1
          - MvPowerSeries.coeff n ((leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K) := by
      rw [show ((f - leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K)
          = f.1 - ((leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K) from rfl, map_sub]
    by_cases hmem : n ∈ leadingSupport f
    · exfalso
      have hzero : MvPowerSeries.coeff n ((f - leadingPart f : TateAlgebra K ι)
          : MvPowerSeries ι K) = 0 := by
        rw [hcoeff, coeff_leadingPart, if_pos hmem, sub_self]
      rw [hzero, norm_zero] at hn
      exact h0 (norm_eq_zero.mp hn.symm)
    · rw [hcoeff, coeff_leadingPart, if_neg hmem, sub_zero]
      exact not_le.mp fun hc => hmem ((mem_leadingSupport hf).mpr hc)

/-- Coefficients away from the leading support are bounded by the norm of the series without its
leading part. -/
theorem norm_coeff_le_of_notMem_leadingSupport (f : TateAlgebra K ι) {n : ι →₀ ℕ}
    (hn : n ∉ leadingSupport f) :
    ‖MvPowerSeries.coeff n f.1‖ ≤ ‖f - leadingPart f‖ := by
  have hcoeff : MvPowerSeries.coeff n f.1
      = MvPowerSeries.coeff n ((f - leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K) := by
    rw [show ((f - leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K)
        = f.1 - ((leadingPart f : TateAlgebra K ι) : MvPowerSeries ι K) from rfl, map_sub,
      coeff_leadingPart, if_neg hn, sub_zero]
  rw [hcoeff]
  exact norm_coeff_le_norm K ι _ n

end TateAlgebra

end Rigid
