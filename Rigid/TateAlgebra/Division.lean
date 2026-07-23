import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.Leading
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.header false

/-!
# The division algorithm in Tate algebras

This file proves the division algorithm of Kato, *Introduction to Rigid Geometry*, Appendix B
(the chapter on the division algorithm in Tate algebras): over a complete nonarchimedean field,
given finitely many nonzero Tate series `G i`, every Tate series `F` admits quotients `Q i` such
that no monomial of `F - ∑ i, Q i * G i` is divisible by any leading monomial
`X ^ leadingDegree m (G i)`.

The proof follows Kato's two-level scheme, after normalizing every divisor to have leading
coefficient one and coefficients of norm at most one. A single sweep
(`TateAlgebra.exists_step_quotients`) removes, by well-founded induction on the monomial order,
every divisible coefficient of norm above a threshold `θ`, producing quotients with
`‖Q i‖ * r ≤ θ`. Here `r < 1` bounds the coefficients of the divisors beyond their leading
degrees, so that the tails only contribute new coefficients of norm at most `θ` and the largest
offending exponent strictly decreases. Iterating the sweep along the geometric thresholds
`‖F‖ * r ^ (k + 1)` produces Cauchy sequences of partial quotients; their limits exist by
completeness of the Tate algebra, and the divisible coefficients of the remainder vanish by
continuity of coefficient extraction.
-/

open Filter
open scoped MonomialOrder Topology

universe u v w

namespace Rigid

namespace TateAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {ι : Type v} {κ : Type w} [Fintype κ]

section Step

variable (m : MonomialOrder ι)
variable {G : κ → TateAlgebra K ι} {ν : κ → ι →₀ ℕ} {r : ℝ}

/-- One sweep of Kato's division algorithm at threshold `θ`: all coefficients of norm above `θ`
sitting at exponents divisible by a leading monomial can be removed by subtracting multiples of
the divisors, whose coefficients satisfy `‖Q i‖ * r ≤ θ`. The hypotheses state that each divisor
`G i` has coefficient `1` at its distinguished exponent `ν i`, coefficients of norm at most one
everywhere, and coefficients of norm at most `r` beyond `ν i`. -/
theorem exists_step_quotients
    (hG1 : ∀ i, MvPowerSeries.coeff (ν i) (G i).1 = 1)
    (hGle : ∀ i n, ‖MvPowerSeries.coeff n (G i).1‖ ≤ 1)
    (hGsmall : ∀ i n, ν i ≺[m] n → ‖MvPowerSeries.coeff n (G i).1‖ ≤ r)
    (hr : 0 ≤ r) {θ : ℝ} (hθ : 0 < θ) (H : TateAlgebra K ι)
    (hH : ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) → ‖MvPowerSeries.coeff μ H.1‖ * r ≤ θ) :
    ∃ Q : κ → TateAlgebra K ι, (∀ i, ‖Q i‖ * r ≤ θ) ∧
      ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
        ‖MvPowerSeries.coeff μ ((H - ∑ i, Q i * G i : TateAlgebra K ι)
          : MvPowerSeries ι K)‖ ≤ θ := by
  classical
  suffices key : ∀ b : m.syn, ∀ H : TateAlgebra K ι,
      (∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) → ‖MvPowerSeries.coeff μ H.1‖ * r ≤ θ) →
      (∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) → θ < ‖MvPowerSeries.coeff μ H.1‖ → m.toSyn μ ≤ b) →
      ∃ Q : κ → TateAlgebra K ι, (∀ i, ‖Q i‖ * r ≤ θ) ∧
        ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
          ‖MvPowerSeries.coeff μ ((H - ∑ i, Q i * G i : TateAlgebra K ι)
            : MvPowerSeries ι K)‖ ≤ θ by
    have hfin : {μ : ι →₀ ℕ | θ ≤ ‖MvPowerSeries.coeff μ H.1‖}.Finite :=
      finite_setOf_le_norm_coeff H hθ
    exact key (hfin.toFinset.sup m.toSyn) H hH fun μ _ hcoeff =>
      Finset.le_sup (hfin.mem_toFinset.mpr hcoeff.le)
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
  intro H hH hb
  -- If nothing offends, there is nothing to do.
  by_cases hS : ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) → ‖MvPowerSeries.coeff μ H.1‖ ≤ θ
  · refine ⟨0, fun i => by simp [hθ.le], fun μ hμ => ?_⟩
    simpa using hS μ hμ
  push Not at hS
  obtain ⟨μ₀, hμ₀M, hμ₀⟩ := hS
  -- The largest offending exponent.
  have hfin : {μ : ι →₀ ℕ | (∃ i, ν i ≤ μ) ∧ θ < ‖MvPowerSeries.coeff μ H.1‖}.Finite :=
    (finite_setOf_le_norm_coeff H hθ).subset fun μ hμ => hμ.2.le
  obtain ⟨μs, hμsS, hmax⟩ := hfin.toFinset.exists_max_image (fun μ => m.toSyn μ)
    ⟨μ₀, hfin.mem_toFinset.mpr ⟨hμ₀M, hμ₀⟩⟩
  rw [hfin.mem_toFinset] at hμsS
  obtain ⟨⟨i₀, hi₀⟩, hμsθ⟩ := hμsS
  set c : K := MvPowerSeries.coeff μs H.1 with hc
  set q : TateAlgebra K ι := monomial (μs - ν i₀) c with hq
  set H' : TateAlgebra K ι := H - q * G i₀ with hH'def
  have hcr : ‖c‖ * r ≤ θ := hH μs ⟨i₀, hi₀⟩
  -- Coefficients of the correction term.
  have hqG : ∀ μ : ι →₀ ℕ,
      MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K)
        = if μs - ν i₀ ≤ μ then c * MvPowerSeries.coeff (μ - (μs - ν i₀)) (G i₀).1 else 0 :=
    fun μ => coeff_monomial_mul _ _ _ μ
  have hqGnorm : ∀ μ : ι →₀ ℕ,
      ‖MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K)‖ ≤ ‖c‖ := by
    intro μ
    rw [hqG μ]
    split_ifs with h
    · calc ‖c * MvPowerSeries.coeff (μ - (μs - ν i₀)) (G i₀).1‖
          ≤ ‖c‖ * ‖MvPowerSeries.coeff (μ - (μs - ν i₀)) (G i₀).1‖ := norm_mul_le _ _
        _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left (hGle i₀ _) (norm_nonneg c)
        _ = ‖c‖ := mul_one _
    · simp
  -- Subtraction of coefficients for the corrected series.
  have hH'coeff : ∀ μ : ι →₀ ℕ, MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)
      = MvPowerSeries.coeff μ H.1
        - MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K) := by
    intro μ
    rw [hH'def, show ((H - q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K)
      = H.1 - ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K) from rfl, map_sub]
  have hH'norm : ∀ μ : ι →₀ ℕ, ‖MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)‖
      ≤ max ‖MvPowerSeries.coeff μ H.1‖
        ‖MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K)‖ := by
    intro μ
    rw [hH'coeff μ, sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [norm_neg])
  -- The coefficient at the largest offender is removed.
  have hμs0 : MvPowerSeries.coeff μs (H' : MvPowerSeries ι K) = 0 := by
    rw [hH'coeff μs, hqG μs, if_pos tsub_le_self, tsub_tsub_cancel_of_le hi₀, hG1 i₀, mul_one,
      ← hc, sub_self]
  -- The smallness hypothesis is preserved.
  have hH'small : ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
      ‖MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)‖ * r ≤ θ := by
    intro μ hμ
    calc ‖MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)‖ * r
        ≤ max ‖MvPowerSeries.coeff μ H.1‖
            ‖MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K)‖ * r :=
          mul_le_mul_of_nonneg_right (hH'norm μ) hr
      _ = max (‖MvPowerSeries.coeff μ H.1‖ * r)
            (‖MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι) : MvPowerSeries ι K)‖ * r) :=
          max_mul_of_nonneg _ _ hr
      _ ≤ θ := max_le (hH μ hμ) ((mul_le_mul_of_nonneg_right (hqGnorm μ) hr).trans hcr)
  -- Every remaining offender lies strictly below the removed one.
  have hH'lt : ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
      θ < ‖MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)‖ → m.toSyn μ < m.toSyn μs := by
    intro μ hμ hθμ
    rcases lt_trichotomy (m.toSyn μ) (m.toSyn μs) with h | h | h
    · exact h
    · exfalso
      rw [m.toSyn.injective h, hμs0, norm_zero] at hθμ
      exact absurd hθμ (not_lt.mpr hθ.le)
    · exfalso
      have hHle : ‖MvPowerSeries.coeff μ H.1‖ ≤ θ := by
        by_contra hcon
        push Not at hcon
        exact absurd h (not_lt.mpr (hmax μ (hfin.mem_toFinset.mpr ⟨hμ, hcon⟩)))
      have hqGle : ‖MvPowerSeries.coeff μ ((q * G i₀ : TateAlgebra K ι)
          : MvPowerSeries ι K)‖ ≤ θ := by
        rw [hqG μ]
        split_ifs with hle
        · have h1 : (μs - ν i₀) + ν i₀ = μs := tsub_add_cancel_of_le hi₀
          have h2 : (μs - ν i₀) + (μ - (μs - ν i₀)) = μ := add_tsub_cancel_of_le hle
          have hτ : ν i₀ ≺[m] μ - (μs - ν i₀) := by
            have hlt : m.toSyn (μs - ν i₀) + m.toSyn (ν i₀)
                < m.toSyn (μs - ν i₀) + m.toSyn (μ - (μs - ν i₀)) := by
              rw [← map_add, ← map_add, h1, h2]
              exact h
            exact lt_of_add_lt_add_left hlt
          calc ‖c * MvPowerSeries.coeff (μ - (μs - ν i₀)) (G i₀).1‖
              ≤ ‖c‖ * ‖MvPowerSeries.coeff (μ - (μs - ν i₀)) (G i₀).1‖ := norm_mul_le _ _
            _ ≤ ‖c‖ * r := mul_le_mul_of_nonneg_left (hGsmall i₀ _ hτ) (norm_nonneg c)
            _ ≤ θ := hcr
        · simpa using hθ.le
      exact absurd hθμ (not_lt.mpr ((hH'norm μ).trans (max_le hHle hqGle)))
  -- Combining a solution for the corrected series with the single-step quotient.
  have hcombine : ∀ Q' : κ → TateAlgebra K ι,
      (∀ i, ‖Q' i‖ * r ≤ θ) →
      (∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
        ‖MvPowerSeries.coeff μ ((H' - ∑ i, Q' i * G i : TateAlgebra K ι)
          : MvPowerSeries ι K)‖ ≤ θ) →
      ∃ Q : κ → TateAlgebra K ι, (∀ i, ‖Q i‖ * r ≤ θ) ∧
        ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
          ‖MvPowerSeries.coeff μ ((H - ∑ i, Q i * G i : TateAlgebra K ι)
            : MvPowerSeries ι K)‖ ≤ θ := by
    intro Q' hQ'1 hQ'2
    refine ⟨fun i => Q' i + if i = i₀ then q else 0, fun i => ?_, fun μ hμ => ?_⟩
    · dsimp only
      by_cases hi : i = i₀
      · rw [if_pos hi]
        calc ‖Q' i + q‖ * r ≤ max ‖Q' i‖ ‖q‖ * r :=
              mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hr
          _ = max (‖Q' i‖ * r) (‖q‖ * r) := max_mul_of_nonneg _ _ hr
          _ ≤ θ := max_le (hQ'1 i) (by rw [hq, norm_monomial]; exact hcr)
      · rw [if_neg hi, add_zero]
        exact hQ'1 i
    · dsimp only
      have halg : H - ∑ i, (Q' i + if i = i₀ then q else 0) * G i
          = H' - ∑ i, Q' i * G i := by
        have hsum : ∑ i, (Q' i + if i = i₀ then q else 0) * G i
            = (∑ i, Q' i * G i) + q * G i₀ := by
          rw [Finset.sum_congr rfl fun i _ => add_mul (Q' i) _ (G i), Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_congr rfl fun i _ => ite_mul (i = i₀) q 0 (G i)]
          simp
        rw [hsum, hH'def]
        abel
      rw [halg]
      exact hQ'2 μ hμ
  by_cases hS' : ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
      ‖MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)‖ ≤ θ
  · exact hcombine 0 (fun i => by simp [hθ.le]) (fun μ hμ => by simpa using hS' μ hμ)
  · push Not at hS'
    obtain ⟨μ₁, hμ₁M, hμ₁⟩ := hS'
    have hfin' : {μ : ι →₀ ℕ | (∃ i, ν i ≤ μ) ∧
        θ < ‖MvPowerSeries.coeff μ (H' : MvPowerSeries ι K)‖}.Finite :=
      (finite_setOf_le_norm_coeff H' hθ).subset fun μ hμ => hμ.2.le
    obtain ⟨μt, hμtS, hmax'⟩ := hfin'.toFinset.exists_max_image (fun μ => m.toSyn μ)
      ⟨μ₁, hfin'.mem_toFinset.mpr ⟨hμ₁M, hμ₁⟩⟩
    rw [hfin'.mem_toFinset] at hμtS
    have hb' : m.toSyn μt < b :=
      lt_of_lt_of_le (hH'lt μt hμtS.1 hμtS.2) (hb μs ⟨i₀, hi₀⟩ hμsθ)
    obtain ⟨Q', hQ'1, hQ'2⟩ := ih (m.toSyn μt) hb' H' hH'small fun μ hμ hcoeff =>
      hmax' μ (hfin'.mem_toFinset.mpr ⟨hμ, hcoeff⟩)
    exact hcombine Q' hQ'1 hQ'2

/-- The division algorithm for normalized divisors: iterating the single sweep along geometric
thresholds and passing to the limit removes every divisible coefficient. -/
theorem exists_div_quotients_aux [CompleteSpace K] (hr0 : 0 < r) (hr1 : r < 1)
    (hG1 : ∀ i, MvPowerSeries.coeff (ν i) (G i).1 = 1)
    (hGle : ∀ i n, ‖MvPowerSeries.coeff n (G i).1‖ ≤ 1)
    (hGsmall : ∀ i n, ν i ≺[m] n → ‖MvPowerSeries.coeff n (G i).1‖ ≤ r)
    (F : TateAlgebra K ι) :
    ∃ Q : κ → TateAlgebra K ι, (∀ i, ‖Q i‖ ≤ ‖F‖) ∧
      ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
        MvPowerSeries.coeff μ
          ((F - ∑ i, Q i * G i : TateAlgebra K ι) : MvPowerSeries ι K) = 0 := by
  classical
  by_cases hF : F = 0
  · exact ⟨0, fun i => by simp [hF], fun μ _ => by simp [hF]⟩
  have hFpos : 0 < ‖F‖ := norm_pos_iff.mpr hF
  set θ : ℕ → ℝ := fun k => ‖F‖ * r ^ (k + 1) with hθdef
  have hθpos : ∀ k, 0 < θ k := fun k => mul_pos hFpos (pow_pos hr0 _)
  -- A total single-sweep function.
  have hstep : ∀ t : ℝ, ∀ H : TateAlgebra K ι, ∃ Q : κ → TateAlgebra K ι,
      (0 < t ∧ ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) → ‖MvPowerSeries.coeff μ H.1‖ * r ≤ t) →
      (∀ i, ‖Q i‖ * r ≤ t) ∧ ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
        ‖MvPowerSeries.coeff μ ((H - ∑ i, Q i * G i : TateAlgebra K ι)
          : MvPowerSeries ι K)‖ ≤ t := by
    intro t H
    by_cases h : 0 < t ∧ ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) → ‖MvPowerSeries.coeff μ H.1‖ * r ≤ t
    · obtain ⟨Q, hQ1, hQ2⟩ := exists_step_quotients m hG1 hGle hGsmall hr0.le h.1 H h.2
      exact ⟨Q, fun _ => ⟨hQ1, hQ2⟩⟩
    · exact ⟨0, fun hcon => absurd hcon h⟩
  choose stepQ hstepQ using hstep
  -- The sequence of partial quotients.
  set U : ℕ → κ → TateAlgebra K ι :=
    fun k => Nat.rec 0 (fun k prev => prev + stepQ (θ k) (F - ∑ i, prev i * G i)) k with hUdef
  have hUsucc : ∀ k, U (k + 1) = U k + stepQ (θ k) (F - ∑ i, U k i * G i) := fun _ => rfl
  have halg : ∀ k, F - ∑ i, U (k + 1) i * G i
      = (F - ∑ i, U k i * G i) - ∑ i, stepQ (θ k) (F - ∑ i, U k i * G i) i * G i := by
    intro k
    rw [hUsucc k]
    simp only [Pi.add_apply]
    rw [Finset.sum_congr rfl fun i _ => add_mul (U k i) _ (G i), Finset.sum_add_distrib]
    abel
  -- The invariant carried along the sweeps.
  have hinv : ∀ k, ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
      ‖MvPowerSeries.coeff μ ((F - ∑ i, U k i * G i : TateAlgebra K ι)
        : MvPowerSeries ι K)‖ * r ≤ θ k := by
    intro k
    induction k with
    | zero =>
      intro μ hμ
      have h0 : (F - ∑ i, U 0 i * G i : TateAlgebra K ι) = F := by
        simp [hUdef]
      rw [h0, hθdef]
      simpa using mul_le_mul_of_nonneg_right (norm_coeff_le_norm K ι F μ) hr0.le
    | succ k ihk =>
      intro μ hμ
      have h := hstepQ (θ k) (F - ∑ i, U k i * G i) ⟨hθpos k, ihk⟩
      rw [halg k]
      calc ‖MvPowerSeries.coeff μ (((F - ∑ i, U k i * G i)
            - ∑ i, stepQ (θ k) (F - ∑ i, U k i * G i) i * G i : TateAlgebra K ι)
            : MvPowerSeries ι K)‖ * r
          ≤ θ k * r := mul_le_mul_of_nonneg_right (h.2 μ hμ) hr0.le
        _ = θ (k + 1) := by rw [hθdef]; ring
  have hbound : ∀ k, ∀ μ : ι →₀ ℕ, (∃ i, ν i ≤ μ) →
      ‖MvPowerSeries.coeff μ ((F - ∑ i, U k i * G i : TateAlgebra K ι)
        : MvPowerSeries ι K)‖ ≤ ‖F‖ * r ^ k := by
    intro k μ hμ
    have h := hinv k μ hμ
    have heq : θ k = (‖F‖ * r ^ k) * r := by rw [hθdef]; ring
    rw [heq] at h
    exact le_of_mul_le_mul_right h hr0
  -- The partial quotients form Cauchy sequences.
  have hdiff : ∀ k i, ‖U (k + 1) i - U k i‖ ≤ ‖F‖ * r ^ k := by
    intro k i
    have h := hstepQ (θ k) (F - ∑ i, U k i * G i) ⟨hθpos k, hinv k⟩
    have heq : θ k = (‖F‖ * r ^ k) * r := by rw [hθdef]; ring
    have hle : ‖stepQ (θ k) (F - ∑ i, U k i * G i) i‖ ≤ ‖F‖ * r ^ k :=
      le_of_mul_le_mul_right ((h.1 i).trans_eq heq) hr0
    calc ‖U (k + 1) i - U k i‖ = ‖stepQ (θ k) (F - ∑ i, U k i * G i) i‖ := by
          rw [hUsucc k]
          simp
      _ ≤ ‖F‖ * r ^ k := hle
  have hUnorm : ∀ k i, ‖U k i‖ ≤ ‖F‖ := by
    intro k
    induction k with
    | zero =>
        intro i
        simp [hUdef]
    | succ k ih =>
        intro i
        have hpow : ‖F‖ * r ^ k ≤ ‖F‖ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (pow_le_one₀ hr0.le hr1.le) (norm_nonneg F)
        have hadd : U k i + (U (k + 1) i - U k i) = U (k + 1) i := by abel
        rw [← hadd]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (ih i) ((hdiff k i).trans hpow))
  have hcauchy : ∀ i, CauchySeq fun k => U k i := by
    intro i
    apply cauchySeq_of_le_geometric r ‖F‖ hr1
    intro k
    rw [dist_eq_norm, norm_sub_rev]
    exact hdiff k i
  choose Qlim hQlim using fun i => cauchySeq_tendsto_of_complete (hcauchy i)
  have hQlimNorm : ∀ i, ‖Qlim i‖ ≤ ‖F‖ := fun i =>
    le_of_tendsto' (hQlim i).norm fun k => hUnorm k i
  refine ⟨Qlim, hQlimNorm, fun μ hμ => ?_⟩
  -- The corrected series converge, hence so do their coefficients.
  have h1 : Tendsto (fun k => F - ∑ i, U k i * G i) atTop (𝓝 (F - ∑ i, Qlim i * G i)) :=
    tendsto_const_nhds.sub (tendsto_finsetSum _ fun i _ => (hQlim i).mul tendsto_const_nhds)
  have h2 : Tendsto (fun k => MvPowerSeries.coeff μ
        ((F - ∑ i, U k i * G i : TateAlgebra K ι) : MvPowerSeries ι K)) atTop
      (𝓝 (MvPowerSeries.coeff μ ((F - ∑ i, Qlim i * G i : TateAlgebra K ι)
        : MvPowerSeries ι K))) :=
    ((lipschitzWith_coeff K ι μ).continuous.tendsto _).comp h1
  have h3 : Tendsto (fun k => ‖MvPowerSeries.coeff μ
        ((F - ∑ i, U k i * G i : TateAlgebra K ι) : MvPowerSeries ι K)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => hbound k μ hμ)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul ‖F‖
  exact norm_eq_zero.mp (tendsto_nhds_unique h2.norm h3)

end Step

/-- **The division algorithm in a Tate algebra** (Kato, *Introduction to Rigid Geometry*,
Appendix B). Over a complete nonarchimedean field, given finitely many nonzero Tate series `G i`
and a monomial order, every `F` admits quotients `Q i` such that no monomial of the remainder
`F - ∑ i, Q i * G i` is divisible by a leading monomial of any `G i`. -/
theorem exists_forall_coeff_eq_zero_of_leadingDegree_le [CompleteSpace K]
    (m : MonomialOrder ι) (G : κ → TateAlgebra K ι) (hG : ∀ i, G i ≠ 0) (F : TateAlgebra K ι) :
    ∃ Q : κ → TateAlgebra K ι, ∀ μ : ι →₀ ℕ, (∃ i, leadingDegree m (G i) ≤ μ) →
      MvPowerSeries.coeff μ ((F - ∑ i, Q i * G i : TateAlgebra K ι) : MvPowerSeries ι K) = 0 := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl hempty => exact ⟨0, fun μ hμ => (hμ.elim fun i _ => (hempty.false i).elim)⟩
  | inr hne =>
  -- Normalize every divisor to leading coefficient one.
  set G' : κ → TateAlgebra K ι := fun i => (leadingCoeff m (G i))⁻¹ • G i with hG'def
  have hlcne : ∀ i, leadingCoeff m (G i) ≠ 0 := fun i => leadingCoeff_ne_zero m (hG i)
  have hG'ne : ∀ i, G' i ≠ 0 := by
    intro i h
    apply hG i
    have h' := congrArg (fun g : TateAlgebra K ι => leadingCoeff m (G i) • g) h
    simpa [hG'def, smul_smul, mul_inv_cancel₀ (hlcne i)] using h'
  have hν' : ∀ i, leadingDegree m (G' i) = leadingDegree m (G i) := fun i =>
    leadingDegree_smul m (inv_ne_zero (hlcne i)) (G i)
  have hG'1 : ∀ i, MvPowerSeries.coeff (leadingDegree m (G' i)) (G' i).1 = 1 := by
    intro i
    rw [hν' i, hG'def]
    dsimp only
    rw [coeff_smul]
    exact inv_mul_cancel₀ (hlcne i)
  have hG'norm : ∀ i, ‖G' i‖ = 1 := by
    intro i
    rw [hG'def]
    dsimp only
    rw [norm_smul, norm_inv, norm_leadingCoeff m (hG i)]
    exact inv_mul_cancel₀ (norm_pos_iff.mpr (hG i)).ne'
  have hG'le : ∀ i n, ‖MvPowerSeries.coeff n (G' i).1‖ ≤ 1 := fun i n =>
    (norm_coeff_le_norm K ι (G' i) n).trans_eq (hG'norm i)
  -- The geometric gap `r < 1` beyond the leading degrees.
  set r : ℝ := max 2⁻¹
    (Finset.univ.sup' Finset.univ_nonempty fun i => ‖G' i - leadingPart (G' i)‖) with hrdef
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hr1 : r < 1 := by
    rw [hrdef]
    apply max_lt (by norm_num)
    rw [Finset.sup'_lt_iff]
    intro i _
    calc ‖G' i - leadingPart (G' i)‖ < ‖G' i‖ := norm_sub_leadingPart_lt (hG'ne i)
      _ = 1 := hG'norm i
  have hGsmall : ∀ i n, leadingDegree m (G' i) ≺[m] n →
      ‖MvPowerSeries.coeff n (G' i).1‖ ≤ r := by
    intro i n hn
    calc ‖MvPowerSeries.coeff n (G' i).1‖ ≤ ‖G' i - leadingPart (G' i)‖ :=
          norm_coeff_le_of_notMem_leadingSupport (G' i)
            (notMem_leadingSupport_of_leadingDegree_lt m (hG'ne i) hn)
      _ ≤ Finset.univ.sup' Finset.univ_nonempty fun i => ‖G' i - leadingPart (G' i)‖ :=
          Finset.le_sup' (fun i => ‖G' i - leadingPart (G' i)‖) (Finset.mem_univ i)
      _ ≤ r := le_max_right _ _
  obtain ⟨Q', _, hQ'⟩ := exists_div_quotients_aux m hr0 hr1 hG'1 hG'le hGsmall F
  refine ⟨fun i => (leadingCoeff m (G i))⁻¹ • Q' i, fun μ hμ => ?_⟩
  have hsum : ∑ i, ((leadingCoeff m (G i))⁻¹ • Q' i) * G i = ∑ i, Q' i * G' i :=
    Finset.sum_congr rfl fun i _ => by
      rw [hG'def]
      dsimp only
      rw [smul_mul_assoc, mul_smul_comm]
  have hμ' : ∃ i, leadingDegree m (G' i) ≤ μ := by
    obtain ⟨i, hi⟩ := hμ
    exact ⟨i, by rw [hν' i]; exact hi⟩
  have h0 := hQ' μ hμ'
  rw [show F - ∑ i, (fun i => (leadingCoeff m (G i))⁻¹ • Q' i) i * G i
      = F - ∑ i, Q' i * G' i by rw [← hsum]]
  exact h0

end TateAlgebra

end Rigid
