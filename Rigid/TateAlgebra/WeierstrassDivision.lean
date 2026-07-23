import Rigid.TateAlgebra.Division
import Rigid.TateAlgebra.LeadingMultiplicative

set_option linter.style.header false

/-!
# Weierstrass division for a distinguished leading monomial

This file exposes the one-divisor consequence of the general Tate-algebra division algorithm.
When the leading monomial of `g` is a pure power of the first variable, every series has a
quotient by `g` and a remainder whose coefficients in that variable vanish from that degree on.
It is the division input to the Weierstrass preparation and Rückert arguments in §4.1 of the
cited draft.
-/

open scoped MonomialOrder

universe u

namespace Rigid

namespace TateAlgebra

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- One-divisor Weierstrass division for a series whose leading degree is a pure power of the
first variable. -/
theorem exists_quotient_remainder_of_leadingDegree_eq_single_zero {n d : ℕ}
    (g : TateAlgebra K (Fin (n + 1))) (hg : g ≠ 0)
    (hgd : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g =
      Finsupp.single 0 d) (f : TateAlgebra K (Fin (n + 1))) :
    ∃ q r : TateAlgebra K (Fin (n + 1)), f = q * g + r ∧
      ∀ μ : Fin (n + 1) →₀ ℕ, d ≤ μ 0 → MvPowerSeries.coeff μ r.1 = 0 := by
  obtain ⟨Q, hQ⟩ := exists_forall_coeff_eq_zero_of_leadingDegree_le
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) (fun _ : Fin 1 ↦ g)
      (fun _ ↦ hg) f
  let q := Q 0
  let r := f - q * g
  refine ⟨q, r, ?_, ?_⟩
  · dsimp only [r]
    abel
  · intro μ hμ
    have hdiv : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g ≤ μ := by
      rw [hgd]
      simpa [Finsupp.single_le_iff] using hμ
    simpa only [q, r, Fin.sum_univ_one] using hQ μ ⟨0, hdiv⟩

/-- Norm-controlled one-divisor division after normalizing the leading coefficient to one. -/
theorem exists_quotient_remainder_norm_le_of_leadingCoeff_eq_one {n d : ℕ}
    (g : TateAlgebra K (Fin (n + 1))) (hg : g ≠ 0)
    (hgd : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g =
      Finsupp.single 0 d)
    (hglc : leadingCoeff (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g = 1)
    (f : TateAlgebra K (Fin (n + 1))) :
    ∃ q r : TateAlgebra K (Fin (n + 1)), ‖q‖ ≤ ‖f‖ ∧ f = q * g + r ∧
      ∀ μ : Fin (n + 1) →₀ ℕ, d ≤ μ 0 → MvPowerSeries.coeff μ r.1 = 0 := by
  classical
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  let G : Fin 1 → TateAlgebra K (Fin (n + 1)) := fun _ ↦ g
  let ν : Fin 1 → Fin (n + 1) →₀ ℕ := fun _ ↦ Finsupp.single 0 d
  have hgnorm : ‖g‖ = 1 := by
    rw [← norm_leadingCoeff m hg, hglc]
    exact norm_one
  have hG1 : ∀ i, MvPowerSeries.coeff (ν i) (G i).1 = 1 := by
    intro i
    change MvPowerSeries.coeff (Finsupp.single 0 d) g.1 = 1
    rw [← hgd]
    exact hglc
  have hGle : ∀ i μ, ‖MvPowerSeries.coeff μ (G i).1‖ ≤ 1 := by
    intro i μ
    exact (norm_coeff_le_norm K _ g μ).trans_eq hgnorm
  let ρ : ℝ := max 2⁻¹ ‖g - leadingPart g‖
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hρ1 : ρ < 1 := by
    exact max_lt (by norm_num) ((norm_sub_leadingPart_lt hg).trans_eq hgnorm)
  have hGsmall : ∀ i μ, ν i ≺[m] μ →
      ‖MvPowerSeries.coeff μ (G i).1‖ ≤ ρ := by
    intro i μ hμ
    exact (norm_coeff_le_of_notMem_leadingSupport g
      (notMem_leadingSupport_of_leadingDegree_lt m hg (by simpa [ν, m, hgd] using hμ))).trans
        (le_max_right _ _)
  obtain ⟨Q, hQnorm, hQrem⟩ :=
    exists_div_quotients_aux m hρ0 hρ1 hG1 hGle hGsmall f
  let q := Q 0
  let r := f - q * g
  refine ⟨q, r, hQnorm 0, ?_, ?_⟩
  · dsimp only [r]
    abel
  · intro μ hμ
    have hdiv : ∃ i, ν i ≤ μ := ⟨0, by simpa [ν, Finsupp.single_le_iff] using hμ⟩
    simpa only [q, r, G, Fin.sum_univ_one] using hQrem μ hdiv

/-- A Tate series which is a monic polynomial of degree `d` in the first variable, with Gauss
norm at most one. -/
def IsWeierstrassOfDegree {n : ℕ} (d : ℕ) (w : TateAlgebra K (Fin (n + 1))) : Prop :=
  ‖w‖ ≤ 1 ∧ MvPowerSeries.coeff (Finsupp.single 0 d) w.1 = 1 ∧
    ∀ μ : Fin (n + 1) →₀ ℕ, μ ≠ Finsupp.single 0 d → d ≤ μ 0 →
      MvPowerSeries.coeff μ w.1 = 0

private theorem single_zero_le_of_lex_lt {n d : ℕ} {μ : Fin (n + 1) →₀ ℕ}
    (hμ : Finsupp.single 0 d ≺[(MonomialOrder.lex : MonomialOrder (Fin (n + 1)))] μ) :
    d ≤ μ 0 := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff] at hμ
  obtain ⟨j, hj, hjlt⟩ := hμ
  by_cases hj0 : j = 0
  · subst j
    simpa using hjlt.le
  · have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
    have heq := hj 0 h0j
    simpa using heq.le

/-- Weierstrass preparation for a series already normalized to have a pure first-variable leading
monomial and leading coefficient one. -/
theorem exists_isUnit_mul_isWeierstrassOfDegree_of_leadingCoeff_eq_one {n d : ℕ}
    (g : TateAlgebra K (Fin (n + 1))) (hg : g ≠ 0)
    (hgd : leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g =
      Finsupp.single 0 d)
    (hglc : leadingCoeff (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) g = 1) :
    ∃ e w : TateAlgebra K (Fin (n + 1)), IsUnit e ∧ IsWeierstrassOfDegree d w ∧
      g = e * w := by
  classical
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  let ν : Fin (n + 1) →₀ ℕ := Finsupp.single 0 d
  let F : TateAlgebra K (Fin (n + 1)) := monomial ν 1
  obtain ⟨q, r, hqnorm, hF, hr⟩ :=
    exists_quotient_remainder_norm_le_of_leadingCoeff_eq_one g hg hgd hglc F
  let w : TateAlgebra K (Fin (n + 1)) := F - r
  have hgnorm : ‖g‖ = 1 := by
    rw [← norm_leadingCoeff m hg, hglc]
    exact norm_one
  have hFnorm : ‖F‖ = 1 := by simp [F]
  have hqg : q * g = w := by
    dsimp only [w]
    rw [hF]
    abel
  have hwnorm : ‖w‖ ≤ 1 := by
    rw [← hqg, norm_mul, hgnorm, mul_one]
    exact hqnorm.trans_eq hFnorm
  have hwcoeff : MvPowerSeries.coeff ν w.1 = 1 := by
    rw [show w = F - r from rfl]
    change MvPowerSeries.coeff ν (F.1 - r.1) = 1
    rw [map_sub, hr ν (by simp [ν])]
    simp [F, ν]
  have hwhigh : ∀ μ : Fin (n + 1) →₀ ℕ, μ ≠ ν → d ≤ μ 0 →
      MvPowerSeries.coeff μ w.1 = 0 := by
    intro μ hμne hμd
    rw [show w = F - r from rfl]
    change MvPowerSeries.coeff μ (F.1 - r.1) = 0
    rw [map_sub, hr μ hμd]
    simp only [sub_zero]
    rw [show F.1 = MvPowerSeries.monomial ν 1 from rfl,
      MvPowerSeries.coeff_monomial, if_neg hμne]
  have hwne : w ≠ 0 := by
    intro hw
    rw [hw] at hwcoeff
    simp at hwcoeff
  have hwnormeq : ‖w‖ = 1 := by
    apply le_antisymm hwnorm
    have hle := norm_coeff_le_norm K _ w ν
    rw [hwcoeff, norm_one] at hle
    exact hle
  have hwdeg : leadingDegree m w = ν := by
    apply leadingDegree_unique m hwne
    · rw [hwcoeff, norm_one, hwnormeq]
    · intro μ hμ
      by_contra hnot
      have hlt : ν ≺[m] μ := lt_of_not_ge hnot
      have hne : μ ≠ ν := by
        intro heq
        subst μ
        exact (lt_irrefl _ hlt)
      have hzero := hwhigh μ hne (single_zero_le_of_lex_lt hlt)
      rw [hzero, norm_zero, hwnormeq] at hμ
      norm_num at hμ
  have hqne : q ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hqg
    exact hwne hqg.symm
  have hqdeg : leadingDegree m q = 0 := by
    have hmul := leadingDegree_mul m hqne hg
    rw [hqg, hwdeg, hgd] at hmul
    apply add_right_cancel (b := ν)
    simpa [ν] using hmul.symm
  have hqunit : IsUnit q := isUnit_of_leadingDegree_eq_zero m hqne hqdeg
  let e : TateAlgebra K (Fin (n + 1)) := ↑hqunit.unit⁻¹
  refine ⟨e, w, hqunit.unit⁻¹.isUnit, ⟨hwnorm, ?_, ?_⟩, ?_⟩
  · simpa [ν] using hwcoeff
  · simpa [ν] using hwhigh
  · rw [← hqg]
    dsimp only [e]
    rw [← mul_assoc]
    have hinv : (↑hqunit.unit⁻¹ : TateAlgebra K (Fin (n + 1))) * q = 1 := by
      calc
        (↑hqunit.unit⁻¹ : TateAlgebra K (Fin (n + 1))) * q =
            ↑hqunit.unit⁻¹ * ↑hqunit.unit :=
          congrArg (fun z : TateAlgebra K (Fin (n + 1)) ↦ ↑hqunit.unit⁻¹ * z)
            hqunit.unit_spec.symm
        _ = 1 := by simp
    rw [hinv, one_mul]

end TateAlgebra

end Rigid
