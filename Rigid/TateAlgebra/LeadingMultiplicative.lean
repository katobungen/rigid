import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.Multiplicative
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finsupp.Antidiagonal

set_option linter.style.header false

/-!
# Multiplicative leading terms in Tate algebras

The leading exponent selected by a monomial order is additive under multiplication.  We also
record the resulting unit criterion: a nonzero finite-variable Tate series whose leading exponent
is zero is invertible.  These are the algebraic inputs needed to pass from Weierstrass division to
Weierstrass preparation.
-/

open scoped MonomialOrder

universe u v

namespace Rigid

namespace TateAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {ι : Type v}

private theorem dominant_leading_pair [DecidableEq ι] (m : MonomialOrder ι)
    {f g : TateAlgebra K ι} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∀ p ∈ Finset.antidiagonal (leadingDegree m f + leadingDegree m g),
      p ≠ (leadingDegree m f, leadingDegree m g) →
      ‖MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1‖ <
        ‖MvPowerSeries.coeff (leadingDegree m f) f.1‖ *
          ‖MvPowerSeries.coeff (leadingDegree m g) g.1‖ := by
  classical
  intro p hp hpair
  have hpadd : p.1 + p.2 = leadingDegree m f + leadingDegree m g :=
    Finset.mem_antidiagonal.mp hp
  have hsum := congrArg m.toSyn hpadd
  simp only [map_add] at hsum
  rw [_root_.norm_mul,
    show ‖MvPowerSeries.coeff (leadingDegree m f) f.1‖ = ‖f‖ from
      norm_leadingCoeff m hf,
    show ‖MvPowerSeries.coeff (leadingDegree m g) g.1‖ = ‖g‖ from
      norm_leadingCoeff m hg]
  rcases lt_trichotomy (m.toSyn (leadingDegree m f)) (m.toSyn p.1) with hfi | heq | hif
  · have hflt : ‖MvPowerSeries.coeff p.1 f.1‖ < ‖f‖ :=
      norm_coeff_lt_of_leadingDegree_lt m hf hfi
    calc
      ‖MvPowerSeries.coeff p.1 f.1‖ * ‖MvPowerSeries.coeff p.2 g.1‖ ≤
          ‖MvPowerSeries.coeff p.1 f.1‖ * ‖g‖ :=
        mul_le_mul_of_nonneg_left (norm_coeff_le_norm K ι g p.2) (norm_nonneg _)
      _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_right hflt (norm_pos_iff.mpr hg)
  · exfalso
    apply hpair
    have hp1 : p.1 = leadingDegree m f := m.toSyn.injective heq.symm
    have hp2 : p.2 = leadingDegree m g := by
      apply add_left_cancel (a := leadingDegree m f)
      simpa only [hp1] using hpadd
    exact Prod.ext hp1 hp2
  · have hgj : m.toSyn (leadingDegree m g) < m.toSyn p.2 := by
      by_contra h
      have hp2le : m.toSyn p.2 ≤ m.toSyn (leadingDegree m g) := le_of_not_gt h
      have hlt := add_lt_add_of_lt_of_le hif hp2le
      rw [hsum] at hlt
      exact lt_irrefl _ hlt
    have hglt : ‖MvPowerSeries.coeff p.2 g.1‖ < ‖g‖ :=
      norm_coeff_lt_of_leadingDegree_lt m hg hgj
    calc
      ‖MvPowerSeries.coeff p.1 f.1‖ * ‖MvPowerSeries.coeff p.2 g.1‖ ≤
          ‖f‖ * ‖MvPowerSeries.coeff p.2 g.1‖ :=
        mul_le_mul_of_nonneg_right (norm_coeff_le_norm K ι f p.1) (norm_nonneg _)
      _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_left hglt (norm_pos_iff.mpr hf)

/-- The coefficient at the sum of the two leading exponents has the product norm. -/
theorem norm_coeff_add_leadingDegree_mul (m : MonomialOrder ι)
    {f g : TateAlgebra K ι} (hf : f ≠ 0) (hg : g ≠ 0) :
    ‖MvPowerSeries.coeff (leadingDegree m f + leadingDegree m g)
        ((f * g : TateAlgebra K ι) : MvPowerSeries ι K)‖ = ‖f‖ * ‖g‖ := by
  classical
  rw [show ((f * g : TateAlgebra K ι) : MvPowerSeries ι K) = f.1 * g.1 from rfl]
  rw [MvPowerSeries.antidiagonal_dominant (fun a : K ↦ ‖a‖) f.1 g.1
    (leadingDegree m f) (leadingDegree m g) IsUltrametricDist.isNonarchimedean_norm
    (fun a b ↦ _root_.norm_mul a b) (fun a ↦ (norm_neg a).symm)
    (dominant_leading_pair m hf hg)]
  rw [_root_.norm_mul]
  simpa only [leadingCoeff] using
    congrArg₂ (· * ·) (norm_leadingCoeff m hf) (norm_leadingCoeff m hg)

/-- Leading exponents are additive under multiplication. -/
theorem leadingDegree_mul (m : MonomialOrder ι) {f g : TateAlgebra K ι}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    leadingDegree m (f * g) = leadingDegree m f + leadingDegree m g := by
  classical
  have hcoeff := norm_coeff_add_leadingDegree_mul m hf hg
  have hfg : f * g ≠ 0 := by
    intro hzero
    have hzeroNorm : 0 = ‖f‖ * ‖g‖ := by simpa [hzero] using hcoeff
    exact (mul_pos (norm_pos_iff.mpr hf) (norm_pos_iff.mpr hg)).ne' hzeroNorm.symm
  refine leadingDegree_unique m hfg ?_ ?_
  · simpa [norm_mul_of_monomialOrder m] using hcoeff
  · intro n hn
    have hcoeffn : ‖MvPowerSeries.coeff n
        ((f * g : TateAlgebra K ι) : MvPowerSeries ι K)‖ = ‖f‖ * ‖g‖ := by
      apply le_antisymm
      · exact (norm_coeff_le_norm K ι (f * g) n).trans_eq
          (norm_mul_of_monomialOrder m f g)
      · simpa [norm_mul_of_monomialOrder m] using hn
    rw [show ((f * g : TateAlgebra K ι) : MvPowerSeries ι K) = f.1 * g.1 from rfl,
      MvPowerSeries.coeff_mul] at hcoeffn
    have hanti : (Finset.antidiagonal n).Nonempty :=
      ⟨(0, n), Finset.mem_antidiagonal.mpr (zero_add n)⟩
    obtain ⟨p, hp, hpsum⟩ :=
      IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hanti
        (fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦
          MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1)
    have hpterm : ‖MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1‖ =
        ‖f‖ * ‖g‖ := by
      apply le_antisymm
      · rw [_root_.norm_mul]
        exact mul_le_mul (norm_coeff_le_norm K ι f p.1) (norm_coeff_le_norm K ι g p.2)
          (norm_nonneg _) (norm_nonneg _)
      · rw [hcoeffn] at hpsum
        exact hpsum
    have hp1 : ‖MvPowerSeries.coeff p.1 f.1‖ = ‖f‖ := by
      apply le_antisymm (norm_coeff_le_norm K ι f p.1)
      by_contra hlt
      have hlt' : ‖MvPowerSeries.coeff p.1 f.1‖ < ‖f‖ := lt_of_not_ge hlt
      have := mul_lt_mul_of_pos_right hlt' (norm_pos_iff.mpr hg)
      exact (not_le_of_gt this) (by
        rw [← hpterm, _root_.norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_coeff_le_norm K ι g p.2) (norm_nonneg _))
    have hp2 : ‖MvPowerSeries.coeff p.2 g.1‖ = ‖g‖ := by
      apply le_antisymm (norm_coeff_le_norm K ι g p.2)
      by_contra hlt
      have hlt' : ‖MvPowerSeries.coeff p.2 g.1‖ < ‖g‖ := lt_of_not_ge hlt
      have := mul_lt_mul_of_pos_left hlt' (norm_pos_iff.mpr hf)
      exact (not_le_of_gt this) (by
        rw [← hpterm, _root_.norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_coeff_le_norm K ι f p.1) (norm_nonneg _))
    have hp1le : m.toSyn p.1 ≤ m.toSyn (leadingDegree m f) :=
      le_leadingDegree m hf hp1.ge
    have hp2le : m.toSyn p.2 ≤ m.toSyn (leadingDegree m g) :=
      le_leadingDegree m hg hp2.ge
    have hpadd : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    calc
      m.toSyn n = m.toSyn (p.1 + p.2) := congrArg m.toSyn hpadd.symm
      _ = m.toSyn p.1 + m.toSyn p.2 := map_add m.toSyn p.1 p.2
      _ ≤ m.toSyn (leadingDegree m f) + m.toSyn (leadingDegree m g) :=
        add_le_add hp1le hp2le
      _ = m.toSyn (leadingDegree m f + leadingDegree m g) :=
        (map_add m.toSyn _ _).symm

/-- A nonzero finite-variable Tate series whose leading exponent is zero is a unit. -/
theorem isUnit_of_leadingDegree_eq_zero [Finite ι] [CompleteSpace K]
    (m : MonomialOrder ι) {f : TateAlgebra K ι} (hf : f ≠ 0)
    (hdeg : leadingDegree m f = 0) : IsUnit f := by
  classical
  let a : K := MvPowerSeries.coeff 0 f.1
  have haNorm : ‖a‖ = ‖f‖ := by
    change ‖MvPowerSeries.coeff 0 f.1‖ = ‖f‖
    rw [← hdeg]
    exact norm_leadingCoeff m hf
  have ha : a ≠ 0 := by
    rw [← norm_ne_zero_iff, haNorm]
    exact norm_ne_zero_iff.mpr hf
  let c : TateAlgebra K ι := C K ι a
  have hcNorm : ‖c‖ = ‖f‖ := by simp [c, haNorm]
  have hsupport : leadingSupport f = {0} := by
    ext n
    simp only [Finset.mem_singleton]
    constructor
    · intro hn
      have hnle := le_leadingDegree m hf ((mem_leadingSupport hf).mp hn)
      rw [hdeg] at hnle
      have hzero : m.toSyn 0 ≤ m.toSyn n := by
        rw [map_zero]
        exact m.zero_le (m.toSyn n)
      exact m.toSyn.injective (le_antisymm hnle hzero)
    · intro hn
      subst n
      exact (mem_leadingSupport hf).mpr (by rw [haNorm])
  have hleading : leadingPart f = c := by
    rw [leadingPart, hsupport]
    simp only [Finset.sum_singleton, c, a]
    apply Subtype.ext
    exact MvPowerSeries.monomial_zero_eq_C_apply _
  have hsmall : ‖f - c‖ < ‖c‖ := by
    rw [hcNorm, ← hleading]
    exact norm_sub_leadingPart_lt hf
  let x : TateAlgebra K ι := -(C K ι a⁻¹ * (f - c))
  have hx : ‖x‖ < 1 := by
    dsimp only [x]
    rw [norm_neg, norm_mul, norm_C, norm_inv]
    rw [haNorm, inv_mul_lt_one₀ (norm_pos_iff.mpr hf)]
    rwa [hcNorm] at hsmall
  have hfactor : f = c * (1 - x) := by
    dsimp only [x]
    rw [sub_neg_eq_add, mul_add, mul_one]
    dsimp only [c]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
    abel
  rw [hfactor]
  exact IsUnit.mul (IsUnit.map (C K ι) (isUnit_iff_ne_zero.mpr ha))
    (isUnit_one_sub_of_norm_lt_one hx)

end TateAlgebra

end Rigid
