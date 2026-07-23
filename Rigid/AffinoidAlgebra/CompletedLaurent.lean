import Rigid.TateAlgebra.RelativeUniversalProperty
import Mathlib.Algebra.Exact.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The completed Laurent coefficient sequence

The middle row in BGR 8.2.3/1 is the completed version of the elementary Laurent-polynomial
sequence.  A restricted Laurent series is a family `(aₙ)ₙ∈ℤ` tending to zero along the cofinite
filter.  Its nonnegative and negative coefficients give two one-variable Tate series, and the only
ambiguity is the constant coefficient.

This file proves that coefficient statement over an arbitrary nonarchimedean Banach algebra.  It
is the analytic input used in the Laurent-cover diagram before passing to the closed ideals
`(T - f)` and `(1 - fS)`.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- Restricted Laurent coefficient families, viewed as a `K`-submodule of all `ℤ`-indexed
families. -/
def seriesSubmodule : Submodule K (ℤ → A) where
  carrier := {a | Tendsto a cofinite (𝓝 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' := by
    intro a b ha hb
    change Tendsto (fun n ↦ a n + b n) cofinite (𝓝 0)
    simpa only [add_zero] using ha.add hb
  smul_mem' := by
    intro c a ha
    change Tendsto (fun n ↦ c • a n) cofinite (𝓝 0)
    simpa only [smul_zero] using
      (tendsto_const_nhds.smul ha : Tendsto (fun n ↦ c • a n) cofinite (𝓝 (c • 0)))

/-- The additive `K`-module of restricted Laurent series. -/
abbrev Series := seriesSubmodule K A

/-- The exponent supported at the unique variable of a one-variable Tate algebra. -/
noncomputable def oneExponent (n : ℕ) : Fin 1 →₀ ℕ :=
  Finsupp.single 0 n

private theorem oneExponent_injective : Function.Injective (oneExponent : ℕ → Fin 1 →₀ ℕ) := by
  intro m n h
  have h0 := congrArg (fun e : Fin 1 →₀ ℕ ↦ e 0) h
  simpa [oneExponent] using h0

private theorem exponent_eq_oneExponent (e : Fin 1 →₀ ℕ) :
    e = oneExponent (e 0) := by
  apply Finsupp.ext
  intro i
  rw [Fin.eq_zero i]
  simp [oneExponent]

private theorem exponentValue_injective :
    Function.Injective (fun e : Fin 1 →₀ ℕ ↦ e 0) := by
  intro e e' h
  rw [exponent_eq_oneExponent e, exponent_eq_oneExponent e']
  exact congrArg oneExponent h

/-- The coefficient sequence of a one-variable Tate series tends to zero. -/
theorem tendsto_oneVariable_coeff (p : TateAlgebra A (Fin 1)) :
    Tendsto (fun n ↦ TateAlgebra.coeff A (Fin 1) (oneExponent n) p)
      cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact (tendsto_norm_coeff_zero A (Fin 1) p).comp
    oneExponent_injective.tendsto_cofinite

/-- Build a one-variable Tate series from a coefficient family tending to zero. -/
noncomputable def ofCoefficients (a : ℕ → A) (ha : Tendsto a cofinite (𝓝 0)) :
    TateAlgebra A (Fin 1) :=
  ⟨fun e ↦ a (e 0), by
    change Tendsto (fun e : Fin 1 →₀ ℕ ↦
      ‖MvPowerSeries.coeff e (fun e : Fin 1 →₀ ℕ ↦ a (e 0) : MvPowerSeries (Fin 1) A)‖ *
        e.prod fun _ n ↦ (1 : ℝ) ^ n) cofinite (𝓝 0)
    simp only [MvPowerSeries.coeff_apply, one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
    exact (tendsto_zero_iff_norm_tendsto_zero.mp ha).comp
      exponentValue_injective.tendsto_cofinite⟩

@[simp]
theorem coeff_ofCoefficients (a : ℕ → A) (ha : Tendsto a cofinite (𝓝 0)) (n : ℕ) :
    TateAlgebra.coeff A (Fin 1) (oneExponent n) (ofCoefficients A a ha) = a n := by
  simp only [TateAlgebra.coeff_apply, ofCoefficients, MvPowerSeries.coeff_apply,
    oneExponent, Finsupp.single_eq_same]

private theorem tendsto_nonnegativeExtension
    (a : ℕ → A) (ha : Tendsto a cofinite (𝓝 0)) :
    Tendsto (fun z : ℤ ↦ if 0 ≤ z then a z.toNat else 0) cofinite (𝓝 0) := by
  rw [tendsto_def]
  intro s hs
  have h0 : (0 : A) ∈ s := mem_of_mem_nhds hs
  have ha' : {n | a n ∈ s} ∈ (cofinite : Filter ℕ) := ha hs
  rw [mem_cofinite] at ha' ⊢
  have hbad : Set.Finite {n : ℕ | a n ∉ s} := by
    simpa only [Set.compl_setOf] using ha'
  let bad : Set ℤ := {z | (if 0 ≤ z then a z.toNat else 0) ∉ s}
  change bad.Finite
  apply Set.Finite.of_finite_image
  · exact hbad.subset (by
      rintro n ⟨z, hz, rfl⟩
      change (if 0 ≤ z then a z.toNat else 0) ∉ s at hz
      by_cases hz0 : 0 ≤ z
      · simpa [hz0] using hz
      · exact (hz (by simpa [hz0] using h0)).elim)
  · intro z hz w hw hzw
    have hz0 : 0 ≤ z := by
      by_contra h
      change (if 0 ≤ z then a z.toNat else 0) ∉ s at hz
      exact hz (by simpa [h] using h0)
    have hw0 : 0 ≤ w := by
      by_contra h
      change (if 0 ≤ w then a w.toNat else 0) ∉ s at hw
      exact hw (by simpa [h] using h0)
    calc
      z = (z.toNat : ℤ) := (Int.toNat_of_nonneg hz0).symm
      _ = (w.toNat : ℤ) := congrArg (fun n : ℕ ↦ (n : ℤ)) hzw
      _ = w := Int.toNat_of_nonneg hw0

/-- Embed a nonnegative restricted power series into restricted Laurent coefficients. -/
noncomputable def positive : TateAlgebra A (Fin 1) →ₗ[K] Series K A where
  toFun p :=
    ⟨fun z ↦ if 0 ≤ z then
        TateAlgebra.coeff A (Fin 1) (oneExponent z.toNat) p else 0,
      tendsto_nonnegativeExtension A _ (tendsto_oneVariable_coeff A p)⟩
  map_add' p q := by
    ext z
    by_cases hz : 0 ≤ z <;> simp [hz, TateAlgebra.coeff]
  map_smul' c p := by
    ext z
    change (if 0 ≤ z then
        TateAlgebra.coeff A (Fin 1) (oneExponent z.toNat) (c • p) else 0) =
      c • (if 0 ≤ z then
        TateAlgebra.coeff A (Fin 1) (oneExponent z.toNat) p else 0)
    by_cases hz : 0 ≤ z
    · rw [if_pos hz, if_pos hz]
      change MvPowerSeries.coeff (oneExponent z.toNat)
          ((c • p : TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A) =
        c • MvPowerSeries.coeff (oneExponent z.toNat) p.1
      simp only [Algebra.smul_def]
      change MvPowerSeries.coeff (oneExponent z.toNat)
          (MvPowerSeries.C (algebraMap K A c) * p.1) =
        algebraMap K A c * MvPowerSeries.coeff (oneExponent z.toNat) p.1
      rw [MvPowerSeries.coeff_C_mul]
    · simp [hz]

/-- Embed a nonpositive restricted power series into restricted Laurent coefficients by sending
`T` to the formal inverse Laurent variable. -/
noncomputable def negative : TateAlgebra A (Fin 1) →ₗ[K] Series K A where
  toFun p :=
    ⟨fun z ↦ (positive K A p).1 (-z),
      (positive K A p).2.comp (Equiv.neg ℤ).injective.tendsto_cofinite⟩
  map_add' p q := by
    ext z
    simp
  map_smul' c p := by
    ext z
    simp

/-- Constants embedded in both one-variable Tate algebras. -/
noncomputable def diagonal : A →ₗ[K] TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) :=
  let base := (IsScalarTower.toAlgHom K A (TateAlgebra A (Fin 1))).toLinearMap
  base.prod base

/-- Difference between the positive and negative Laurent expansions. -/
noncomputable def difference :
    TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K] Series K A :=
  (positive K A).comp (LinearMap.fst K _ _) -
    (negative K A).comp (LinearMap.snd K _ _)

@[simp]
theorem diagonal_apply (a : A) :
    diagonal K A a = (TateAlgebra.C A (Fin 1) a, TateAlgebra.C A (Fin 1) a) :=
  rfl

@[simp]
theorem difference_coeff_zero (p q : TateAlgebra A (Fin 1)) :
    (difference K A (p, q)).1 0 =
      TateAlgebra.coeff A (Fin 1) (oneExponent 0) p -
        TateAlgebra.coeff A (Fin 1) (oneExponent 0) q := by
  rfl

theorem difference_coeff_pos (p q : TateAlgebra A (Fin 1)) (n : ℕ) (hn : 0 < n) :
    (difference K A (p, q)).1 (n : ℤ) =
      TateAlgebra.coeff A (Fin 1) (oneExponent n) p := by
  simp [difference, positive, negative, hn.ne']

theorem difference_coeff_neg (p q : TateAlgebra A (Fin 1)) (n : ℕ) (hn : 0 < n) :
    (difference K A (p, q)).1 (-(n : ℤ)) =
      -TateAlgebra.coeff A (Fin 1) (oneExponent n) q := by
  simp [difference, positive, negative, hn.ne']

/-- The image of the diagonal constants is the kernel of Laurent coefficient difference. -/
theorem exact : Function.Exact (diagonal K A) (difference K A) := by
  rintro ⟨p, q⟩
  constructor
  · intro h
    let a := TateAlgebra.coeff A (Fin 1) (oneExponent 0) p
    have hzero := congrArg (fun z : Series K A ↦ z.1 0) h
    change (difference K A (p, q)).1 0 = 0 at hzero
    rw [difference_coeff_zero] at hzero
    have hp : p = TateAlgebra.C A (Fin 1) a := by
      apply TateAlgebra.ext
      intro e
      rw [exponent_eq_oneExponent e]
      by_cases he : e 0 = 0
      · rw [he]
        simp [a, oneExponent]
      · have hn : 0 < e 0 := Nat.pos_of_ne_zero he
        have hcoeff := congrArg (fun z : Series K A ↦ z.1 (e 0 : ℤ)) h
        change (difference K A (p, q)).1 (e 0 : ℤ) = 0 at hcoeff
        rw [difference_coeff_pos K A p q (e 0) hn] at hcoeff
        have hexp : oneExponent (e 0) ≠ 0 := by
          intro hexp
          have := congrArg (fun d : Fin 1 →₀ ℕ ↦ d 0) hexp
          exact he (by simpa [oneExponent] using this)
        rw [TateAlgebra.coeff_C, if_neg hexp]
        exact hcoeff
    have hq : q = TateAlgebra.C A (Fin 1) a := by
      apply TateAlgebra.ext
      intro e
      rw [exponent_eq_oneExponent e]
      by_cases he : e 0 = 0
      · rw [he]
        rw [TateAlgebra.coeff_C, if_pos (by simp [oneExponent])]
        simpa [a] using (sub_eq_zero.mp hzero).symm
      · have hn : 0 < e 0 := Nat.pos_of_ne_zero he
        have hcoeff := congrArg (fun z : Series K A ↦ z.1 (-(e 0 : ℤ))) h
        change (difference K A (p, q)).1 (-(e 0 : ℤ)) = 0 at hcoeff
        rw [difference_coeff_neg K A p q (e 0) hn] at hcoeff
        have hqzero :
            TateAlgebra.coeff A (Fin 1) (oneExponent (e 0)) q = 0 := by
          simpa using neg_eq_zero.mp hcoeff
        have hexp : oneExponent (e 0) ≠ 0 := by
          intro hexp
          have := congrArg (fun d : Fin 1 →₀ ℕ ↦ d 0) hexp
          exact he (by simpa [oneExponent] using this)
        rw [TateAlgebra.coeff_C, if_neg hexp]
        exact hqzero
    exact ⟨a, by simp [hp, hq]⟩
  · rintro ⟨a, ha⟩
    rw [← ha, diagonal_apply]
    ext z
    by_cases hz : z = 0
    · subst z
      simp [difference_coeff_zero, oneExponent]
    · by_cases hz0 : 0 < z
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hz0.le
        subst z
        have hn0 : 0 < n := by
          simpa using hz0
        rw [difference_coeff_pos K A _ _ n hn0]
        rw [TateAlgebra.coeff_C]
        simp [oneExponent, hn0.ne']
      · have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hz0) hz
        obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hzneg
        rw [hn, Int.negSucc_eq]
        convert difference_coeff_neg K A
          (TateAlgebra.C A (Fin 1) a) (TateAlgebra.C A (Fin 1) a)
          (n + 1) (Nat.succ_pos n) using 1 <;>
          simp [oneExponent]

/-- Every restricted Laurent coefficient family splits into a nonnegative and a nonpositive Tate
series. -/
theorem difference_surjective : Function.Surjective (difference K A) := by
  intro a
  let pa : ℕ → A := fun n ↦ a.1 (n : ℤ)
  have hpa : Tendsto pa cofinite (𝓝 0) :=
    a.2.comp (show Function.Injective (fun n : ℕ ↦ (n : ℤ)) by
      intro n m h
      exact Int.ofNat.inj h).tendsto_cofinite
  let qa : ℕ → A := fun n ↦ if n = 0 then 0 else -a.1 (-(n : ℤ))
  have hbase : Tendsto (fun n : ℕ ↦ -a.1 (-(n : ℤ))) cofinite (𝓝 0) := by
    have ht := a.2.neg.comp
      (show Function.Injective (fun n : ℕ ↦ -(n : ℤ)) by
        intro n m h
        exact Int.ofNat.inj (Int.neg_inj.mp h)).tendsto_cofinite
    change Tendsto (fun n : ℕ ↦ -a.1 (-(n : ℤ))) cofinite (𝓝 (-0)) at ht
    simpa only [neg_zero] using ht
  have hqa : Tendsto qa cofinite (𝓝 0) := by
    apply hbase.congr'
    filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
    have hn' : n ≠ 0 := by simpa using hn
    simp [qa, hn']
  refine ⟨(ofCoefficients A pa hpa, ofCoefficients A qa hqa), ?_⟩
  ext z
  by_cases hz : z = 0
  · subst z
    rw [difference_coeff_zero, coeff_ofCoefficients, coeff_ofCoefficients]
    simp [pa, qa]
  · by_cases hz0 : 0 < z
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hz0.le
      subst z
      have hn0 : 0 < n := by simpa using hz0
      rw [difference_coeff_pos K A _ _ n hn0]
      rw [coeff_ofCoefficients]
    · have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hz0) hz
      obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hzneg
      rw [hn, Int.negSucc_eq]
      convert difference_coeff_neg K A
        (ofCoefficients A pa hpa) (ofCoefficients A qa hqa)
        (n + 1) (Nat.succ_pos n) using 1
      · simp
      · rw [coeff_ofCoefficients]
        simp [qa]

/-- The completed Laurent coefficient sequence is short exact. -/
theorem shortExact :
    Function.Injective (diagonal K A) ∧
      Function.Exact (diagonal K A) (difference K A) ∧
      Function.Surjective (difference K A) := by
  refine ⟨?_, exact K A, difference_surjective K A⟩
  intro a b h
  have hfirst := congrArg Prod.fst h
  have hcoeff := congrArg
    (fun p : TateAlgebra A (Fin 1) ↦ TateAlgebra.coeff A (Fin 1) (oneExponent 0) p)
    hfirst
  simpa [TateAlgebra.coeff_C, oneExponent] using hcoeff

end CompletedLaurent

end Rigid
