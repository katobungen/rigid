import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.Berkovich.RelativeSpectrum

set_option linter.style.header false

/-!
# Basic lemmas on power-bounded elements

This file records reusable closure properties of `Rigid.IsPowerBounded`. They are used by the
Berkovich spectral seminorm foundations and by future affinoid power-bounded arguments.
-/

universe u v w

open scoped BigOperators

namespace Rigid

section SeminormedRing

variable {B : Type u} [SeminormedRing B]

theorem IsPowerBounded.pow {x : B} (hx : IsPowerBounded x) (n : ℕ) :
    IsPowerBounded (x ^ n) := by
  rcases hx with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  rintro _ ⟨m, rfl⟩
  simpa [pow_mul] using hM ⟨n * m, rfl⟩

/-- Power-boundedness is unchanged by negation. -/
theorem IsPowerBounded.neg {x : B} (hx : IsPowerBounded x) : IsPowerBounded (-x) := by
  rcases hx with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(-x) ^ n‖ ≤ M
  rw [neg_pow]
  rcases neg_one_pow_eq_or B n with hn | hn
  · rw [hn, one_mul]
    exact hM ⟨n, rfl⟩
  · rw [hn, neg_one_mul, norm_neg]
    exact hM ⟨n, rfl⟩

end SeminormedRing

section SeminormedCommRing

variable {B : Type u} [SeminormedCommRing B]

theorem IsPowerBounded.mul {x y : B} (hx : IsPowerBounded x) (hy : IsPowerBounded y) :
    IsPowerBounded (x * y) := by
  rcases hx with ⟨Mx, hx⟩
  rcases hy with ⟨My, hy⟩
  refine ⟨max ‖(1 : B)‖ (Mx * My), ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    ‖(x * y) ^ n‖ = ‖x ^ n * y ^ n‖ := by rw [mul_pow]
    _ ≤ ‖x ^ n‖ * ‖y ^ n‖ := norm_mul_le _ _
    _ ≤ Mx * My := by
      nlinarith [hx ⟨n, rfl⟩, hy ⟨n, rfl⟩, norm_nonneg (x ^ n), norm_nonneg (y ^ n)]
    _ ≤ max ‖(1 : B)‖ (Mx * My) := le_max_right _ _

end SeminormedCommRing

section Ultrametric

variable {B : Type u} [SeminormedCommRing B] [IsUltrametricDist B]

/-- In a nonarchimedean seminormed ring, every natural number has norm at most `‖1‖`. -/
theorem norm_natCast_le_norm_one (n : ℕ) : ‖(n : B)‖ ≤ ‖(1 : B)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max (n : B) 1).trans (max_le ih le_rfl)

omit [IsUltrametricDist B] in
/-- Nilpotent elements are power-bounded because only finitely many powers are nonzero. -/
theorem isPowerBounded_of_isNilpotent {x : B} (hx : IsNilpotent x) : IsPowerBounded x := by
  rcases hx with ⟨n, hn⟩
  refine
    (Set.Finite.insert 0 (Set.finite_range fun m : Fin n ↦ ‖x ^ (m : ℕ)‖)).bddAbove.mono ?_
  rintro _ ⟨m, rfl⟩
  by_cases hm : m < n
  · exact Set.mem_insert_of_mem _ ⟨⟨m, hm⟩, rfl⟩
  · have hnm : n ≤ m := Nat.le_of_not_lt hm
    have hpow : x ^ m = 0 := by
      rw [← pow_mul_pow_sub x hnm, hn, zero_mul]
    simp [hpow]

omit [IsUltrametricDist B] in
@[simp]
theorem IsNilpotent.isPowerBounded {x : B} (hx : IsNilpotent x) : IsPowerBounded x :=
  isPowerBounded_of_isNilpotent hx

/-- Natural numbers are power-bounded in a nonarchimedean seminormed ring. -/
theorem isPowerBounded_natCast (n : ℕ) : IsPowerBounded (n : B) := by
  refine ⟨‖(1 : B)‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  simpa [Nat.cast_pow] using norm_natCast_le_norm_one (B := B) (n := n ^ m)

theorem IsPowerBounded.add {x y : B} (hx : IsPowerBounded x) (hy : IsPowerBounded y) :
    IsPowerBounded (x + y) := by
  rcases hx with ⟨Mx, hx⟩
  rcases hy with ⟨My, hy⟩
  have hMx0 : 0 ≤ Mx := (norm_nonneg (1 : B)).trans (hx ⟨0, by simp⟩)
  have hMy0 : 0 ≤ My := (norm_nonneg (1 : B)).trans (hy ⟨0, by simp⟩)
  refine ⟨max ‖(1 : B)‖ (‖(1 : B)‖ * (Mx * My)), ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(x + y) ^ n‖ ≤ max ‖(1 : B)‖ (‖(1 : B)‖ * (Mx * My))
  rw [add_pow]
  refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (show 0 ≤ ‖(1 : B)‖ * (Mx * My) by positivity) fun m hm ↦ ?_).trans
    (le_max_right _ _)
  calc
    ‖x ^ m * y ^ (n - m) * (n.choose m : B)‖
        ≤ ‖x ^ m * y ^ (n - m)‖ * ‖(n.choose m : B)‖ := norm_mul_le _ _
    _ ≤ (‖x ^ m‖ * ‖y ^ (n - m)‖) * ‖(n.choose m : B)‖ := by
      gcongr
      exact norm_mul_le _ _
    _ = ‖(n.choose m : B)‖ * (‖x ^ m‖ * ‖y ^ (n - m)‖) := by ring
    _ ≤ ‖(1 : B)‖ * (Mx * My) := by
      gcongr
      · exact norm_natCast_le_norm_one (B := B) (n := n.choose m)
      · exact hx ⟨m, rfl⟩
      · exact hy ⟨n - m, rfl⟩

/-- The power-bounded elements form a subring. -/
def IsPowerBounded.subring (B : Type u) [SeminormedCommRing B] [IsUltrametricDist B] :
    Subring B where
  carrier := {x | IsPowerBounded x}
  zero_mem' := isPowerBounded_zero
  one_mem' := isPowerBounded_one
  add_mem' := IsPowerBounded.add
  neg_mem' := IsPowerBounded.neg
  mul_mem' := IsPowerBounded.mul

end Ultrametric

section Integral

variable {B : Type u} [NormedCommRing B]

/-- An element integral over a uniformly bounded coefficient subring is power-bounded. -/
theorem IsPowerBounded.of_isIntegral_over_bounded_subring (S : Subring B)
    (hS : BddAbove (Set.range fun s : S ↦ ‖(s : B)‖)) {x : B} (hx : IsIntegral S x) :
    IsPowerBounded x := by
  obtain ⟨C, hC⟩ := hS
  obtain ⟨d, v, hv⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hx.fg_adjoin_singleton
  let D : ℝ := ∑ i, ‖v i‖
  refine ⟨max 0 C * D, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hxpow : x ^ n ∈ Algebra.adjoin S {x} :=
    (Algebra.adjoin S {x}).pow_mem (Algebra.subset_adjoin (Set.mem_singleton x)) n
  have hxspan : x ^ n ∈ Submodule.span S (Set.range v) := by
    rw [hv]
    exact hxpow
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hxspan
  change ‖x ^ n‖ ≤ max 0 C * D
  rw [← hc]
  calc
    ‖∑ i, c i • v i‖ ≤ ∑ i, ‖c i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, max 0 C * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(c i : B) * v i‖ ≤ max 0 C * ‖v i‖
      exact (norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_right
        ((hC ⟨c i, rfl⟩).trans (le_max_right 0 C)) (norm_nonneg _)
    _ = max 0 C * D := by rw [Finset.mul_sum]

end Integral

section ContinuousAlgHom

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
variable {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- Continuous algebra homomorphisms send power-bounded elements to power-bounded elements. -/
theorem IsPowerBounded.map_continuousAlgHom (φ : ContinuousAlgHom K A B) {x : A}
    (hx : IsPowerBounded x) : IsPowerBounded (φ x) := by
  rcases hx with ⟨M, hM⟩
  obtain ⟨C, hCpos, hC⟩ := SemilinearMapClass.bound_of_continuous φ φ.continuous
  refine ⟨max ‖(1 : B)‖ (C * M), ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    ‖(φ x) ^ n‖ = ‖φ (x ^ n)‖ := by rw [← map_pow]
    _ ≤ C * ‖x ^ n‖ := hC _
    _ ≤ C * M := mul_le_mul_of_nonneg_left (hM ⟨n, rfl⟩) hCpos.le
    _ ≤ max ‖(1 : B)‖ (C * M) := le_max_right _ _

end ContinuousAlgHom

section BerkovichSpectrumOver

variable {B : Type u} [NormedCommRing B]

/-- A power-bounded element has value at most one at every relative Berkovich point. -/
theorem IsPowerBounded.apply_le_one
    (K : Type v) [NormedField K] [Algebra K B]
    (x : BerkovichSpectrumOver K B) {b : B} (hb : IsPowerBounded b) : x b ≤ 1 := by
  rcases hb with ⟨C, hC⟩
  by_contra h
  have hxb : 1 < x b := lt_of_not_ge h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hxb
  apply not_le_of_gt hn
  calc
    x b ^ n = x (b ^ n) := (map_pow x.toBerkovichSpectrum.seminorm b n).symm
    _ ≤ ‖b ^ n‖ := BerkovichSpectrumOver.le_norm K B x _
    _ ≤ C := hC ⟨n, rfl⟩

end BerkovichSpectrumOver

end Rigid
