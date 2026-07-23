import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Banach
import Rigid.AffinoidAlgebra.RationalDatum

set_option linter.style.header false

/-!
# Basic lemmas on power-bounded elements

This file records reusable closure properties of `Rigid.IsPowerBounded`. They are used by the
Berkovich spectral seminorm foundations and by future affinoid power-bounded arguments.
-/

universe u v w

namespace Rigid

section SeminormedRing

variable {B : Type u} [SeminormedRing B]

theorem IsPowerBounded.pow {x : B} (hx : IsPowerBounded x) (n : ℕ) :
    IsPowerBounded (x ^ n) := by
  rcases hx with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  rintro _ ⟨m, rfl⟩
  simpa [pow_mul] using hM ⟨n * m, rfl⟩

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


end Ultrametric

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

end Rigid
