import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Polynomial.Laurent

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The algebraic Laurent-cover exact sequence

The coefficient-splitting step in Tate's Laurent-cover argument is already visible on the dense
polynomial subalgebras.  A Laurent polynomial splits into a polynomial in `T` and a polynomial in
`T⁻¹`; their intersection consists precisely of constants.  This file proves the resulting short
exact sequence.  The Banach-algebra proof follows the same decomposition after completing and
then descends it through the closed ideals `(T - f)` and `(1 - fT⁻¹)`, as in BGR 8.2.3/2.
-/

open Polynomial
open LaurentPolynomial
open scoped LaurentPolynomial

universe u

namespace Rigid

namespace LaurentCover

variable (R : Type u) [CommRing R]

/-- Constants embed diagonally into the two polynomial charts. -/
noncomputable def polynomialDiagonal : R →+ R[X] × R[X] where
  toFun a := (Polynomial.C a, Polynomial.C a)
  map_zero' := by simp
  map_add' a b := by simp

/-- The difference of the positive and negative polynomial expansions in the Laurent overlap. -/
noncomputable def polynomialDifference : R[X] × R[X] →+ R[T;T⁻¹] where
  toFun z := Polynomial.toLaurent z.1 - LaurentPolynomial.invert (Polynomial.toLaurent z.2)
  map_zero' := by simp
  map_add' p q := by simp; abel

private theorem positive_coeff_eq_zero_of_toLaurent_eq_invert
    {p q : R[X]} (h : Polynomial.toLaurent p = LaurentPolynomial.invert (Polynomial.toLaurent q))
    (n : ℕ) (hn : n ≠ 0) : p.coeff n = 0 := by
  have hc := congrArg (fun z : R[T;T⁻¹] ↦ z.coeff (n : ℤ)) h
  simp only [LaurentPolynomial.invert_apply, LaurentPolynomial.coeff_toLaurent] at hc
  have hleft :
      (Finsupp.mapDomain (⇑Nat.castEmbedding) p.toFinsupp.coeff) (n : ℤ) = p.coeff n := by
    exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ n
  rw [hleft] at hc
  rw [Finsupp.mapDomain_notin_range] at hc
  · exact hc
  · rintro ⟨k, hk⟩
    change (k : ℤ) = -(n : ℤ) at hk
    omega

private theorem eq_C_coeff_zero_of_toLaurent_eq_invert
    {p q : R[X]} (h : Polynomial.toLaurent p = LaurentPolynomial.invert (Polynomial.toLaurent q)) :
    p = Polynomial.C (p.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hp0 : p.coeff n = 0 :=
      positive_coeff_eq_zero_of_toLaurent_eq_invert R h n hn
    rw [hp0, Polynomial.coeff_C]
    simp [hn]

/-- The polynomial Laurent difference is onto: split a Laurent polynomial into its nonnegative
and negative powers. -/
theorem polynomialDifference_surjective :
    Function.Surjective (polynomialDifference R) := by
  intro z
  induction z using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add (polynomialDifference R) p' q'⟩
  | C_mul_T n a =>
      by_cases hn : 0 ≤ n
      · let p : R[X] := Polynomial.monomial n.toNat a
        refine ⟨(p, 0), ?_⟩
        simp [polynomialDifference, p, Polynomial.toLaurent_C_mul_T,
          Int.toNat_of_nonneg hn]
      · have hn' : n < 0 := lt_of_not_ge hn
        let q : R[X] := Polynomial.monomial (-n).toNat (-a)
        refine ⟨(0, q), ?_⟩
        simp [polynomialDifference, q, Polynomial.toLaurent_C_mul_T,
          Int.toNat_of_nonneg (Int.neg_nonneg.mpr hn'.le), sub_eq_add_neg]

/-- The image of the diagonal constants is exactly the kernel of the Laurent difference. -/
theorem polynomial_exact :
    Function.Exact (polynomialDiagonal R) (polynomialDifference R) := by
  intro z
  constructor
  · intro hz
    have heq : Polynomial.toLaurent z.1 =
        LaurentPolynomial.invert (Polynomial.toLaurent z.2) := by
      exact sub_eq_zero.mp hz
    have hp : z.1 = Polynomial.C (z.1.coeff 0) :=
      eq_C_coeff_zero_of_toLaurent_eq_invert R heq
    have heq' : Polynomial.toLaurent z.2 =
        LaurentPolynomial.invert (Polynomial.toLaurent z.1) := by
      calc
        Polynomial.toLaurent z.2 =
            LaurentPolynomial.invert (LaurentPolynomial.invert (Polynomial.toLaurent z.2)) :=
          (LaurentPolynomial.involutive_invert _).symm
        _ = LaurentPolynomial.invert (Polynomial.toLaurent z.1) :=
          (congrArg LaurentPolynomial.invert heq).symm
    have hq : z.2 = Polynomial.C (z.2.coeff 0) :=
      eq_C_coeff_zero_of_toLaurent_eq_invert R heq'
    have hcoeff : z.1.coeff 0 = z.2.coeff 0 := by
      have heqConstants := heq
      rw [hp, hq] at heqConstants
      have hzero := congrArg (fun w : R[T;T⁻¹] ↦ w.coeff 0) heqConstants
      simpa using hzero
    refine ⟨z.1.coeff 0, ?_⟩
    apply Prod.ext
    · simpa [polynomialDiagonal] using hp.symm
    · simpa [polynomialDiagonal, hcoeff] using hq.symm
  · rintro ⟨a, rfl⟩
    simp [polynomialDiagonal, polynomialDifference]

/-- The algebraic Laurent sequence is short exact. -/
theorem polynomial_shortExact :
    Function.Injective (polynomialDiagonal R) ∧
      Function.Exact (polynomialDiagonal R) (polynomialDifference R) ∧
      Function.Surjective (polynomialDifference R) := by
  refine ⟨?_, polynomial_exact R, polynomialDifference_surjective R⟩
  intro a b h
  have hfirst := congrArg Prod.fst h
  simpa [polynomialDiagonal] using Polynomial.C_injective hfirst

end LaurentCover

end Rigid
