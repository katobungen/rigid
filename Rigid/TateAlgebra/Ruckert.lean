import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Rigid.TateAlgebra.FirstVariable

set_option linter.style.header false

/-!
# Rückert properties for strict Tate algebras

This file proves the quotient comparison in Definition 4.1.13 (R3).  A monic polynomial in the
first variable and the corresponding Weierstrass element define isomorphic quotient rings.  The
proof is the algebraic form of Weierstrass finiteness in §1.9: use polynomial division on the
source and Weierstrass division on the target.
-/

open scoped MonomialOrder

universe u

namespace Rigid

namespace TateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

private theorem isWeierstrass_ne_zero {n d : ℕ}
    {w : TateAlgebra K (Fin (n + 1))} (hw : IsWeierstrassOfDegree d w) : w ≠ 0 := by
  intro h
  have hnorm := hw.norm_eq_one K
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-- The first coordinate of the leading exponent of a first-variable polynomial is at most its
polynomial degree. -/
theorem leadingDegree_zero_le_natDegree_firstVariablePolynomialMap {n : ℕ}
    {p : Polynomial (TateAlgebra K (Fin n))} (hp : p ≠ 0) :
    (leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1)))
      (firstVariablePolynomialMap K n p)) 0 ≤ p.natDegree := by
  have hmap : firstVariablePolynomialMap K n p ≠ 0 :=
    fun h ↦ hp (firstVariablePolynomialMap_injective K n (by simpa using h))
  by_contra hnot
  have hlt : p.natDegree <
      (leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1)))
        (firstVariablePolynomialMap K n p)) 0 := Nat.lt_of_not_ge hnot
  have hcoeffzero : MvPowerSeries.coeff
      (leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1)))
        (firstVariablePolynomialMap K n p))
      (firstVariablePolynomialMap K n p).1 = 0 := by
    rw [coeff_firstVariablePolynomialMap]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    rfl
  have hnorm := norm_leadingCoeff
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) hmap
  rw [leadingCoeff, hcoeffzero, norm_zero] at hnorm
  exact (norm_pos_iff.mpr hmap).ne' hnorm.symm

/-- A polynomial of degree below a Weierstrass polynomial cannot become a nonzero multiple of
that Weierstrass element in the Tate algebra. -/
theorem eq_zero_of_natDegree_lt_of_firstVariablePolynomialMap_dvd_weierstrass
    {n d : ℕ} {W r : Polynomial (TateAlgebra K (Fin n))}
    {w : TateAlgebra K (Fin (n + 1))}
    (hW : Polynomial.IsMonicOfDegree W d)
    (hw : IsWeierstrassOfDegree d w)
    (hWw : firstVariablePolynomialMap K n W = w)
    (hrdeg : r.natDegree < d)
    (hrdvd : w ∣ firstVariablePolynomialMap K n r) : r = 0 := by
  by_contra hr
  obtain ⟨q, hq⟩ := hrdvd
  have hmapr : firstVariablePolynomialMap K n r ≠ 0 :=
    fun h ↦ hr (firstVariablePolynomialMap_injective K n (by simpa using h))
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hmapr hq
  have hw0 := isWeierstrass_ne_zero K hw
  have hlead := leadingDegree_mul
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) hw0 hq0
  rw [← hWw, hWw, ← hq] at hlead
  have hfirst : d ≤
      (leadingDegree (MonomialOrder.lex : MonomialOrder (Fin (n + 1)))
        (firstVariablePolynomialMap K n r)) 0 := by
    rw [hlead, hw.leadingDegree K]
    simp
  have hupper := leadingDegree_zero_le_natDegree_firstVariablePolynomialMap K hr
  omega

/-- The map to the quotient by a Weierstrass element. -/
noncomputable def weierstrassQuotientMap {n : ℕ}
    (w : TateAlgebra K (Fin (n + 1))) :
    Polynomial (TateAlgebra K (Fin n)) →+*
      TateAlgebra K (Fin (n + 1)) ⧸ Ideal.span ({w} : Set (TateAlgebra K (Fin (n + 1)))) :=
  (Ideal.Quotient.mk _).comp (firstVariablePolynomialMap K n)

theorem ker_weierstrassQuotientMap {n d : ℕ}
    {W : Polynomial (TateAlgebra K (Fin n))}
    {w : TateAlgebra K (Fin (n + 1))}
    (hW : Polynomial.IsMonicOfDegree W d)
    (hw : IsWeierstrassOfDegree d w)
    (hWw : firstVariablePolynomialMap K n W = w) :
    RingHom.ker (weierstrassQuotientMap K w) = Ideal.span ({W} : Set _) := by
  ext p
  constructor
  · intro hp
    rw [RingHom.mem_ker] at hp
    change Ideal.Quotient.mk (Ideal.span ({w} : Set _))
      (firstVariablePolynomialMap K n p) = 0 at hp
    have hpdiv : w ∣ firstVariablePolynomialMap K n p :=
      (Ideal.Quotient.eq_zero_iff_dvd w _).mp hp
    let r := p %ₘ W
    let s := p /ₘ W
    have hdecomp : r + W * s = p := Polynomial.modByMonic_add_div p W
    have hrdiv : w ∣ firstVariablePolynomialMap K n r := by
      obtain ⟨q, hq⟩ := hpdiv
      refine ⟨q - firstVariablePolynomialMap K n s, ?_⟩
      have hmapdecomp := congrArg (firstVariablePolynomialMap K n) hdecomp
      simp only [map_add, map_mul] at hmapdecomp
      rw [hWw] at hmapdecomp
      rw [hq] at hmapdecomp
      calc
        firstVariablePolynomialMap K n r =
            w * q - w * firstVariablePolynomialMap K n s := by
          rw [← hmapdecomp]
          abel
        _ = w * (q - firstVariablePolynomialMap K n s) := by ring
    have hrzero : r = 0 := by
      by_cases hWone : W = 1
      · simp [r, hWone]
      · apply eq_zero_of_natDegree_lt_of_firstVariablePolynomialMap_dvd_weierstrass
          K hW hw hWw
        · dsimp only [r]
          simpa [hW.natDegree_eq] using
            Polynomial.natDegree_modByMonic_lt p hW.monic hWone
        · exact hrdiv
    rw [Ideal.mem_span_singleton]
    refine ⟨s, ?_⟩
    rw [← hdecomp, hrzero, zero_add]
  · intro hp
    rw [Ideal.mem_span_singleton] at hp
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk (Ideal.span ({w} : Set _))
      (firstVariablePolynomialMap K n p) = 0
    apply (Ideal.Quotient.eq_zero_iff_dvd w _).mpr
    rw [← hWw]
    exact map_dvd (firstVariablePolynomialMap K n) hp

theorem weierstrassQuotientMap_surjective {n d : ℕ}
    {w : TateAlgebra K (Fin (n + 1))} (hw : IsWeierstrassOfDegree d w) :
    Function.Surjective (weierstrassQuotientMap K w) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hw0 := isWeierstrass_ne_zero K hw
  obtain ⟨q, r, hf, hr⟩ :=
    exists_quotient_remainder_of_leadingDegree_eq_single_zero w hw0
      (hw.leadingDegree K) f
  let p := toFirstVariablePolynomial K n d r
  have hpr : firstVariablePolynomialMap K n p = r :=
    firstVariablePolynomialMap_toFirstVariablePolynomial K r hr
  refine ⟨p, ?_⟩
  change Ideal.Quotient.mk (Ideal.span ({w} : Set _))
      (firstVariablePolynomialMap K n p) =
    Ideal.Quotient.mk (Ideal.span ({w} : Set _)) f
  rw [hpr, hf]
  simp only [map_add, map_mul, Ideal.Quotient.mk_singleton_self, mul_zero, zero_add]

/-- Rückert's quotient comparison (Definition 4.1.13, R3). -/
noncomputable def weierstrassQuotientEquiv {n d : ℕ}
    {W : Polynomial (TateAlgebra K (Fin n))}
    {w : TateAlgebra K (Fin (n + 1))}
    (hW : Polynomial.IsMonicOfDegree W d)
    (hw : IsWeierstrassOfDegree d w)
    (hWw : firstVariablePolynomialMap K n W = w) :
    (Polynomial (TateAlgebra K (Fin n)) ⧸ Ideal.span ({W} : Set _)) ≃+*
      (TateAlgebra K (Fin (n + 1)) ⧸ Ideal.span ({w} : Set _)) :=
  (Ideal.quotEquivOfEq (ker_weierstrassQuotientMap K hW hw hWw).symm).trans
    ((weierstrassQuotientMap K w).quotientKerEquivOfSurjective
      (weierstrassQuotientMap_surjective K hw))

/-- Prime monic polynomials remain prime after evaluation in the first Tate variable. -/
theorem prime_firstVariablePolynomialMap_of_prime {n d : ℕ}
    {W : Polynomial (TateAlgebra K (Fin n))}
    {w : TateAlgebra K (Fin (n + 1))}
    (hW : Polynomial.IsMonicOfDegree W d)
    (hw : IsWeierstrassOfDegree d w)
    (hWw : firstVariablePolynomialMap K n W = w)
    (hprime : Prime W) : Prime w := by
  have hw0 := isWeierstrass_ne_zero K hw
  rw [← Ideal.span_singleton_prime hw0]
  rw [Ideal.isPrime_iff]
  let φ := weierstrassQuotientMap K w
  have hker : RingHom.ker φ = Ideal.span ({W} : Set _) :=
    ker_weierstrassQuotientMap K hW hw hWw
  have hsource : (Ideal.span ({W} : Set _)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hprime
  have hsurj : Function.Surjective φ := weierstrassQuotientMap_surjective K hw
  constructor
  · intro htop
    apply hsource.ne_top
    rw [← hker, Ideal.eq_top_iff_one, RingHom.mem_ker]
    change Ideal.Quotient.mk (Ideal.span ({w} : Set _))
      (firstVariablePolynomialMap K n (1 : Polynomial (TateAlgebra K (Fin n)))) = 0
    rw [map_one, htop]
    exact Subsingleton.elim _ _
  · intro a b hab
    obtain ⟨p, hp⟩ := hsurj
      (Ideal.Quotient.mk (Ideal.span ({w} : Set _)) a)
    obtain ⟨q, hq⟩ := hsurj
      (Ideal.Quotient.mk (Ideal.span ({w} : Set _)) b)
    have hpq : p * q ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_mul, hp, hq, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hab
    rw [hker] at hpq
    rcases hsource.mem_or_mem hpq with hpW | hqW
    · left
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hp]
      exact RingHom.mem_ker.mp (hker ▸ hpW)
    · right
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hq]
      exact RingHom.mem_ker.mp (hker ▸ hqW)

end TateAlgebra

end Rigid
