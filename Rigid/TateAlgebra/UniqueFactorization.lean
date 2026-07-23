import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Rigid.TateAlgebra.Domain
import Rigid.TateAlgebra.EmptyVariables
import Rigid.TateAlgebra.Noetherian
import Rigid.TateAlgebra.Ruckert
import Rigid.TateAlgebra.WeierstrassPreparation

set_option linter.style.header false

/-!
# Unique factorization in strict Tate algebras

This is the Rückert induction of Proposition 4.1.14 and Theorem 4.1.15 in the cited draft.
The induction step uses Weierstrass preparation (R2), factor closure (R1), and the quotient
comparison / prime transfer (R3).
-/

universe u

namespace Rigid

namespace TateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A monic polynomial whose first-variable image is a Weierstrass unit has degree zero. -/
theorem natDegree_eq_zero_of_isUnit_firstVariablePolynomialMap {n d : ℕ}
    {p : Polynomial (TateAlgebra K (Fin n))}
    (hp : Polynomial.IsMonicOfDegree p d)
    (hweier : IsWeierstrassOfDegree d (firstVariablePolynomialMap K n p))
    (hunit : IsUnit (firstVariablePolynomialMap K n p)) :
    p.natDegree = 0 := by
  have hpunit : IsUnit p := by
    rw [isUnit_iff_dvd_one, ← Ideal.mem_span_singleton]
    rw [← ker_weierstrassQuotientMap K hp hweier rfl, RingHom.mem_ker]
    change Ideal.Quotient.mk
      (Ideal.span ({firstVariablePolynomialMap K n p} :
        Set (TateAlgebra K (Fin (n + 1)))))
      (firstVariablePolynomialMap K n (1 : Polynomial (TateAlgebra K (Fin n)))) = 0
    rw [map_one]
    exact (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr (isUnit_iff_dvd_one.mp hunit)
  rw [hp.monic.eq_one_of_isUnit hpunit, Polynomial.natDegree_one]

/-- The Rückert induction step: adjoining one restricted variable preserves unique
factorization. -/
theorem uniqueFactorizationMonoidSucc (n : ℕ)
    [UniqueFactorizationMonoid (TateAlgebra K (Fin n))] :
    UniqueFactorizationMonoid (TateAlgebra K (Fin (n + 1))) :=
  { (IsNoetherianRing.wfDvdMonoid :
      WfDvdMonoid (TateAlgebra K (Fin (n + 1)))) with
    irreducible_iff_prime := by
      intro f
      constructor
      · intro hf
        obtain ⟨ψ, d, e, w, he, hw, hψf⟩ :=
          exists_algEquiv_isUnit_mul_isWeierstrassOfDegree f hf.ne_zero
        let W : Polynomial (TateAlgebra K (Fin n)) :=
          weierstrassPolynomial K (d := d) w
        have hW : Polynomial.IsMonicOfDegree W d :=
          isMonicOfDegree_weierstrassPolynomial K hw
        have hWw : firstVariablePolynomialMap K n W = w :=
          firstVariablePolynomialMap_weierstrassPolynomial K hw
        have hψirr : Irreducible (ψ f) :=
          (MulEquiv.irreducible_iff ψ.toRingEquiv.toMulEquiv).mpr hf
        have hwirr : Irreducible w := by
          rw [hψf] at hψirr
          exact (irreducible_isUnit_mul he).mp hψirr
        have hWirr : Irreducible W := by
          rw [hW.monic.irreducible_iff_natDegree]
          constructor
          · intro hWone
            apply hf.not_isUnit
            have hwone : w = 1 := by
              rw [← hWw, hWone, map_one]
            have hψunit : IsUnit (ψ f) := by
              rw [hψf, hwone, mul_one]
              exact he
            have hback := hψunit.map ψ.symm.toAlgHom
            simpa using hback
          · intro p q hp hq hpq
            let hpdeg : Polynomial.IsMonicOfDegree p p.natDegree := ⟨rfl, hp⟩
            let hqdeg : Polynomial.IsMonicOfDegree q q.natDegree := ⟨rfl, hq⟩
            have hdeg : p.natDegree + q.natDegree = d := by
              rw [← hp.natDegree_mul hq, hpq, hW.natDegree_eq]
            have hpqweier :
                IsWeierstrassOfDegree (p.natDegree + q.natDegree)
                  (firstVariablePolynomialMap K n (p * q)) := by
              rw [hdeg, hpq, hWw]
              exact hw
            obtain ⟨hpweier, hqweier⟩ :=
              (isWeierstrassOfDegree_mul_iff K hpdeg hqdeg).mp hpqweier
            have hfactor :
                w = firstVariablePolynomialMap K n p *
                  firstVariablePolynomialMap K n q := by
              rw [← hWw, ← map_mul, hpq]
            rcases hwirr.isUnit_or_isUnit hfactor with hpunit | hqunit
            · left
              exact natDegree_eq_zero_of_isUnit_firstVariablePolynomialMap
                K hpdeg hpweier hpunit
            · right
              exact natDegree_eq_zero_of_isUnit_firstVariablePolynomialMap
                K hqdeg hqweier hqunit
        have hWprime : Prime W :=
          UniqueFactorizationMonoid.irreducible_iff_prime.mp hWirr
        have hwprime : Prime w :=
          prime_firstVariablePolynomialMap_of_prime K hW hw hWw hWprime
        have hψprime : Prime (ψ f) := by
          rw [hψf]
          exact (prime_isUnit_mul he).mpr hwprime
        exact (MulEquiv.prime_iff ψ.toRingEquiv.toMulEquiv).mp hψprime
      · exact Prime.irreducible }

/-- Every finite-variable strict Tate algebra over the ground field is a unique factorization
monoid. -/
noncomputable instance uniqueFactorizationMonoid (n : ℕ) :
    UniqueFactorizationMonoid (TateAlgebra K (Fin n)) := by
  induction n with
  | zero =>
      exact (equivEmpty (R := K) (iota := Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
        (inferInstance : UniqueFactorizationMonoid K)
  | succ n ih =>
      letI : UniqueFactorizationMonoid (TateAlgebra K (Fin n)) := ih
      exact uniqueFactorizationMonoidSucc K n

end TateAlgebra

end Rigid
