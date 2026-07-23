import Rigid.TateAlgebra.Multiplicative

set_option linter.style.header false

/-!
# The Tate algebra is a domain

Multiplicativity of the Gauss norm immediately rules out zero divisors in a strict Tate algebra
in finitely many variables.  This elementary consequence is useful in the minimal-polynomial
step of Noether normalization.
-/

universe u v

namespace Rigid.TateAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v) [Finite ι]

noncomputable instance noZeroDivisors : NoZeroDivisors (TateAlgebra K ι) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    have hnorm : ‖f‖ * ‖g‖ = 0 := by
      rw [← norm_mul f g, hfg, norm_zero]
    exact (mul_eq_zero.mp hnorm).imp norm_eq_zero.mp norm_eq_zero.mp

noncomputable instance isDomain : IsDomain (TateAlgebra K ι) := by
  rw [isDomain_iff_noZeroDivisors_and_nontrivial]
  exact ⟨inferInstance, inferInstance⟩

end Rigid.TateAlgebra
