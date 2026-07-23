import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Rigid.TateAlgebra.Basic

set_option linter.style.header false

/-!
# Tate algebras with no variables

The Tate algebra indexed by an empty type is canonically the ground ring.  In particular, over a
field it is integrally closed.  This is the base case for the Rückert/Weierstrass induction used in
§4.1 of the cited draft.
-/

universe u v

namespace Rigid

namespace TateAlgebra

variable {R : Type u} [NormedCommRing R] [IsUltrametricDist R]
variable {iota : Type v}

/-- Constant coefficient as a ring homomorphism on the Tate algebra. -/
noncomputable def constantCoeff : TateAlgebra R iota →+* R :=
  (MvPowerSeries.constantCoeff : MvPowerSeries iota R →+* R).comp
    (MvPowerSeries.IsRestricted.subring (fun _ : iota ↦ (1 : ℝ))).subtype

@[simp]
theorem constantCoeff_apply (f : TateAlgebra R iota) :
    constantCoeff f = coeff R iota 0 f := by
  change MvPowerSeries.constantCoeff (f : MvPowerSeries iota R) =
    MvPowerSeries.coeff 0 (f : MvPowerSeries iota R)
  exact (MvPowerSeries.coeff_zero_eq_constantCoeff_apply _).symm

/-- With no variables, taking the constant coefficient is a ring equivalence. -/
noncomputable def equivEmpty [IsEmpty iota] : TateAlgebra R iota ≃+* R where
  toFun := constantCoeff
  invFun := C R iota
  left_inv f := by
    apply ext
    intro n
    have hn : n = 0 := Subsingleton.elim _ _
    subst n
    simp
  right_inv r := by simp
  map_add' x y := map_add (constantCoeff) x y
  map_mul' x y := map_mul (constantCoeff) x y

@[simp]
theorem equivEmpty_apply [IsEmpty iota] (f : TateAlgebra R iota) :
    equivEmpty f = coeff R iota 0 f :=
  constantCoeff_apply f

@[simp]
theorem equivEmpty_symm_apply [IsEmpty iota] (r : R) :
    (equivEmpty (R := R) (iota := iota)).symm r = C R iota r :=
  rfl

/-- The empty-variable Tate algebra over a field is integrally closed. -/
theorem isIntegrallyClosed_of_isEmpty {K : Type u} [NormedField K] [IsUltrametricDist K]
    {sigma : Type v} [IsEmpty sigma] : IsIntegrallyClosed (TateAlgebra K sigma) :=
  IsIntegrallyClosed.of_equiv (equivEmpty (R := K) (iota := sigma)).symm

end TateAlgebra

end Rigid
