import Rigid.AffinoidAlgebra.NoetherNormalization
import Rigid.TateAlgebra.WeierstrassDivision

set_option linter.style.header false

/-!
# Weierstrass preparation after a coordinate change

This file combines the triangular coordinate change used in Noether normalization with the
norm-controlled division theorem.  It supplies Rückert axiom (R2): after an algebra automorphism,
every nonzero Tate series is a unit times a Weierstrass polynomial in the first variable.
-/

open scoped MonomialOrder

universe u

namespace Rigid

namespace TateAlgebra

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- After a triangular coordinate change, every nonzero finite Tate series is a unit times a
Weierstrass polynomial in the first variable. -/
theorem exists_algEquiv_isUnit_mul_isWeierstrassOfDegree {n : ℕ}
    (f : TateAlgebra K (Fin (n + 1))) (hf : f ≠ 0) :
    ∃ (ψ : TateAlgebra K (Fin (n + 1)) ≃ₐ[K] TateAlgebra K (Fin (n + 1)))
      (d : ℕ) (e w : TateAlgebra K (Fin (n + 1))),
      IsUnit e ∧ IsWeierstrassOfDegree d w ∧ ψ f = e * w := by
  classical
  obtain ⟨ψ, d, hψdeg⟩ := exists_algEquiv_leadingDegree_eq_single_zero K f hf
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  let a : K := leadingCoeff m (ψ f)
  have hψne : ψ f ≠ 0 := fun h ↦ hf (ψ.injective (by simpa using h))
  have ha : a ≠ 0 := leadingCoeff_ne_zero m hψne
  let g : TateAlgebra K (Fin (n + 1)) := a⁻¹ • ψ f
  have hg : g ≠ 0 := by
    intro hg0
    apply hψne
    have h := congrArg (fun z : TateAlgebra K (Fin (n + 1)) ↦ a • z) hg0
    simpa [g, smul_smul, mul_inv_cancel₀ ha] using h
  have hgdeg : leadingDegree m g = Finsupp.single 0 d := by
    change leadingDegree m (a⁻¹ • ψ f) = Finsupp.single 0 d
    rw [leadingDegree_smul m (inv_ne_zero ha), hψdeg]
  have hglc : leadingCoeff m g = 1 := by
    change leadingCoeff m (a⁻¹ • ψ f) = 1
    rw [leadingCoeff_smul m (inv_ne_zero ha)]
    exact inv_mul_cancel₀ ha
  obtain ⟨e, w, he, hw, hgw⟩ :=
    exists_isUnit_mul_isWeierstrassOfDegree_of_leadingCoeff_eq_one g hg hgdeg hglc
  let c : TateAlgebra K (Fin (n + 1)) := C K _ a
  refine ⟨ψ, d, c * e, w, IsUnit.mul (IsUnit.map (C K _) (isUnit_iff_ne_zero.mpr ha)) he,
    hw, ?_⟩
  have hag : a • g = ψ f := by
    dsimp only [g]
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [← hag, hgw, Algebra.smul_def, mul_assoc]
  rfl

end TateAlgebra

end Rigid
