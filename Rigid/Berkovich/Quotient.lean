import Mathlib.RingTheory.Valuation.Quotient
import Rigid.Berkovich.CompletedResidue

set_option linter.style.header false

/-!
# Berkovich points on quotients

A bounded multiplicative seminorm whose kernel contains an ideal factors through the corresponding
quotient.  When the ideal is closed, the quotient norm makes the descended seminorm contractive.
This is the pointwise ingredient in the minimal-prime comparison of spectral radii.
-/

open scoped NNReal

universe u v

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NontriviallyNormedField K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]

/-- A Berkovich point descends through every closed ideal contained in its kernel. -/
noncomputable def descendQuotient (x : Rigid.BerkovichSpectrumOver K A)
    (I : Ideal A) [IsClosed (I : Set A)] (hI : I ≤ x.kernel) :
    Rigid.BerkovichSpectrumOver K (A ⧸ I) where
  toBerkovichSpectrum :=
    { seminorm :=
        { toFun := fun z ↦ ((valuation x).onQuot (by
              simpa only [valuation_supp_eq_kernel] using hI) z : ℝ)
          map_zero' := by simp
          add_le' := by
            intro a b
            calc
              (((valuation x).onQuot (by
                  simpa only [valuation_supp_eq_kernel] using hI)) (a + b) : ℝ) ≤
                  max
                    (((valuation x).onQuot (by
                      simpa only [valuation_supp_eq_kernel] using hI)) a : ℝ)
                    (((valuation x).onQuot (by
                      simpa only [valuation_supp_eq_kernel] using hI)) b : ℝ) := by
                exact_mod_cast ((valuation x).onQuot (by
                  simpa only [valuation_supp_eq_kernel] using hI)).map_add a b
              _ ≤
                  (((valuation x).onQuot (by
                    simpa only [valuation_supp_eq_kernel] using hI)) a : ℝ) +
                  (((valuation x).onQuot (by
                    simpa only [valuation_supp_eq_kernel] using hI)) b : ℝ) :=
                max_le (le_add_of_nonneg_right NNReal.zero_le_coe)
                  (le_add_of_nonneg_left NNReal.zero_le_coe)
          neg' := by
            intro a
            exact_mod_cast ((valuation x).onQuot (by
              simpa only [valuation_supp_eq_kernel] using hI)).map_neg a
          map_one' := by simp
          map_mul' := by
            intro a b
            exact_mod_cast ((valuation x).onQuot (by
              simpa only [valuation_supp_eq_kernel] using hI)).map_mul a b }
      le_norm' := by
        intro z
        refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        obtain ⟨a, rfl, ha⟩ := Ideal.Quotient.norm_mk_lt z hε
        change x a ≤ ‖Ideal.Quotient.mk I a‖ + ε
        exact (le_norm K A x a).trans (le_of_lt ha) }
  map_algebraMap' := by
    intro r
    change x (algebraMap K A r) = ‖r‖
    exact map_algebraMap K A x r

@[simp]
theorem descendQuotient_apply_mk (x : Rigid.BerkovichSpectrumOver K A)
    (I : Ideal A) [IsClosed (I : Set A)] (hI : I ≤ x.kernel) (a : A) :
    descendQuotient K A x I hI (Ideal.Quotient.mk I a) = x a :=
  rfl

end Rigid.BerkovichSpectrumOver
