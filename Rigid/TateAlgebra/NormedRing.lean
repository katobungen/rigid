import Rigid.TateAlgebra.GaussNorm
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.MvPolynomial.Eval

set_option linter.style.header false

/-!
# The normed algebra structure on a Tate algebra

This file bundles the Gauss norm into a `NormedCommRing`, `NormedAlgebra`, and
`IsUltrametricDist` structure on the strict Tate algebra. It also provides the canonical
algebra homomorphism from polynomials and proves that its range is dense, which is the key
topological input for the universal property in `Rigid.TateAlgebra.UniversalProperty`.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

variable (K : Type u) [NormedCommRing K] [IsUltrametricDist K]
variable (ι : Type v)

/-- The Gauss norm bundled as an `AddGroupNorm`. -/
noncomputable def gaussAddGroupNorm : AddGroupNorm (TateAlgebra K ι) where
  toFun := gaussNorm K ι
  map_zero' := gaussNorm_zero K ι
  add_le' := gaussNorm_add_le K ι
  neg' := gaussNorm_neg K ι
  eq_zero_of_map_eq_zero' := fun _ h ↦ (gaussNorm_eq_zero_iff K ι).mp h

/-- The normed group structure induced by the Gauss norm.  This is only a construction
step: the registered instance is `Rigid.tateAlgebraNormedCommRing` below, so that all
topological data on the Tate algebra comes from a single instance. -/
noncomputable abbrev tateAlgebraNormedAddCommGroup : NormedAddCommGroup (TateAlgebra K ι) :=
  (gaussAddGroupNorm K ι).toNormedAddCommGroup

noncomputable instance tateAlgebraNormedCommRing : NormedCommRing (TateAlgebra K ι) :=
  { (inferInstance : CommRing (TateAlgebra K ι)), tateAlgebraNormedAddCommGroup K ι with
    norm_mul_le := fun f g ↦ by exact gaussNorm_mul_le K ι f g }

instance tateAlgebraNormOneClass [NormOneClass K] : NormOneClass (TateAlgebra K ι) :=
  ⟨by exact gaussNorm_one K ι⟩

instance tateAlgebraIsUltrametricDist : IsUltrametricDist (TateAlgebra K ι) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun f g ↦ by exact gaussNorm_add_le_max K ι f g

noncomputable instance tateAlgebraNormedAlgebra
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] (ι : Type v) :
    NormedAlgebra K (TateAlgebra K ι) where
  __ := tateAlgebraAlgebra K ι
  norm_smul_le c f := by exact le_of_eq (gaussNorm_smul K ι c f)

theorem norm_def (f : TateAlgebra K ι) : ‖f‖ = gaussNorm K ι f := rfl

/-- The Gauss norm is the supremum norm on coefficients. -/
theorem norm_eq_sSup_coeff (f : TateAlgebra K ι) :
    ‖f‖ = sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) := rfl

/-- Every coefficient norm is bounded by the Gauss norm. -/
theorem norm_coeff_le_norm (f : TateAlgebra K ι) (n : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff n f.1‖ ≤ ‖f‖ :=
  norm_coeff_le_gaussNorm K ι f n

@[simp]
theorem norm_C (a : K) : ‖TateAlgebra.C K ι a‖ = ‖a‖ :=
  gaussNorm_C K ι a

@[simp]
theorem norm_tateVariable [NormOneClass K] (i : ι) : ‖tateVariable K ι i‖ = 1 :=
  gaussNorm_tateVariable K ι i

/-- All nonnegative powers of a Tate variable have norm bounded by the norm of `1`. -/
theorem norm_tateVariable_pow_le (i : ι) (m : ℕ) :
    ‖tateVariable K ι i ^ m‖ ≤ ‖(1 : K)‖ := by
  classical
  rw [norm_eq_sSup_coeff]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  change ‖MvPowerSeries.coeff n
      ((tateVariable K ι i ^ m : TateAlgebra K ι) : MvPowerSeries ι K)‖ ≤ ‖(1 : K)‖
  rw [show ((tateVariable K ι i ^ m : TateAlgebra K ι) : MvPowerSeries ι K) =
      MvPowerSeries.X i ^ m from rfl, MvPowerSeries.coeff_X_pow]
  split_ifs
  · exact le_rfl
  · exact norm_zero.trans_le (norm_nonneg 1)

/-! ## Polynomials inside the Tate algebra -/

/-- Polynomials are restricted power series. -/
theorem isRestricted_coe_polynomial (p : MvPolynomial ι K) :
    (p : MvPowerSeries ι K)
      ∈ MvPowerSeries.IsRestricted.subring (R := K) (fun _ : ι ↦ (1 : ℝ)) := by
  refine MvPolynomial.induction_on' p (fun n a ↦ ?_) (fun p q hp hq ↦ ?_)
  · rw [MvPolynomial.coe_monomial]
    exact MvPowerSeries.isRestricted_monomial _ n a
  · rw [MvPolynomial.coe_add]
    exact add_mem hp hq

/-- The canonical algebra homomorphism from polynomials into the Tate algebra. -/
noncomputable def TateAlgebra.ofPolynomial : MvPolynomial ι K →ₐ[K] TateAlgebra K ι :=
  { MvPolynomial.coeToMvPowerSeries.ringHom.codRestrict
      (MvPowerSeries.IsRestricted.subring (fun _ : ι ↦ (1 : ℝ)))
      (isRestricted_coe_polynomial K ι) with
    commutes' := fun c ↦ Subtype.ext <| by
      simp [MvPolynomial.algebraMap_eq, MvPolynomial.coeToMvPowerSeries.ringHom_apply] }

@[simp]
theorem coe_ofPolynomial (p : MvPolynomial ι K) :
    ((TateAlgebra.ofPolynomial K ι p : TateAlgebra K ι) : MvPowerSeries ι K) = ↑p := rfl

@[simp]
theorem ofPolynomial_C (a : K) :
    TateAlgebra.ofPolynomial K ι (MvPolynomial.C a) = TateAlgebra.C K ι a :=
  Subtype.ext (MvPolynomial.coe_C a)

@[simp]
theorem ofPolynomial_X (i : ι) :
    TateAlgebra.ofPolynomial K ι (MvPolynomial.X i) = tateVariable K ι i :=
  Subtype.ext (MvPolynomial.coe_X i)

/-- The polynomial inclusion is evaluation at the Tate variables with the constant-series map on
coefficients. -/
theorem ofPolynomial_eq_eval₂ (p : MvPolynomial ι K) :
    TateAlgebra.ofPolynomial K ι p =
      MvPolynomial.eval₂ (TateAlgebra.C K ι) (tateVariable K ι) p := by
  let Φ : MvPolynomial ι K →+* TateAlgebra K ι :=
    (TateAlgebra.ofPolynomial K ι).toRingHom
  let Ψ : MvPolynomial ι K →+* TateAlgebra K ι :=
    MvPolynomial.eval₂Hom (TateAlgebra.C K ι) (tateVariable K ι)
  have h : Φ = Ψ := MvPolynomial.ringHom_ext
    (fun a ↦ by
      change TateAlgebra.ofPolynomial K ι (MvPolynomial.C a) =
        MvPolynomial.eval₂ (TateAlgebra.C K ι) (tateVariable K ι) (MvPolynomial.C a)
      rw [ofPolynomial_C, MvPolynomial.eval₂_C])
    (fun i ↦ by
      change TateAlgebra.ofPolynomial K ι (MvPolynomial.X i) =
        MvPolynomial.eval₂ (TateAlgebra.C K ι) (tateVariable K ι) (MvPolynomial.X i)
      rw [ofPolynomial_X, MvPolynomial.eval₂_X])
  exact RingHom.congr_fun h p

/-- Polynomials are dense in the Tate algebra: any Tate series is approximated by the partial
sums over the finitely many coefficients that are not yet small. -/
theorem denseRange_ofPolynomial : DenseRange (TateAlgebra.ofPolynomial K ι) := by
  classical
  rw [Metric.denseRange_iff]
  intro f ε hε
  have hev : ∀ᶠ n : ι →₀ ℕ in cofinite, ‖MvPowerSeries.coeff n f.1‖ < ε / 2 :=
    (tendsto_norm_coeff_zero K ι f).eventually (eventually_lt_nhds (by linarith))
  have hfin : {n : ι →₀ ℕ | ¬ ‖MvPowerSeries.coeff n f.1‖ < ε / 2}.Finite := by
    simpa [Filter.eventually_cofinite] using hev
  refine ⟨∑ n ∈ hfin.toFinset, MvPolynomial.monomial n (MvPowerSeries.coeff n f.1), ?_⟩
  set p : MvPolynomial ι K
    := ∑ n ∈ hfin.toFinset, MvPolynomial.monomial n (MvPowerSeries.coeff n f.1) with hp
  rw [dist_eq_norm]
  have hcoeff : ∀ n : ι →₀ ℕ,
      MvPowerSeries.coeff n
          ((TateAlgebra.ofPolynomial K ι p : TateAlgebra K ι) : MvPowerSeries ι K)
        = if n ∈ hfin.toFinset then MvPowerSeries.coeff n f.1 else 0 := by
    intro n
    rw [coe_ofPolynomial, MvPolynomial.coeff_coe, hp]
    simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  have hb : ‖f - TateAlgebra.ofPolynomial K ι p‖ ≤ ε / 2 := by
    rw [norm_eq_sSup_coeff]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [show ((f - TateAlgebra.ofPolynomial K ι p : TateAlgebra K ι) : MvPowerSeries ι K)
        = f.1 - ((TateAlgebra.ofPolynomial K ι p : TateAlgebra K ι) : MvPowerSeries ι K)
        from rfl, map_sub, hcoeff n]
    by_cases hn : n ∈ hfin.toFinset
    · simp only [hn, if_true, sub_self, norm_zero]
      linarith
    · simp only [hn, if_false, sub_zero]
      have hlt : ‖MvPowerSeries.coeff n f.1‖ < ε / 2 := by
        by_contra hcon
        exact hn (hfin.mem_toFinset.mpr hcon)
      linarith
  linarith [hb]

end Rigid
