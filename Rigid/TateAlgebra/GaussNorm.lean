import Rigid.TateAlgebra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Real.Pointwise
import Mathlib.Topology.Order.LiminfLimsup

set_option linter.style.header false

/-!
# The Gauss norm on a Tate algebra

This file defines the Gauss norm as the supremum of the coefficient norms and establishes its
order-theoretic and algebraic properties: it is definite, ultrametric, submultiplicative, and
homogeneous with respect to scalars. The bundled normed-algebra structure is assembled in
`Rigid.TateAlgebra.NormedRing`, which is also where the `‖·‖` notation becomes available.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

variable (K : Type u) [NormedCommRing K] [IsUltrametricDist K]
variable (ι : Type v)

/-- The Gauss norm of a strict Tate series, defined as the supremum of its coefficient norms. -/
noncomputable def gaussNorm (f : TateAlgebra K ι) : ℝ :=
  sSup (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖)

/-- The coefficient norms of a Tate series tend to zero along the cofinite filter. -/
theorem tendsto_norm_coeff_zero (f : TateAlgebra K ι) :
    Tendsto (fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) cofinite (𝓝 0) := by
  have h := f.2
  change Tendsto
    (fun n : ι →₀ ℕ ↦
      ‖MvPowerSeries.coeff n f.1‖ * n.prod (fun _ e ↦ (1 : ℝ) ^ e))
    cofinite (𝓝 0) at h
  convert h using 1
  ext n
  simp [Finsupp.prod]

/-- The coefficient norms of a Tate series are bounded above. -/
theorem bddAbove_range_norm_coeff (f : TateAlgebra K ι) :
    BddAbove (Set.range fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖) :=
  (tendsto_norm_coeff_zero K ι f).bddAbove_range_of_cofinite

/-- Every coefficient norm is bounded by the Gauss norm. -/
theorem norm_coeff_le_gaussNorm (f : TateAlgebra K ι) (n : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff n f.1‖ ≤ gaussNorm K ι f :=
  le_csSup (bddAbove_range_norm_coeff K ι f) ⟨n, rfl⟩

/-- The Gauss norm is nonnegative. -/
theorem gaussNorm_nonneg (f : TateAlgebra K ι) : 0 ≤ gaussNorm K ι f :=
  (norm_nonneg (MvPowerSeries.coeff 0 f.1)).trans
    (norm_coeff_le_gaussNorm K ι f 0)

@[simp]
theorem gaussNorm_zero : gaussNorm K ι (0 : TateAlgebra K ι) = 0 := by
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    simp
  · exact gaussNorm_nonneg K ι 0

@[simp]
theorem gaussNorm_C (a : K) : gaussNorm K ι (TateAlgebra.C K ι a) = ‖a‖ := by
  classical
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    rw [TateAlgebra.coe_C]
    dsimp only
    rw [MvPowerSeries.coeff_C]
    split_ifs <;> simp
  · simpa using norm_coeff_le_gaussNorm K ι (TateAlgebra.C K ι a) 0

@[simp]
theorem gaussNorm_one [NormOneClass K] : gaussNorm K ι (1 : TateAlgebra K ι) = 1 := by
  simpa using gaussNorm_C K ι 1

@[simp]
theorem gaussNorm_tateVariable [NormOneClass K] (i : ι) :
    gaussNorm K ι (tateVariable K ι i) = 1 := by
  classical
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    rw [coe_tateVariable]
    dsimp only
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  · simpa using
      norm_coeff_le_gaussNorm K ι (tateVariable K ι i) (Finsupp.single i 1)

/-- The Gauss norm is definite. -/
theorem gaussNorm_eq_zero_iff {f : TateAlgebra K ι} : gaussNorm K ι f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ gaussNorm_zero K ι⟩
  ext n
  have h1 : ‖MvPowerSeries.coeff n f.1‖ ≤ 0 := (norm_coeff_le_gaussNorm K ι f n).trans h.le
  have h2 : MvPowerSeries.coeff n f.1 = 0 := norm_le_zero_iff.mp h1
  simp [h2]

@[simp]
theorem gaussNorm_neg (f : TateAlgebra K ι) : gaussNorm K ι (-f) = gaussNorm K ι f := by
  have h : (fun n : ι →₀ ℕ ↦
        ‖MvPowerSeries.coeff n ((-f : TateAlgebra K ι) : MvPowerSeries ι K)‖)
      = fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖ := by
    funext n
    rw [show ((-f : TateAlgebra K ι) : MvPowerSeries ι K) = -(f : MvPowerSeries ι K) from rfl,
      map_neg, norm_neg]
  unfold gaussNorm
  rw [h]

/-- The Gauss norm is ultrametric. -/
theorem gaussNorm_add_le_max (f g : TateAlgebra K ι) :
    gaussNorm K ι (f + g) ≤ max (gaussNorm K ι f) (gaussNorm K ι g) := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  dsimp only
  rw [show ((f + g : TateAlgebra K ι) : MvPowerSeries ι K)
      = (f : MvPowerSeries ι K) + (g : MvPowerSeries ι K) from rfl, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_coeff_le_gaussNorm K ι f n) (norm_coeff_le_gaussNorm K ι g n))

/-- The Gauss norm is subadditive. -/
theorem gaussNorm_add_le (f g : TateAlgebra K ι) :
    gaussNorm K ι (f + g) ≤ gaussNorm K ι f + gaussNorm K ι g :=
  (gaussNorm_add_le_max K ι f g).trans
    (max_le_add_of_nonneg (gaussNorm_nonneg K ι f) (gaussNorm_nonneg K ι g))

/-- The Gauss norm is submultiplicative.  Over a nonarchimedean field it is in fact
multiplicative, but that requires a maximal-coefficient argument and is proved later. -/
theorem gaussNorm_mul_le (f g : TateAlgebra K ι) :
    gaussNorm K ι (f * g) ≤ gaussNorm K ι f * gaussNorm K ι g := by
  classical
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  dsimp only
  rw [show ((f * g : TateAlgebra K ι) : MvPowerSeries ι K)
      = (f : MvPowerSeries ι K) * (g : MvPowerSeries ι K) from rfl, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (gaussNorm_nonneg K ι f) (gaussNorm_nonneg K ι g)) fun p _ ↦ ?_
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_coeff_le_gaussNorm K ι f p.1) (norm_coeff_le_gaussNorm K ι g p.2)
      (norm_nonneg _) (gaussNorm_nonneg K ι f))

/-- Multiplication by a coefficient is bounded for the Gauss norm. -/
theorem gaussNorm_smul_le (c : K) (f : TateAlgebra K ι) :
    gaussNorm K ι (c • f) ≤ ‖c‖ * gaussNorm K ι f := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  dsimp only
  have hcoe : ((c • f : TateAlgebra K ι) : MvPowerSeries ι K)
      = MvPowerSeries.C c * (f : MvPowerSeries ι K) := by
    rw [Algebra.smul_def, algebraMap_apply]
    rfl
  rw [hcoe, MvPowerSeries.coeff_C_mul]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_coeff_le_gaussNorm K ι f n) (norm_nonneg c))

/-- The Gauss norm is homogeneous when the coefficient norm is multiplicative. -/
theorem gaussNorm_smul [NormMulClass K] (c : K) (f : TateAlgebra K ι) :
    gaussNorm K ι (c • f) = ‖c‖ * gaussNorm K ι f := by
  have h : (fun n : ι →₀ ℕ ↦
        ‖MvPowerSeries.coeff n ((c • f : TateAlgebra K ι) : MvPowerSeries ι K)‖)
      = fun n : ι →₀ ℕ ↦ ‖c‖ * ‖MvPowerSeries.coeff n f.1‖ := by
    funext n
    have hcoe : ((c • f : TateAlgebra K ι) : MvPowerSeries ι K)
        = MvPowerSeries.C c * (f : MvPowerSeries ι K) := by
      rw [Algebra.smul_def, algebraMap_apply]
      rfl
    rw [hcoe, MvPowerSeries.coeff_C_mul, norm_mul]
  unfold gaussNorm
  rw [h]
  exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

end Rigid
