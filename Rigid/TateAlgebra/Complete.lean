import Rigid.TateAlgebra.NormedRing

set_option linter.style.header false

/-!
# Completeness of a Tate algebra

The strict Tate algebra over a complete field is complete for the Gauss norm: a Cauchy sequence
converges coefficientwise, the coefficientwise limit is again a restricted power series, and the
convergence is uniform across coefficients, hence holds in the Gauss norm. This is the argument
sketched in the subsection on the Gauss norm in Kato, *Introduction to Rigid Geometry*.

Completeness does not require the variable set to be finite: each restricted series individually
has cofinitely small coefficients.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v)

/-- Extracting a coefficient is a `1`-Lipschitz map on the Tate algebra. -/
theorem lipschitzWith_coeff (n : ι →₀ ℕ) :
    LipschitzWith 1 fun f : TateAlgebra K ι ↦ MvPowerSeries.coeff n f.1 := by
  refine LipschitzWith.mk_one fun f g ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖MvPowerSeries.coeff n f.1 - MvPowerSeries.coeff n g.1‖
      = ‖MvPowerSeries.coeff n ((f - g : TateAlgebra K ι) : MvPowerSeries ι K)‖ := by
        rw [show ((f - g : TateAlgebra K ι) : MvPowerSeries ι K)
            = (f : MvPowerSeries ι K) - (g : MvPowerSeries ι K) from rfl, map_sub]
    _ ≤ ‖f - g‖ := norm_coeff_le_norm K ι (f - g) n

/-- The Tate algebra over a complete field is complete: a Cauchy sequence converges
coefficientwise, uniformly in the coefficient, and the coefficientwise limit is again a
restricted power series. The variable set need not be finite. -/
instance tateAlgebraComplete [CompleteSpace K] : CompleteSpace (TateAlgebra K ι) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  -- Each coefficient sequence is Cauchy in `K`, hence converges.
  choose c hc using fun n : ι →₀ ℕ ↦ cauchySeq_tendsto_of_complete
    (((lipschitzWith_coeff K ι n).uniformContinuous).comp_cauchySeq hu)
  -- The coefficientwise convergence is uniform in the coefficient.
  have key : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ n : ι →₀ ℕ,
      ‖MvPowerSeries.coeff n (u k).1 - c n‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun k hk n ↦ ?_⟩
    have hlim : Tendsto
        (fun l ↦ ‖MvPowerSeries.coeff n (u k).1 - MvPowerSeries.coeff n (u l).1‖)
        atTop (𝓝 ‖MvPowerSeries.coeff n (u k).1 - c n‖) :=
      ((hc n).const_sub _).norm
    refine le_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun l hl ↦ ?_⟩)
    have hkl : ‖u k - u l‖ < ε := by
      have h := hN k hk l hl
      rwa [dist_eq_norm] at h
    have hle : ‖MvPowerSeries.coeff n (u k).1 - MvPowerSeries.coeff n (u l).1‖
        ≤ ‖u k - u l‖ := by
      rw [show MvPowerSeries.coeff n (u k).1 - MvPowerSeries.coeff n (u l).1
          = MvPowerSeries.coeff n ((u k - u l : TateAlgebra K ι) : MvPowerSeries ι K) by
        rw [show ((u k - u l : TateAlgebra K ι) : MvPowerSeries ι K)
            = (u k : MvPowerSeries ι K) - (u l : MvPowerSeries ι K) from rfl, map_sub]]
      exact norm_coeff_le_norm K ι (u k - u l) n
    exact hle.trans hkl.le
  -- The limit coefficients tend to zero along the cofinite filter.
  have hc0 : Tendsto (fun n : ι →₀ ℕ ↦ c n) cofinite (𝓝 (0 : K)) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := key (ε / 2) (by linarith)
    have hsmall : ∀ᶠ n : ι →₀ ℕ in cofinite, ‖MvPowerSeries.coeff n (u N).1‖ < ε / 2 :=
      (tendsto_norm_coeff_zero K ι (u N)).eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hsmall] with n hn
    have h1 : ‖c n - MvPowerSeries.coeff n (u N).1‖ ≤ ε / 2 := by
      rw [norm_sub_rev]
      exact hN N le_rfl n
    have h2 : ‖c n‖ ≤ ‖c n - MvPowerSeries.coeff n (u N).1‖
        + ‖MvPowerSeries.coeff n (u N).1‖ := by
      simpa using norm_add_le (c n - MvPowerSeries.coeff n (u N).1)
        (MvPowerSeries.coeff n (u N).1)
    linarith
  -- Hence the coefficientwise limit is a restricted power series.
  have hmem : (fun n : ι →₀ ℕ ↦ c n) ∈
      MvPowerSeries.IsRestricted.subring (R := K) (fun _ : ι ↦ (1 : ℝ)) := by
    change Tendsto (fun n : ι →₀ ℕ ↦
      ‖MvPowerSeries.coeff n (fun m : ι →₀ ℕ ↦ c m : MvPowerSeries ι K)‖
        * n.prod fun _ e ↦ (1 : ℝ) ^ e) cofinite (𝓝 0)
    have h : (fun n : ι →₀ ℕ ↦
        ‖MvPowerSeries.coeff n (fun m : ι →₀ ℕ ↦ c m : MvPowerSeries ι K)‖
          * n.prod fun _ e ↦ (1 : ℝ) ^ e) = fun n : ι →₀ ℕ ↦ ‖c n‖ := by
      funext n
      rw [MvPowerSeries.coeff_apply]
      simp [Finsupp.prod]
    rw [h]
    exact tendsto_zero_iff_norm_tendsto_zero.mp hc0
  -- The Cauchy sequence converges to the coefficientwise limit in the Gauss norm.
  refine ⟨⟨fun n ↦ c n, hmem⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := key (ε / 2) (by linarith)
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [dist_eq_norm]
  have hle : ‖u k - (⟨fun n ↦ c n, hmem⟩ : TateAlgebra K ι)‖ ≤ ε / 2 := by
    rw [norm_eq_sSup_coeff]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    dsimp only
    rw [show ((u k - (⟨fun n ↦ c n, hmem⟩ : TateAlgebra K ι) : TateAlgebra K ι)
          : MvPowerSeries ι K)
        = (u k : MvPowerSeries ι K)
          - (⟨fun m : ι →₀ ℕ ↦ c m, hmem⟩ : TateAlgebra K ι).1 from rfl,
      map_sub, MvPowerSeries.coeff_apply]
    exact hN k hk n
  linarith

end Rigid
