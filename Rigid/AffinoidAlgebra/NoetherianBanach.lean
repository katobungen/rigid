import Mathlib

set_option linter.style.header false

open Filter
open scoped Topology

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K]

section

variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A] [IsNoetherianRing A]

private noncomputable def continuousLinearMapOfFiniteFree
    {M : Type v} [NormedAddCommGroup M] [Module A M] [NormedSpace K M]
    [IsScalarTower K A M] [SMulCommClass K A M] [IsBoundedSMul A M]
    {n : ℕ} (f : (Fin n → A) →ₗ[A] M) : (Fin n → A) →L[K] M := by
  let fK : (Fin n → A) →ₗ[K] M := f.restrictScalars K
  let C : ℝ := 1 + ∑ i, ‖f (Pi.single i 1)‖
  have hC : 0 ≤ C := by positivity
  have hbound (x : Fin n → A) : ‖fK x‖ ≤ C * ‖x‖ := by
    have hx : x = ∑ i, Pi.single i (x i) :=
      (LinearMap.sum_single_apply (fun _ : Fin n ↦ A) x).symm
    have hfx : fK x = ∑ i, fK (Pi.single i (x i)) := by
      calc
        fK x = fK (∑ i, Pi.single i (x i)) := congrArg fK hx
        _ = ∑ i, fK (Pi.single i (x i)) := by rw [map_sum]
    calc
      ‖fK x‖ = ‖∑ i, fK (Pi.single i (x i))‖ := congrArg norm hfx
      _ ≤
          ∑ i, ‖fK (Pi.single i (x i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖x i‖ * ‖f (Pi.single i 1)‖ := by
        gcongr with i
        have hi : Pi.single i (x i) = x i • Pi.single i 1 := by
          ext j
          by_cases hij : i = j <;> simp [hij]
        change ‖f (Pi.single i (x i))‖ ≤ _
        rw [hi, map_smul]
        exact norm_smul_le _ _
      _ ≤ ∑ i, ‖x‖ * ‖f (Pi.single i 1)‖ := by
        gcongr
        exact norm_le_pi_norm x i
      _ = ‖x‖ * (∑ i, ‖f (Pi.single i 1)‖) := by
        rw [Finset.mul_sum]
      _ = (∑ i, ‖f (Pi.single i 1)‖) * ‖x‖ := mul_comm _ _
      _ ≤ C * ‖x‖ := by
        gcongr
        exact le_add_of_nonneg_left zero_le_one
  exact fK.mkContinuous C hbound

omit [CompleteSpace K] [IsUltrametricDist K] in
include K in
theorem isClosed_ideal_of_isNoetherianRing (I : Ideal A) :
    IsClosed (I : Set A) := by
  let J : Ideal A := I.topologicalClosure
  letI : CompleteSpace J := Submodule.topologicalClosure.completeSpace I
  letI : IsBoundedSMul A J := IsBoundedSMul.of_norm_smul_le fun a x ↦ by
    change ‖a * (x : A)‖ ≤ ‖a‖ * ‖(x : A)‖
    exact norm_mul_le _ _
  letI : Module.Finite A J := Module.Finite.of_fg (IsNoetherian.noetherian J)
  obtain ⟨n, fA, hf⟩ := Module.Finite.exists_fin' A J
  let f : (Fin n → A) →L[K] J := continuousLinearMapOfFiniteFree (K := K) fA
  have hf' : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨x, hx⟩
  obtain ⟨C, hC, hpre⟩ := f.exists_preimage_norm_le hf'
  let δ : ℝ := (2 * C)⁻¹
  let N : ℝ := n + 1
  let ε : ℝ := δ / N
  have hδ : 0 < δ := by positivity
  have hN : 0 < N := by positivity
  have hε : 0 < ε := div_pos hδ hN
  have happrox (i : Fin n) : ∃ a : A, a ∈ I ∧
      ‖(fA (Pi.single i 1) : A) - a‖ < ε := by
    have hi : (fA (Pi.single i 1) : A) ∈ closure (I : Set A) :=
      (fA (Pi.single i 1)).property
    obtain ⟨a, haI, ha⟩ := Metric.mem_closure_iff.1 hi ε hε
    exact ⟨a, haI, by simpa [dist_eq_norm] using ha⟩
  choose a haI ha using happrox
  let aJ : Fin n → J := fun i ↦ ⟨a i, Submodule.le_topologicalClosure I (haI i)⟩
  let gA : (Fin n → A) →ₗ[A] J := Fintype.linearCombination A aJ
  let g : (Fin n → A) →L[K] J := continuousLinearMapOfFiniteFree (K := K) gA
  let d : ℝ := ∑ i, ‖fA (Pi.single i 1) - aJ i‖
  have hdi (i : Fin n) : ‖fA (Pi.single i 1) - aJ i‖ < ε := by
    change ‖(fA (Pi.single i 1) : A) - a i‖ < ε
    exact ha i
  have hd : d < δ := by
    calc
      d ≤ ∑ _i : Fin n, ε := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hdi i).le
      _ = (n : ℝ) * ε := by simp
      _ < N * ε := by
        apply mul_lt_mul_of_pos_right _ hε
        simp [N]
      _ = δ := by
        simp only [ε]
        field_simp [hN.ne']
  have hclose (x : Fin n → A) : ‖f x - g x‖ ≤ δ * ‖x‖ := by
    have hx : x = ∑ i, x i • Pi.single i 1 := by
      calc
        x = ∑ i, Pi.single i (x i) :=
          (LinearMap.sum_single_apply (fun _ : Fin n ↦ A) x).symm
        _ = ∑ i, x i • Pi.single i 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          ext j
          by_cases hij : i = j <;> simp [hij]
    have hfA_apply : fA x = ∑ i, x i • fA (Pi.single i 1) := by
      calc
        fA x = fA (∑ i, x i • Pi.single i 1) := congrArg fA hx
        _ = ∑ i, x i • fA (Pi.single i 1) := by simp
    have hgA_apply : gA x = ∑ i, x i • aJ i := by
      simp [gA, Fintype.linearCombination_apply]
    change ‖fA x - gA x‖ ≤ δ * ‖x‖
    rw [hfA_apply, hgA_apply, ← Finset.sum_sub_distrib]
    calc
      ‖∑ i, (x i • fA (Pi.single i 1) - x i • aJ i)‖ ≤
          ∑ i, ‖x i • fA (Pi.single i 1) - x i • aJ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖x i • (fA (Pi.single i 1) - aJ i)‖ := by
        congr 1
        funext i
        rw [smul_sub]
      _ ≤ ∑ i, ‖x i‖ * ‖fA (Pi.single i 1) - aJ i‖ := by
        gcongr with i
        exact norm_smul_le _ _
      _ ≤ ∑ i, ‖x‖ * ‖fA (Pi.single i 1) - aJ i‖ := by
        gcongr with i
        exact norm_le_pi_norm x i
      _ = d * ‖x‖ := by
        rw [Finset.sum_mul]
        simp only [mul_comm]
      _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hd.le (norm_nonneg x)
  choose lift hlift hlift_norm using hpre
  let h : J → J := fun y ↦ y - g (lift y)
  have hδC : δ * C = (1 / 2 : ℝ) := by
    dsimp [δ]
    field_simp [hC.ne']
  have hle (y : J) : ‖h y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    calc
      ‖h y‖ = ‖f (lift y) - g (lift y)‖ := by
        change ‖y - g (lift y)‖ = ‖f (lift y) - g (lift y)‖
        rw [hlift y]
      _ ≤ δ * ‖lift y‖ := hclose _
      _ ≤ δ * (C * ‖y‖) := by gcongr; exact hlift_norm y
      _ = (1 / 2 : ℝ) * ‖y‖ := by rw [← mul_assoc, hδC]
  have hg_surjective : Function.Surjective g := by
    intro y
    have hnle : ∀ m : ℕ, ‖h^[m] y‖ ≤ (1 / 2 : ℝ) ^ m * ‖y‖ := by
      intro m
      induction m with
      | zero => simp
      | succ m hm =>
          rw [Function.iterate_succ']
          apply (hle _).trans
          rw [pow_succ', mul_assoc]
          gcongr
    let u : ℕ → (Fin n → A) := fun m ↦ lift (h^[m] y)
    have hule : ∀ m, ‖u m‖ ≤ (1 / 2 : ℝ) ^ m * (C * ‖y‖) := fun m ↦ by
      apply (hlift_norm _).trans
      calc
        C * ‖h^[m] y‖ ≤ C * ((1 / 2 : ℝ) ^ m * ‖y‖) := by
          gcongr
          exact hnle m
        _ = (1 / 2 : ℝ) ^ m * (C * ‖y‖) := by ring
    have hnorm_summable : Summable fun m ↦ ‖u m‖ := by
      refine Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) hule ?_
      exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    have hu_summable : Summable u := hnorm_summable.of_norm
    let x : Fin n → A := ∑' m, u m
    have hpartial : ∀ m : ℕ, g (∑ i ∈ Finset.range m, u i) = y - h^[m] y := by
      intro m
      induction m with
      | zero => simp [g.map_zero]
      | succ m hm =>
          rw [Finset.sum_range_succ, g.map_add, hm, Function.iterate_succ_apply', sub_add]
    have hsum_tendsto :
        Tendsto (fun m ↦ ∑ i ∈ Finset.range m, u i) atTop (nhds x) :=
      hu_summable.hasSum.tendsto_sum_nat
    have hg_tendsto :
        Tendsto (fun m ↦ g (∑ i ∈ Finset.range m, u i)) atTop (nhds (g x)) :=
      (g.continuous.tendsto x).comp hsum_tendsto
    simp only [hpartial] at hg_tendsto
    have hresidual_tendsto : Tendsto (fun m ↦ y - h^[m] y) atTop (nhds (y - 0)) := by
      refine tendsto_const_nhds.sub ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      refine squeeze_zero (fun _ ↦ norm_nonneg _) hnle ?_
      rw [← zero_mul ‖y‖]
      exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul
        tendsto_const_nhds
    have hgxy : g x = y - 0 := tendsto_nhds_unique hg_tendsto hresidual_tendsto
    exact ⟨x, by simpa using hgxy⟩
  have hg_mem (x : Fin n → A) : (g x : A) ∈ I := by
    have hgA_apply : gA x = ∑ i, x i • aJ i := by
      simp [gA, Fintype.linearCombination_apply]
    change (gA x : A) ∈ I
    rw [hgA_apply]
    simpa [aJ] using
      (Submodule.sum_mem I fun i (_hi : i ∈ Finset.univ) ↦ I.mul_mem_left (x i) (haI i))
  apply isClosed_of_closure_subset
  intro y hy
  let yJ : J := ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hg_surjective yJ
  have hxI := hg_mem x
  have hxval : (g x : A) = y := congrArg Subtype.val hx
  rwa [hxval] at hxI

omit [IsUltrametricDist K] in
/-- A linear functional is continuous when its kernel contains an ideal with finite-dimensional
quotient in a complete Noetherian normed algebra. -/
theorem continuous_linearForm_of_ideal_le_ker
    (I : Ideal A) [Module.Finite K (A ⧸ I)] (L : A →ₗ[K] K)
    (hI : ∀ x, x ∈ I → L x = 0) : Continuous L := by
  let S : Submodule K A := I.restrictScalars K
  let e : (A ⧸ S) ≃ₗ[K] (A ⧸ I) :=
    Submodule.Quotient.restrictScalarsEquiv K I
  letI : FiniteDimensional K (A ⧸ S) := e.symm.finiteDimensional
  apply L.continuous_of_isClosed_ker
  apply Submodule.isClosed_mono_of_finiteDimensional_quotient
    (s := S) (t := LinearMap.ker L)
  · simpa [S] using isClosed_ideal_of_isNoetherianRing K I
  · intro x hx
    exact hI x hx

end

end Rigid
