import Rigid.AffinoidAlgebra.Basic
import Rigid.TateAlgebra.RelativeUniversalProperty
import Mathlib.Analysis.Normed.Operator.Banach

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Affinoidness of relative Tate algebras

If a Banach `K`-algebra `A` admits a continuous surjection from a finite Tate algebra, then every
finite relative Tate algebra `A⟨T₁, ..., Tₙ⟩` is again `K`-affinoid.  The proof combines the old and
new variables in one Tate algebra.  Surjectivity is obtained from polynomial density and a bounded
lifting argument, followed by the standard Banach-space iteration from the open mapping theorem.
-/

open Filter
open scoped Topology

universe u v w

namespace Rigid

section ApproximateSurjectivity

variable {K : Type u} [NontriviallyNormedField K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

/-- A bounded linear map with uniformly bounded half-error preimages is surjective. -/
private theorem surjective_of_exists_approx_preimage_norm_le (T : E →L[K] F) (C : ℝ)
    (hC : 0 ≤ C)
    (happrox : ∀ y : F, ∃ x : E,
      dist (T x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) : Function.Surjective T := by
  choose g hg using happrox
  let h : F → F := fun y ↦ y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ']
      exact (hle _).trans <| by
        rw [pow_succ', mul_assoc]
        gcongr
  let z : ℕ → E := fun n ↦ g (h^[n] y)
  have zle : ∀ n, ‖z n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    refine (hg _).2.trans ?_
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have szNorm : Summable fun n ↦ ‖z n‖ := by
    refine .of_nonneg_of_le (fun n ↦ norm_nonneg _) zle ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have sz : Summable z := szNorm.of_norm
  let x : E := ∑' n, z n
  have hpartial : ∀ n : ℕ, T (∑ i ∈ Finset.range n, z i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [T.map_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, T.map_add, ih, Function.iterate_succ_apply', sub_add]
  have hlim₁ : Tendsto (fun n ↦ T (∑ i ∈ Finset.range n, z i)) atTop (𝓝 (T x)) :=
    (T.continuous.tendsto _).comp sz.hasSum.tendsto_sum_nat
  simp only [hpartial] at hlim₁
  have hlim₂ : Tendsto (fun n ↦ y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul
      tendsto_const_nhds
  have hx : T x = y - 0 := tendsto_nhds_unique hlim₁ hlim₂
  exact ⟨x, by simpa using hx⟩

end ApproximateSurjectivity

section Maps

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The ground-field map into a Banach `K`-algebra. -/
private noncomputable def groundMap
    (B : Type w) [NormedCommRing B] [NormedAlgebra K B] : ContinuousAlgHom K K B where
  toFun := algebraMap K B
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ ↦ rfl
  cont := continuous_algebraMap K B

/-- The constant-series map into a relative Tate algebra. -/
private noncomputable def constantMap (n : ℕ) :
    ContinuousAlgHom K A (TateAlgebra A (Fin n)) where
  toFun := TateAlgebra.C A (Fin n)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ ↦ rfl
  cont := AddMonoidHomClass.continuous_of_bound (TateAlgebra.C A (Fin n)) 1 fun a ↦ by
    rw [norm_C, one_mul]

/-- Embed the old Tate variables into the first block of a larger Tate algebra. -/
private noncomputable def leftMap (m n : ℕ) :
    ContinuousAlgHom K (TateAlgebra K (Fin m)) (TateAlgebra K (Fin (m + n))) :=
  TateAlgebra.eval K (Fin m)
    (fun i ↦ tateVariable K (Fin (m + n)) (Fin.castAdd n i)) (fun i ↦ by simp)

@[simp]
private theorem leftMap_tateVariable (m n : ℕ) (i : Fin m) :
    leftMap K m n (tateVariable K (Fin m) i) =
      tateVariable K (Fin (m + n)) (Fin.castAdd n i) :=
  TateAlgebra.eval_tateVariable K (Fin m) (fun _ ↦ by simp) i

private theorem norm_leftMap_le (m n : ℕ) (b : TateAlgebra K (Fin m)) :
    ‖leftMap K m n b‖ ≤ ‖b‖ := by
  change ‖TateAlgebra.evalFun K (Fin m)
    (fun i ↦ tateVariable K (Fin (m + n)) (Fin.castAdd n i)) b‖ ≤ ‖b‖
  simpa using TateAlgebra.norm_evalFun_le K (Fin m) (x := fun i ↦
    tateVariable K (Fin (m + n)) (Fin.castAdd n i)) (fun i ↦ by simp) b

private noncomputable def combinedTuple (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) :
    Fin (m + n) → TateAlgebra A (Fin n) :=
  Fin.addCases
    (fun i ↦ TateAlgebra.C A (Fin n) (π (tateVariable K (Fin m) i)))
    (fun j ↦ tateVariable A (Fin n) j)

private theorem combinedTuple_isPowerBounded (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) :
    ∀ i, IsPowerBounded (combinedTuple K A m n π i) := by
  have hleft : ∀ i : Fin m,
      IsPowerBounded (TateAlgebra.C A (Fin n) (π (tateVariable K (Fin m) i))) := by
    intro i
    refine ⟨‖π.toContinuousLinearMap‖, ?_⟩
    rintro _ ⟨r, rfl⟩
    calc
      ‖(TateAlgebra.C A (Fin n) (π (tateVariable K (Fin m) i))) ^ r‖ =
          ‖π ((tateVariable K (Fin m) i) ^ r)‖ := by
        rw [← map_pow, norm_C, ← map_pow]
      _ ≤ ‖π.toContinuousLinearMap‖ * ‖(tateVariable K (Fin m) i) ^ r‖ :=
        ContinuousLinearMap.le_opNorm π.toContinuousLinearMap _
      _ ≤ ‖π.toContinuousLinearMap‖ * 1 := mul_le_mul_of_nonneg_left
        (by simpa using norm_tateVariable_pow_le K (Fin m) i r) (norm_nonneg _)
      _ = ‖π.toContinuousLinearMap‖ := mul_one _
  have hright : ∀ j : Fin n, IsPowerBounded (tateVariable A (Fin n) j) := by
    intro j
    refine ⟨‖(1 : A)‖, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact norm_tateVariable_pow_le A (Fin n) j r
  intro i
  refine Fin.addCases (motive := fun i ↦
    IsPowerBounded (combinedTuple K A m n π i)) ?_ ?_ i
  · intro j
    simpa only [combinedTuple, Fin.addCases_left] using hleft j
  · intro j
    simpa only [combinedTuple, Fin.addCases_right] using hright j

/-- The map from the Tate algebra in the combined old and new variables. -/
private noncomputable def combinedMap (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) :
    ContinuousAlgHom K (TateAlgebra K (Fin (m + n))) (TateAlgebra A (Fin n)) :=
  RelativeTateAlgebra.eval K K (groundMap K (TateAlgebra A (Fin n)))
    (combinedTuple K A m n π) (combinedTuple_isPowerBounded K A m n π)

@[simp]
private theorem combinedMap_tateVariable_left (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) (i : Fin m) :
    combinedMap K A m n π (tateVariable K (Fin (m + n)) (Fin.castAdd n i)) =
      TateAlgebra.C A (Fin n) (π (tateVariable K (Fin m) i)) := by
  rw [combinedMap, RelativeTateAlgebra.eval_tateVariable]
  simp [combinedTuple]

@[simp]
private theorem combinedMap_tateVariable_right (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) (j : Fin n) :
    combinedMap K A m n π (tateVariable K (Fin (m + n)) (Fin.natAdd m j)) =
      tateVariable A (Fin n) j := by
  rw [combinedMap, RelativeTateAlgebra.eval_tateVariable]
  simp [combinedTuple]

private theorem combinedMap_comp_leftMap (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) :
    (combinedMap K A m n π).comp (leftMap K m n) = (constantMap K A n).comp π := by
  apply RelativeTateAlgebra.hom_ext K K
  · intro a
    change combinedMap K A m n π
        (leftMap K m n (TateAlgebra.C K (Fin m) a)) =
      constantMap K A n (π (TateAlgebra.C K (Fin m) a))
    exact ((combinedMap K A m n π).comp (leftMap K m n)).commutes a |>.trans
      (((constantMap K A n).comp π).commutes a).symm
  · intro i
    change combinedMap K A m n π
        (leftMap K m n (tateVariable K (Fin m) i)) =
      constantMap K A n (π (tateVariable K (Fin m) i))
    rw [leftMap_tateVariable, combinedMap_tateVariable_left]
    rfl

private noncomputable def rightMonomial (m n : ℕ) (ν : Fin n →₀ ℕ) :
    TateAlgebra K (Fin (m + n)) :=
  TateAlgebra.evalMonomial
    (fun j ↦ tateVariable K (Fin (m + n)) (Fin.natAdd m j)) ν

private theorem norm_rightMonomial_le_one (m n : ℕ) (ν : Fin n →₀ ℕ) :
    ‖rightMonomial K m n ν‖ ≤ 1 := by
  simpa [rightMonomial] using TateAlgebra.norm_evalMonomial_le
    (x := fun j ↦ tateVariable K (Fin (m + n)) (Fin.natAdd m j)) (fun j ↦ by simp) ν

private theorem combinedMap_rightMonomial (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) (ν : Fin n →₀ ℕ) :
    combinedMap K A m n π (rightMonomial K m n ν) =
      TateAlgebra.evalMonomial (tateVariable A (Fin n)) ν := by
  classical
  simp [rightMonomial, TateAlgebra.evalMonomial]

private theorem exists_polynomial_preimage (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ a : A, ∃ b : TateAlgebra K (Fin m), π b = a ∧ ‖b‖ ≤ N * ‖a‖)
    (P : MvPolynomial (Fin n) A) :
    ∃ G : TateAlgebra K (Fin (m + n)),
      combinedMap K A m n π G = TateAlgebra.ofPolynomial A (Fin n) P ∧
        ‖G‖ ≤ N * ‖TateAlgebra.ofPolynomial A (Fin n) P‖ := by
  classical
  have hlift : ∀ ν : Fin n →₀ ℕ, ∃ b : TateAlgebra K (Fin m),
      π b = P.coeff ν ∧ ‖b‖ ≤ N * ‖P.coeff ν‖ := fun ν ↦ hN (P.coeff ν)
  choose b hb using hlift
  let G : TateAlgebra K (Fin (m + n)) :=
    ∑ ν ∈ P.support, leftMap K m n (b ν) * rightMonomial K m n ν
  refine ⟨G, ?_, ?_⟩
  · have hleft := combinedMap_comp_leftMap K A m n π
    calc
      combinedMap K A m n π G =
          ∑ ν ∈ P.support,
            TateAlgebra.C A (Fin n) (π (b ν)) *
              TateAlgebra.evalMonomial (tateVariable A (Fin n)) ν := by
        simp only [G, map_sum]
        apply Finset.sum_congr rfl
        intro ν hν
        rw [map_mul, combinedMap_rightMonomial]
        change combinedMap K A m n π (leftMap K m n (b ν)) * _ = _
        rw [show combinedMap K A m n π (leftMap K m n (b ν)) =
          constantMap K A n (π (b ν)) from congrArg (fun q :
            ContinuousAlgHom K (TateAlgebra K (Fin m)) (TateAlgebra A (Fin n)) ↦ q (b ν)) hleft]
        rfl
      _ = ∑ ν ∈ P.support,
            TateAlgebra.C A (Fin n) (P.coeff ν) *
              TateAlgebra.evalMonomial (tateVariable A (Fin n)) ν := by
        apply Finset.sum_congr rfl
        intro ν hν
        rw [(hb ν).1]
      _ = TateAlgebra.ofPolynomial A (Fin n) P := by
        rw [ofPolynomial_eq_eval₂, MvPolynomial.eval₂_eq]
        rfl
  · let M := N * ‖TateAlgebra.ofPolynomial A (Fin n) P‖
    have hM : 0 ≤ M := mul_nonneg hN0 (norm_nonneg _)
    have hterm : ∀ ν,
        ‖leftMap K m n (b ν) * rightMonomial K m n ν‖ ≤ M := by
      intro ν
      have hcoeff : ‖P.coeff ν‖ ≤ ‖TateAlgebra.ofPolynomial A (Fin n) P‖ := by
        simpa using norm_coeff_le_norm A (Fin n) (TateAlgebra.ofPolynomial A (Fin n) P) ν
      calc
        ‖leftMap K m n (b ν) * rightMonomial K m n ν‖ ≤
            ‖leftMap K m n (b ν)‖ * ‖rightMonomial K m n ν‖ := norm_mul_le _ _
        _ ≤ ‖b ν‖ * 1 := mul_le_mul (norm_leftMap_le K m n (b ν))
          (norm_rightMonomial_le_one K m n ν) (norm_nonneg _) (norm_nonneg _)
        _ = ‖b ν‖ := mul_one _
        _ ≤ N * ‖P.coeff ν‖ := (hb ν).2
        _ ≤ M := mul_le_mul_of_nonneg_left hcoeff hN0
    change ‖∑ ν ∈ P.support, leftMap K m n (b ν) * rightMonomial K m n ν‖ ≤ M
    induction P.support using Finset.induction_on with
    | empty => simpa using hM
    | @insert ν s hν ih =>
        rw [Finset.sum_insert hν]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · exact hterm ν
        · exact ih

private theorem combinedMap_surjective (m n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) (hπ : Function.Surjective π) :
    Function.Surjective (combinedMap K A m n π) := by
  obtain ⟨N, hNpos, hN⟩ := π.toContinuousLinearMap.exists_preimage_norm_le hπ
  apply surjective_of_exists_approx_preimage_norm_le
    (combinedMap K A m n π).toContinuousLinearMap N hNpos.le
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp⟩
  · have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    obtain ⟨P, hP⟩ := Metric.denseRange_iff.mp (denseRange_ofPolynomial A (Fin n)) y
      (‖y‖ / 2) (half_pos hypos)
    obtain ⟨G, hGmap, hGnorm⟩ :=
      exists_polynomial_preimage K A m n π N hNpos.le hN P
    refine ⟨G, ?_, ?_⟩
    · change dist (combinedMap K A m n π G) y ≤ 1 / 2 * ‖y‖
      rw [hGmap, dist_comm]
      exact hP.le.trans_eq (by ring)
    · refine hGnorm.trans (mul_le_mul_of_nonneg_left ?_ hNpos.le)
      calc
        ‖TateAlgebra.ofPolynomial A (Fin n) P‖ =
            ‖y + (TateAlgebra.ofPolynomial A (Fin n) P - y)‖ := by
          congr 1
          abel
        _ ≤ max ‖y‖ ‖TateAlgebra.ofPolynomial A (Fin n) P - y‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ = ‖y‖ := max_eq_left <| by
          rw [← dist_eq_norm]
          rw [dist_comm]
          exact hP.le.trans (by linarith)

/-- A finite relative Tate algebra is affinoid whenever the coefficient algebra has a continuous
surjective finite Tate presentation. -/
theorem isAffinoidAlgebra_relativeTateAlgebra_of_surjective (m : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin m)) A) (hπ : Function.Surjective π) (n : ℕ) :
    IsAffinoidAlgebra K (TateAlgebra A (Fin n)) := by
  let Ψ := combinedMap K A m n π
  have hΨ : Function.Surjective Ψ := combinedMap_surjective K A m n π hπ
  exact ⟨
    { n := m + n
      ideal := RingHom.ker Ψ.toRingHom
      equiv := Ideal.quotientKerAlgEquivOfSurjective hΨ }⟩

end Maps

end Rigid
