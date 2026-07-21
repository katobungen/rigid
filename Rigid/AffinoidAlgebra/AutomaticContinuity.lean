import Mathlib
import Rigid.AffinoidAlgebra.Basic
import Rigid.AffinoidAlgebra.NoetherNormalization
import Rigid.TateAlgebra.Complete
import Rigid.TateAlgebra.Noetherian

set_option linter.style.header false

/-!
# Automatic continuity for affinoid algebras

This file isolates the proof of automatic continuity used by the Development comparator.  It
follows Proposition 1.4.11: first handle finite-dimensional targets, and then apply the closed
graph theorem together with the finite-dimensional quotients by powers of maximal ideals.
-/

universe u v w

open Filter
open scoped Topology

namespace Rigid

open TateAlgebra

section

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [CommRing A] [Algebra K A]

private theorem tateAlgebra_ideal_isClosed {n : ℕ}
    (I : Ideal (TateAlgebra K (Fin n))) : IsClosed (I : Set (TateAlgebra K (Fin n))) := by
  classical
  let m : MonomialOrder (Fin n) := MonomialOrder.lex
  let L : Set (Fin n →₀ ℕ) :=
    (fun f ↦ leadingDegree m f) '' {f : TateAlgebra K (Fin n) | f ∈ I ∧ f ≠ 0}
  obtain ⟨T, hTL, hdom⟩ := TateAlgebra.exists_finset_dominating L
  have hchoice : ∀ t : {x // x ∈ T}, ∃ g : TateAlgebra K (Fin n),
      g ∈ I ∧ g ≠ 0 ∧ leadingDegree m g = t.1 := by
    intro t
    obtain ⟨g, hg, hgdeg⟩ := hTL t.2
    exact ⟨g, hg.1, hg.2, hgdeg⟩
  choose g hgI hgne hgdeg using hchoice
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro F hF
  obtain ⟨Q, hQ⟩ := exists_forall_coeff_eq_zero_of_leadingDegree_le m g hgne F
  let R : TateAlgebra K (Fin n) := F - ∑ t, Q t * g t
  have hRne : R ≠ 0 := by
    intro hR
    apply hF
    rw [Set.mem_compl_iff] at hF
    have hFI : F = ∑ t, Q t * g t := sub_eq_zero.mp hR
    rw [hFI]
    exact Submodule.sum_mem I fun t _ ↦ I.mul_mem_left _ (hgI t)
  refine ⟨‖R‖, norm_pos_iff.mpr hRne, ?_⟩
  intro H hHF hHI
  rw [Set.mem_compl_iff] at hF
  have hHdist : ‖H - F‖ < ‖R‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hHF
  let S : TateAlgebra K (Fin n) := H - ∑ t, Q t * g t
  have hSI : S ∈ I := I.sub_mem hHI (Submodule.sum_mem I fun t _ ↦ I.mul_mem_left _ (hgI t))
  have hSR : ‖S - R‖ < ‖R‖ := by
    simpa [S, R, sub_sub_sub_cancel_right] using hHdist
  have hSnorm : ‖S‖ = ‖R‖ := by
    have hSR' : ‖S + -R‖ < max ‖S‖ ‖-R‖ := by
      calc
        ‖S + -R‖ = ‖S - R‖ := by rw [sub_eq_add_neg]
        _ < ‖R‖ := hSR
        _ = ‖-R‖ := norm_neg R |>.symm
        _ ≤ max ‖S‖ ‖-R‖ := le_max_right _ _
    simpa using
      (IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := S) (y := -R) hSR')
  have hSne : S ≠ 0 := by
    rw [← norm_ne_zero_iff, hSnorm]
    exact norm_ne_zero_iff.mpr hRne
  obtain ⟨t, htT, htdeg⟩ := hdom (leadingDegree m S) ⟨S, ⟨hSI, hSne⟩, rfl⟩
  let t' : {x // x ∈ T} := ⟨t, htT⟩
  have hRcoeff : MvPowerSeries.coeff (leadingDegree m S) R.1 = 0 := by
    exact hQ (leadingDegree m S) ⟨t', by simpa [t', hgdeg t'] using htdeg⟩
  have hcoeff : ‖S‖ ≤ ‖S - R‖ := by
    calc
      ‖S‖ = ‖MvPowerSeries.coeff (leadingDegree m S) S.1‖ := (norm_leadingCoeff m hSne).symm
      _ = ‖MvPowerSeries.coeff (leadingDegree m S) (S - R).1‖ := by
        simp [hRcoeff]
      _ ≤ ‖S - R‖ := norm_coeff_le_norm K (Fin n) (S - R) (leadingDegree m S)
  exact (not_lt_of_ge (hSnorm ▸ hcoeff) hSR).elim

private noncomputable def pushForwardPresentation
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (P : AffinoidPresentation K A) (f : A →ₐ[K] B) (hf : Function.Surjective f) :
    AffinoidPresentation K B := by
  let g : TateAlgebra K (Fin P.n) →ₐ[K] B := f.comp P.toAlgHom
  have hg : Function.Surjective g := hf.comp P.toAlgHom_surjective
  exact
    { n := P.n
      ideal := RingHom.ker g
      equiv := Ideal.quotientKerAlgEquivOfSurjective hg }

private theorem continuous_for_residueTopology_of_surjective
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (P : AffinoidPresentation K A) (f : A →ₐ[K] B) (hf : Function.Surjective f) :
    @Continuous A B P.residueTopology (pushForwardPresentation K P f hf).residueTopology f := by
  let g : TateAlgebra K (Fin P.n) →ₐ[K] B := f.comp P.toAlgHom
  let Q : AffinoidPresentation K B := pushForwardPresentation K P f hf
  have hQg : Q.toAlgHom = g := by
    dsimp [Q, pushForwardPresentation]
    ext x
    exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := f.comp P.toAlgHom)
      (hf.comp P.toAlgHom_surjective) x
  letI : TopologicalSpace A := P.residueTopology
  letI : TopologicalSpace B := Q.residueTopology
  change Continuous f
  have hP : IsOpenQuotientMap P.toAlgHom :=
    isOpenQuotientMap_coinduced P.toAlgHom P.toAlgHom_surjective
  apply hP.continuous_comp_iff.mp
  have hQcont : Continuous Q.toAlgHom := continuous_coinduced_rng
  rw [hQg] at hQcont
  dsimp [Q, pushForwardPresentation] at hQcont
  change Continuous (f.comp P.toAlgHom)
  exact hQcont

private theorem isNoetherianRing_of_isAffinoidAlgebra
    {A : Type v} [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing A := by
  let P := hA.presentation
  haveI : IsNoetherianRing (TateAlgebra K (Fin P.n) ⧸ P.ideal) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk P.ideal)
      Ideal.Quotient.mk_surjective
  exact isNoetherianRing_of_ringEquiv _ P.equiv.toRingEquiv

@[reducible]
private noncomputable def compatibleResidueNormedAddCommGroup
    (P : AffinoidPresentation K A) : NormedAddCommGroup A := by
  letI : IsClosed (P.ideal : Set (TateAlgebra K (Fin P.n))) :=
    tateAlgebra_ideal_isClosed K P.ideal
  letI : NormedCommRing (TateAlgebra K (Fin P.n) ⧸ P.ideal) := inferInstance
  letI : NormedCommRing A := NormedCommRing.induced A
    (TateAlgebra K (Fin P.n) ⧸ P.ideal) P.equiv.symm.toRingHom P.equiv.symm.injective
  infer_instance

@[reducible]
private noncomputable def compatibleResidueNormedSpace (P : AffinoidPresentation K A) :
    letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
    NormedSpace K A := by
  letI : IsClosed (P.ideal : Set (TateAlgebra K (Fin P.n))) :=
    tateAlgebra_ideal_isClosed K P.ideal
  letI : NormedCommRing (TateAlgebra K (Fin P.n) ⧸ P.ideal) := inferInstance
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
  exact NormedSpace.induced K A (TateAlgebra K (Fin P.n) ⧸ P.ideal)
    P.equiv.symm.toLinearEquiv

private theorem compatibleResidueCompleteSpace (P : AffinoidPresentation K A) :
    letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
    CompleteSpace A := by
  letI : IsClosed (P.ideal : Set (TateAlgebra K (Fin P.n))) :=
    tateAlgebra_ideal_isClosed K P.ideal
  letI : NormedCommRing (TateAlgebra K (Fin P.n) ⧸ P.ideal) := inferInstance
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
  let e : A ≃ₗᵢ[K] (TateAlgebra K (Fin P.n) ⧸ P.ideal) :=
    { P.equiv.symm.toLinearEquiv with norm_map' := fun _ ↦ rfl }
  exact (completeSpace_congr (e := e.toEquiv) e.isometry.isUniformEmbedding).2 inferInstance

private theorem compatibleResidueTopology_eq (P : AffinoidPresentation K A) :
    (letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
     inferInstance : TopologicalSpace A) = P.residueTopology := by
  letI : IsClosed (P.ideal : Set (TateAlgebra K (Fin P.n))) :=
    tateAlgebra_ideal_isClosed K P.ideal
  letI : NormedCommRing (TateAlgebra K (Fin P.n) ⧸ P.ideal) := inferInstance
  change TopologicalSpace.induced P.equiv.symm inferInstance =
    TopologicalSpace.coinduced P.toAlgHom inferInstance
  calc
    TopologicalSpace.induced P.equiv.symm
        (inferInstance : TopologicalSpace (TateAlgebra K (Fin P.n) ⧸ P.ideal)) =
      TopologicalSpace.coinduced P.equiv
        (inferInstance : TopologicalSpace (TateAlgebra K (Fin P.n) ⧸ P.ideal)) :=
      congrFun P.equiv.toEquiv.induced_symm _
    _ = TopologicalSpace.coinduced P.toAlgHom inferInstance := by
      change (TopologicalSpace.coinduced (Ideal.Quotient.mk P.ideal) inferInstance).coinduced
        P.equiv = TopologicalSpace.coinduced P.toAlgHom inferInstance
      rw [coinduced_compose]
      rfl

private theorem residueT2Space (P : AffinoidPresentation K A) :
    @T2Space A P.residueTopology := by
  rw [← compatibleResidueTopology_eq K A P]
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A P
  infer_instance

private theorem continuous_for_residueTopology_of_finite_codomain
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Finite K B]
    (PA : AffinoidPresentation K A) (PB : AffinoidPresentation K B) (f : A →ₐ[K] B) :
    @Continuous A B PA.residueTopology PB.residueTopology f := by
  let C := f.range
  let q : A →ₐ[K] C := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  let PC : AffinoidPresentation K C := pushForwardPresentation K PA q hq
  have hqcont : @Continuous A C PA.residueTopology PC.residueTopology q :=
    continuous_for_residueTopology_of_surjective K PA q hq
  letI : NormedAddCommGroup C := compatibleResidueNormedAddCommGroup K C PC
  letI : NormedSpace K C := compatibleResidueNormedSpace K C PC
  letI : NormedAddCommGroup B := compatibleResidueNormedAddCommGroup K B PB
  letI : NormedSpace K B := compatibleResidueNormedSpace K B PB
  letI : TopologicalSpace C := PC.residueTopology
  letI : IsTopologicalRing C := PC.residueIsTopologicalRing
  letI : ContinuousSMul K C := PC.residueContinuousSMul
  letI : T2Space C := residueT2Space K C PC
  letI : TopologicalSpace B := PB.residueTopology
  letI : IsTopologicalRing B := PB.residueIsTopologicalRing
  letI : ContinuousSMul K B := PB.residueContinuousSMul
  have hval : Continuous (f.range.val : C →ₐ[K] B) :=
    f.range.val.toLinearMap.continuous_of_finiteDimensional
  letI : TopologicalSpace A := PA.residueTopology
  letI : TopologicalSpace C := PC.residueTopology
  letI : TopologicalSpace B := PB.residueTopology
  exact hval.comp hqcont

omit [CompleteSpace K] [IsUltrametricDist K] in
private theorem continuous_linearMap_of_seq_closed_graph
    {A : Type v} [NormedAddCommGroup A] [NormedSpace K A] [CompleteSpace A]
    {B : Type w} [NormedAddCommGroup B] [NormedSpace K B] [CompleteSpace B]
    (f : A →ₗ[K] B)
    (hgraph : ∀ (u : ℕ → A) (x : A) (y : B), Tendsto u atTop (𝓝 x) →
      Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) : Continuous f :=
  f.continuous_of_seq_closed_graph hgraph

/-- The affinoid Nullstellensatz consequence of Noether normalization used in
Proposition 1.4.11: residue fields at maximal ideals are finite over the ground field. -/
private theorem finite_residueField_of_maximal_isAffinoidAlgebra
    {B : Type w} [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B)
    (m : Ideal B) (hm : m.IsMaximal) : Module.Finite K (B ⧸ m) :=
  finite_of_isField_of_isAffinoidAlgebra K (IsAffinoidAlgebra.quotient K hB m)
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm)

/-- Powers of maximal ideals have finite-dimensional quotient. -/
private theorem finite_quotient_maximal_pow_of_isAffinoidAlgebra
    {B : Type w} [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B)
    (m : Ideal B) (hm : m.IsMaximal) (l : ℕ) (hl : 1 ≤ l) :
    Module.Finite K (B ⧸ m ^ l) := by
  letI : IsNoetherianRing B := isNoetherianRing_of_isAffinoidAlgebra K hB
  letI : IsNoetherianRing (B ⧸ m ^ l) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk (m ^ l))
      Ideal.Quotient.mk_surjective
  letI : Module.Finite K (B ⧸ m) :=
    finite_residueField_of_maximal_isAffinoidAlgebra K hB m hm
  have hpow : m ^ l ≤ m := Ideal.pow_le_self (Nat.ne_of_gt hl)
  let q : (B ⧸ m ^ l) →ₐ[K] (B ⧸ m) := Ideal.Quotient.factorₐ K hpow
  have hqkerFG : (RingHom.ker q).FG := IsNoetherian.noetherian _
  refine Module.finite_of_surjective_of_ker_le_nilradical q
    (Ideal.Quotient.factor_surjective hpow) ?_ hqkerFG
  apply hqkerFG.isNilpotent_iff_le_nilradical.mp
  use l
  change RingHom.ker (Ideal.Quotient.factor hpow) ^ l = ⊥
  rw [Ideal.Quotient.factor_ker hpow, ← Ideal.map_pow, Ideal.map_quotient_self]

/-- The Krull-intersection consequence used in Proposition 1.4.11. -/
private theorem eq_zero_of_mem_all_maximal_powers_of_isAffinoidAlgebra
    {B : Type w} [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B) (b : B)
    (hb : ∀ (m : Ideal B), m.IsMaximal → ∀ l : ℕ, 1 ≤ l → b ∈ m ^ l) : b = 0 := by
  letI : IsNoetherianRing B := isNoetherianRing_of_isAffinoidAlgebra K hB
  by_contra hb0
  let N : Submodule B B := Submodule.span B ({b} : Set B)
  let J : Ideal B := N.annihilator
  have hJ : J ≠ ⊤ := by
    intro htop
    have hmem : (1 : B) ∈ J := by rw [htop]; exact Submodule.mem_top
    have : (1 : B) * b = 0 := by
      simpa [J, N] using (Submodule.mem_annihilator_span_singleton b 1).mp hmem
    exact hb0 (by simpa using this)
  obtain ⟨m, hm, hJm⟩ := J.exists_le_maximal hJ
  have hbInf : b ∈ (⨅ i : ℕ, m ^ i • (⊤ : Submodule B B)) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    rcases i with _ | i
    · simp
    · exact hb m hm (i + 1) (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero i))
  obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff b).mp hbInf
  have hsub : (1 - (r : B)) ∈ J := by
    apply (Submodule.mem_annihilator_span_singleton b (1 - (r : B))).mpr
    rw [sub_smul, one_smul, hr, sub_self]
  have hone : (1 : B) ∈ m := by
    simpa using m.add_mem (hJm hsub) r.2
  exact hm.ne_top (m.eq_top_iff_one.mpr hone)

private theorem continuous_for_residueTopology
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    (PA : AffinoidPresentation K A) (PB : AffinoidPresentation K B) (f : A →ₐ[K] B) :
    @Continuous A B PA.residueTopology PB.residueTopology f := by
  let fLinear : A →ₗ[K] B := f.toLinearMap
  letI : NormedAddCommGroup A := compatibleResidueNormedAddCommGroup K A PA
  letI : NormedSpace K A := compatibleResidueNormedSpace K A PA
  letI : CompleteSpace A := compatibleResidueCompleteSpace K A PA
  letI : NormedAddCommGroup B := compatibleResidueNormedAddCommGroup K B PB
  letI : NormedSpace K B := compatibleResidueNormedSpace K B PB
  letI : CompleteSpace B := compatibleResidueCompleteSpace K B PB
  have hAtop : (inferInstance : TopologicalSpace A) = PA.residueTopology :=
    compatibleResidueTopology_eq K A PA
  have hBtop : (inferInstance : TopologicalSpace B) = PB.residueTopology :=
    compatibleResidueTopology_eq K B PB
  have hfmetric := continuous_linearMap_of_seq_closed_graph K fLinear (by
    intro u x y hu hfu
    suffices y - f x = 0 by simpa [fLinear] using (sub_eq_zero.mp this)
    apply eq_zero_of_mem_all_maximal_powers_of_isAffinoidAlgebra K
      (show IsAffinoidAlgebra K B from ⟨PB⟩)
    intro m hm l hl
    let q : B →ₐ[K] B ⧸ m ^ l := Ideal.Quotient.mkₐ K (m ^ l)
    have hqsurj : Function.Surjective q := Ideal.Quotient.mkₐ_surjective K (m ^ l)
    let PQ : AffinoidPresentation K (B ⧸ m ^ l) :=
      pushForwardPresentation K PB q hqsurj
    letI : Module.Finite K (B ⧸ m ^ l) :=
      finite_quotient_maximal_pow_of_isAffinoidAlgebra K
        (show IsAffinoidAlgebra K B from ⟨PB⟩) m hm l hl
    have hqf := continuous_for_residueTopology_of_finite_codomain K PA PQ (q.comp f)
    have hq : @Continuous B (B ⧸ m ^ l) PB.residueTopology PQ.residueTopology q :=
      continuous_for_residueTopology_of_surjective K PB q hqsurj
    rw [← hAtop] at hqf
    rw [← hBtop] at hq
    letI : TopologicalSpace (B ⧸ m ^ l) := PQ.residueTopology
    letI : T2Space (B ⧸ m ^ l) := residueT2Space K (B ⧸ m ^ l) PQ
    have hlim₁ : Tendsto (fun n ↦ q (f (u n))) atTop (𝓝 (q (f x))) :=
      (hqf.tendsto x).comp hu
    have hlim₂ : Tendsto (fun n ↦ q (f (u n))) atTop (𝓝 (q y)) :=
      (hq.tendsto y).comp hfu
    have heq : q (f x) = q y := tendsto_nhds_unique hlim₁ hlim₂
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q (y - f x) = 0
    rw [map_sub, heq, sub_self])
  change @Continuous A B (inferInstance : TopologicalSpace A)
    (inferInstance : TopologicalSpace B) f at hfmetric
  rwa [hAtop, hBtop] at hfmetric

/-- Automatic continuity written directly in terms of two quotient presentations. -/
theorem continuous_for_affinoidPresentationData
    {A : Type v} [CommRing A] [Algebra K A]
    {B : Type w} [CommRing B] [Algebra K B]
    {nA nB : ℕ} (IA : Ideal (TateAlgebra K (Fin nA)))
    (eA : (TateAlgebra K (Fin nA) ⧸ IA) ≃ₐ[K] A)
    (IB : Ideal (TateAlgebra K (Fin nB)))
    (eB : (TateAlgebra K (Fin nB) ⧸ IB) ≃ₐ[K] B) (f : A →ₐ[K] B) :
    @Continuous A B
      (TopologicalSpace.coinduced
        (eA.toAlgHom.comp (Ideal.Quotient.mkₐ K IA)) inferInstance)
      (TopologicalSpace.coinduced
        (eB.toAlgHom.comp (Ideal.Quotient.mkₐ K IB)) inferInstance) f := by
  let PA : AffinoidPresentation K A := { n := nA, ideal := IA, equiv := eA }
  let PB : AffinoidPresentation K B := { n := nB, ideal := IB, equiv := eB }
  change @Continuous A B PA.residueTopology PB.residueTopology f
  exact continuous_for_residueTopology K PA PB f

end

end Rigid
