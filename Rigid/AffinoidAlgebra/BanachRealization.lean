import Rigid.AffinoidAlgebra.QuotientNorm
import Rigid.AffinoidAlgebra.NoetherianBanach
import Rigid.AffinoidAlgebra.ResidueNorm

set_option linter.style.header false

/-!
# Banach realizations of affinoid algebras

This module records the formal consequences of identifying a complete normed realization of an
affinoid algebra with its canonical quotient topology. The topology-identification theorem itself
is the substantive BGR automatic-continuity result.
-/

universe u v w

open Filter
open scoped Topology

namespace Rigid

private structure CanonicalCopy (A : Type v) where
  val : A

private def CanonicalCopy.equiv (A : Type v) : CanonicalCopy A ≃ A :=
  { toFun := CanonicalCopy.val
    invFun := fun a ↦ ⟨a⟩
    left_inv := by intro x; cases x; rfl
    right_inv := by intro a; rfl }

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A complete normed realization of an algebraic affinoid presentation has the presentation's
canonical quotient topology. -/
theorem topology_eq_affinoidTopology_of_presentation
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (n : ℕ) (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A) :
    (inferInstance : TopologicalSpace A) =
      TopologicalSpace.coinduced
        (e.toAlgHom.comp (Ideal.Quotient.mkₐ K I)) inferInstance := by
  let givenTopology : ULift.{0} (TopologicalSpace A) := ⟨inferInstance⟩
  let originalCommRing : ULift.{0} (CommRing A) := ⟨inferInstance⟩
  let originalAlgebra : ULift.{0} (Algebra K A) := ⟨inferInstance⟩
  change givenTopology.down = _
  letI : IsNoetherianRing (TateAlgebra K (Fin n) ⧸ I) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  let hA : IsAffinoidAlgebra K A :=
    ⟨{ n := n, ideal := I, equiv := e }⟩
  let canonicalNormedCommRing : ULift.{0} (NormedCommRing A) :=
    ⟨@residueNormedCommRing K _ _ _ A originalCommRing.down originalAlgebra.down n I e⟩
  let canonicalTopology : ULift.{0} (TopologicalSpace A) :=
    ⟨TopologicalSpace.coinduced
      (e.toAlgHom.comp (Ideal.Quotient.mkₐ K I)) inferInstance⟩
  have hgraph (u : ℕ → A) (x y : A)
      (hux : Tendsto u atTop (@nhds A givenTopology.down x))
      (huy : Tendsto u atTop (@nhds A canonicalTopology.down y)) : y = x := by
    apply sub_eq_zero.mp
    apply eq_zero_of_mem_all_maximal_powers_of_isAffinoidAlgebra K hA
    intro m hm l hl
    let Q := A ⧸ m ^ l
    let q : A →ₐ[K] Q := Ideal.Quotient.mkₐ K (m ^ l)
    letI : Module.Finite K Q :=
      finite_quotient_maximal_pow_of_isAffinoidAlgebra K hA m hm l hl
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (Module.forall_dual_apply_eq_zero_iff K (q (y - x))).mp
    intro ell
    let L : A →ₗ[K] K := ell.comp q.toLinearMap
    have hker : ∀ z, z ∈ m ^ l → L z = 0 := by
      intro z hz
      change ell (q z) = 0
      have hqz : q z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
      rw [hqz, map_zero]
    have hLgiven : @Continuous A K givenTopology.down inferInstance L :=
      by
        have hcont := continuous_linearForm_of_ideal_le_ker K (m ^ l) (L := L) hker
        simpa [givenTopology] using hcont
    have hLcanonical : @Continuous A K canonicalTopology.down inferInstance L := by
      letI : NormedCommRing A := canonicalNormedCommRing.down
      letI : NormedAlgebra K A :=
        @residueNormedAlgebra K _ _ _ A originalCommRing.down originalAlgebra.down n I e
      letI : CompleteSpace A :=
        @residueCompleteSpace K _ _ _ A originalCommRing.down originalAlgebra.down n I e
      letI : IsUltrametricDist A :=
        @residueIsUltrametricDist K _ _ _ A originalCommRing.down originalAlgebra.down n I e
      have hcont := continuous_linearForm_of_ideal_le_ker K (m ^ l) (L := L) hker
      change @Continuous A K (inferInstance : TopologicalSpace A) inferInstance L at hcont
      rw [residueNormedCommRing_topology_eq K A n I e] at hcont
      exact hcont
    have hlimx : Tendsto (L ∘ u) atTop (nhds (L x)) :=
      (@Continuous.tendsto A K givenTopology.down inferInstance L hLgiven x).comp hux
    have hlimy : Tendsto (L ∘ u) atTop (nhds (L y)) :=
      (@Continuous.tendsto A K canonicalTopology.down inferInstance L hLcanonical y).comp huy
    have hLxy : L x = L y := tendsto_nhds_unique hlimx hlimy
    change L (y - x) = 0
    rw [map_sub, hLxy, sub_self]
  let B := CanonicalCopy A
  let copyEquiv : B ≃ A := CanonicalCopy.equiv A
  letI : CommRing B := Equiv.commRing copyEquiv
  letI : Algebra K B := Equiv.algebra K copyEquiv
  let copyAlgEquiv : B ≃ₐ[K] A := Equiv.algEquiv K copyEquiv
  let eB : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] B := e.trans copyAlgEquiv.symm
  letI : NormedCommRing B := residueNormedCommRing K B n I eB
  letI : NormedAlgebra K B := residueNormedAlgebra K B n I eB
  letI : CompleteSpace B := residueCompleteSpace K B n I eB
  letI : IsUltrametricDist B := residueIsUltrametricDist K B n I eB
  let bCanonicalTopology : ULift.{0} (TopologicalSpace B) :=
    ⟨TopologicalSpace.coinduced
      (eB.toAlgHom.comp (Ideal.Quotient.mkₐ K I)) inferInstance⟩
  let upEquiv : A ≃ₐ[K] B := copyAlgEquiv.symm
  let upLinear : A →ₗ[K] B := upEquiv.toLinearEquiv.toLinearMap
  let downLinear : B →ₗ[K] A := upEquiv.symm.toLinearEquiv.toLinearMap
  have hBtop : (inferInstance : TopologicalSpace B) = bCanonicalTopology.down :=
    residueNormedCommRing_topology_eq K B n I eB
  have hupCanonical : @Continuous A B canonicalTopology.down bCanonicalTopology.down upEquiv :=
    continuous_for_affinoidPresentationData K I e I eB upEquiv.toAlgHom
  have hdownCanonical :
      @Continuous B A bCanonicalTopology.down canonicalTopology.down upEquiv.symm :=
    continuous_for_affinoidPresentationData K I eB I e upEquiv.symm.toAlgHom
  have hdownNorm : @Continuous B A inferInstance canonicalTopology.down upEquiv.symm := by
    rwa [hBtop]
  have hforwardNorm : @Continuous A B givenTopology.down inferInstance upEquiv := by
    exact upLinear.continuous_of_seq_closed_graph (by
      intro u x y hux huy
      have hdownLim : Tendsto (upEquiv.symm ∘ upEquiv ∘ u) atTop
          (@nhds A canonicalTopology.down (upEquiv.symm y)) :=
        (@Continuous.tendsto B A inferInstance canonicalTopology.down upEquiv.symm
          hdownNorm y).comp huy
      have hcanonicalLim : Tendsto u atTop
          (@nhds A canonicalTopology.down (upEquiv.symm y)) := by
        simpa [Function.comp_def] using hdownLim
      apply upEquiv.symm.injective
      simpa [upLinear] using hgraph u x (upEquiv.symm y) hux hcanonicalLim)
  have hreverseNorm : @Continuous B A inferInstance givenTopology.down upEquiv.symm := by
    exact downLinear.continuous_of_seq_closed_graph (by
      intro u x y hux huy
      have hcanonicalLim : Tendsto (upEquiv.symm ∘ u) atTop
          (@nhds A canonicalTopology.down (upEquiv.symm x)) :=
        (@Continuous.tendsto B A inferInstance canonicalTopology.down upEquiv.symm
          hdownNorm x).comp hux
      exact (hgraph (upEquiv.symm ∘ u) y (upEquiv.symm x) huy hcanonicalLim).symm)
  have hforward : @Continuous A B givenTopology.down bCanonicalTopology.down upEquiv := by
    rwa [← hBtop]
  have hreverse : @Continuous B A bCanonicalTopology.down givenTopology.down upEquiv.symm := by
    rwa [← hBtop]
  apply le_antisymm
  · have hid : @Continuous A A givenTopology.down canonicalTopology.down id := by
      change @Continuous A A givenTopology.down canonicalTopology.down (fun x ↦ x)
      exact @Continuous.comp A B A givenTopology.down bCanonicalTopology.down canonicalTopology.down
        upEquiv upEquiv.symm hdownCanonical hforward
    simpa [canonicalTopology] using continuous_id_iff_le.mp hid
  · have hid : @Continuous A A canonicalTopology.down givenTopology.down id := by
      change @Continuous A A canonicalTopology.down givenTopology.down (fun x ↦ x)
      exact @Continuous.comp A B A canonicalTopology.down bCanonicalTopology.down givenTopology.down
        upEquiv upEquiv.symm hreverse hupCanonical
    simpa [canonicalTopology] using continuous_id_iff_le.mp hid

/-- Once a Banach realization has the canonical topology, its chosen affinoid presentation is a
continuous surjection and hence induces an equivalent quotient norm. -/
theorem exists_equivalent_quotientNorm_presentation_of_presentation_topology_eq
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (n : ℕ) (I : Ideal (TateAlgebra K (Fin n)))
    (e : (TateAlgebra K (Fin n) ⧸ I) ≃ₐ[K] A)
    (htop : (inferInstance : TopologicalSpace A) =
      TopologicalSpace.coinduced
        (e.toAlgHom.comp (Ideal.Quotient.mkₐ K I)) inferInstance) :
    ∃ (n : ℕ) (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) A),
      IsEquivalentQuotientNorm (π : TateAlgebra K (Fin n) → A) := by
  let f : TateAlgebra K (Fin n) →ₐ[K] A :=
    e.toAlgHom.comp (Ideal.Quotient.mkₐ K I)
  have hcont : Continuous f := by
    have hcanonical : @Continuous (TateAlgebra K (Fin n)) A inferInstance
        (TopologicalSpace.coinduced f inferInstance) f := continuous_coinduced_rng
    rwa [← htop] at hcanonical
  let π : ContinuousAlgHom K (TateAlgebra K (Fin n)) A := { f with cont := hcont }
  exact ⟨n, π, isEquivalentQuotientNorm_of_surjective_continuousAlgHom π
    (e.surjective.comp (Ideal.Quotient.mkₐ_surjective K I))⟩

/-- Canonical-topology automatic continuity transfers to any two Banach realizations whose
topologies have been identified with their canonical affinoid topologies. -/
theorem continuous_of_presentation_topology_eq
    {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [IsUltrametricDist B] {nA nB : ℕ}
    (IA : Ideal (TateAlgebra K (Fin nA)))
    (eA : (TateAlgebra K (Fin nA) ⧸ IA) ≃ₐ[K] A)
    (IB : Ideal (TateAlgebra K (Fin nB)))
    (eB : (TateAlgebra K (Fin nB) ⧸ IB) ≃ₐ[K] B) (f : A →ₐ[K] B)
    (hAtop : (inferInstance : TopologicalSpace A) =
      TopologicalSpace.coinduced
        (eA.toAlgHom.comp (Ideal.Quotient.mkₐ K IA)) inferInstance)
    (hBtop : (inferInstance : TopologicalSpace B) =
      TopologicalSpace.coinduced
        (eB.toAlgHom.comp (Ideal.Quotient.mkₐ K IB)) inferInstance) : Continuous f := by
  have hcanonical := continuous_for_affinoidPresentationData K
    IA eA IB eB f
  rwa [← hAtop, ← hBtop] at hcanonical

end Rigid
