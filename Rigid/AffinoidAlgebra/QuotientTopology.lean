import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.MulAction

set_option linter.style.header false

/-!
# The topology coinduced by a surjective homomorphism

An affinoid presentation transports the topology of a Tate algebra to its target along a
surjective algebra homomorphism. This file proves the general facts underlying that transport:
a surjective homomorphism of additive groups is an open quotient map onto the topology it
coinduces, the topology coinduced by a surjective ring homomorphism out of a topological ring is
again a ring topology, and continuity of scalar multiplication descends along a surjective
equivariant homomorphism.
-/

universe u v w

namespace Rigid

variable {R : Type u} {S : Type v} {F : Type w} [TopologicalSpace R]

/-- A surjective additive homomorphism out of a topological additive group is an open quotient
map onto the topology it coinduces. -/
theorem isOpenQuotientMap_coinduced [AddGroup R] [AddGroup S] [ContinuousAdd R]
    [FunLike F R S] [AddMonoidHomClass F R S] (f : F) (hf : Function.Surjective f) :
    letI : TopologicalSpace S := TopologicalSpace.coinduced f inferInstance
    IsOpenQuotientMap f := by
  letI : TopologicalSpace S := TopologicalSpace.coinduced f inferInstance
  exact AddMonoidHom.isOpenQuotientMap_of_isQuotientMap ⟨⟨rfl⟩, hf⟩

/-- The topology coinduced by a surjective ring homomorphism out of a topological ring is a ring
topology. -/
theorem isTopologicalRing_coinduced [Ring R] [Ring S] [IsTopologicalRing R]
    [FunLike F R S] [RingHomClass F R S] (f : F) (hf : Function.Surjective f) :
    letI : TopologicalSpace S := TopologicalSpace.coinduced f inferInstance
    IsTopologicalRing S := by
  letI : TopologicalSpace S := TopologicalSpace.coinduced f inferInstance
  have hoq : IsOpenQuotientMap f := isOpenQuotientMap_coinduced f hf
  refine { continuous_add := ?_, continuous_mul := ?_, continuous_neg := ?_ }
  · rw [← (hoq.prodMap hoq).continuous_comp_iff]
    have h : ((fun p : S × S ↦ p.1 + p.2) ∘ Prod.map f f)
        = fun p : R × R ↦ f (p.1 + p.2) := by
      funext p
      exact (map_add f p.1 p.2).symm
    rw [h]
    exact hoq.continuous.comp continuous_add
  · rw [← (hoq.prodMap hoq).continuous_comp_iff]
    have h : ((fun p : S × S ↦ p.1 * p.2) ∘ Prod.map f f)
        = fun p : R × R ↦ f (p.1 * p.2) := by
      funext p
      exact (map_mul f p.1 p.2).symm
    rw [h]
    exact hoq.continuous.comp continuous_mul
  · rw [← hoq.continuous_comp_iff]
    have h : ((fun y : S ↦ -y) ∘ f) = fun x : R ↦ f (-x) := by
      funext x
      exact (map_neg f x).symm
    rw [h]
    exact hoq.continuous.comp continuous_neg

/-- Continuity of scalar multiplication descends to the topology coinduced by a surjective
equivariant additive homomorphism. -/
theorem continuousSMul_coinduced {G : Type*} [TopologicalSpace G]
    [AddGroup R] [AddGroup S] [ContinuousAdd R] [SMul G R] [SMul G S] [ContinuousSMul G R]
    [FunLike F R S] [AddMonoidHomClass F R S] (f : F) (hf : Function.Surjective f)
    (hsmul : ∀ (c : G) (x : R), f (c • x) = c • f x) :
    letI : TopologicalSpace S := TopologicalSpace.coinduced f inferInstance
    ContinuousSMul G S := by
  letI : TopologicalSpace S := TopologicalSpace.coinduced f inferInstance
  have hoq : IsOpenQuotientMap f := isOpenQuotientMap_coinduced f hf
  refine ⟨?_⟩
  rw [← (IsOpenQuotientMap.id.prodMap hoq).continuous_comp_iff]
  have h : ((fun p : G × S ↦ p.1 • p.2) ∘ Prod.map id f)
      = fun p : G × R ↦ f (p.1 • p.2) := by
    funext p
    exact (hsmul p.1 p.2).symm
  rw [h]
  exact hoq.continuous.comp continuous_smul

end Rigid
