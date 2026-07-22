import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import Rigid.Berkovich.Spectrum

set_option linter.style.header false

/-!
# Relative Berkovich spectra

The relative Berkovich spectrum of a normed `K`-algebra consists of the contractive multiplicative
seminorms whose restriction to `K` is the given norm. This is the point set used by affinoid
Berkovich geometry over a fixed ground field; the unrestricted `BerkovichSpectrum A` remains useful
for ring-theoretic arguments.
-/

open scoped Topology

universe u v w

namespace Rigid

variable (K : Type u) [NormedField K]
variable (A : Type v) [NormedCommRing A] [Algebra K A]

/-- The Berkovich spectrum of `A` relative to `K`: contractive multiplicative seminorms on `A`
whose restriction to `K` is the given norm. -/
structure BerkovichSpectrumOver where
  toBerkovichSpectrum : BerkovichSpectrum A
  map_algebraMap' : ∀ r : K, toBerkovichSpectrum (algebraMap K A r) = ‖r‖

instance berkovichSpectrumOverCoeFun : CoeFun (BerkovichSpectrumOver K A) (fun _ ↦ A → ℝ) :=
  ⟨fun x ↦ x.toBerkovichSpectrum⟩

namespace BerkovichSpectrumOver

/-- Two relative Berkovich points are equal when all their values are equal. -/
@[ext]
theorem ext {x y : BerkovichSpectrumOver K A} (h : ∀ a, x a = y a) : x = y := by
  cases x
  cases y
  congr
  exact BerkovichSpectrum.ext A h

@[simp]
theorem map_algebraMap (x : BerkovichSpectrumOver K A) (r : K) :
    x (algebraMap K A r) = ‖r‖ :=
  x.map_algebraMap' r

@[simp]
theorem map_zero (x : BerkovichSpectrumOver K A) : x 0 = 0 :=
  x.toBerkovichSpectrum.map_zero

@[simp]
theorem map_one (x : BerkovichSpectrumOver K A) : x 1 = 1 :=
  x.toBerkovichSpectrum.map_one

@[simp]
theorem map_neg (x : BerkovichSpectrumOver K A) (a : A) : x (-a) = x a :=
  BerkovichSpectrum.map_neg A x.toBerkovichSpectrum a

@[simp]
theorem map_mul (x : BerkovichSpectrumOver K A) (a b : A) : x (a * b) = x a * x b :=
  BerkovichSpectrum.map_mul A x.toBerkovichSpectrum a b

theorem map_add_le (x : BerkovichSpectrumOver K A) (a b : A) : x (a + b) ≤ x a + x b :=
  BerkovichSpectrum.map_add_le A x.toBerkovichSpectrum a b

theorem nonneg (x : BerkovichSpectrumOver K A) (a : A) : 0 ≤ x a :=
  BerkovichSpectrum.nonneg A x.toBerkovichSpectrum a

theorem le_norm (x : BerkovichSpectrumOver K A) (a : A) : x a ≤ ‖a‖ :=
  BerkovichSpectrum.le_norm A x.toBerkovichSpectrum a

/-- The prime kernel of a relative Berkovich point. -/
def kernel (x : BerkovichSpectrumOver K A) : Ideal A :=
  x.toBerkovichSpectrum.kernel

@[simp]
theorem mem_kernel_iff (x : BerkovichSpectrumOver K A) (a : A) :
    a ∈ x.kernel ↔ x a = 0 :=
  Iff.rfl

theorem kernel_isPrime (x : BerkovichSpectrumOver K A) : x.kernel.IsPrime :=
  x.toBerkovichSpectrum.kernel_isPrime

/-- Pull back a relative point along a norm-nonincreasing algebra homomorphism. -/
def comap {B : Type w} [NormedCommRing B] [Algebra K B] (f : A →ₐ[K] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (x : BerkovichSpectrumOver K B) :
    BerkovichSpectrumOver K A where
  toBerkovichSpectrum := BerkovichSpectrum.comap A f.toRingHom hf x.toBerkovichSpectrum
  map_algebraMap' r := by
    rw [BerkovichSpectrum.comap_apply]
    simp

@[simp]
theorem comap_apply {B : Type w} [NormedCommRing B] [Algebra K B] (f : A →ₐ[K] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (x : BerkovichSpectrumOver K B) (a : A) :
    comap K A f hf x a = x (f a) :=
  rfl

/-- Evaluation after a continuous algebra homomorphism is contractive, even when the homomorphism
itself is only bounded by a constant. Multiplicativity removes the constant after taking powers. -/
theorem eval_continuousAlgHom_le_norm
    (K' : Type u) [NontriviallyNormedField K']
    (A' : Type v) [NormedCommRing A'] [NormedAlgebra K' A']
    {B : Type w} [NormedCommRing B] [NormedAlgebra K' B]
    (f : ContinuousAlgHom K' A' B) (x : BerkovichSpectrumOver K' B) (a : A') :
    x (f a) ≤ ‖a‖ := by
  apply contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm A')
    (nβ := fun b : B ↦ x b)
  · intro b n hn
    exact map_pow x.toBerkovichSpectrum.seminorm b n
  · obtain ⟨M, hM, hf⟩ := SemilinearMapClass.bound_of_continuous f f.continuous
    exact ⟨M, hM, fun a ↦ (le_norm K' B x (f a)).trans (hf a)⟩

/-- Pull back a relative Berkovich point along an arbitrary continuous algebra homomorphism. -/
noncomputable def comapContinuous
    (K' : Type u) [NontriviallyNormedField K']
    (A' : Type v) [NormedCommRing A'] [NormedAlgebra K' A']
    {B : Type w} [NormedCommRing B] [NormedAlgebra K' B]
    (f : ContinuousAlgHom K' A' B) (x : BerkovichSpectrumOver K' B) :
    BerkovichSpectrumOver K' A' where
  toBerkovichSpectrum :=
    { seminorm :=
        { toFun := fun a ↦ x (f a)
          map_zero' := by simp
          add_le' := by
            intro a b
            simpa only [map_add] using map_add_le K' B x (f a) (f b)
          neg' := by simp
          map_one' := by simp
          map_mul' := by simp }
      le_norm' := eval_continuousAlgHom_le_norm K' A' f x }
  map_algebraMap' r := by
    change x (f (algebraMap K' A' r)) = ‖r‖
    calc
      x (f (algebraMap K' A' r)) = x (algebraMap K' B r) :=
        congrArg (fun b : B ↦ x b) (f.commutes r)
      _ = ‖r‖ := x.map_algebraMap' r

@[simp]
theorem comapContinuous_apply
    (K' : Type u) [NontriviallyNormedField K']
    (A' : Type v) [NormedCommRing A'] [NormedAlgebra K' A']
    {B : Type w} [NormedCommRing B] [NormedAlgebra K' B]
    (f : ContinuousAlgHom K' A' B) (x : BerkovichSpectrumOver K' B) (a : A') :
    comapContinuous K' A' f x a = x (f a) :=
  rfl

end BerkovichSpectrumOver

/-- The relative spectrum carries the subspace topology inherited from the unrestricted spectrum. -/
noncomputable instance berkovichSpectrumOverTopologicalSpace :
    TopologicalSpace (BerkovichSpectrumOver K A) :=
  TopologicalSpace.induced BerkovichSpectrumOver.toBerkovichSpectrum inferInstance

namespace BerkovichSpectrumOver

/-- The forgetful map from the relative spectrum to the unrestricted spectrum is an embedding. -/
theorem isEmbedding_toBerkovichSpectrum :
    Topology.IsEmbedding
      (toBerkovichSpectrum : BerkovichSpectrumOver K A → BerkovichSpectrum A) := by
  refine ⟨Topology.IsInducing.induced _, ?_⟩
  intro x y h
  cases x
  cases y
  simp_all

/-- Evaluation at an algebra element is continuous. -/
theorem continuous_eval (a : A) : Continuous fun x : BerkovichSpectrumOver K A ↦ x a :=
  (BerkovichSpectrum.continuous_eval A a).comp (isEmbedding_toBerkovichSpectrum K A).continuous

/-- A map into the relative spectrum is continuous exactly when all evaluations are continuous. -/
theorem continuous_iff_eval {X : Type w} [TopologicalSpace X] {f : X → BerkovichSpectrumOver K A} :
    Continuous f ↔ ∀ a : A, Continuous fun x ↦ f x a := by
  constructor
  · intro hf a
    exact (continuous_eval K A a).comp hf
  · intro hf
    rw [continuous_induced_rng]
    exact (BerkovichSpectrum.continuous_iff_eval A).2 hf

/-- Pullback of relative points is continuous. -/
theorem continuous_comap {B : Type w} [NormedCommRing B] [Algebra K B] (f : A →ₐ[K] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) : Continuous (comap K A f hf) :=
  (continuous_iff_eval K A).2 fun a ↦ continuous_eval K B (f a)

noncomputable instance berkovichSpectrumOverT2Space : T2Space (BerkovichSpectrumOver K A) :=
  (isEmbedding_toBerkovichSpectrum K A).t2Space

private theorem isClosed_range_toBerkovichSpectrum :
    IsClosed (Set.range
      (toBerkovichSpectrum : BerkovichSpectrumOver K A → BerkovichSpectrum A)) := by
  let C : Set (BerkovichSpectrum A) :=
    ⋂ r : K, {x | x (algebraMap K A r) = ‖r‖}
  have hC : IsClosed C := by
    dsimp only [C]
    exact isClosed_iInter fun r ↦
      isClosed_eq (BerkovichSpectrum.continuous_eval A _) continuous_const
  have hrange : Set.range
      (toBerkovichSpectrum : BerkovichSpectrumOver K A → BerkovichSpectrum A) = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp [C]
    · intro hx
      simp only [C, Set.mem_iInter, Set.mem_setOf_eq] at hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rwa [hrange]

/-- The relative Berkovich spectrum is compact. -/
theorem isCompact_univ : IsCompact (Set.univ : Set (BerkovichSpectrumOver K A)) := by
  rw [(isEmbedding_toBerkovichSpectrum K A).isCompact_iff, Set.image_univ]
  exact (isClosed_range_toBerkovichSpectrum K A).isCompact

noncomputable instance berkovichSpectrumOverCompactSpace :
    CompactSpace (BerkovichSpectrumOver K A) :=
  isCompact_univ_iff.mp (isCompact_univ K A)

/-- Relative Berkovich points over a nonarchimedean ring are nonarchimedean. -/
theorem map_add_le_max [IsUltrametricDist A] (x : BerkovichSpectrumOver K A) (a b : A) :
    x (a + b) ≤ max (x a) (x b) :=
  BerkovichSpectrum.map_add_le_max x.toBerkovichSpectrum a b

end BerkovichSpectrumOver

end Rigid
