import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Rigid.AffinoidAlgebra.NoetherNormalization

set_option linter.style.header false

/-!
# Maximal spectra of affinoid algebras

This file proves that inverse images of maximal ideals under algebra homomorphisms into affinoid
algebras are maximal. It then packages inverse image as a contravariant map on maximal spectra and
proves its identity and composition laws.

The key input is the affinoid Nullstellensatz. For a maximal ideal `m` of an affinoid algebra `B`,
the residue field `B ⧸ m` is finite-dimensional over the ground field. The quotient
`A ⧸ f⁻¹(m)` embeds into that residue field, so it is also finite-dimensional. Since it is a domain
integral over the ground field, it is a field.
-/

universe u v w z

namespace Rigid

section MaximalSpectrum

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The inverse image of a maximal ideal under an algebra homomorphism into an affinoid algebra is
maximal. -/
theorem Ideal.IsMaximal.comap_algHom_of_isAffinoidAlgebra
    {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) {m : Ideal B} (hm : m.IsMaximal) :
    (m.comap f).IsMaximal := by
  letI : m.IsMaximal := hm
  let q : (A ⧸ m.comap f) →ₐ[K] (B ⧸ m) := Ideal.quotientMapₐ m f le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective
  haveI : Module.Finite K (B ⧸ m) :=
    finite_of_isField_of_isAffinoidAlgebra K (IsAffinoidAlgebra.quotient K hB m)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm)
  haveI : Module.Finite K (A ⧸ m.comap f) :=
    Module.Finite.of_injective q.toLinearMap hq
  letI : (m.comap f).IsPrime := m.comap_isPrime f
  have hfield : IsField (A ⧸ m.comap f) :=
    isField_of_isIntegral_of_isField' (Field.toIsField K)
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient (m.comap f)).mpr hfield

/-- Pullback of maximal ideals along an algebra homomorphism into an affinoid algebra. -/
noncomputable def maximalSpectrumComap {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (_hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B) :
    MaximalSpectrum B → MaximalSpectrum A :=
  fun x ↦ ⟨Ideal.comap f x.asIdeal,
    Ideal.IsMaximal.comap_algHom_of_isAffinoidAlgebra K hB f x.isMaximal⟩

/-- Pullback on maximal spectra has ideal-theoretic inverse image as its underlying ideal. -/
@[simp]
theorem maximalSpectrumComap_asIdeal {A : Type v} {B : Type w}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (x : MaximalSpectrum B) :
    (maximalSpectrumComap K hA hB f x).asIdeal = Ideal.comap f x.asIdeal := rfl

/-- Pullback on maximal spectra sends the identity algebra homomorphism to the identity map. -/
@[simp]
theorem maximalSpectrumComap_id {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    maximalSpectrumComap K hA hA (AlgHom.id K A) = id := by
  funext x
  ext
  simp

/-- Pullback on maximal spectra reverses composition of algebra homomorphisms. -/
@[simp]
theorem maximalSpectrumComap_comp {A : Type v} {B : Type w} {C : Type z}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    maximalSpectrumComap K hA hC (g.comp f) =
      maximalSpectrumComap K hA hB f ∘ maximalSpectrumComap K hB hC g := by
  funext x
  ext
  simp

end MaximalSpectrum

end Rigid
