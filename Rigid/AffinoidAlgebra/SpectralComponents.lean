import Rigid.AffinoidAlgebra.ClosedIdeals
import Rigid.Berkovich.Quotient
import Rigid.Berkovich.SpectralRadius

set_option linter.style.header false

/-!
# Spectral radii on minimal-prime components

The spectral radius of an element of an affinoid algebra is attained on one of its
minimal-prime quotients.  This is the elementwise form of Mattias, Proposition 4.5.1: the map to
the product of the irreducible components is an isometry for the spectral seminorm.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A] [Nontrivial A]

/-- For every element, some minimal-prime quotient preserves its spectral radius. -/
theorem exists_minimalPrime_spectralRadius_eq_quotient
    (hA : IsAffinoidAlgebra K A)
    (htop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA)
    (a : A) :
    ∃ q ∈ minimalPrimes A,
      letI : IsClosed (q : Set A) :=
        isClosed_ideal_of_topology_eq_affinoidTopology K A hA htop q
      BerkovichSpectrum.spectralRadius (A ⧸ q) (Ideal.Quotient.mk q a) =
        BerkovichSpectrum.spectralRadius A a := by
  obtain ⟨x, hx⟩ :=
    BerkovichSpectrumOver.exists_apply_eq_spectralRadius K A a
  letI : x.kernel.IsPrime := x.kernel_isPrime
  obtain ⟨q, hq, hqx⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := x.kernel) bot_le
  refine ⟨q, hq, ?_⟩
  letI : IsClosed (q : Set A) :=
    isClosed_ideal_of_topology_eq_affinoidTopology K A hA htop q
  letI : q.IsPrime := hq.isPrime
  let y : BerkovichSpectrumOver K (A ⧸ q) :=
    BerkovichSpectrumOver.descendQuotient K A x q hqx
  apply le_antisymm
  · exact BerkovichSpectrumOver.spectralRadius_map_le K A
      (idealQuotientMk K q) a
  · rw [← hx]
    exact BerkovichSpectrumOver.le_spectralRadius K (A ⧸ q) y
      (Ideal.Quotient.mk q a)

end Rigid
