import Rigid.AffinoidAlgebra.SpectralPolynomial
import Rigid.AffinoidAlgebra.TateRealization

set_option linter.style.header false

/-!
# The spectral power-boundedness criterion for affinoid domains

This file joins the algebraic/spectral argument of Proposition 4.5.3 with automatic continuity.
The only topological hypothesis is the standard identification of the chosen Banach topology with
the canonical affinoid quotient topology.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- Proposition 4.5.12 for an affinoid domain in a Banach realization carrying its canonical
topology. -/
theorem hasPowerBoundedSpectralCriterion_of_affinoidDomain
    [IsDomain A] (hA : IsAffinoidAlgebra K A)
    (htop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA) :
    HasPowerBoundedSpectralCriterion A :=
  SpectralPolynomial.hasPowerBoundedSpectralCriterion_of_isAffinoidAlgebra_of_isDomain K hA
    fun π ↦ continuous_tateAlgebra_to_affinoid K hA htop π

end Rigid
