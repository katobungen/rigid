import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Rigid.AffinoidAlgebra.ClosedIdeals
import Rigid.AffinoidAlgebra.SpectralPolynomial
import Rigid.AffinoidAlgebra.TateRealization

set_option linter.style.header false

/-!
# Spectral relations over one affinoid presentation

For each minimal-prime quotient, Noether normalization is performed inside the same surjective
Tate presentation.  The resulting factor is isometric, so its sharp polynomial can be mapped back
to the presentation without changing its spectral value.  Thus all component relations have
coefficients in one Gauss unit ball and can be multiplied before the nilpotent error is removed.
This supplies the coefficient-comparison step suppressed in the printed proof of Mattias,
Proposition 4.5.3.
-/

open scoped Polynomial

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- Affinoid algebras are Noetherian, recorded in the production namespace. -/
theorem isNoetherianRing_of_affinoidAlgebra (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing A := by
  let P := hA.presentation
  haveI : IsNoetherianRing
      (TateAlgebra K (Fin P.n) ⧸ P.ideal) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk P.ideal)
      Ideal.Quotient.mk_surjective
  exact isNoetherianRing_of_ringEquiv _ P.equiv.toRingEquiv

namespace SpectralPolynomial

/-- A minimal component has a Gauss-unit-ball relation over the original affinoid presentation,
not merely over a separately chosen normalization of the component. -/
theorem hasUnitBallRelation_minimalPrime_of_affinoidPresentation
    [Nontrivial A] (hA : IsAffinoidAlgebra K A)
    (htop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA)
    (c : A) (hc : BerkovichSpectrum.spectralRadius A c ≤ 1)
    (q : Ideal A) (hq : q ∈ minimalPrimes A) :
    HasUnitBallRelation K hA.presentation.n
      ((Ideal.Quotient.mk q).comp hA.presentation.toAlgHom.toRingHom)
      (Ideal.Quotient.mk q c) := by
  letI : IsClosed (q : Set A) :=
    isClosed_ideal_of_topology_eq_affinoidTopology K A hA htop q
  letI : q.IsPrime := hq.isPrime
  letI : IsUltrametricDist (A ⧸ q) := idealQuotientIsUltrametricDist q
  let φ : ContinuousAlgHom K (TateAlgebra K (Fin hA.presentation.n)) A :=
    { toAlgHom := hA.presentation.toAlgHom
      cont := continuous_tateAlgebra_to_affinoid K hA htop hA.presentation.toAlgHom }
  let φq : ContinuousAlgHom K (TateAlgebra K (Fin hA.presentation.n)) (A ⧸ q) :=
    (idealQuotientMk K q).comp φ
  have hφq : Function.Surjective φq :=
    Ideal.Quotient.mk_surjective.comp hA.presentation.toAlgHom_surjective
  obtain ⟨d, j, hjnorm, hιinj, hιfinite⟩ :=
    TateAlgebra.exists_isometric_normalizationFactor_of_surjective K
      hA.presentation.n φq.toAlgHom hφq
  have hjcont : Continuous j :=
    (AddMonoidHomClass.isometry_of_norm j hjnorm).continuous
  let jcont : ContinuousAlgHom K (TateAlgebra K (Fin d))
      (TateAlgebra K (Fin hA.presentation.n)) :=
    { toAlgHom := j, cont := hjcont }
  let ι : ContinuousAlgHom K (TateAlgebra K (Fin d)) (A ⧸ q) :=
    φq.comp jcont
  obtain ⟨P, hPmonic, hPeval, hPsharp⟩ :=
    hasSharpSpectralPolynomial_of_integrallyClosedNormalization K ι.toAlgHom
      hιinj hιfinite ι.continuous (Ideal.Quotient.mk q c)
  let Q : (TateAlgebra K (Fin hA.presentation.n))[X] := P.map j.toRingHom
  have hQmonic : Q.Monic := hPmonic.map j.toRingHom
  have hQeval :
      Polynomial.eval₂ φq.toRingHom (Ideal.Quotient.mk q c) Q = 0 := by
    change Polynomial.eval₂ φq.toRingHom (Ideal.Quotient.mk q c)
      (P.map j.toRingHom) = 0
    rw [Polynomial.eval₂_map]
    have hmapι : φq.toRingHom.comp j.toRingHom = ι.toRingHom := by
      ext a
      rfl
    rw [hmapι]
    exact hPeval
  have hQsharp :
      BerkovichSpectrum.spectralRadius (A ⧸ q) (Ideal.Quotient.mk q c) =
        spectralValue Q := by
    rw [hPsharp]
    exact (spectralValue_map_eq j.toRingHom hjnorm hPmonic).symm
  have hcq :
      BerkovichSpectrum.spectralRadius (A ⧸ q) (Ideal.Quotient.mk q c) ≤ 1 :=
    (BerkovichSpectrumOver.spectralRadius_map_le K A (idealQuotientMk K q) c).trans hc
  have hrelation : HasUnitBallRelation K hA.presentation.n φq.toRingHom
      (Ideal.Quotient.mk q c) :=
    hasUnitBallRelation_of_hasSharpSpectralPolynomial K φq.toAlgHom
      (Ideal.Quotient.mk q c) hcq
      ⟨Q, hQmonic, hQeval, hQsharp⟩
  have hmap :
      φq.toRingHom =
        (Ideal.Quotient.mk q).comp hA.presentation.toAlgHom.toRingHom := by
    ext a
    rfl
  rw [hmap] at hrelation
  exact hrelation

/-- Proposition 4.5.12 for an arbitrary affinoid algebra in a Banach realization carrying its
canonical topology. -/
theorem hasPowerBoundedSpectralCriterion_of_affinoidAlgebra
    [Nontrivial A] (hA : IsAffinoidAlgebra K A)
    (htop : (inferInstance : TopologicalSpace A) = affinoidTopology K A hA) :
    HasPowerBoundedSpectralCriterion A := by
  letI : IsNoetherianRing A := isNoetherianRing_of_affinoidAlgebra K hA
  let φ : ContinuousAlgHom K (TateAlgebra K (Fin hA.presentation.n)) A :=
    { toAlgHom := hA.presentation.toAlgHom
      cont := continuous_tateAlgebra_to_affinoid K hA htop hA.presentation.toAlgHom }
  apply hasPowerBoundedSpectralCriterion_of_minimalPrime_relations K φ
  intro c hc q hq
  simpa [φ] using
    hasUnitBallRelation_minimalPrime_of_affinoidPresentation K hA htop c hc q hq

/-- Presentation-level form of the general spectral criterion.  This avoids any dependence on
the particular presentation chosen from an `IsAffinoidAlgebra` witness. -/
theorem hasPowerBoundedSpectralCriterion_of_affinoidPresentation
    [Nontrivial A] (P : AffinoidPresentation K A)
    (htop : (inferInstance : TopologicalSpace A) = P.residueTopology) :
    HasPowerBoundedSpectralCriterion A := by
  let hA : IsAffinoidAlgebra K A := ⟨P⟩
  have hchosen :
      hA.presentation.residueTopology = P.residueTopology :=
    residueTopology_eq_for_affinoidPresentationData K
      hA.presentation.ideal hA.presentation.equiv P.ideal P.equiv
  have hcanonical :
      (inferInstance : TopologicalSpace A) = affinoidTopology K A hA := by
    change (inferInstance : TopologicalSpace A) = hA.presentation.residueTopology
    exact htop.trans hchosen.symm
  exact hasPowerBoundedSpectralCriterion_of_affinoidAlgebra K hA hcanonical

end SpectralPolynomial

end Rigid
