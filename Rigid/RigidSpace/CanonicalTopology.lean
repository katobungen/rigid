import Rigid.RigidSpace.AdmissibleSite

set_option linter.style.header false
set_option linter.checkUnivs false

/-!
# The canonical point-cover G-topology

This file constructs the canonical pretopology in which every set-theoretic covering by
admissible opens is admissible. The construction is separate from `AdmissibleSite` because rigid
affinoid spaces generally use a stricter choice of admissible coverings.
-/

open CategoryTheory
open CategoryTheory.Limits

universe p o

namespace Rigid

namespace AdmissibleBasis

variable (B : AdmissibleBasis.{p, o})

/-- The precoverage consisting of all presieves whose domains cover the underlying point set. -/
def pointCoverPrecoverage : Precoverage B.Open where
  coverings U :=
    {R | ∀ x ∈ B.carrier U, ∃ (V : B.Open) (f : V ⟶ U), R f ∧ x ∈ B.carrier V}

instance pointCoverPrecoverage_hasIsos :
    B.pointCoverPrecoverage.HasIsos where
  mem_coverings_of_isIso {U V} f _ x hx := by
    refine ⟨U, f, Presieve.singleton_self f, ?_⟩
    exact B.carrier_mono (leOfHom (inv f)) hx

instance pointCoverPrecoverage_isStableUnderBaseChange :
    B.pointCoverPrecoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι S U} f hR {V} g {P} p₁ p₂ hp x hxV := by
    have hxS : x ∈ B.carrier S := B.carrier_mono (leOfHom g) hxV
    obtain ⟨_, _, ⟨i⟩, hxUi⟩ := hR x hxS
    let T := B.inter V (U i)
    let q₁ : T ⟶ V := homOfLE (B.inter_le_left V (U i))
    let q₂ : T ⟶ U i := homOfLE (B.inter_le_right V (U i))
    let l : T ⟶ P i := (hp i).lift q₁ q₂ (Subsingleton.elim _ _)
    refine ⟨P i, p₁ i, Presieve.ofArrows.mk i, B.carrier_mono (leOfHom l) ?_⟩
    rw [B.carrier_inter]
    exact ⟨hxV, hxUi⟩

instance pointCoverPrecoverage_isStableUnderComposition :
    B.pointCoverPrecoverage.IsStableUnderComposition where
  comp_mem_coverings {ι S U} f hf {σ W} g hg x hxS := by
    obtain ⟨_, _, ⟨i⟩, hxUi⟩ := hf x hxS
    obtain ⟨_, _, ⟨j⟩, hxWij⟩ := hg i x hxUi
    refine ⟨W i j, g i j ≫ f i, ?_, hxWij⟩
    exact Presieve.ofArrows.mk (Sigma.mk i j)

/-- The pretopology of all point-set covers. Its three axioms are supplied by the
`Precoverage` instances above. -/
def pointCoverPretopology : Pretopology B.Open :=
  B.pointCoverPrecoverage.toPretopology

/-- The canonical G-site associated with an admissible basis: all point-set covering families are
admissible. -/
def toCanonicalSite : AdmissibleSite.{p, o} where
  toAdmissibleBasis := B
  pretopology := B.pointCoverPretopology
  precover_covers := fun h ↦ h

end AdmissibleBasis

end Rigid
