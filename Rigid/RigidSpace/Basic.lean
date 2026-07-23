import Rigid.AffinoidAlgebra.MaximalSpectrum
import Rigid.RigidSpace.Morphism

set_option linter.style.header false

/-!
# Rigid analytic spaces

The definition here follows Chapters 4 and 5 of
`Introduction_to_Rigid_Geometry(personal_version)_English.tex`.

A rigid analytic space is more than a G-locally ringed space. Its G-topology contains the empty
and whole opens, is local for admissible coverings, is saturated under refinements, and the space
has an admissible affinoid covering. Saturation of coverings is already a theorem of the
Grothendieck topology (`AdmissibleSite.IsCover.of_refinement`), so it is not stored again.

An `AffinoidChart` records the affinoid identification through the coordinate algebra of global
sections, its maximal spectrum, and an affinoid basis for the induced strong G-topology. This
distinguishes the strong topology used to glue rigid spaces from the weak finite-cover topology on
an affinoid basis.
-/

universe k

namespace Rigid

variable (K : Type k) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The local affinoid data on an admissible open `U`.

The coordinate algebra of the chart is `Γ(U, 𝒪)`. Its points are identified with the maximal
spectrum of that algebra. The final field expresses the strong-topology property: every
admissible subopen has an admissible covering by opens with the same two affinoid
characterizations. -/
structure AffinoidChart (X : LocallyGRingedSpace.{k} K)
    (U : X.toAdmissibleSite.Open) where
  sections_isAffinoid :
    IsAffinoidAlgebra K (GRingedSpace.Sections K X.toGRingedSpace U)
  pointsEquiv :
    {x : X.toAdmissibleSite.Point // x ∈ X.toAdmissibleSite.carrier U} ≃
      MaximalSpectrum (GRingedSpace.Sections K X.toGRingedSpace U)
  affinoidBasis :
    ∀ {V : X.toAdmissibleSite.Open}, V ≤ U →
      ∃ (ι : Type k) (W : ι → X.toAdmissibleSite.Open),
        X.toAdmissibleSite.IsCover W V ∧
          ∀ i,
            IsAffinoidAlgebra K (GRingedSpace.Sections K X.toGRingedSpace (W i)) ∧
              Nonempty
                ({x : X.toAdmissibleSite.Point //
                    x ∈ X.toAdmissibleSite.carrier (W i)} ≃
                  MaximalSpectrum
                    (GRingedSpace.Sections K X.toGRingedSpace (W i)))

/-- A rigid analytic space over `K`.

Besides its underlying G-locally ringed space, this stores precisely the additional global
conditions from Definition 5.1 of the reference:

* the empty set (the whole set is already `toAdmissibleSite.top`) is admissible;
* admissibility of a subset is local for an admissible covering;
* there is an admissible covering by affinoid charts.

The third saturation axiom for coverings is derived from the associated Grothendieck topology,
rather than duplicated as structure data. -/
structure RigidSpace extends LocallyGRingedSpace.{k} K where
  empty : toLocallyGRingedSpace.toAdmissibleSite.Open
  carrier_empty :
    toLocallyGRingedSpace.toAdmissibleSite.carrier empty = ∅
  admissibleOpen_local :
    ∀ {ι : Type k}
      {U : ι → toLocallyGRingedSpace.toAdmissibleSite.Open}
      {V : toLocallyGRingedSpace.toAdmissibleSite.Open},
      toLocallyGRingedSpace.toAdmissibleSite.IsCover U V →
        ∀ (S : Set toLocallyGRingedSpace.toAdmissibleSite.Point),
          S ⊆ toLocallyGRingedSpace.toAdmissibleSite.carrier V →
          (∀ i, ∃ W : toLocallyGRingedSpace.toAdmissibleSite.Open,
            toLocallyGRingedSpace.toAdmissibleSite.carrier W =
              S ∩ toLocallyGRingedSpace.toAdmissibleSite.carrier (U i)) →
          ∃ W : toLocallyGRingedSpace.toAdmissibleSite.Open,
            toLocallyGRingedSpace.toAdmissibleSite.carrier W = S
  AtlasIndex : Type k
  atlasOpen : AtlasIndex → toLocallyGRingedSpace.toAdmissibleSite.Open
  atlasChart :
    ∀ i, AffinoidChart K toLocallyGRingedSpace (atlasOpen i)
  atlasCover :
    toLocallyGRingedSpace.toAdmissibleSite.IsCover atlasOpen
      toLocallyGRingedSpace.toAdmissibleSite.top

namespace RigidSpace

variable (X : RigidSpace.{k} K)

/-- The empty admissible open is uniquely determined by its carrier. -/
theorem empty_unique {U : X.toAdmissibleSite.Open}
    (hU : X.toAdmissibleSite.carrier U = ∅) : U = X.empty :=
  X.toAdmissibleSite.toAdmissibleBasis.carrier_injective
    (hU.trans X.carrier_empty.symm)

/-- The selected affinoid charts cover the underlying point set. -/
theorem atlas_iUnion_carrier :
    X.toAdmissibleSite.carrier X.toAdmissibleSite.top =
      ⋃ i, X.toAdmissibleSite.carrier (X.atlasOpen i) :=
  X.atlasCover.iUnion_carrier

/-- The covering-saturation axiom of a rigid G-topology is inherited from its Grothendieck
topology: a covering family with an admissible covering refinement is admissible. -/
theorem cover_of_refinement {ι κ : Type*}
    {U : ι → X.toAdmissibleSite.Open} {W : κ → X.toAdmissibleSite.Open}
    {V : X.toAdmissibleSite.Open} (hUV : ∀ i, U i ≤ V)
    (hW : X.toAdmissibleSite.IsCover W V) (r : κ → ι)
    (hr : ∀ j, W j ≤ U (r j)) :
    X.toAdmissibleSite.IsCover U V :=
  AdmissibleSite.IsCover.of_refinement hUV hW r hr

/-- Morphisms of rigid analytic spaces are morphisms of the underlying G-locally ringed spaces,
as in Definition 5.1(2) of the reference. -/
abbrev Hom (X Y : RigidSpace.{k} K) :=
  LocallyGRingedSpace.Hom K X.toLocallyGRingedSpace Y.toLocallyGRingedSpace

end RigidSpace

end Rigid
