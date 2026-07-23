import Rigid.RigidSpace.Basic

set_option linter.style.header false

/-!
# Comparator adapters for G-locally ringed spaces

These abbreviations isolate the global comparator-facing vocabulary from the implementation of
sites, sheaves, and stalk colimits.  They are intentionally production declarations in namespace
`Rigid`; the comparator remains in its separate `RigidChallenge` namespace.
-/

universe u

namespace Rigid

namespace ComparatorAdapter

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The production candidate underlying the comparator's global rigid-space interface. -/
abbrev RigidSpace :=
  Rigid.RigidSpace.{u} K

/-- Analytic points of the production G-locally ringed space. -/
abbrev Point (X : RigidSpace K) : Type (u + 1) :=
  ULift.{u + 1, u} X.toAdmissibleSite.Point

/-- Admissible opens of the production G-site. -/
abbrev AdmissibleOpen (X : RigidSpace K) : Type (u + 1) :=
  ULift.{u + 1, u} X.toAdmissibleSite.Open

/-- The point set of an admissible open. -/
abbrev carrier {X : RigidSpace K} (U : AdmissibleOpen K X) : Set (Point K X) :=
  {x | x.down ∈ X.toAdmissibleSite.carrier U.down}

/-- Indexed admissible covers are the covering sieves of the generated Grothendieck topology. -/
abbrev IsCover {X : RigidSpace K} {ι : Type (u + 1)}
    (U : ι → AdmissibleOpen K X) (V : AdmissibleOpen K X) : Prop :=
  X.toAdmissibleSite.IsCover (fun i ↦ (U i).down) V.down

/-- Evaluation of the bundled structure sheaf. -/
abbrev Sections {X : RigidSpace K} (U : AdmissibleOpen K X) : Type u :=
  GRingedSpace.Sections K X.toGRingedSpace U.down

/-- Restriction is the corresponding map of the structure presheaf. -/
def restriction {X : RigidSpace K} {U V : AdmissibleOpen K X} (hUV : carrier K U ⊆ carrier K V) :
    Sections K V →ₐ[K] Sections K U :=
  GRingedSpace.restriction K X.toGRingedSpace
    (X.toAdmissibleSite.le_iff.mpr (fun x hx ↦ by
      have hx' : (ULift.up x : Point K X) ∈ carrier K U := hx
      exact hUV hx'))

/-- Stalks are the neighbourhood colimits constructed in `GRingedSpace`. -/
noncomputable abbrev Stalk (X : RigidSpace K) (x : Point K X) : Type u :=
  GRingedSpace.Stalk K X.toGRingedSpace x.down

/-- Germs are the canonical maps into those colimits. -/
noncomputable def germ {X : RigidSpace K} {U : AdmissibleOpen K X}
    {x : Point K X} (hx : x ∈ carrier K U) :
    Sections K U →ₐ[K] Stalk K X x :=
  GRingedSpace.germ K X.toGRingedSpace hx

/-- Production analytic morphism data, with the stalk map derived rather than stored. -/
abbrev AnalyticMorphismData (X Y : RigidSpace K) :=
  Rigid.RigidSpace.Hom K X Y

end ComparatorAdapter

end Rigid
