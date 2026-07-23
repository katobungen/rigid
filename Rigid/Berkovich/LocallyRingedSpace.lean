import Mathlib.AlgebraicGeometry.Spec

set_option linter.style.header false

/-!
# The ordinary locally ringed core of a Berkovich space

The ordinary locally ringed layer of a Berkovich space over `K` is a locally ringed space equipped
with a structure morphism to `Spec K`. We express this directly as a mathlib over category, using a
universe lift of `K` so that point spaces and section rings may live one universe above the ground
field. The structure sheaf, stalks, germ maps, locally ringed morphisms, and category structure then
come from mathlib.

This core does not include the norm on `K`, analytic domains, an admissible G-topology, or an
affinoid atlas. Those belong to the later analytic-space layer.
-/

open CategoryTheory
open Opposite
open TopologicalSpace

universe u

namespace Rigid.Berkovich

/-- The ordinary locally ringed-space data of a Berkovich space over `K`.

An object consists of a locally ringed space in universe `u + 1` and a structure morphism to the
spectrum of the canonical universe lift of `K`. Analytic data added later can project to this core
without storing separate section, stalk, or germ data. -/
abbrev LocallyRingedCore (K : Type u) [CommRing K] :=
  Over (AlgebraicGeometry.Spec.locallyRingedSpaceObj
    (CommRingCat.of (ULift.{u + 1, u} K)))

namespace LocallyRingedCore

variable {K : Type u} [CommRing K]

/-- Forget the structure morphism to `Spec K` and retain the underlying locally ringed space. -/
noncomputable def locallyRingedSpaceFunctor :
    LocallyRingedCore K ⥤ AlgebraicGeometry.LocallyRingedSpace.{u + 1} :=
  Over.forget _

noncomputable instance locallyRingedSpaceFunctorFaithful :
    (locallyRingedSpaceFunctor (K := K)).Faithful where
  map_injective h := Over.OverMorphism.ext h

/-- The functor assigning the underlying topological point space to a locally ringed core. -/
noncomputable def pointFunctor : LocallyRingedCore K ⥤ TopCat.{u + 1} :=
  locallyRingedSpaceFunctor ⋙ AlgebraicGeometry.LocallyRingedSpace.forgetToTop

/-- The points of an ordinary locally ringed core. -/
abbrev Point (X : LocallyRingedCore K) : Type (u + 1) := X.left

/-- The core point topology is the topology underlying its locally ringed space. -/
noncomputable def pointHomeomorph (X : LocallyRingedCore K) :
    Point X ≃ₜ X.left.toTopCat :=
  Homeomorph.refl _

namespace Point

/-- The point map induced by a morphism of ordinary locally ringed cores. -/
noncomputable def map {X Y : LocallyRingedCore K} (f : X ⟶ Y) : Point X → Point Y :=
  (locallyRingedSpaceFunctor.map f).toHom.base

/-- Point maps induced by locally ringed morphisms are continuous. -/
theorem continuous_map {X Y : LocallyRingedCore K} (f : X ⟶ Y) : Continuous (map f) :=
  ((locallyRingedSpaceFunctor.map f).toHom.base).hom.continuous

@[simp]
theorem map_id (X : LocallyRingedCore K) : map (𝟙 X) = id :=
  rfl

@[simp]
theorem map_comp {X Y Z : LocallyRingedCore K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map g ∘ map f :=
  rfl

end Point

/-- Naturality of the point identification with the underlying locally ringed space. -/
@[simp]
theorem pointHomeomorph_naturality {X Y : LocallyRingedCore K} (f : X ⟶ Y)
    (x : Point X) :
    pointHomeomorph Y (Point.map f x) =
      (locallyRingedSpaceFunctor.map f).toHom.base (pointHomeomorph X x) :=
  rfl

namespace StructureSheaf

/-- Sections on an ordinary open, obtained from the mathlib structure sheaf. -/
abbrev Sections (X : LocallyRingedCore K) (U : Opens (Point X)) : Type (u + 1) :=
  X.left.presheaf.obj (op U)

/-- The stalk at a point, obtained from the mathlib structure sheaf. -/
noncomputable abbrev Stalk (X : LocallyRingedCore K) (x : Point X) : Type (u + 1) :=
  X.left.presheaf.stalk x

instance stalkIsLocalRing (X : LocallyRingedCore K) (x : Point X) :
    IsLocalRing (Stalk X x) :=
  inferInstance

/-- The canonical germ map supplied by the mathlib structure sheaf. -/
noncomputable def germ (X : LocallyRingedCore K) (U : Opens (Point X))
    (x : Point X) (hx : x ∈ U) : Sections X U →+* Stalk X x :=
  (X.left.presheaf.germ U x hx).hom

end StructureSheaf

end LocallyRingedCore

end Rigid.Berkovich
