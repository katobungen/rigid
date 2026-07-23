import Mathlib.CategoryTheory.Sites.CoverPreserving
import Rigid.RigidSpace.GRingedSpace

set_option linter.style.header false

/-!
# Morphisms of G-ringed spaces

A continuous map carries an inverse-image functor on admissible opens together with mathlib's
`Functor.IsContinuous` site condition.  A morphism of G-ringed spaces adds a morphism from the
target structure sheaf to the continuous pushforward of the source structure sheaf.  Its maps on
stalks are then constructed from the universal property of the neighbourhood colimit.
-/

open CategoryTheory
open CategoryTheory.Limits

universe pX oX pY oY k a v

namespace Rigid

namespace AdmissibleSite

/-- Point-set and inverse-image data for a map of admissible sites. -/
structure MapData (X : AdmissibleSite.{pX, oX}) (Y : AdmissibleSite.{pY, oY}) where
  toFun : X.Point → Y.Point
  preimage : Y.Open → X.Open
  monotone_preimage : Monotone preimage
  carrier_preimage :
    ∀ U, X.carrier (preimage U) = toFun ⁻¹' Y.carrier U

namespace MapData

variable {X : AdmissibleSite.{pX, oX}} {Y : AdmissibleSite.{pY, oY}}

/-- Inverse image as a functor between the inclusion categories of admissible opens. -/
abbrev preimageFunctor (f : MapData X Y) : Y.Open ⥤ X.Open :=
  f.monotone_preimage.functor

end MapData

/-- A continuous map of admissible sites. -/
structure Hom (X : AdmissibleSite.{pX, oX}) (Y : AdmissibleSite.{pY, oY})
    extends MapData X Y where
  continuous :
    Functor.IsContinuous toMapData.preimageFunctor Y.topology X.topology

namespace Hom

variable {X : AdmissibleSite.{pX, oX}} {Y : AdmissibleSite.{pY, oY}}

/-- The mathlib continuous pushforward along the inverse-image functor on opens. -/
noncomputable def pushforwardSheaf (f : Hom X Y) {A : Type a} [Category.{v} A]
    (F : Sheaf X.topology A) : Sheaf Y.topology A := by
  letI := f.continuous
  exact (f.toMapData.preimageFunctor.sheafPushforwardContinuous
    A Y.topology X.topology).obj F

end Hom

end AdmissibleSite

variable (K : Type k) [CommRing K]

namespace GRingedSpace

variable {X Y : GRingedSpace.{k} K}

/-- A morphism of G-ringed spaces: a continuous map of sites and a morphism of structure
sheaves. -/
structure Hom (X Y : GRingedSpace.{k} K) where
  base : AdmissibleSite.Hom X.toAdmissibleSite Y.toAdmissibleSite
  pullback :
    Y.structureSheaf.obj ⟶
      base.toMapData.preimageFunctor.op ⋙ X.structureSheaf.obj

namespace Hom

variable (f : Hom K X Y)

/-- The pullback natural transformation bundled as a morphism of sheaves. -/
noncomputable def pullbackSheafHom :
    Y.structureSheaf ⟶
      f.base.pushforwardSheaf (A := CommAlgCat.{k} K) X.structureSheaf :=
  ObjectProperty.homMk f.pullback

/-- Inverse image sends a neighbourhood of `f(x)` to a neighbourhood of `x`. -/
@[reducible]
def preimageNeighborhood (x : X.toAdmissibleSite.Point)
    (U : Neighborhood K Y (f.base.toMapData.toFun x)) :
    Neighborhood K X x where
  obj := f.base.toMapData.preimage U.obj
  mem := by
    rw [f.base.toMapData.carrier_preimage]
    exact U.mem

/-- Pullback of sections on one admissible open. -/
noncomputable def pullbackApp (U : Y.toAdmissibleSite.Open) :
    Sections K Y U →ₐ[K] Sections K X (f.base.toMapData.preimage U) :=
  (f.pullback.app (Opposite.op U)).hom

/-- The cocone from target neighbourhood sections to the source stalk. -/
noncomputable def stalkCocone (x : X.toAdmissibleSite.Point) :
    Cocone (stalkDiagram K Y (f.base.toMapData.toFun x)) where
  pt := stalkObj K X x
  ι :=
    { app := fun U ↦
        f.pullback.app (Opposite.op U.obj) ≫
          colimit.ι (stalkDiagram K X x) (preimageNeighborhood K f x U)
      naturality := by
        intro U V h
        let h' : preimageNeighborhood K f x U ⟶ preimageNeighborhood K f x V :=
          homOfLE (f.base.toMapData.monotone_preimage (leOfHom h))
        simp only [Functor.const_obj_map]
        change
          Y.structureSheaf.obj.map
                (homOfLE (show V.obj ≤ U.obj from leOfHom h)).op ≫
              f.pullback.app (Opposite.op V.obj) ≫
                colimit.ι (stalkDiagram K X x) (preimageNeighborhood K f x V) =
            f.pullback.app (Opposite.op U.obj) ≫
              colimit.ι (stalkDiagram K X x) (preimageNeighborhood K f x U)
        rw [← Category.assoc]
        rw [f.pullback.naturality]
        rw [Category.assoc]
        have hmap :
            (f.base.toMapData.preimageFunctor.op ⋙ X.structureSheaf.obj).map
                (homOfLE (show V.obj ≤ U.obj from leOfHom h)).op =
              (stalkDiagram K X x).map h' := rfl
        rw [hmap]
        exact congrArg
          (fun q ↦ f.pullback.app (Opposite.op U.obj) ≫ q)
          (colimit.w (stalkDiagram K X x) h') }

/-- The induced map on stalks, obtained from the colimit universal property. -/
noncomputable def stalkMap (x : X.toAdmissibleSite.Point) :
    stalkObj K Y (f.base.toMapData.toFun x) ⟶ stalkObj K X x :=
  colimit.desc (stalkDiagram K Y (f.base.toMapData.toFun x)) (stalkCocone K f x)

/-- The induced stalk map carries the germ of a section to the germ of its pullback. -/
@[simp]
theorem germ_stalkMap {U : Y.toAdmissibleSite.Open} {x : X.toAdmissibleSite.Point}
    (hx : f.base.toMapData.toFun x ∈ Y.toAdmissibleSite.carrier U) :
    (stalkMap K f x).hom.comp (germ K Y hx) =
      (germ K X (by
        rw [f.base.toMapData.carrier_preimage]
        exact hx)).comp (pullbackApp K f U) := by
  exact congrArg CommAlgCat.Hom.hom
    (colimit.ι_desc (stalkCocone K f x) ⟨U, hx⟩)

end Hom

end GRingedSpace

namespace LocallyGRingedSpace

variable {X Y : LocallyGRingedSpace.{k} K}

/-- A morphism of G-locally ringed spaces is a G-ringed-space morphism whose canonically induced
maps on stalks are local. -/
structure Hom (X Y : LocallyGRingedSpace.{k} K) where
  toGRingedSpaceHom : GRingedSpace.Hom K X.toGRingedSpace Y.toGRingedSpace
  local_stalk :
    ∀ x : X.toAdmissibleSite.Point,
      IsLocalHom (GRingedSpace.Hom.stalkMap K toGRingedSpaceHom x).hom

end LocallyGRingedSpace

end Rigid
