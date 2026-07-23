import Rigid.AffinoidAlgebra.MaximalSpectrum

set_option linter.style.header false

/-!
# Point models for rigid spaces

This file supplies the point-set part of the global rigid-space interface.  An affinoid algebra is
represented through its chosen finite Tate-algebra presentation, whose quotient lives in the
ground-field universe.  Its rigid points are the maximal ideals of that quotient; transport along
the presentation equivalence identifies them with the maximal ideals of the original algebra.
-/

universe u v

namespace Rigid

/-- The point-set data underlying a rigid space.  Further global geometric structure is supplied
by the global rigid-space interface. -/
structure RigidSpace where
  Point : Type u

namespace RigidSpace

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The rigid-space point model associated to a strict affinoid algebra. -/
noncomputable def ofAffinoid {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) : RigidSpace where
  Point :=
    MaximalSpectrum
      (TateAlgebra K (Fin hA.presentation.n) ⧸ hA.presentation.ideal)

/-- The points in the affinoid point model are canonically the maximal ideals of its coordinate
algebra. -/
noncomputable def pointsOfAffinoidEquiv {A : Type v} [CommRing A] [Algebra K A]
    (hA : IsAffinoidAlgebra K A) :
    (ofAffinoid K hA).Point ≃ MaximalSpectrum A :=
  maximalSpectrumEquiv hA.presentation.equiv.toRingEquiv

end RigidSpace

end Rigid
