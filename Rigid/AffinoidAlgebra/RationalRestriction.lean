import Rigid.AffinoidAlgebra.PowerBounded
import Rigid.AffinoidAlgebra.RationalLocalization

set_option linter.style.header false

/-!
# Maps out of rational localizations

This file isolates the algebraic part of restriction along an inclusion of rational domains.  If
the target makes the denominator invertible and all quotient coordinates power-bounded, the
universal property gives a canonical map from the rational localization.  Its uniqueness only
uses invertibility of the denominator.
-/

universe u v w

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace RationalLocalization

variable {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [IsUltrametricDist B]

/-- The quotient coordinate `fᵢ / g` in a target in which the image of `g` is a unit. -/
noncomputable def quotientCoordinate {n : ℕ} {g : A} {f : Fin n → A}
    (φ : ContinuousAlgHom K A B) (hg : IsUnit (φ g)) (i : Fin n) : B :=
  (↑hg.unit⁻¹ : B) * φ (f i)

omit [CompleteSpace K] [IsUltrametricDist K] [CompleteSpace A] [IsUltrametricDist A]
  [CompleteSpace B] [IsUltrametricDist B] in
@[simp]
theorem denominator_mul_quotientCoordinate {n : ℕ} {g : A} {f : Fin n → A}
    (φ : ContinuousAlgHom K A B) (hg : IsUnit (φ g)) (i : Fin n) :
    φ g * quotientCoordinate K A (f := f) φ hg i = φ (f i) := by
  change φ g * ((↑hg.unit⁻¹ : B) * φ (f i)) = φ (f i)
  calc
    _ = (↑hg.unit : B) * ((↑hg.unit⁻¹ : B) * φ (f i)) := by
      rw [IsUnit.unit_spec hg]
    _ = φ (f i) := by rw [← mul_assoc]; simp

/-- The canonical map from a rational localization to a target in which its denominator is a unit
and its quotient coordinates are power-bounded. -/
noncomputable def liftOfIsUnit {n : ℕ} {g : A} {f : Fin n → A}
    (φ : ContinuousAlgHom K A B) (hg : IsUnit (φ g))
    (hbounded : ∀ i : Fin n, IsPowerBounded (quotientCoordinate K A (f := f) φ hg i)) :
    ContinuousAlgHom K (RationalLocalization K A n g f) B :=
  lift K A n g f φ (quotientCoordinate K A (f := f) φ hg) hbounded
    (denominator_mul_quotientCoordinate K A (f := f) φ hg)

@[simp]
theorem liftOfIsUnit_comp_baseMap {n : ℕ} {g : A} {f : Fin n → A}
    (φ : ContinuousAlgHom K A B) (hg : IsUnit (φ g))
    (hbounded : ∀ i : Fin n, IsPowerBounded (quotientCoordinate K A (f := f) φ hg i)) :
    (liftOfIsUnit K A φ hg hbounded).comp (baseMap K A n g f) = φ :=
  lift_comp_baseMap K A n g f φ _ hbounded _

@[simp]
theorem liftOfIsUnit_coordinate {n : ℕ} {g : A} {f : Fin n → A}
    (φ : ContinuousAlgHom K A B) (hg : IsUnit (φ g))
    (hbounded : ∀ i : Fin n, IsPowerBounded (quotientCoordinate K A (f := f) φ hg i))
    (i : Fin n) :
    liftOfIsUnit K A φ hg hbounded (coordinate K A n g f i) =
      quotientCoordinate K A (f := f) φ hg i :=
  lift_coordinate K A n g f φ _ hbounded _ i

omit [CompleteSpace B] [IsUltrametricDist B] in
/-- Maps out of a rational localization are determined by their restriction to the base whenever
the image of the denominator is a unit. -/
theorem hom_ext_of_isUnit {n : ℕ} {g : A} {f : Fin n → A}
    (φ ψ : ContinuousAlgHom K (RationalLocalization K A n g f) B)
    (hg : IsUnit (φ (baseMap K A n g f g)))
    (hbase : φ.comp (baseMap K A n g f) = ψ.comp (baseMap K A n g f)) : φ = ψ := by
  apply hom_ext K A n g f φ ψ hbase
  intro i
  apply hg.mul_left_cancel
  have hbase_g : φ (baseMap K A n g f g) = ψ (baseMap K A n g f g) :=
    congrArg (fun q : ContinuousAlgHom K A B ↦ q g) hbase
  have hbase_f : φ (baseMap K A n g f (f i)) = ψ (baseMap K A n g f (f i)) :=
    congrArg (fun q : ContinuousAlgHom K A B ↦ q (f i)) hbase
  have hφ := congrArg φ (baseMap_denominator_mul_coordinate K A n g f i)
  have hψ := congrArg ψ (baseMap_denominator_mul_coordinate K A n g f i)
  calc
    φ (baseMap K A n g f g) * φ (coordinate K A n g f i) =
        φ (baseMap K A n g f (f i)) := by simpa only [map_mul] using hφ
    _ = ψ (baseMap K A n g f (f i)) := hbase_f
    _ = ψ (baseMap K A n g f g) * ψ (coordinate K A n g f i) := by
      simpa only [map_mul] using hψ.symm
    _ = φ (baseMap K A n g f g) * ψ (coordinate K A n g f i) := by rw [hbase_g]

end RationalLocalization

end Rigid
