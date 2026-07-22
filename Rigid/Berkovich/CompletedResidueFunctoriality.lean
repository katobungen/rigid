import Rigid.Berkovich.CompletedResidue

set_option linter.style.header false

/-!
# Functoriality of completed residue fields

An algebra homomorphism `f : A →ₐ[K] B` relating Berkovich points `x` and `y` induces injective
maps from the residue domain of `x` to that of `y`, from the residue fraction field of `x` to that
of `y`, and from the completed residue field of `x` to that of `y`. The latter two maps are
isometries. This file proves compatibility with evaluation and the identity and composition laws.

The construction is stated for points satisfying `x a = y (f a)`. Norm-nonincreasing pullback is
the main special case, packaged as `completedResidueFieldComap`.
-/

open scoped NNReal

universe u v w z

namespace Rigid.BerkovichSpectrumOver

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [NormedCommRing A] [Algebra K A] [IsUltrametricDist A]
variable {B : Type w} [NormedCommRing B] [Algebra K B] [IsUltrametricDist B]
variable {C : Type z} [NormedCommRing C] [Algebra K C] [IsUltrametricDist C]

omit [IsUltrametricDist A] [IsUltrametricDist B] in
/-- Kernels pull back when two Berkovich points are related by an algebra homomorphism. -/
theorem kernel_eq_comap_of_map_eq (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : x.kernel = Ideal.comap f y.kernel := by
  ext a
  rw [mem_kernel_iff, Ideal.mem_comap, mem_kernel_iff, hxy]

/-- The map between residue domains induced by a map relating two Berkovich points. -/
noncomputable def residueDomainMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : ResidueDomain x →ₐ[K] ResidueDomain y :=
  Ideal.quotientMapₐ y.kernel f (kernel_eq_comap_of_map_eq f x y hxy).le

omit [IsUltrametricDist A] [IsUltrametricDist B] in
@[simp]
theorem residueDomainMap_mk (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (a : A) :
    residueDomainMap f x y hxy (Ideal.Quotient.mk x.kernel a) =
      Ideal.Quotient.mk y.kernel (f a) := rfl

omit [IsUltrametricDist A] [IsUltrametricDist B] in
/-- The induced map between residue domains is injective. -/
theorem residueDomainMap_injective (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : Function.Injective (residueDomainMap f x y hxy) := by
  exact Ideal.quotientMap_injective' (H := (kernel_eq_comap_of_map_eq f x y hxy).le)
    (kernel_eq_comap_of_map_eq f x y hxy).ge

/-- The map between residue fraction fields induced by a map relating two Berkovich points. -/
noncomputable def residueFractionFieldMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : ResidueFractionField x →+* ResidueFractionField y := by
  let g : ResidueDomain x →+* ResidueFractionField y :=
    (algebraMap (ResidueDomain y) (ResidueFractionField y)).comp
      (residueDomainMap f x y hxy).toRingHom
  exact IsFractionRing.lift (g := g)
    ((IsFractionRing.injective (ResidueDomain y) (ResidueFractionField y)).comp
      (residueDomainMap_injective f x y hxy) : Function.Injective g)

omit [IsUltrametricDist A] [IsUltrametricDist B] in
@[simp]
theorem residueFractionFieldMap_algebraMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (a : ResidueDomain x) :
    residueFractionFieldMap f x y hxy (algebraMap (ResidueDomain x) (ResidueFractionField x) a) =
      algebraMap (ResidueDomain y) (ResidueFractionField y) (residueDomainMap f x y hxy a) := by
  simp [residueFractionFieldMap]

@[simp]
theorem quotientValuation_residueDomainMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (a : ResidueDomain x) :
    quotientValuation y (residueDomainMap f x y hxy a) = quotientValuation x a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply NNReal.eq
  exact (hxy a).symm

@[simp]
theorem fractionValuation_residueFractionFieldMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (r : ResidueFractionField x) :
    fractionValuation y (residueFractionFieldMap f x y hxy r) = fractionValuation x r := by
  obtain ⟨⟨a, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (ResidueDomain x)) r
  simp [residueFractionFieldMap, fractionValuation]

/-- The induced map between residue fraction fields preserves norms. -/
@[simp]
theorem norm_residueFractionFieldMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (r : ResidueFractionField x) :
    ‖residueFractionFieldMap f x y hxy r‖ = ‖r‖ := by
  change (fractionValuation y (residueFractionFieldMap f x y hxy r) : ℝ) =
    (fractionValuation x r : ℝ)
  rw [fractionValuation_residueFractionFieldMap]

/-- The induced map between residue fraction fields is an isometry. -/
theorem isometry_residueFractionFieldMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : Isometry (residueFractionFieldMap f x y hxy) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_residueFractionFieldMap f x y hxy)

/-- The map between completed residue fields induced by a map relating two Berkovich points. -/
noncomputable def completedResidueFieldMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : CompletedResidueField x →+* CompletedResidueField y :=
  (isometry_residueFractionFieldMap f x y hxy).mapRingHom

@[simp]
theorem completedResidueFieldMap_coe (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (r : ResidueFractionField x) :
    completedResidueFieldMap f x y hxy (r : CompletedResidueField x) =
      (residueFractionFieldMap f x y hxy r : CompletedResidueField y) :=
  (isometry_residueFractionFieldMap f x y hxy).mapRingHom_coe r

/-- The induced map between completed residue fields is an isometry. -/
theorem isometry_completedResidueFieldMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : Isometry (completedResidueFieldMap f x y hxy) :=
  (isometry_residueFractionFieldMap f x y hxy).isometry_mapRingHom

omit [IsUltrametricDist A] [IsUltrametricDist B] in
@[simp]
theorem residueFractionFieldMap_residueFractionMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (a : A) :
    residueFractionFieldMap f x y hxy (residueFractionMap x a) = residueFractionMap y (f a) := by
  simp [residueFractionMap]

/-- The induced map on completed residue fields is compatible with evaluation. -/
@[simp]
theorem completedResidueFieldMap_completedResidueMap (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (a : A) :
    completedResidueFieldMap f x y hxy (completedResidueMap x a) =
      completedResidueMap y (f a) := by
  change completedResidueFieldMap f x y hxy
      (residueFractionMap x a : CompletedResidueField x) =
    (residueFractionMap y (f a) : CompletedResidueField y)
  rw [completedResidueFieldMap_coe, residueFractionFieldMap_residueFractionMap]

/-- The induced map on completed residue fields as a `K`-algebra homomorphism. -/
noncomputable def completedResidueFieldAlgHom (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : CompletedResidueField x →ₐ[K] CompletedResidueField y where
  __ := completedResidueFieldMap f x y hxy
  commutes' r := by
    change completedResidueFieldMap f x y hxy (completedResidueMap x (algebraMap K A r)) =
      completedResidueMap y (algebraMap K B r)
    rw [completedResidueFieldMap_completedResidueMap, f.commutes]

@[simp]
theorem completedResidueFieldAlgHom_apply (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) (r : CompletedResidueField x) :
    completedResidueFieldAlgHom f x y hxy r = completedResidueFieldMap f x y hxy r := rfl

/-- The induced algebra homomorphism is an isometry. -/
theorem isometry_completedResidueFieldAlgHom (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : Isometry (completedResidueFieldAlgHom f x y hxy) :=
  isometry_completedResidueFieldMap f x y hxy

/-- The induced algebra homomorphism is injective. -/
theorem completedResidueFieldAlgHom_injective (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) : Function.Injective (completedResidueFieldAlgHom f x y hxy) :=
  (isometry_completedResidueFieldAlgHom f x y hxy).injective

/-- Functoriality of completed residues gives a commutative square with algebra evaluation. -/
@[simp]
theorem completedResidueFieldAlgHom_comp_completedResidueAlgHom (f : A →ₐ[K] B)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (hxy : ∀ a, x a = y (f a)) :
    (completedResidueFieldAlgHom f x y hxy).comp (completedResidueAlgHom x) =
      (completedResidueAlgHom y).comp f := by
  ext a
  exact completedResidueFieldMap_completedResidueMap f x y hxy a

/-- The map on completed residue fields associated to pullback of a Berkovich point. -/
noncomputable def completedResidueFieldComap (f : A →ₐ[K] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (y : Rigid.BerkovichSpectrumOver K B) :
    CompletedResidueField (comap K A f hf y) →ₐ[K] CompletedResidueField y :=
  completedResidueFieldAlgHom f (comap K A f hf y) y fun _ => rfl

@[simp]
theorem completedResidueFieldComap_completedResidueMap (f : A →ₐ[K] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (y : Rigid.BerkovichSpectrumOver K B) (a : A) :
    completedResidueFieldComap f hf y (completedResidueMap (comap K A f hf y) a) =
      completedResidueMap y (f a) :=
  completedResidueFieldMap_completedResidueMap f _ y (fun _ => rfl) a

/-- Pullback functoriality on completed residue fields is isometric. -/
theorem isometry_completedResidueFieldComap (f : A →ₐ[K] B)
    (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (y : Rigid.BerkovichSpectrumOver K B) :
    Isometry (completedResidueFieldComap f hf y) :=
  isometry_completedResidueFieldAlgHom f _ y fun _ => rfl

omit [IsUltrametricDist A] in
/-- The map on residue domains associated to the identity is the identity. -/
@[simp]
theorem residueDomainMap_id (x : Rigid.BerkovichSpectrumOver K A) :
    residueDomainMap (AlgHom.id K A) x x (fun _ => rfl) = AlgHom.id K (ResidueDomain x) := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

omit [IsUltrametricDist A] [IsUltrametricDist B] [IsUltrametricDist C] in
/-- Maps on residue domains preserve composition. -/
@[simp]
theorem residueDomainMap_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (q : Rigid.BerkovichSpectrumOver K C) (hxy : ∀ a, x a = y (f a))
    (hyq : ∀ b, y b = q (g b)) :
    (residueDomainMap g y q hyq).comp (residueDomainMap f x y hxy) =
      residueDomainMap (g.comp f) x q (fun a => (hxy a).trans (hyq (f a))) := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

omit [IsUltrametricDist A] in
/-- The map on residue fraction fields associated to the identity is the identity. -/
@[simp]
theorem residueFractionFieldMap_id (x : Rigid.BerkovichSpectrumOver K A) :
    residueFractionFieldMap (AlgHom.id K A) x x (fun _ => rfl) =
      RingHom.id (ResidueFractionField x) := by
  apply IsFractionRing.ringHom_ext (A := ResidueDomain x)
  intro a
  rw [residueFractionFieldMap_algebraMap, residueDomainMap_id]
  rfl

omit [IsUltrametricDist A] [IsUltrametricDist B] [IsUltrametricDist C] in
/-- Maps on residue fraction fields preserve composition. -/
@[simp]
theorem residueFractionFieldMap_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (q : Rigid.BerkovichSpectrumOver K C) (hxy : ∀ a, x a = y (f a))
    (hyq : ∀ b, y b = q (g b)) :
    (residueFractionFieldMap g y q hyq).comp (residueFractionFieldMap f x y hxy) =
      residueFractionFieldMap (g.comp f) x q (fun a => (hxy a).trans (hyq (f a))) := by
  apply IsFractionRing.ringHom_ext (A := ResidueDomain x)
  intro a
  simp only [RingHom.comp_apply, residueFractionFieldMap_algebraMap]
  exact congrArg (algebraMap (ResidueDomain q) (ResidueFractionField q))
    (AlgHom.congr_fun (residueDomainMap_comp f g x y q hxy hyq) a)

/-- The map on completed residue fields associated to the identity is the identity. -/
@[simp]
theorem completedResidueFieldMap_id (x : Rigid.BerkovichSpectrumOver K A) :
    completedResidueFieldMap (AlgHom.id K A) x x (fun _ => rfl) =
      RingHom.id (CompletedResidueField x) := by
  ext r
  induction r using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (isometry_completedResidueFieldMap _ _ _ _).continuous continuous_id
  | ih r =>
      rw [completedResidueFieldMap_coe, residueFractionFieldMap_id]
      rfl

/-- Maps on completed residue fields preserve composition. -/
@[simp]
theorem completedResidueFieldMap_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (q : Rigid.BerkovichSpectrumOver K C) (hxy : ∀ a, x a = y (f a))
    (hyq : ∀ b, y b = q (g b)) :
    (completedResidueFieldMap g y q hyq).comp (completedResidueFieldMap f x y hxy) =
      completedResidueFieldMap (g.comp f) x q (fun a => (hxy a).trans (hyq (f a))) := by
  ext r
  induction r using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((isometry_completedResidueFieldMap _ _ _ _).continuous.comp
          (isometry_completedResidueFieldMap _ _ _ _).continuous)
        (isometry_completedResidueFieldMap _ _ _ _).continuous
  | ih r =>
      simp only [RingHom.comp_apply, completedResidueFieldMap_coe]
      exact congrArg ((↑) : ResidueFractionField q → CompletedResidueField q)
        (RingHom.congr_fun (residueFractionFieldMap_comp f g x y q hxy hyq) r)

/-- The identity law for completed residue field algebra homomorphisms. -/
@[simp]
theorem completedResidueFieldAlgHom_id (x : Rigid.BerkovichSpectrumOver K A) :
    completedResidueFieldAlgHom (AlgHom.id K A) x x (fun _ => rfl) =
      AlgHom.id K (CompletedResidueField x) := by
  apply AlgHom.ext
  exact RingHom.congr_fun (completedResidueFieldMap_id x)

/-- The composition law for completed residue field algebra homomorphisms. -/
@[simp]
theorem completedResidueFieldAlgHom_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (x : Rigid.BerkovichSpectrumOver K A) (y : Rigid.BerkovichSpectrumOver K B)
    (q : Rigid.BerkovichSpectrumOver K C) (hxy : ∀ a, x a = y (f a))
    (hyq : ∀ b, y b = q (g b)) :
    (completedResidueFieldAlgHom g y q hyq).comp (completedResidueFieldAlgHom f x y hxy) =
      completedResidueFieldAlgHom (g.comp f) x q (fun a => (hxy a).trans (hyq (f a))) := by
  apply AlgHom.ext
  exact RingHom.congr_fun (completedResidueFieldMap_comp f g x y q hxy hyq)

end Rigid.BerkovichSpectrumOver
