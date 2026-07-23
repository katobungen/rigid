import Rigid.AffinoidSpectrum.RationalCover

set_option linter.style.header false
set_option linter.unusedSectionVars false

open scoped BigOperators

/-!
# Rational-cover refinement from a dominating family

BGR 8.2.2 refines a finite rational cover by forming finitely many products of its defining
functions.  The formal argument naturally separates into two parts: the products span the unit
ideal, and at every Berkovich point one of the proposed denominators dominates every numerator.
This file packages the second, reusable part.  A later product-family construction can therefore
produce a rational cover and its refinement by proving only finite pointwise inequalities.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

namespace AffinoidRationalSubdomain.Cover

/-- A member of a rational cover obtained by choosing one element of a unit-ideal family as
denominator and keeping the whole family as numerators. -/
noncomputable def dominatingDomain {r s : ℕ} (p : Fin r → A)
    (hp : Ideal.span (Set.range p) = ⊤) (denominator : Fin s → Fin r) (i : Fin s) :
    AffinoidRationalSubdomain K A where
  n := r
  g := p (denominator i)
  f := p
  isRational := by
    apply top_unique
    rw [← hp]
    exact Ideal.span_mono (Set.subset_insert (p (denominator i)) (Set.range p))

@[simp]
theorem mem_dominatingDomain_carrier {r s : ℕ} (p : Fin r → A)
    (hp : Ideal.span (Set.range p) = ⊤) (denominator : Fin s → Fin r) (i : Fin s)
    (x : BerkovichSpectrumOver K A) :
    x ∈ (dominatingDomain K A p hp denominator i).carrier ↔
      ∀ j, x (p j) ≤ x (p (denominator i)) := by
  rfl

/-- A pointwise dominating subfamily of a unit-ideal family gives a rational cover of the whole
affinoid spectrum. -/
noncomputable def ofDominatingFamily {r s : ℕ} (p : Fin r → A)
    (hp : Ideal.span (Set.range p) = ⊤) (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i))) :
    AffinoidRationalSubdomain.Cover K A (AffinoidRationalSubdomain.whole K A) where
  m := s
  domain := dominatingDomain K A p hp denominator
  subset := fun _ ↦ by
    rw [AffinoidRationalSubdomain.carrier_whole]
    exact Set.subset_univ _
  covers := by
    rw [AffinoidRationalSubdomain.carrier_whole]
    symm
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hdom x
    exact Set.mem_iUnion.mpr ⟨i,
      (mem_dominatingDomain_carrier K A p hp denominator i x).2 hi⟩

/-- Refinement criterion for a dominating-family cover.  Each proposed denominator is assigned an
old cover member, and its domination inequalities are used to prove containment in that member. -/
def refinementOfDominatingFamily
    (𝒰 : AffinoidRationalSubdomain.Cover K A (AffinoidRationalSubdomain.whole K A))
    {r s : ℕ} (p : Fin r → A) (hp : Ideal.span (Set.range p) = ⊤)
    (denominator : Fin s → Fin r)
    (hdom : ∀ x : BerkovichSpectrumOver K A,
      ∃ i : Fin s, ∀ j : Fin r, x (p j) ≤ x (p (denominator i)))
    (owner : Fin s → Fin 𝒰.m)
    (hrefines : ∀ i x,
      (∀ j : Fin r, x (p j) ≤ x (p (denominator i))) → x ∈ (𝒰.domain (owner i)).carrier) :
    Refinement K A (ofDominatingFamily K A p hp denominator hdom) 𝒰 where
  index := owner
  subset := by
    intro i x hx
    exact hrefines i x
      ((mem_dominatingDomain_carrier K A p hp denominator i x).1 hx)

/-! ## The product family attached to a rational cover -/

/-- The denominator followed by the numerators in a rational datum. -/
def datumTerm (U : AffinoidRationalSubdomain K A) : Fin (U.n + 1) → A :=
  Fin.cases U.g U.f

@[simp]
theorem datumTerm_zero (U : AffinoidRationalSubdomain K A) : datumTerm K A U 0 = U.g :=
  rfl

@[simp]
theorem datumTerm_succ (U : AffinoidRationalSubdomain K A) (i : Fin U.n) :
    datumTerm K A U i.succ = U.f i :=
  rfl

theorem range_datumTerm (U : AffinoidRationalSubdomain K A) :
    Set.range (datumTerm K A U) = Set.insert U.g (Set.range U.f) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩

/-- A choice of one defining function from every member of a finite rational cover. -/
abbrev ProductChoice
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :=
  ∀ i : Fin 𝒰.m, Fin ((𝒰.domain i).n + 1)

/-- The product associated with a choice of one defining function from each cover member. -/
def productTerm
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (choice : ProductChoice K A 𝒰) : A :=
  ∏ i, datumTerm K A (𝒰.domain i) (choice i)

/-- Enumerate all products of one defining function from every cover member. -/
noncomputable def productFamily
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :
    Fin (Fintype.card (ProductChoice K A 𝒰)) → A := fun j ↦
  productTerm K A 𝒰 ((Fintype.equivFin (ProductChoice K A 𝒰)).symm j)

/-- The full product family spans the unit ideal.  This is the algebraic part of BGR's
rational-cover refinement: every defining family spans the unit ideal, so a maximal ideal cannot
contain every possible product. -/
theorem span_range_productFamily_eq_top
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :
    Ideal.span (Set.range (productFamily K A 𝒰)) = ⊤ := by
  by_contra htop
  obtain ⟨m, hm, hle⟩ :=
    (Ideal.span (Set.range (productFamily K A 𝒰))).exists_le_maximal htop
  letI : m.IsMaximal := hm
  have hexists (i : Fin 𝒰.m) :
      ∃ j : Fin ((𝒰.domain i).n + 1), datumTerm K A (𝒰.domain i) j ∉ m := by
    by_contra h
    push Not at h
    have hdatum : Ideal.span (Set.range (datumTerm K A (𝒰.domain i))) ≤ m :=
      Ideal.span_le.mpr fun a ha ↦ by
        obtain ⟨j, rfl⟩ := ha
        exact h j
    have htop_le : (⊤ : Ideal A) ≤ m := by
      rw [← (𝒰.domain i).isRational, ← range_datumTerm K A]
      exact hdatum
    exact hm.ne_top (top_unique htop_le)
  choose choice hchoice using hexists
  have hproduct_not_mem : productTerm K A 𝒰 choice ∉ m := by
    intro hproduct
    rw [productTerm, Ideal.IsPrime.prod_mem_iff] at hproduct
    obtain ⟨i, -, hi⟩ := hproduct
    exact hchoice i hi
  let j : Fin (Fintype.card (ProductChoice K A 𝒰)) :=
    Fintype.equivFin (ProductChoice K A 𝒰) choice
  have hj : productFamily K A 𝒰 j = productTerm K A 𝒰 choice := by
    simp [productFamily, j]
  apply hproduct_not_mem
  apply hle
  apply Ideal.subset_span
  exact ⟨j, hj⟩

/-- Choices containing at least one denominator.  These are the proposed denominators in BGR's
product refinement. -/
abbrev DenominatorChoice
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :=
  {choice : ProductChoice K A 𝒰 // ∃ i, choice i = 0}

/-- Locate a denominator-containing product inside the enumeration of all products. -/
noncomputable def denominatorIndex
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :
    Fin (Fintype.card (DenominatorChoice K A 𝒰)) →
      Fin (Fintype.card (ProductChoice K A 𝒰)) := fun j ↦
  Fintype.equivFin (ProductChoice K A 𝒰)
    ((Fintype.equivFin (DenominatorChoice K A 𝒰)).symm j).1

/-- At every point of a rationally covered affinoid spectrum, a product containing an old
denominator dominates every product in the full family.  This is the finite maximum argument in
BGR 8.2.2/2. -/
theorem productFamily_dominated_by_denominator
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (x : BerkovichSpectrumOver K A) (hx𝒲 : x ∈ 𝒲.carrier) :
    ∃ i : Fin (Fintype.card (DenominatorChoice K A 𝒰)),
      ∀ j : Fin (Fintype.card (ProductChoice K A 𝒰)),
        x (productFamily K A 𝒰 j) ≤
          x (productFamily K A 𝒰 (denominatorIndex K A 𝒰 i)) := by
  let zeroChoice : ProductChoice K A 𝒰 := fun _ ↦ 0
  let j₀ : Fin (Fintype.card (ProductChoice K A 𝒰)) :=
    Fintype.equivFin (ProductChoice K A 𝒰) zeroChoice
  letI : Nonempty (Fin (Fintype.card (ProductChoice K A 𝒰))) := ⟨j₀⟩
  obtain ⟨jmax, hjmax⟩ :=
    Finite.exists_max (fun j : Fin (Fintype.card (ProductChoice K A 𝒰)) ↦
      x (productFamily K A 𝒰 j))
  rw [𝒰.covers] at hx𝒲
  obtain ⟨owner, hxowner⟩ := Set.mem_iUnion.mp hx𝒲
  let choice : ProductChoice K A 𝒰 :=
    (Fintype.equivFin (ProductChoice K A 𝒰)).symm jmax
  let choice' : ProductChoice K A 𝒰 := Function.update choice owner 0
  have hchoice'_denominator : ∃ i, choice' i = 0 := by
    exact ⟨owner, by simp [choice']⟩
  let denominatorChoice : DenominatorChoice K A 𝒰 :=
    ⟨choice', hchoice'_denominator⟩
  let chosen : Fin (Fintype.card (DenominatorChoice K A 𝒰)) :=
    Fintype.equivFin (DenominatorChoice K A 𝒰) denominatorChoice
  have hfactor :
      x (datumTerm K A (𝒰.domain owner) (choice owner)) ≤
        x (datumTerm K A (𝒰.domain owner) 0) := by
    refine Fin.cases ?_ (fun i ↦ ?_) (choice owner)
    · exact le_rfl
    · exact hxowner i
  have hproduct :
      x (productTerm K A 𝒰 choice) ≤ x (productTerm K A 𝒰 choice') := by
    rw [productTerm, productTerm, map_prod, map_prod]
    apply Finset.prod_le_prod
    · intro i _
      exact BerkovichSpectrumOver.nonneg K A x _
    · intro i _
      by_cases hi : i = owner
      · subst i
        simpa [choice'] using hfactor
      · simp [choice', hi]
  refine ⟨chosen, fun j ↦ (hjmax j).trans ?_⟩
  simpa [productFamily, denominatorIndex, chosen, denominatorChoice, choice', choice] using hproduct

/-- The rational domain in the product refinement corresponding to a product containing an old
denominator. -/
noncomputable def productDomain
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (i : Fin (Fintype.card (DenominatorChoice K A 𝒰))) :
    AffinoidRationalSubdomain K A :=
  dominatingDomain K A (productFamily K A 𝒰)
    (span_range_productFamily_eq_top K A 𝒰) (denominatorIndex K A 𝒰) i

/-- Choose an old cover member whose denominator occurs in a proposed product denominator. -/
noncomputable def denominatorOwner
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (i : Fin (Fintype.card (DenominatorChoice K A 𝒰))) : Fin 𝒰.m :=
  Classical.choose ((Fintype.equivFin (DenominatorChoice K A 𝒰)).symm i).2

@[simp]
theorem denominatorChoice_apply_owner
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (i : Fin (Fintype.card (DenominatorChoice K A 𝒰))) :
    ((Fintype.equivFin (DenominatorChoice K A 𝒰)).symm i).1
        (denominatorOwner K A 𝒰 i) = 0 :=
  Classical.choose_spec ((Fintype.equivFin (DenominatorChoice K A 𝒰)).symm i).2

/-- Each member of the BGR product cover is contained in an original rational-cover member. -/
theorem productDomain_subset
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (i : Fin (Fintype.card (DenominatorChoice K A 𝒰))) :
    (productDomain K A 𝒰 i).carrier ⊆
      (𝒰.domain (denominatorOwner K A 𝒰 i)).carrier := by
  intro x hx
  let denominatorChoice : DenominatorChoice K A 𝒰 :=
    (Fintype.equivFin (DenominatorChoice K A 𝒰)).symm i
  let choice : ProductChoice K A 𝒰 := denominatorChoice.1
  let owner : Fin 𝒰.m := denominatorOwner K A 𝒰 i
  have hchoice_owner : choice owner = 0 := by
    simp [choice, owner, denominatorChoice]
  have hdom : ∀ j : Fin (Fintype.card (ProductChoice K A 𝒰)),
      x (productFamily K A 𝒰 j) ≤
        x (productFamily K A 𝒰 (denominatorIndex K A 𝒰 i)) := by
    exact (mem_dominatingDomain_carrier K A (productFamily K A 𝒰)
      (span_range_productFamily_eq_top K A 𝒰) (denominatorIndex K A 𝒰) i x).1 hx
  intro k
  let choice' : ProductChoice K A 𝒰 := Function.update choice owner k.succ
  let j : Fin (Fintype.card (ProductChoice K A 𝒰)) :=
    Fintype.equivFin (ProductChoice K A 𝒰) choice'
  have hproduct : x (productTerm K A 𝒰 choice') ≤ x (productTerm K A 𝒰 choice) := by
    simpa [productFamily, denominatorIndex, j, choice', choice, denominatorChoice] using hdom j
  let rest : A := (Finset.univ.erase owner).prod fun t ↦
    datumTerm K A (𝒰.domain t) (choice t)
  have hchoice_product :
      productTerm K A 𝒰 choice =
        datumTerm K A (𝒰.domain owner) (choice owner) * rest := by
    exact (Finset.mul_prod_erase Finset.univ
      (fun t ↦ datumTerm K A (𝒰.domain t) (choice t)) (Finset.mem_univ owner)).symm
  have hchoice'_product :
      productTerm K A 𝒰 choice' =
        datumTerm K A (𝒰.domain owner) (choice' owner) * rest := by
    rw [productTerm]
    calc
      ∏ t, datumTerm K A (𝒰.domain t) (choice' t) =
          datumTerm K A (𝒰.domain owner) (choice' owner) *
            (Finset.univ.erase owner).prod
              (fun t ↦ datumTerm K A (𝒰.domain t) (choice' t)) :=
        (Finset.mul_prod_erase Finset.univ
          (fun t ↦ datumTerm K A (𝒰.domain t) (choice' t))
          (Finset.mem_univ owner)).symm
      _ = datumTerm K A (𝒰.domain owner) (choice' owner) * rest := by
        congr 1
        apply Finset.prod_congr rfl
        intro t ht
        have hne : t ≠ owner := Finset.ne_of_mem_erase ht
        simp [choice', hne]
  have hxdenominator : x (productTerm K A 𝒰 choice) ≠ 0 := by
    have hxdom : x ∈ (dominatingDomain K A (productFamily K A 𝒰)
        (span_range_productFamily_eq_top K A 𝒰) (denominatorIndex K A 𝒰) i).carrier :=
      (mem_dominatingDomain_carrier K A (productFamily K A 𝒰)
        (span_range_productFamily_eq_top K A 𝒰) (denominatorIndex K A 𝒰) i x).2 hdom
    have hne := BerkovichSpectrumOver.RationalDomain.denominator_ne_zero K A
      (dominatingDomain K A (productFamily K A 𝒰)
        (span_range_productFamily_eq_top K A 𝒰) (denominatorIndex K A 𝒰) i).isRational
      ⟨x, hxdom⟩
    simpa [dominatingDomain, denominatorIndex, productFamily, choice, denominatorChoice] using hne
  have hxrest_ne : x rest ≠ 0 := by
    intro hzero
    apply hxdenominator
    rw [hchoice_product, BerkovichSpectrumOver.map_mul, hzero, mul_zero]
  have hxrest_pos : 0 < x rest :=
    lt_of_le_of_ne (BerkovichSpectrumOver.nonneg K A x rest) hxrest_ne.symm
  apply le_of_mul_le_mul_right _ hxrest_pos
  simpa [hchoice'_product, hchoice_product, hchoice_owner, choice'] using hproduct

/-- The BGR product construction gives a rational cover of an arbitrary rational subdomain. -/
noncomputable def productCover
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :
    AffinoidRationalSubdomain.Cover K A 𝒲 where
  m := Fintype.card (DenominatorChoice K A 𝒰)
  domain := productDomain K A 𝒰
  subset := fun i ↦ (productDomain_subset K A 𝒰 i).trans (𝒰.subset _)
  covers := by
    apply Set.Subset.antisymm
    · intro x hx𝒲
      obtain ⟨i, hi⟩ := productFamily_dominated_by_denominator K A 𝒰 x hx𝒲
      exact Set.mem_iUnion.mpr ⟨i,
        (mem_dominatingDomain_carrier K A (productFamily K A 𝒰)
          (span_range_productFamily_eq_top K A 𝒰)
          (denominatorIndex K A 𝒰) i x).2 hi⟩
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact 𝒰.subset _ (productDomain_subset K A 𝒰 i hxi)

/-- Each member of the BGR product cover is contained in an original rational-cover member. -/
theorem productCover_domain_subset
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲)
    (i : Fin (Fintype.card (DenominatorChoice K A 𝒰))) :
    ((productCover K A 𝒰).domain i).carrier ⊆
      (𝒰.domain (denominatorOwner K A 𝒰 i)).carrier :=
  productDomain_subset K A 𝒰 i

/-- **Rational-cover refinement.** Every finite rational cover of an arbitrary rational subdomain
is refined by the BGR product cover. -/
noncomputable def productCoverRefinement
    {𝒲 : AffinoidRationalSubdomain K A}
    (𝒰 : AffinoidRationalSubdomain.Cover K A 𝒲) :
    Refinement K A (productCover K A 𝒰) 𝒰 where
  index := denominatorOwner K A 𝒰
  subset := productCover_domain_subset K A 𝒰

end AffinoidRationalSubdomain.Cover

end Rigid
