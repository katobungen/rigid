import Rigid.TateAlgebra.Division
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.Noetherian.Basic

set_option linter.style.header false

/-!
# Noetherianity of Tate algebras

The strict Tate algebra over a complete nonarchimedean field in finitely many variables is a
Noetherian ring. This is the corollary on standard bases in Appendix B of Kato, *Introduction to
Rigid Geometry*: by Dickson's lemma, the leading degrees of the nonzero elements of an ideal are
dominated by finitely many of them; elements realizing these leading degrees form a *standard
basis*, and the division algorithm shows that they generate the ideal, because a nonzero
remainder would have a leading degree both divisible and not divisible by a leading monomial of
the basis.
-/

open scoped MonomialOrder

universe u v

namespace Rigid

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {ι : Type v}

namespace TateAlgebra

/-- **Dickson's lemma**, domination form: any set of multi-indices in finitely many variables
contains a finite subset such that every element of the set is componentwise at least one of the
chosen ones. -/
theorem exists_finset_dominating [Finite ι] (L : Set (ι →₀ ℕ)) :
    ∃ T : Finset (ι →₀ ℕ), ↑T ⊆ L ∧ ∀ μ ∈ L, ∃ t ∈ T, t ≤ μ := by
  classical
  by_contra hcon
  push Not at hcon
  choose pick hpickL hpick using hcon
  -- Iteratively pick elements not dominated by anything chosen so far.
  set T : ℕ → {s : Finset (ι →₀ ℕ) // ↑s ⊆ L} :=
    fun n => Nat.rec ⟨∅, by simp⟩
      (fun _ prev => ⟨insert (pick prev.1 prev.2) prev.1, by
        rw [Finset.coe_insert]
        exact Set.insert_subset (hpickL prev.1 prev.2) prev.2⟩) n with hTdef
  set f : ℕ → ι →₀ ℕ := fun n => pick (T n).1 (T n).2 with hfdef
  have hTsucc : ∀ n, (T (n + 1)).1 = insert (f n) (T n).1 := fun n => rfl
  have hTmono : ∀ n k, k ≤ n → (T k).1 ⊆ (T n).1 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [Nat.le_zero.mp hk]
    | succ n ihn =>
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hlt
      · exact Finset.Subset.refl _
      · refine (ihn k (Nat.lt_succ_iff.mp hlt)).trans ?_
        rw [hTsucc]
        exact Finset.subset_insert _ _
  have hmem : ∀ k n, k < n → f k ∈ (T n).1 := by
    intro k n hkn
    have h1 : f k ∈ (T (k + 1)).1 := by
      rw [hTsucc]
      exact Finset.mem_insert_self _ _
    exact hTmono n (k + 1) hkn h1
  -- A bad sequence contradicts the well-quasi-ordering of `ι →₀ ℕ`.
  obtain ⟨a, b, hab, hle⟩ := wellQuasiOrdered_le (α := ι →₀ ℕ) f
  exact hpick (T b).1 (T b).2 (f a) (hmem a b hab) hle

end TateAlgebra

open TateAlgebra in
/-- **Tate algebras are Noetherian** (Kato, *Introduction to Rigid Geometry*, Appendix B,
corollary of the theory of standard bases): the strict Tate algebra in finitely many variables
over a complete nonarchimedean field is a Noetherian ring. -/
instance tateAlgebraIsNoetherianRing [Finite ι] [CompleteSpace K] :
    IsNoetherianRing (TateAlgebra K ι) := by
  classical
  -- Fix a monomial order on the exponents.
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  letI : LinearOrder ι := LinearOrder.lift' e e.injective
  haveI : WellFoundedGT ι := Finite.to_wellFoundedGT
  set m : MonomialOrder ι := MonomialOrder.lex with hmdef
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  -- The leading degrees of the nonzero elements of the ideal, dominated by finitely many.
  set L : Set (ι →₀ ℕ) :=
    (fun f => leadingDegree m f) '' {f : TateAlgebra K ι | f ∈ I ∧ f ≠ 0} with hLdef
  obtain ⟨T, hTL, hdom⟩ := exists_finset_dominating L
  -- A standard basis: elements of the ideal realizing the dominating leading degrees.
  have hchoice : ∀ t : {x // x ∈ T}, ∃ g : TateAlgebra K ι,
      g ∈ I ∧ g ≠ 0 ∧ leadingDegree m g = t.1 := by
    intro t
    obtain ⟨g, hg, hgdeg⟩ := hTL t.2
    exact ⟨g, hg.1, hg.2, hgdeg⟩
  choose g hgI hgne hgdeg using hchoice
  refine ⟨T.attach.image g, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨t, -, rfl⟩ := hx
    exact hgI t
  · intro F hF
    -- Divide by the standard basis; a nonzero remainder is impossible.
    obtain ⟨Q, hQ⟩ := exists_forall_coeff_eq_zero_of_leadingDegree_le m g hgne F
    have hR : F - ∑ t, Q t * g t = 0 := by
      by_contra hR0
      have hmemL : leadingDegree m (F - ∑ t, Q t * g t) ∈ L :=
        ⟨F - ∑ t, Q t * g t,
          ⟨I.sub_mem hF (Submodule.sum_mem I fun t _ => I.mul_mem_left _ (hgI t)), hR0⟩, rfl⟩
      obtain ⟨t, htT, htle⟩ := hdom _ hmemL
      have h0 := hQ (leadingDegree m (F - ∑ t, Q t * g t))
        ⟨⟨t, htT⟩, by rw [hgdeg ⟨t, htT⟩]; exact htle⟩
      exact leadingCoeff_ne_zero m hR0 h0
    rw [show F = ∑ t, Q t * g t from sub_eq_zero.mp hR]
    exact Submodule.sum_mem _ fun t _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span (by
        rw [Finset.coe_image]
        exact ⟨t, Finset.mem_coe.mpr (Finset.mem_attach T t), rfl⟩))

end Rigid
