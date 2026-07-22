import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.Berkovich.RelativeSpectrum

set_option linter.style.header false

/-!
# Affinoid domains in relative Berkovich spectra

This file starts the domain theory with rational domains. A rational datum `(g, f₁, ..., fₙ)` cuts
out the points satisfying `|fᵢ(x)| ≤ |g(x)|`. These loci are closed and compact. If the datum
generates the unit ideal, its denominator is nonzero at every point of the rational domain.
-/

open scoped Topology

universe u v

namespace Rigid.BerkovichSpectrumOver

variable (K : Type u) [NormedField K]
variable (A : Type v) [NormedCommRing A] [Algebra K A]

/-- The rational locus associated to `g, f₁, ..., fₙ` in a relative Berkovich spectrum. -/
def rationalDomainSet {n : ℕ} (g : A) (f : Fin n → A) :
    Set (Rigid.BerkovichSpectrumOver K A) :=
  {x | ∀ i, x (f i) ≤ x g}

/-- A rational domain as a topological subspace of the relative Berkovich spectrum. -/
abbrev RationalDomain {n : ℕ} (g : A) (f : Fin n → A) :=
  ↥(rationalDomainSet K A g f)

namespace RationalDomain

/-- The inclusion of a rational domain into its ambient relative spectrum. -/
def inclusion {n : ℕ} (g : A) (f : Fin n → A) :
    RationalDomain K A g f → Rigid.BerkovichSpectrumOver K A :=
  Subtype.val

/-- The inclusion of a rational domain is an embedding. -/
theorem isEmbedding_inclusion {n : ℕ} (g : A) (f : Fin n → A) :
    Topology.IsEmbedding (inclusion K A g f) :=
  Topology.IsEmbedding.subtypeVal

/-- Rational loci are closed in the relative Berkovich spectrum. -/
theorem isClosed_rationalDomainSet {n : ℕ} (g : A) (f : Fin n → A) :
    IsClosed (rationalDomainSet K A g f) := by
  rw [show rationalDomainSet K A g f = ⋂ i, {x | x (f i) ≤ x g} by
    ext x
    simp [rationalDomainSet]]
  exact isClosed_iInter fun i ↦ isClosed_le (continuous_eval K A _) (continuous_eval K A _)

noncomputable instance rationalDomainCompactSpace {n : ℕ} (g : A) (f : Fin n → A) :
    CompactSpace (RationalDomain K A g f) :=
  isCompact_iff_compactSpace.mp (isClosed_rationalDomainSet K A g f).isCompact

/-- Rational domains are compact. -/
theorem isCompact_univ {n : ℕ} (g : A) (f : Fin n → A) :
    IsCompact (Set.univ : Set (RationalDomain K A g f)) :=
  _root_.isCompact_univ

/-- Evaluation at an ambient algebra element is continuous on a rational domain. -/
theorem continuous_eval {n : ℕ} (g : A) (f : Fin n → A) (a : A) :
    Continuous fun x : RationalDomain K A g f ↦ (x.1 : A → ℝ) a :=
  (BerkovichSpectrumOver.continuous_eval K A a).comp continuous_subtype_val

/-- On a rational domain attached to a rational datum, the denominator does not vanish. -/
theorem denominator_ne_zero {n : ℕ} {g : A} {f : Fin n → A}
    (hgf : IsRationalDatum g f) (x : RationalDomain K A g f) : x.1 g ≠ 0 := by
  intro hg
  have hnonneg (a : A) : 0 ≤ x.1 a := BerkovichSpectrumOver.nonneg K A x.1 a
  have hfi (i : Fin n) : x.1 (f i) = 0 :=
    le_antisymm ((x.2 i).trans_eq hg) (hnonneg (f i))
  have hgenerators : Set.insert g (Set.range f) ⊆ x.1.kernel := by
    intro a ha
    change x.1 a = 0
    rcases ha with rfl | ⟨i, rfl⟩
    · exact hg
    · exact hfi i
  have htop : (⊤ : Ideal A) ≤ x.1.kernel := by
    rw [← hgf]
    exact Ideal.span_le.2 hgenerators
  exact x.1.kernel_isPrime.ne_top (top_unique htop)

end RationalDomain

end Rigid.BerkovichSpectrumOver
