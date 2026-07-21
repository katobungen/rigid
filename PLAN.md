# Rigid analytic geometry formalization plan

## Initial scope

The first pass will treat a complete nontrivially normed field `K` with
`IsUltrametricDist K` and strict analytic geometry over `K`.

- Tate algebras initially have finitely many variables and unit polyradius.
- A strict affinoid algebra is a `K`-algebra isomorphic to a quotient of a Tate algebra; no norm or
  topology is part of the affinoidness predicate.
- The Berkovich spectrum of a normed ring consists of contractive multiplicative real-valued
  seminorms; it does not depend on a choice of ground field.
- Global spaces and morphisms will be built only after the affinoid theory and its sheaf theorem are
  available.
- `Rigid/Challenge.lean` is a standalone specification file. It has only mathlib imports and keeps
  all target declarations independent of the implementation import graph.
- `Rigid/Development.lean` mirrors the complete challenge declaration list in namespace
  `RigidChallenge` but may import project modules. Its declaration bodies are replaced with
  production terms and proofs as those become available.

This deliberately postpones non-strict polyradii, trivially valued fields, adic spaces, and general
Huber pairs.

## Dependency order

### 1. Tate algebra

Reuse `MvPowerSeries.IsRestricted` from mathlib for the underlying restricted power series.

1. Define coordinates and the Gauss norm. **Done** (`TateAlgebra/Basic`, `TateAlgebra/GaussNorm`).
2. Construct the normed commutative `K`-algebra structure. **Done** (`TateAlgebra/NormedRing`).
3. Prove the ultrametric inequality (**done**), completeness (**done**, `TateAlgebra/Complete`;
   finiteness of the variable set was not needed), and multiplicativity of the Gauss norm.
4. Prove density of polynomials and the universal property for tuples of norm at most one.
   **Done** (`TateAlgebra/NormedRing`, `TateAlgebra/UniversalProperty`); neither completeness of `K`
   nor finiteness of the variable set was needed.
5. Extend the universal property from tuples of norm at most one to power-bounded tuples.
6. Generalize to positive polyradii only after the strict unit-radius API is stable.

The multiplicativity proof is the first substantial algebraic milestone. It will likely need a
carefully chosen maximal coefficient argument rather than only generic norm estimates.

The universal property required a correction to the challenge statement: the codomain must be a
`NormedCommRing` rather than a `SeminormedCommRing`. Uniqueness genuinely needs the codomain to be
Hausdorff — when the seminorm has a nontrivial null ideal, one can perturb a continuous algebra
homomorphism by a suitable derivation vanishing on polynomials (which are dense) without changing
its values on the coordinates.

### 2. Affinoid algebra

1. Define quotient seminorms and prove completeness after quotienting by a closed ideal.
2. Bundle strict affinoid `K`-algebras and bounded/continuous homomorphisms.
3. Prove that algebra homomorphisms between affinoid algebras are continuous.
4. Prove Noetherianity (Tate's theorem).
5. Define rational and Weierstrass localizations and prove their universal properties.
6. Prove invariance under equivalent admissible Banach norms.

The current `IsAffinoidAlgebra` predicate is algebraic: it asks for an isomorphism to
`K⟨T₁, ..., Tₙ⟩ / I` and assumes no norm or topology on the target. An `AffinoidPresentation`
transports the quotient topology and residue norm to the target. The quotient topology is independent
of the presentation, while the residue norm itself may depend on it. For any complete
nonarchimedean normed realization, `exists_equivalent_quotientNorm_presentation_of_isAffinoidAlgebra`
records equivalence with a presentation quotient norm. `IsQuotientNorm` remains available for the
exact residue norm attached to a chosen presentation.

The transport of the topology is implemented (`AffinoidAlgebra/QuotientTopology`): the topology
coinduced by a surjective homomorphism out of a topological ring is a ring topology with
continuous scalar multiplication, which settles `toAlgHom_surjective`,
`residueIsTopologicalRing`, `residueContinuousSMul`, and their affinoid corollaries.
Presentation-independence of the topology and the bundled residue norm remain open: both need
closedness of ideals in Tate algebras and automatic continuity (Tate's theorem together with the
Banach open mapping machinery — BGR 3.7.5 and 6.1.1, or the finite-module completeness
propositions in Kato's book). In particular the residue norm is a genuine norm only because
kernels of presentations are closed, which is part of that machinery.

The rational-localization interface follows the unit-radius construction
`A⟨T₁, ..., Tₙ⟩ / (gTᵢ - fᵢ)`. `IsRationalDatum g f` records that `g` and the `fᵢ` generate the unit
ideal. Coordinates are required to be power-bounded rather than to have norm at most one, so the
universal property is unchanged when the admissible Banach norm is replaced by an equivalent norm.
The API exposes the canonical base map, coordinates and their relations, invertibility of the
denominator for rational data, the continuous universal mapping property, and preservation of the
affinoid condition.

### 3. Affinoid geometry

1. Define rational domains and rational coverings.
2. Define the structure presheaf on the rational basis.
3. Prove Tate acyclicity for finite rational covers.
4. Extend the presheaf to the affinoid admissible site and prove the sheaf condition.
5. Define affinoid spectra and establish the contravariant algebra/geometry correspondence.

Tate acyclicity is the critical prerequisite for defining global rigid spaces as locally ringed
geometric objects.

### 4. Rigid spaces

1. Define admissible opens and admissible coverings (or a site presenting the same geometry).
2. Bundle locally affinoid locally ringed objects with analytic morphisms.
3. Construct gluing and open subspaces.
4. Define quasi-compact, quasi-separated, separated, and paracompact/finite-type-cover predicates.
5. Build the category and the affinoid spectrum functor.

### 5. Berkovich spaces

1. Put the evaluation topology on the Berkovich spectrum of an affinoid algebra.
2. Prove nonemptiness, compactness, and Hausdorffness.
3. Define completed residue fields and evaluation maps.
4. Define affinoid domains and analytic functions.
5. Build Berkovich spaces from affinoid atlases, then define good, strict, Hausdorff, and
   paracompact objects and analytic morphisms.

### 6. Comparison

1. Construct the comparison on affinoid objects and prove compatibility with rational domains.
2. Show that it respects admissible gluing and analytic morphisms.
3. Prove full faithfulness.
4. Characterize the essential image.
5. Package the result as `rigidToBerkovich_isEquivalence` and
   `rigidBerkovichEquivalence`.
6. Prove that separated rigid spaces correspond to Hausdorff Berkovich spaces.

## The comparison statement still needs a fixed reference

The predicates in `Rigid/Challenge.lean` currently encode the provisional comparison

- rigid side: locally affinoid, quasi-separated, and paracompact (typically via an affinoid cover of
  finite type);
- Berkovich side: good, strict, and paracompact.

Before proof work starts on the global comparison, choose a precise source and mirror its
conventions. In particular, verify:

- whether `good` is an assumption or follows from the chosen atlas convention;
- the exact rigid condition corresponding to Berkovich paracompactness;
- whether quasi-separatedness is independent or built into that condition;
- whether the base field must be nontrivially valued;
- whether Hausdorff/separated objects form the main equivalence or a restricted corollary.

Until these are settled, the comparison declarations are useful dependency targets rather than a
canonical theorem statement.

## Proposed file layout after the API stabilizes

```text
Rigid/
  TateAlgebra/Basic.lean
  TateAlgebra/GaussNorm.lean
  TateAlgebra/UniversalProperty.lean
  AffinoidAlgebra/Basic.lean
  AffinoidAlgebra/Localization.lean
  AffinoidAlgebra/Noetherian.lean
  AffinoidSpectrum/Basic.lean
  AffinoidSpectrum/TateAcyclicity.lean
  RigidSpace/Basic.lean
  RigidSpace/Gluing.lean
  Berkovich/Spectrum.lean
  Berkovich/Space.lean
  Comparison/Affinoid.lean
  Comparison/Global.lean
  Challenge.lean
  Development.lean
```

Keep the implementation split by dependency. The root module imports `Development.lean`, while the
challenge file remains a separately checked, mathlib-only specification. Production declarations
use namespace `Rigid`; both comparator files use `RigidChallenge`. Their declaration lists must stay
identical. As each declaration is implemented, import its production module from Development and
replace only the corresponding sorried Development body.

## Near-term milestone

Implement the strict Tate algebra through completeness and its universal property. This validates
that mathlib's restricted multivariate power series are the right foundation before introducing
quotients, sites, or global spaces.
