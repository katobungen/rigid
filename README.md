# rigid

A Lean/mathlib formalization project for rigid analytic geometry, including Tate and affinoid
algebras, rigid spaces, Berkovich spaces, and their comparison.

The standalone mathlib-only specification is [`Rigid/Challenge.lean`](Rigid/Challenge.lean). The
implementation-facing comparator copy is [`Rigid/Development.lean`](Rigid/Development.lean). Both
contain the same declarations in namespace `RigidChallenge`; Development imports project modules and
replaces sorried bodies as implementations become available. See [`PLAN.md`](PLAN.md) for the
dependency order and scope decisions. The global comparison target follows Berkovich's fully
faithful and paracompact-equivalence theorem in §1.6 of *Étale cohomology for non-Archimedean
analytic spaces*.

## Claiming an issue

Anyone can claim an issue by posting a comment containing a line whose entire content is:

```text
claimed
```

This adds the `claimed` label; it does not assign the issue to the commenter. To release a claim,
post a comment containing a line whose entire content is `-claimed`.
