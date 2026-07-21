# Agent workflow for `rigid`

## Synchronize with GitHub

Pull requests may be merged while an agent is working.

1. Before starting work, run `git fetch origin` and compare `HEAD...origin/main`.
2. Fast-forward a clean local branch before editing.
3. Fetch again immediately before every push.
4. If `origin/main` advanced after a local commit, rebase the local commit onto `origin/main`, rerun
   affected checks, and then push.
5. Push `main` after every commit.

Do not overwrite or force-push merged remote work.

## Challenge/Development comparator pair

`Rigid/Challenge.lean` and `Rigid/Development.lean` are a comparator pair.

- `Challenge.lean` must import only `Mathlib` or `Mathlib.*` modules. It must never import project
  implementation modules.
- `Development.lean` may import modules from this repository.
- Both files declare the complete comparator API in the custom namespace `RigidChallenge`.
- Production code belongs in namespace `Rigid`. The distinct namespace prevents imported production
  declarations from colliding with the comparator declarations.
- The declaration lists in Challenge and Development must match exactly: preserve names, kinds,
  binders, types, attributes, order, and documentation. Never remove an implemented declaration
  from Development.
- The only expected differences are imports and declaration bodies. Challenge bodies may contain
  `sorry`; Development bodies should be replaced with terms or proofs from production modules as
  those become available.
- When changing the specification, make the same declaration-level change in both files in the same
  commit. The safest workflow is to edit Challenge first, copy the corresponding declaration to
  Development, and then restore Development's implementation body.
- When closing a target, edit only its body in Development. Leave the Challenge declaration and
  body unchanged.
- Keep assumptions that do not occur syntactically in a result explicit with `include ... in`; this
  prevents a solved Development body from silently dropping a section variable from its elaborated
  declaration type.

Production modules such as `Rigid/TateAlgebra/Basic.lean`,
`Rigid/TateAlgebra/GaussNorm.lean`, and `Rigid/AffinoidAlgebra/QuotientNorm.lean` should contain no
`sorry`.

## Root all-import module

`Rigid.lean` must directly import every project module under `Rigid/` so the default CI build cannot
silently omit a new file. The sole exception is `Rigid/Challenge.lean`: Challenge and Development
declare the same names and cannot be imported into one environment. `Rigid.lean` imports
Development, while the comparator check builds Challenge separately.

Whenever a Lean module is added, renamed, or removed:

1. Update the sorted import list in `Rigid.lean`.
2. Run `./scripts/check_root_imports.sh`.
3. Run the comparator check so the separately imported Challenge module is also built.

Do not leave a project module reachable only through another module's transitive imports. CI runs
the root-import and comparator checks to ensure every module is covered.

## Required checks

After changing comparator declarations or production code, run:

```bash
./scripts/check_root_imports.sh
./scripts/check_challenge_development.sh
lake build Rigid
```

The root-import check verifies that `Rigid.lean` directly imports every compatible project module.
The comparator check verifies that Challenge and Development expose identical public declaration
names, kinds, and elaborated types. Also verify that Challenge has only mathlib imports and inspect
the source diff. Any declaration-level difference is a bug; only import lines and implementation
bodies may differ. Expected `sorry` warnings in the comparator files are acceptable. New production
modules should compile without `sorry` warnings.
