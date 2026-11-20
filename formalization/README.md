# Torus Euler formalization

The Lean targets follow the torus paper and terminal smoothness note frozen
at `torus-paper-freeze-2026-11-18` (manuscript `65d47fd`).
[`Theorem11`](lean/TorusEuler/Statement.lean) states the main theorem on
periodic Euclidean lifts. [`TorusEuler.theorem11`](lean/TorusEuler/Theorem11.lean)
proves the main theorem. [`TorusEuler.auxiliaryTerminalSmoothness`](lean/TorusEuler/AuxiliaryTerminalSmoothness.lean)
proves the stronger extension for the same Euler solution and selected
sequence, with both auxiliary estimates. The [proof blueprint](blueprint.md)
records the statement correspondence and the proof dependencies.

## Build and verify

The project uses Lean
`v4.34.0-rc2` and mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
The [lockfile](lean/lake-manifest.json) records the full dependency set.
From `formalization/lean`, on a host with working Lake, obtain the package
cache with `lake exe cache get`, then run

```sh
lake build
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true Verify.lean
```

Lake exited with code 133 on the host used for the original checkpoint.
The pinned native arm64 toolchain runs Lake on the recovered checkout.
For hosts where Lake fails, build or obtain the locked package checkouts in
`.lake/packages`. Then `python3 check.py` checks their Git revisions, follows the imports from
`TorusEuler.lean`, compiles them in a fresh temporary directory with Lean
directly, and runs
[`Verify.lean`](lean/Verify.lean). The verifier checks the types of both
unconditional theorems and the transitive axiom dependencies of all
imported `TorusEuler` declarations.

The [paper coverage ledger](paper-coverage.md) maps the numbered results
of the frozen main paper and auxiliary note to their Lean declarations.
Run the coverage check from `formalization/lean` after `lake build`.

```sh
TORUS_PAPER_REQUIRE_COMPLETE=1 lake env lean \
  -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true VerifyPaper.lean
```

This mode requires a verified theorem for every frozen assertion, including
the unconditional auxiliary theorem. It checks the source anchors and the
transitive axiom dependencies of the listed declarations.

[Draft proof attempts](drafts/README.md) are kept outside the library.

## Archive provenance

Some declarations are adapted from the CCPoint Lean project (Lean `v4.32.2`, mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`), distributed under the
[Apache 2.0 license](../sources/ccpoint-lean/LICENSE); see its
[notice](../sources/ccpoint-lean/NOTICE).
