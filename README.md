# Finite-Time Singularity Formation for the Three-Dimensional Euler Equations

Levent Alpöge, Tristan Buckmaster and Matei P. Coiculescu

This repository contains the manuscript, its auxiliary note on terminal smoothness, and a Lean 4
formalization of the main theorem.

## Manuscript

[`manuscript/paper.pdf`](manuscript/paper.pdf) is the version submitted to arXiv.
[`manuscript/source/`](manuscript/source) is the arXiv source package: the TeX, the figures, and the
auxiliary note in [`anc/auxiliary/`](manuscript/source/anc/auxiliary) (TeX and PDF).

## Lean formalization

[`formalization/`](formalization) is a Lean 4 formalization by the authors.
`TorusEuler.Theorem11` in [`Statement.lean`](formalization/lean/TorusEuler/Statement.lean) states
Theorem 1.1. `TorusEuler.theorem11` in
[`Theorem11.lean`](formalization/lean/TorusEuler/Theorem11.lean) proves it without hypotheses, and
`TorusEuler.auxiliaryTerminalSmoothness` proves the smooth extension of the auxiliary note. The
sources contain no `sorry`, and these theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The project uses Lean `v4.34.0-rc2` and the mathlib revision
fixed in [`lake-manifest.json`](formalization/lean/lake-manifest.json). Build instructions, the
proof blueprint and the correspondence with the numbered results are in
[`formalization/README.md`](formalization/README.md),
[`blueprint.md`](formalization/blueprint.md) and
[`paper-coverage.md`](formalization/paper-coverage.md). In this copy, the links to the frozen
manuscript point to [`frozen-manuscript/`](frozen-manuscript), and the notes on the development
workflow were removed from `formalization/README.md`. The Lean sources are unchanged except for
comments that give the path of the adapted files in [`sources/ccpoint-lean/`](sources/ccpoint-lean).

This formalization follows the frozen version of the manuscript of 18 November 2026 in
[`frozen-manuscript/`](frozen-manuscript), not the arXiv version above. We will soon provide a Lean
formalization in one-to-one correspondence with the arXiv version of the manuscript.

Some declarations are adapted from an earlier Lean development distributed under the Apache License
2.0; its [license](sources/ccpoint-lean/LICENSE) and
[notice](sources/ccpoint-lean/NOTICE) are included.

## Frozen manuscript

[`frozen-manuscript/`](frozen-manuscript) is the manuscript and the auxiliary note as frozen on
18 November 2026, the version that the Lean formalization follows:
[`paper.pdf`](frozen-manuscript/paper.pdf),
[`auxiliary/terminal_smoothness.pdf`](frozen-manuscript/auxiliary/terminal_smoothness.pdf) and the
TeX source. For packaging, the figure paths in the TeX point to
[`frozen-manuscript/figures/`](frozen-manuscript/figures), which holds the figures of the arXiv
package; the scripts that generate them are the same for both versions. The arXiv version differs
from the frozen one by a revision of Section 2 (scaled components, the reference angle and a
separate coupling lemma, which changes the numbering in Section 2) and by edits to the
introduction.
