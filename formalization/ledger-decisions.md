# Decisions on the citation ledger

The ledger [`spine.json`](spine.json) records, for every numbered result R of the manuscript,
the results that the TeX proof of R cites (`cites`), the cited displays (`text_cites`), the
results whose notation only is used (`notation_only`), the results whose objects form R's setting
(`setting`), and the library declarations that carry the proof of R (`content`). The checker
[`VerifySpine.lean`](lean/VerifySpine.lean) requires the Lean proof of R to take exactly the
cited results as hypotheses and to reach no declaration listed as content of another result.
A declaration listed nowhere is *glue*: it may be used by every proof.

The decisions below fix the ledger where the citations of the TeX are implicit, where a display
inside one proof is used by another, or where a library declaration is generic rather than the
proof of one result. Each was checked against the TeX of the arXiv version (manuscript commit
`cb23bf14`); line numbers refer to `paper/craik_criminale_rewrite/sections/`.

## General rules

* **Displays inside a proof.** A display inside the proof of a result R that a later proof cites
  is a separate node (`Text eq_*`). R's own proof either derives it in place or takes it from the
  node, and R's `text_cites` record which. No display is proved twice.
* **Running-text consequences of definitions**, for example (3.4), (5.16), (5.33), (5.42), (7.6),
  are glue.
* **Generic analytic facts** that the TeX uses without citation in several places (Leibniz and
  Hölder-algebra product bounds, Faà di Bruno bounds, norm identities) are glue, also when one
  display states them. Where the TeX does cite such a display, the proof takes it from the node.
* **Implicit citations.** When a proof uses a conclusion of a result without naming it (for
  example "the profiles of Proposition 5.4"), the result is cited.

## Decisions

| # | Decision | Evidence |
| --- | --- | --- |
| D1 | `hierarchyFiniteWordNorm_holder_le` is content of Text eq_D_2 | it is the bound that (D.2) states (appD_finite_norms.tex:35); `paperAppendixD_holderComparison` wraps it |
| D2 | `norm_iteratedFDeriv_ringInverse_comp_le` is glue, not content of D.2 | a generic Faà di Bruno bound for `Ring.inverse ∘ F`; the proof of Lemma A.2 uses it for the frozen symbol without citing Lemma D.2 |
| D3 | `spatialHolderHalf_bilinear` is glue; the proof of 5.11 takes (5.59) from the node Text eq_5_59 | (5.59) is stated "by Leibniz' rule and the algebra inequality" (08_exact_wave.tex:424-428); the proofs of A.2 and 5.9 use the product rule without citing it |
| D4 | `paperMeanIntegratedInverse_of_coercivity` is content of A.1, not of 4.2 | it carries the proof of Theorem A.1 (appA_mean_regularity.tex:199-240); the proof of Theorem 4.2 rescales and cites A.1 |
| D5 | the passage between (4.11) and (4.9) (`exists_of_displacement_pressure_equation`, `exists_integratedSolution`) is glue | running text before Theorem 4.2: (4.9) is (4.11) "integrated once in time" (06b_mean_inverse.tex:136-139) |
| D6 | (3.4) is glue | derived in running text from the seed equation (04_localized_wave.tex:68-74) |
| D7 | `exists_seedOn_of_coframe_bounds`, `exists_seedOn_of_parent_bounds` are content of 5.3 | they prove (5.19) by the variation-of-constants argument of the proof of Lemma 5.3 |
| D8 | the two lemmas of the proof of Lemma 2.3 are its content | they carry its two conclusions |
| D9 | Lemma 5.10 cites Proposition 5.4 | Subsection 5.6 starts from "the profiles W, 𝖯 of Proposition 5.4" (08_exact_wave.tex:1-7); the proof uses 𝐝̃·W = 0 (:300-302) |
| D10 | the product bounds in the proof of 5.10 are pointwise Leibniz glue | |
| D11 | Theorem 7.1 exports the comparison hypotheses (2.7) and the window bound of item 2 of its proof (fields `comparison`, `window_upper` of `Theorem71Conclusions`) | item 2 checks (2.7) and bounds the normalized window (08b_induction.tex:306-326); the proof of Proposition 8.2 reads them "by item 2 of the proof of Theorem 7.1" (09b_terminal_properties.tex:28, :41) |
| D13 | displays (5.13) and (5.14) are nodes (Text eq_5_13, eq_5_14) | they are cited outside the proof of Proposition 5.2, in the auxiliary note (terminal_smoothness.tex:254, :261) |
| D17 | Proposition 5.2 cites 5.1 and D.1 and the displays (D.2) and (5.14) | Theorem 4.2, Lemmas D.2, D.3 and (5.13) enter its proof only through (5.13), (5.14) (06d_mean_estimates.tex:30-58) |
| D18 | Text eq_5_13 cites 5.1 and D.2; Theorem 4.2 is notation only | the constant A of (4.10) enters as a hypothesis A ≤ 𝖣^{C_A} supplied by the citing proofs |
| D19 | Text eq_5_14 cites 4.2, 5.1, D.2, D.3 and the display (5.13) | the bound A ≤ 𝖣^C comes from 5.1 and D.2(a) (06d_mean_estimates.tex:24-38) |
| D20 | `periodicPoissonPressure_unique` is glue | uniqueness of zero-mean periodic solutions of the Poisson equation |
| D21 | Lemma 5.9 cites Proposition 5.4 | the supports and the vanishing before t₀ of the profiles (08_exact_wave.tex:226, :266-267) |
| D22 | `affineWave_propagation` is glue; Lemma 2.1 is notation only for Theorem 7.1 | the persistence of κ·𝐚 = 0 along (2.1) holds for every background B and is used in running text (04_localized_wave.tex:58-59, 08b_induction.tex:296), where the hypothesis of Lemma 2.1 fails |
| D23 | Theorem 7.1 cites Lemma 2.5 | Propositions 2.6-2.8 are statements about the reference solution Y of (2.12), which Lemma 2.5 provides |
| D27 | `appendixFiniteDerivativeNorm_scaled` is glue | it factors the weights out of the finite derivative norm (D.1), an identity of the definition |
| D28 | the auxiliary note is formalized by the library theorems `auxiliaryTerminalSmoothness`, `auxiliaryLemma12`, `auxiliaryLemma13`, outside the spine; Remark 1.2 is proved from `auxiliaryTerminalSmoothness` (ledger mode `library`) and is the only node exempt from the one-to-one checks | the note is unchanged since the manuscript of 18 November 2026 except for the title of the main paper; the library results concern one construction (the dyadic cutoff symbol and a large exponent), not every construction with the conclusions of Theorem 7.1 |
| D29 | (7.6), used in the proof of Proposition 8.2 (09b_terminal_properties.tex:41), is glue: a consequence of Lemma B.1 applied to (T1)-(T2) of Theorem 7.1, so 8.2 cites B.1. The implicit citations 2.6 → 2.5, 2.7 → 2.4, 5.6 → B.1, 5.9 → 3.1, 8.1 → 1.3, 8.4 → 1.3 are recorded in the row notes | |

Decisions D12, D14-D16 and D24-D26 concerned rows of the auxiliary note and the display (5.58),
which are no longer in the ledger after D28. The displays (5.1), (5.2), (5.5), (5.6), which the
proof of Theorem 7.1 uses, are running-text glue.

**Route of Corollary 8.3.** The TeX proof cites the periodic Beale–Kato–Majda criterion, which is
not formalized. The Lean proof obtains the divergence of the curl integral from the curl lower
bound displayed in the proof of Proposition 8.2, which Proposition 8.2 exports.
