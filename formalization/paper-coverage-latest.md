# Lean coverage of the latest manuscript

Generated from [`spine.json`](spine.json) by `spine_gen.py`. The target is the latest
manuscript (arXiv version, manuscript commit cb23bf14); its auxiliary note is covered outside the spine (below). Each row is one spine
node `TorusEuler.Paper.<name>` of type `TorusEuler.Paper.Statement.<name>`, proved by
applying `Paper.Proof.<name>_of` to the spine nodes of exactly the cited results.
`VerifySpine.lean` checks the frontier, the content lists and the axioms.

Rows marked *library* are proved from the library and are not one-to-one with their TeX
proofs; for them the column lists what the TeX proof cites, which the checker does not enforce.
Only Remark 1.2 is a library row (decision D28): the auxiliary note (Aux 1.1-1.3) has no
spine rows; it is formalized by the library theorems `TorusEuler.auxiliaryTerminalSmoothness`,
`TorusEuler.auxiliaryLemma12` and `TorusEuler.auxiliaryLemma13`, which are not spine nodes.
Remark 1.2 is proved from `auxiliaryTerminalSmoothness`.

| Result | TeX | Lean | Proof cites | Setting | Notation only | Exports |
| --- | --- | --- | --- | --- | --- | --- |
| 1.1 | `cc:target:unforced` sections/01_problem.tex:60 | `theorem_1_1` | 8.1, 8.2, 8.3, 8.4, Text section8_setting |  |  |  |
| 1.2 | `unlabeled` sections/01_problem.tex:80 | `remark_1_2` | *library*; TeX cites: Aux 1.1 |  |  |  |
| 1.3 | `cc:uf:tower:lem:slow-orders` sections/01b_parameters.tex:54 | `lemma_1_3` | none |  |  |  |
| 2.1 | `cc:lem:wave` sections/02_affine.tex:9 | `lemma_2_1` | none |  |  |  |
| 2.2 | `cc:lem:frame` sections/02_affine.tex:65 | `lemma_2_2` | none |  |  |  |
| 2.3 | `cc:lem:strong-shear` sections/03_amplification.tex:113 | `lemma_2_3` | 2.2 |  |  |  |
| 2.4 | `cc:uf:exact:lem:additive` sections/03_amplification.tex:265 | `lemma_2_4` | 2.2 |  | 2.1, 2.3 | continuity of the error matrix E on [0,T] (sections/03_amplification.tex:640-648, variation of constants in the proof of Lemma 2.6); sup|sigma_p/sigma - 1| <= 2T delta from the proof (sections/03_amplification.tex:302-309), read by the proof of Lemma 2.7 (:847-850) |
| 2.5 | `cc:lem:model` sections/03_amplification.tex:452 | `lemma_2_5` | none |  |  |  |
| 2.6 | `cc:lem:finite-comparison` sections/03_amplification.tex:597 | `lemma_2_6` | 2.4, 2.5 |  |  |  |
| 2.7 | `cc:lem:new-wave-couplings` sections/03_amplification.tex:718 | `lemma_2_7` | 2.4, 2.5, 2.6 |  |  |  |
| 2.8 | `cc:prop:finite-return` sections/03_amplification.tex:894 | `proposition_2_8` | 2.4, 2.5, 2.6, 2.7 |  |  |  |
| 3.1 | `cc:uf:exact:lem:profile` sections/04_localized_wave.tex:152 | `lemma_3_1` | none |  |  |  |
| 4.1 | `cc:uf:mean:hardy` sections/06b_mean_inverse.tex:104 | `lemma_4_1` | none |  |  |  |
| 4.2 | `cc:uf:mean:inverse` sections/06b_mean_inverse.tex:143 | `theorem_4_2` | 4.1, A.1, A.2 |  |  |  |
| 5.1 | `cc:uf:trunc:prop:parent` sections/05b_parent_coefficients.tex:16 | `proposition_5_1` | B.1, D.2 |  |  |  |
| 5.2 | `cc:uf:mean:columns` sections/06d_mean_estimates.tex:22 | `proposition_5_2` | 5.1, D.1, Text eq_D_2, Text eq_5_14 |  |  |  |
| 5.3 | `cc:uf:tower:lem:inverse` sections/06c_finite_hierarchy.tex:54 | `lemma_5_3` | 3.1, 5.1, D.1, D.2, D.3 |  |  |  |
| 5.4 | `cc:uf:hier:prop:identity` sections/06c_finite_hierarchy.tex:304 | `proposition_5_4` | 4.2 |  |  | existence of the seed of Section 5.1 (the solution of (3.2) with (5.4) on [t0,T]), from which the profiles start; part of 'the profiles are well defined' |
| 5.5 | `cc:uf:hier:lem:relay` sections/06c_finite_hierarchy.tex:399 | `lemma_5_5` | 5.1, D.1 |  |  |  |
| 5.6 | `cc:uf:hier:thm:depth` sections/06c_finite_hierarchy.tex:469 | `theorem_5_6` | 5.1, 5.2, 5.3, 5.4, 5.5, D.1, B.1 |  |  |  |
| 5.7 | `cc:uf:hier:lem:physical` sections/08_exact_wave.tex:32 | `lemma_5_7` | 5.1, D.1 |  |  |  |
| 5.8 | `cc:uf:step:lem:approximate` sections/08_exact_wave.tex:82 | `lemma_5_8` | 5.3, 5.4, 5.5, 5.6, 5.7 |  |  |  |
| 5.9 | `cc:uf:step:lem:pressure-center` sections/08_exact_wave.tex:158 | `lemma_5_9` | 3.1, 4.2, 5.1, 5.3, 5.6, 5.7, B.1, D.1, 5.4 |  |  |  |
| 5.10 | `cc:uf:step:lem:flow-bounds` sections/08_exact_wave.tex:290 | `lemma_5_10` | 5.1, 5.6, 5.4 |  |  |  |
| 5.11 | `cc:uf:step:thm:step` sections/08_exact_wave.tex:379 | `proposition_5_11` | 5.8, 5.9, B.1, Text eq_5_59 |  |  |  |
| 6.1 | `cc:uf:base:lem:first` sections/03a_exact_base.tex:38 | `lemma_6_1` | 2.2 |  |  |  |
| 7.1 | `cc:uf:tower:thm:finite` sections/08b_induction.tex:142 | `theorem_7_1` | 1.3, 2.2, 2.5, 2.6, 2.7, 2.8, 5.4, 5.8, 5.9, 5.10, 5.11, 6.1, B.1 |  | 2.1 | the step data of the construction, in the vocabulary of Section 5, kept for the out-of-spine auxiliary statements (decision D28); read by no spine row (Theorem71Steps c a psi: for every step j >= 1 the parent U_{j-1} with its flow and pressure under the hypotheses of Subsection 5.1 with D = lambda_{j-1}^9 and lambda = lambda_j, wave j launched at t_j with its seed and its seed at the center a_j, the expansion of Subsection 5.5 at depth P = 6K_{j+1} with l_* = D^{-a} and the cutoff chi_j, the approximate solution V = U_{j-1} + W^nat, Pi = pi_{j-1} + P^nat with (5.46) of Lemma 5.8, U_j and pi_j the truncation S_{Lambda_j} V with the symbol psi, and O_j = W_osc^nat of Lemma 5.8), for every cutoff symbol psi of Appendix B and an envelope exponent a above any floor, both fixed before B; P.strengthConstant = C; the central waves, crossing windows, the comparison hypotheses (2.7) of item 2 for every constant and all large j (field comparison) and the window bound of item 2 (field window_upper), (5.5) of each wave and the bounds (7.7) (read by Section 8; 09b_terminal_properties.tex:28, :41) |
| 8.1 | `cc:uf:terminal:agreement` sections/09_limit.tex:11 | `proposition_8_1` | 1.3, Text eq_5_59 | 7.1 |  |  |
| 8.2 | `cc:uf:terminal:velocity-curl` sections/09b_terminal_properties.tex:3 | `proposition_8_2` | 1.3, 2.2, 2.4, B.1 | 7.1, 8.1 |  | the curl lower bound (8.2) displayed in the proof, passed to the limit u (Proposition82Conclusions.curl_lower), used by Corollary 8.3 in place of the Beale-Kato-Majda criterion |
| 8.3 | `cc:uf:terminal:time` sections/09b_terminal_properties.tex:69 | `corollary_8_3` | none | 7.1, 8.1, 8.2 |  |  |
| 8.4 | `cc:uf:terminal:off-origin` sections/09b_terminal_properties.tex:88 | `proposition_8_4` | 1.3 | 7.1, 8.1 |  |  |
| A.1 | `cc:holder:linear` sections/appA_mean_regularity.tex:26 | `theorem_A_1` | A.2 |  |  |  |
| A.2 | `cc:holder:freezing` sections/appA_mean_regularity.tex:71 | `lemma_A_2` | none |  |  |  |
| B.1 | `cc:uf:trunc:lem:cutoff` sections/appB_cutoff.tex:12 | `lemma_B_1` | none |  |  |  |
| Text eq_D_2 | `cc:uf:trunc:eq:holder-sup` sections/appD_finite_norms.tex:35 | `Text.eq_D_2` | none |  |  |  |
| D.1 | `cc:uf:trunc:lem:fields` sections/appD_finite_norms.tex:42 | `lemma_D_1` | none |  |  |  |
| D.2 | `cc:uf:trunc:lem:coefficients` sections/appD_finite_norms.tex:93 | `lemma_D_2` | none |  |  |  |
| D.3 | `cc:uf:trunc:lem:lifting` sections/appD_finite_norms.tex:133 | `lemma_D_3` | none |  |  |  |
| Text section8_setting | `unlabeled` sections/09_limit.tex:2 | `Text.section8_setting` | 7.1 |  |  |  |
| Text eq_5_59 | `cc:holder:product-growth` sections/08_exact_wave.tex (proof of Proposition 5.11) | `Text.eq_5_59` | none |  |  |  |
| Text eq_5_13 | `cc:uf:mean:thresholds` sections/06d_mean_estimates.tex:42 (proof of Proposition 5.2) | `Text.eq_5_13` | 5.1, D.2, Text eq_D_2 |  | 4.2 |  |
| Text eq_5_14 | `cc:uf:mean:holder-bound` sections/06d_mean_estimates.tex:56 (proof of Proposition 5.2) | `Text.eq_5_14` | 4.2, 5.1, D.2, D.3, Text eq_5_13 |  |  |  |
