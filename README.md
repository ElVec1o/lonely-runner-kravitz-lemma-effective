# An effective all-residue form of Kravitz's lemma, with applications to deleting one speed

Pre-release draft of 25 November 2026 (private repository). Author: Vico Bonfioli. License: CC-BY-4.0 (`LICENSE.md`). Not peer reviewed. No DOI yet.
Paper: `paper/paperA2.pdf` (source `paper/paperA2.tex`). Companion drafts (not released): the other two papers of the series; dependency diagram `paper/dependency.pdf`.

## Abstract

For a finite set B of positive integers (speeds) let ML(B) = max_t min_{b in B} dist(tb, Z); the Lonely Runner Conjecture says ML >= 1/(N+1) for every set of N speeds. Kravitz showed that adding one very large speed w to B changes ML(B) by an explicit formula but, except for a remark after his Lemma 9.4, gave no size for "very large" and treated the added speed only in special residue classes.
The paper gives two effective forms. Theorem 1.1 is his Lemma 9.4 (the added speed is an integer at the top peaks, for instance a multiple of the lcm of their denominators): ML(B u {w}) = wL/(w+v_mu) for w >= 2(max B)^3, with an upper bound for every admissible w. Theorem 1.2 is the all-residue form: a closed form H_p(w) at each local maximum p of the profile of B, the upper bound max_p H_p(w) for every positive integer w, and equality for w >= 2M(M-1), where M bounds the speeds of B. Both are evaluated for {1,...,N} with one speed r <= N/2 deleted, whose loneliness is Liu's value 2/D_0 (D_0 the least integer >= N+1+r coprime to r): this gives the exact loneliness after a multiple w >= 2N^2 of D_0 is added (Theorem 1.3) and bounds for every w >= 4N (Proposition 4.3).

## Idea of the proof

Near a peak p of the profile f of B, f lies under a tent with slope rho_p on the left and -lambda_p on the right, where rho_p and lambda_p are the speeds of the fastest runners at distances +mu_p and -mu_p from an integer at time p. An added speed w contributes the sawtooth dist(theta + wh) at time p+h, theta = wp mod 1, and ML(B u {w}) is the height of the highest point under both. Theorem 1.1 is this picture at the top peaks: a speed w that is an integer at the peak cuts all peaks at one height, wL/(w+v_mu). Theorem 1.2 applies it at every peak: the highest point under both is H_p(w), and for large w the crossing is so close to the peak that no old runner can interfere.

## Main results

Numbers are those of the PDF of this version. "Lean" means: the declarations named are in the Lean repository `lonely-runner-near-tight-lean`, the saved build logs of the author's development tree end with `Build completed successfully`, no `sorryAx` occurs and only the three standard axioms are printed; a clean-checkout build of the umbrella module `LRSpectrumFull.Sext6.Gap.All` (362 modules, public five-speed v1.0.2 plus the overlay) was run on 25 November 2026: 0 failures, and its axiom output is identical to the saved one; the larger `Release` closure was not rebuilt from a clean checkout. The status of every statement of the paper (Lean, hand, computed, conjecture) is the table "Status per statement" in the paper; where the entry below says mixed, that table decides.

| paper | statement (short; the paper has the full statement) | label |
|---|---|---|
| Theorem 1.1 | Kravitz's Lemma 9.4 with a size: `ML(B u {w}) = wL/(w+v_mu)` for `w >= 2(max B)^3` with `wp` an integer at every equality time; upper bound for every admissible `w` | Lean (`Gap.Kstar_E`, `K_upper`, `K_eq`); the term `L2` of part (a) is by hand |
| Corollary 2.8 | Kravitz's Theorem 5.1: `ML(1,...,n-1,ns) = s/(ns+1)`, `n >= 3` | Lean (`Gap.kravitz_5_1`) |
| Theorem 1.2 | all-residue insertion: `ML(B u {w}) <= max_p H_p(w)` for every `w`; equality for `w >= 2M(M-1)` when `ML(B) < 1/2` | Lean in the form with a number `c` (`Gap.ML_snoc_le_Hform`, `ins_E`); the identification of `c` with the maximum over all peaks is by hand |
| Theorem 1.3 | exact loneliness of `[N]\{r}` with a multiple `w >= 2N^2` of `D_0` added; the extremal times and slopes | Lean for the one-entry engine (`OneRL2Val`); orientation of the slopes by hand |
| Proposition 4.3 | bounds for every `w >= 4N` | hand (reviewed by a second pass of an AI system); computed checks (`14 <= N <= 120`, `N = 14..40`); not Lean |
| Conjecture 3.3 | equality in Theorem 1.2 already for `w >= (max B)^2` | CONJECTURE (evidence: 3,392,809 pairs over 1,604 bases, no failure; computed) |

Companions: A2 is readable alone; A1 cites it for two hand proofs, and A2 uses A1 only in Remark 2.9. A footnote of Section 1.2 and Appendix A state, hedged, that the pairing of residue terms in the arXiv v1 print of Kravitz's Lemma 10.1 appears to be swapped relative to its own definitions; this has not been checked with the published version or with the author of that lemma.

## Where the evidence is

* Lean: `Gap/KStar*`, `Ins*`, `OneRArc`, `OneRVal`, `OneRL2`, `OneRL2Val`, `OneRG`, `OneRGh` (rows 20 to 22 of `repro/MAP.md` in the Lean repository). Saved `#print axioms` lines: `repro/expected_output/` of the Lean repository (names as cited in the paper's Lean section); verdict script `repro/judge_axioms.sh`.
* Computed: `code/` (Theorem K* engines, insertion-formula engine, one-entry engines). See `code/README.md`: which program supports which statement is the packager's identification, not re-run; a list of computed statements with no identified program is at its end.
* By hand: the arguments of the paper marked "hand"; the ones marked "reviewed" were re-derived by a second pass of an AI system that did not write them. No human referee has read the paper.

## Not done yet

Blind reads by independent readers of the current text, the talk and the FAQ of the release rules, a refresh of the prior-art search (searches of 25 November 2026 are described in the paper and expire), a clean-checkout build of the full `Release` closure of the Lean repository, and a reproduction script for the computed tables.

## Build the paper

`pdflatex` on `paper/paperA2.tex`, three rounds (the three drafts read each other's `.aux` files through `xr-hyper`; the companion `.aux` files of this version are in `paper/`; a companion number prints as `??` if they are missing). Compile the companions to regenerate them.

## Files

| path | content |
|---|---|
| `paper/` | `paperA2.tex`, `paperA2.pdf`, companion `.aux` files, `dependency.tex`, `dependency.pdf` |
| `code/` | the programs cited as "computed" (Rust, C), `build.sh`, `tools/launch_lite.sh`, `README.md` |
| `CHECKSUMS.sha256` | sha256 of every file of this repository except itself; check: `shasum -a 256 -c CHECKSUMS.sha256 | grep -vc ': OK'` prints `0` |
| `CITATION.cff`, `LICENSE.md`, `.gitignore` | citation data, license |

## Use of AI

The mathematical ideas, proofs, computations, Lean code and text of this work were produced with substantial assistance from AI systems (Anthropic's Claude models), working under the direction of the author, V. Bonfioli, who selected the problems, set the standards of verification, reviewed the results and takes responsibility for the contents. Every statement marked Lean-verified is checked by the Lean kernel and the printed axiom lists, not by the author or the AI systems; computed statements come from the programs in the paper repositories; statements labelled by hand are not machine-checked. The arguments marked reviewed were re-derived by a second pass of an AI system that did not write them; no human referee has read them. The arguments have not been refereed.

## Prior art and credit

* Goddyn and Wong (tight instances; the acceleration and the numerical criterion), Kravitz (barely lonely runners; the lemmas on one added speed and Theorem 5.1), Liu (the value of the one-deletion set; survey), Zhang (one-entry modifications and tight instances; Lemma 5.3, Question 8.1), Peng (unrefereed record 24363090), Fan and Sun (amended spectrum conjecture), Jain and Kravitz (relative spectra), Giri and Kravitz (structure of spectra), Yi, Gill and Bu (four runners; the height method), Cordella (six and seven speeds), and the unrefereed repository of 1337isnot1337. Full references and the exact attribution of each result are in the papers (sections "Attribution" and "Prior art").
