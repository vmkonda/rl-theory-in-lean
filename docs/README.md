# Write-ups

Each write-up is a LaTeX source (`.tex`) with a generated Markdown version that renders on
GitHub. PDFs, with the same theorem and equation numbering, are built locally with
`./build.sh` and are not tracked in git.

| Topic | Markdown | Source |
|---|---|---|
| Policy gradients for discounted finite MDPs (formalized in Lean) | [policy-gradient.md](policy-gradient.md) | [tex](policy-gradient.tex) |
| Rates of convergence of TD(λ) in finite discounted MDPs | [td-lambda-rates.md](td-lambda-rates.md) | [tex](td-lambda-rates.tex) |
| Asymptotic covariance of linear SA with Markov noise | [markov-sa-covariance.md](markov-sa-covariance.md) | [tex](markov-sa-covariance.tex) |
| Two-time-scale SA with Markov and multiplicative noise | [two-time-scale-covariance.md](two-time-scale-covariance.md) | [tex](two-time-scale-covariance.tex) |
| Rates of actor-critic vs actor-only (loss in expected reward) | [actor-critic-rates.md](actor-critic-rates.md) | [tex](actor-critic-rates.tex) |

Results are labelled as theorems (proved), *cited facts* (used without proof), or
*observations* (supported only by computation; code in [`../experiments`](../experiments)).

## Checking the proofs

Each formalized statement is followed by a *Lean* note that names the theorem in `RLTheory/`.
To check it:

1. Build the library from the repository root: `lake exe cache get && lake build`. The build
   fails on any error, and a `sorry` shows up as a warning.
2. Check that a theorem rests only on the standard axioms. Put this in a scratch file and run
   `lake env lean <file>`:
   ```lean
   import RLTheory.Basic
   #print axioms StochasticApproximation.ScoreChain.restart_actor_loss_mono
   ```
   The expected output is `[propext, Classical.choice, Quot.sound]`.
3. Compare the Lean statement with the write-up. The hypotheses of the Lean theorem are the
   assumptions of the result; anything a chapter does not name as formalized is proved on paper only.

The actor-critic chapter ends with a section *What is checked in Lean* that lists what is
formalized and what is not.

## Rebuilding

Edit the `.tex` file, then run `./build.sh` (or `./build.sh <name>`), which regenerates
both the PDF and the Markdown. With no arguments it also builds `book.pdf`, the five chapters as one book with continuous
numbering (chapter.section.n), cross-references, a preface, a single bibliography and an appendix
on checking the formalization. The book is generated from the chapter sources by
[`book/make_book.py`](book/make_book.py), with front matter in [`book/book.tex`](book/book.tex). It requires `tectonic` and `pandoc`
(`brew install tectonic pandoc`). The Markdown conversion uses the Pandoc filter
[`tools/gfm.lua`](tools/gfm.lua).
