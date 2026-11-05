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

## Rebuilding

Edit the `.tex` file, then run `./build.sh` (or `./build.sh <name>`), which regenerates
both the PDF and the Markdown. It requires `tectonic` and `pandoc`
(`brew install tectonic pandoc`). The Markdown conversion uses the Pandoc filter
[`tools/gfm.lua`](tools/gfm.lua).
