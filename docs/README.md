# Write-ups

Each write-up is a LaTeX source (`.tex`) with two generated versions: a PDF and a Markdown
file that renders on GitHub, both with the same theorem and equation numbering.

| Topic | Markdown | PDF |
|---|---|---|
| Policy gradients for discounted finite MDPs (formalized in Lean) | [policy-gradient.md](policy-gradient.md) | [PDF](policy-gradient.pdf) |
| Rates of convergence of TD(λ) in finite discounted MDPs | [td-lambda-rates.md](td-lambda-rates.md) | [PDF](td-lambda-rates.pdf) |
| Asymptotic covariance of linear SA with Markov noise | [markov-sa-covariance.md](markov-sa-covariance.md) | [PDF](markov-sa-covariance.pdf) |

Results are labelled as theorems (proved), *cited facts* (used without proof), or
*observations* (supported only by computation; code in [`../experiments`](../experiments)).

## Rebuilding

Edit the `.tex` file, then run `./build.sh` (or `./build.sh <name>`), which regenerates
both the PDF and the Markdown. It requires `tectonic` and `pandoc`
(`brew install tectonic pandoc`). The Markdown conversion uses the Pandoc filter
[`tools/gfm.lua`](tools/gfm.lua).
