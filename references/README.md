# References

## Konda (2002), *Actor-Critic Algorithms*

PhD thesis, MIT EECS, June 2002. Advisor: John N. Tsitsiklis.
Available on [MIT DSpace](https://dspace.mit.edu/entities/publication/de41d9e3-f2ba-4327-bdaa-32014dd235ae).

- `konda-2002-actor-critic-algorithms.pdf` is the scanned thesis (147 pages). It is git-ignored, so download it from the DSpace link above and save it here under this name.
- `konda-2002-actor-critic-algorithms.txt` is OCR text pulled from the PDF so it can be searched with grep. Page markers look like `===== page N =====`. Math does not survive OCR well, so check the PDF before formalizing anything.

### How the chapters relate to this repo

| Thesis chapter | Topic | Related code here |
|---|---|---|
| 2 | Policy gradient formulas (average, discounted, total reward) | `MarkovDecisionProcess/` |
| 3 | Linear SA driven by slowly varying Markov chains | `StochasticApproximation/MarkovSamples.lean`, `Iterates.lean` |
| 4 | The critic: TD(λ) with linear function approximation | `Algorithm/LinearTD.lean` (currently TD(0)) |
| 5 | Actor-critic algorithms and their convergence (two time scales) | none yet |
| 6 | Rate of convergence of TD and LSTD | none yet |
| 7 | Rate of convergence of two-time-scale SA | none yet |
| 8 | Rate of convergence of actor-critic algorithms | none yet |
