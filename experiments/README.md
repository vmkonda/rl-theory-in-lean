# Experiments

Exact asymptotic-rate computations for finite discounted MDPs, used in the write-ups in `docs/`.

Setup:

```
cd experiments
uv venv .venv && uv pip install --python .venv/bin/python numpy matplotlib
```

| Script | Purpose |
|---|---|
| `td_lambda.py` | Exact bias and intrinsic variance of TD(λ)/LSTD(λ); Monte Carlo checker |
| `trace_cov.py` | Exact long-run covariance of trace-driven Markov noise (general engine) |
| `ac_rates.py` | Actor-only and actor-critic: limits, asymptotic covariances, well-posed test MDPs |
| `check_exact.py` | Exact intrinsic variance vs simulation; basis invariance |
| `explore_lambda.py`, `sweep.py`, `sweep2.py`, `bias_dep.py` | λ and feature effects for TD(λ) |
| `figures_td.py` | Figures for `docs/td-lambda-rates.tex` |
| `compare_ac.py`, `check_patterns.py`, `summary_ac.py` | Actor-only vs actor-critic comparisons |
| `sim_ac.py`, `sim_ac_tuned.py` | Simulation of the actual two-time-scale algorithms vs predictions |
| `check_poisson.py` | Poisson-equation identities and the Markov-noise covariance theorem |
| `check_two_time_scale.py` | Two-time-scale covariance with Markov noise: simulation vs Corollary 2.2 |
| `rates_chapter.py` | Numbers for `docs/actor-critic-rates.tex`: Theorems 4.1–4.2 and the loss table |
| `explore_value_critic.py` | Tabular-critic noise covariance across λ vs REINFORCE (Observation 4.6) |
| `check_projection.py` | Monte Carlo regression of the REINFORCE noise on the actor-critic noise |
| `check_projection_exact.py`, `check_td0_gap.py` | Exact checks of Theorem 4.5 (orthogonality and the gap formula) |
| `crossover.py` | Finite-time loss of REINFORCE vs the tabular TD(0) critic as the table grows (Remark 4.7) |
