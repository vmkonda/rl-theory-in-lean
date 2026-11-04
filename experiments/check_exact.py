"""Validate the exact intrinsic-variance formula against Monte Carlo LSTD(lambda)."""
import numpy as np
from td_lambda import random_mrp, ring_mrp, fourier_features, td_lambda_exact, simulate_lstd_iv

rng = np.random.default_rng(1)
cases = [
    ("random S=8, m=3", random_mrp(8, 0.9, seed=3), rng.normal(size=(8, 3))),
    ("ring S=12, m=3", ring_mrp(12, 0.9, stay=0.3, seed=0), fourier_features(12, 3)),
]
for name, mrp, Phi in cases:
    for lam in [0.0, 0.5, 0.9]:
        res = td_lambda_exact(mrp, Phi, lam)
        mc = simulate_lstd_iv(mrp, Phi, lam, n_steps=4000, n_runs=4000, r_star=res.r_star, seed=7)
        print(f"{name:18s} lam={lam:.1f}  exact IV={res.iv:9.4f}   MC IV={mc:9.4f}   ratio={mc/res.iv:.3f}")
    # basis invariance (thesis Sec 6.2.1): Phi -> Phi B
    B = rng.normal(size=(Phi.shape[1],) * 2)
    print(f"{'':18s} basis change: IV {td_lambda_exact(mrp, Phi, 0.5).iv:.6f} -> {td_lambda_exact(mrp, Phi @ B, 0.5).iv:.6f}")
