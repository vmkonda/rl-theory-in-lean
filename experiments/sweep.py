"""Which lambda-patterns hold across many random MRPs?"""
import numpy as np
from td_lambda import MRP, td_lambda_exact, td_recursive_iv

lams = np.linspace(0, 0.99, 34)
stats = dict(iv_incr=0, bias_decr=0, td_ge_lstd=0, interior=0, n=0)
ratios, examples = [], []
for seed in range(300):
    rng = np.random.default_rng(seed)
    S = rng.integers(5, 15); m = rng.integers(1, min(S, 5))
    P = rng.random((S, S)) ** rng.uniform(1, 6); P /= P.sum(1, keepdims=True)
    mrp = MRP(P, rng.normal(size=S), rng.choice([0.8, 0.9, 0.95]))
    Phi = rng.normal(size=(S, m))
    res = [td_lambda_exact(mrp, Phi, l) for l in lams]
    iv = np.array([r.iv for r in res]); bias = np.array([r.bias for r in res])
    stats["n"] += 1
    stats["iv_incr"] += np.all(np.diff(iv) >= -1e-9 * iv[:-1])
    stats["bias_decr"] += np.all(np.diff(bias) <= 1e-9)
    pi = mrp.stationary()
    td = min(td_recursive_iv(res[10], Phi, pi, a) for a in np.geomspace(0.05, 500, 200))
    stats["td_ge_lstd"] += td >= res[10].iv * (1 - 1e-9)
    ratios.append(td / res[10].iv)
    # is the best lambda strictly inside (0,1) for some sample size?
    for n in [10, 100, 1000, 10000]:
        j = np.argmin(bias**2 + iv / n)
        if 0 < j < len(lams) - 1:
            stats["interior"] += 1; examples.append((seed, n, lams[j])); break
print(stats)
print("TD*/LSTD intrinsic-variance ratio at lambda=0.3: min %.3f median %.3f max %.3f"
      % (min(ratios), np.median(ratios), max(ratios)))
print("bias not monotone in", stats["n"] - stats["bias_decr"], "cases; IV not monotone in",
      stats["n"] - stats["iv_incr"])
print("examples with interior lambda*:", examples[:8])
