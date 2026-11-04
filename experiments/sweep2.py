import numpy as np
from td_lambda import MRP, td_lambda_exact
lams = np.linspace(0, 0.99, 34)
both = ivonly = bonly = 0; ms = []; mags = []
for seed in range(300):
    rng = np.random.default_rng(seed)
    S = rng.integers(5, 15); m = rng.integers(1, min(S, 5))
    P = rng.random((S, S)) ** rng.uniform(1, 6); P /= P.sum(1, keepdims=True)
    mrp = MRP(P, rng.normal(size=S), rng.choice([0.8, 0.9, 0.95]))
    Phi = rng.normal(size=(S, m))
    res = [td_lambda_exact(mrp, Phi, l) for l in lams]
    iv = np.array([r.iv for r in res]); bias = np.array([r.bias for r in res])
    a = not np.all(np.diff(iv) >= -1e-9 * iv[:-1]); b = not np.all(np.diff(bias) <= 1e-9)
    both += a and b; ivonly += a and not b; bonly += b and not a
    if a: ms.append(int(m)); mags.append(float((iv.max() - iv[-1]) / iv.max()))
    if b and seed < 60: print(f"seed {seed}: m={m}, bias(0)={bias[0]:.3f} min={bias.min():.3f} at lam={lams[bias.argmin()]:.2f}, bias(.99)={bias[-1]:.3f}")
print("non-monotone: both", both, "IV only", ivonly, "bias only", bonly)
print("m among IV-non-monotone:", np.bincount(ms), " max relative IV drop:", max(mags))
