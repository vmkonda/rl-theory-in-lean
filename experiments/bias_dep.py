import numpy as np
from td_lambda import MRP, td_lambda_exact
lams = np.linspace(0, 0.99, 34); deps = []
for seed in range(300):
    rng = np.random.default_rng(seed)
    S = rng.integers(5, 15); m = rng.integers(1, min(S, 5))
    P = rng.random((S, S)) ** rng.uniform(1, 6); P /= P.sum(1, keepdims=True)
    mrp = MRP(P, rng.normal(size=S), rng.choice([0.8, 0.9, 0.95])); Phi = rng.normal(size=(S, m))
    b = np.array([td_lambda_exact(mrp, Phi, l).bias for l in lams])
    rise = max(0.0, max(np.maximum.accumulate(b[::-1])[::-1][1:] - b[:-1]))  # largest later increase
    rises = np.max(b[1:] - np.minimum.accumulate(b)[:-1])
    if rises > 1e-9: deps.append(rises / b[0])
print(len(deps), "non-monotone; largest rise relative to bias(0): %.4f, median %.4f" % (max(deps), np.median(deps)))
