"""Bias / intrinsic variance of TD(lambda) as functions of lambda and of the features."""
import numpy as np
from td_lambda import (random_mrp, ring_mrp, fourier_features, td_lambda_exact,
                       td_recursive_iv, mixing_factor)

lams = [0.0, 0.3, 0.5, 0.7, 0.9, 0.95, 0.99]
rng = np.random.default_rng(1)
cases = {
    "random": (random_mrp(8, 0.9, seed=3), rng.normal(size=(8, 3))),
    "ring":   (ring_mrp(30, 0.95, stay=0.5, seed=0), fourier_features(30, 3)),
}
for name, (mrp, Phi) in cases.items():
    pi = mrp.stationary()
    print(f"\n== {name}: S={mrp.S}, m={Phi.shape[1]}, gamma={mrp.gamma}, SLEM={mixing_factor(mrp.P):.3f}")
    print(f"{'lam':>5} {'kappa':>7} {'bias':>8} {'TvR bnd':>8} {'proj':>7} {'IV_LSTD':>9} {'IV_TD*':>9} {'alpha*':>7}")
    for lam in lams:
        r = td_lambda_exact(mrp, Phi, lam)
        kappa = mrp.gamma * (1 - lam) / (1 - mrp.gamma * lam)
        alphas = np.geomspace(0.05, 200, 300)
        tds = [td_recursive_iv(r, Phi, pi, a) for a in alphas]
        i = int(np.argmin(tds))
        print(f"{lam:5.2f} {kappa:7.3f} {r.bias:8.4f} {r.proj_err/np.sqrt(1-kappa**2):8.4f} "
              f"{r.proj_err:7.4f} {r.iv:9.3f} {tds[i]:9.3f} {alphas[i]:7.2f}")
    print("  best lambda for n samples (minimizing bias^2 + IV/n):")
    fine = np.linspace(0, 0.995, 200)
    res = [td_lambda_exact(mrp, Phi, l) for l in fine]
    for n in [10**2, 10**3, 10**4, 10**5, 10**6]:
        mse = [x.bias**2 + x.iv / n for x in res]
        j = int(np.argmin(mse))
        print(f"    n=1e{int(np.log10(n))}: lambda*={fine[j]:.3f}  mse={mse[j]:.4f}  (lam=0: {mse[0]:.4f}, lam=.99: {mse[-1]:.4f})")

print("\n== ring: effect of adding features (nested Fourier bases), lambda=0.5")
mrp = cases["ring"][0]
for m in [1, 3, 5, 7, 9, 15]:
    r = td_lambda_exact(mrp, fourier_features(30, m), 0.5)
    print(f"  m={m:2d}: bias={r.bias:.4f}  proj={r.proj_err:.4f}  IV={r.iv:9.3f}")
