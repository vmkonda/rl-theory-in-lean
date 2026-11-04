"""Figures and numbers for docs/td-lambda-rates.tex."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from td_lambda import MRP, random_mrp, ring_mrp, fourier_features, td_lambda_exact, mixing_factor

plt.rcParams.update({"font.size": 10, "figure.dpi": 150})
lams = np.linspace(0, 0.99, 100)

def curves(mrp, Phi):
    res = [td_lambda_exact(mrp, Phi, l) for l in lams]
    return np.array([r.bias for r in res]), np.array([r.iv for r in res]), res[0].proj_err

def sweep_instance(seed):
    rng = np.random.default_rng(seed)
    S = rng.integers(5, 15); m = rng.integers(1, min(S, 5))
    P = rng.random((S, S)) ** rng.uniform(1, 6); P /= P.sum(1, keepdims=True)
    return MRP(P, rng.normal(size=S), rng.choice([0.8, 0.9, 0.95])), rng.normal(size=(S, m))

# counterexample: largest relative drop of IV in lambda
best = None
for seed in range(300):
    mrp, Phi = sweep_instance(seed)
    iv = np.array([td_lambda_exact(mrp, Phi, l).iv for l in np.linspace(0, .99, 34)])
    drop = (iv.max() - iv[-1]) / iv.max()
    if best is None or drop > best[0]:
        best = (drop, seed)
print("largest IV drop: %.2f at seed %d" % best)
cx_mrp, cx_Phi = sweep_instance(best[1])
print("  S=%d m=%d gamma=%.2f SLEM=%.3f" % (cx_mrp.S, cx_Phi.shape[1], cx_mrp.gamma, mixing_factor(cx_mrp.P)))

rng = np.random.default_rng(1)
panels = [("(a) random chain, $S=8$, $m=3$, $\\gamma=0.9$", random_mrp(8, 0.9, seed=3), rng.normal(size=(8, 3))),
          ("(b) ring, $S=30$, Fourier $m=3$, $\\gamma=0.95$", ring_mrp(30, 0.95, stay=0.5, seed=0), fourier_features(30, 3)),
          ("(c) counterexample (seed %d)" % best[1], cx_mrp, cx_Phi)]
fig, axes = plt.subplots(1, 3, figsize=(11, 3.1))
for ax, (title, mrp, Phi) in zip(axes, panels):
    bias, iv, proj = curves(mrp, Phi)
    kappa = mrp.gamma * (1 - lams) / (1 - mrp.gamma * lams)
    ax.plot(lams, bias, color="C0", label="bias $\\|\\Phi r^*_\\lambda - V\\|_D$")
    ax.plot(lams, proj / np.sqrt(1 - kappa**2), color="C0", ls=":", label="bound (Thm 2.5)")
    ax.axhline(proj, color="C0", ls="--", lw=0.8, label="$\\|\\Pi V - V\\|_D$")
    ax.set_xlabel("$\\lambda$"); ax.set_title(title, fontsize=9)
    ax2 = ax.twinx(); ax2.plot(lams, iv, color="C3", label="intrinsic variance")
    ax2.tick_params(axis="y", colors="C3")
    if ax is axes[0]:
        h1, l1 = ax.get_legend_handles_labels(); h2, l2 = ax2.get_legend_handles_labels()
        ax.legend(h1 + h2, l1 + l2, fontsize=7, loc="upper center")
fig.tight_layout(); fig.savefig("../docs/figures/td_bias_variance.png")

# best lambda as a function of n
fig, ax = plt.subplots(figsize=(4.5, 3))
ns = np.geomspace(1, 1e5, 60)
for (title, mrp, Phi), c in zip([panels[0], panels[2]] + [("seed 0",) + sweep_instance(0), ("seed 5",) + sweep_instance(5)], ["C0", "C2", "C1", "C4"]):
    bias, iv, _ = curves(mrp, Phi)
    ax.plot(ns, [lams[np.argmin(bias**2 + iv / n)] for n in ns], color=c, label=title.split(",")[0])
ax.set_xscale("log"); ax.set_xlabel("number of samples $n$"); ax.set_ylabel("$\\lambda^*(n)$")
ax.legend(fontsize=7); fig.tight_layout(); fig.savefig("../docs/figures/td_best_lambda.png")
print("saved figures")
