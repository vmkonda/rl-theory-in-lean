"""Is the value-function critic's noise covariance below actor-only's, and monotone in lambda?

At theta* both methods are unbiased with the same H, so (Proposition 3.6) the loss comparison is
the Loewner comparison of the effective noise covariances Gamma(lambda) (tabular critic) and
Gamma_AO (REINFORCE). For each well-posed instance we report
  min eigenvalue of Gamma_AO - Gamma(0)                      (>= 0: critic better, Loewner)
  min eigenvalue of Gamma(lam_i) - Gamma(lam_{i+1})  over a decreasing lambda grid (>= 0: monotone)
"""
import warnings
import numpy as np
from ac_rates import aliased_mdp, optimum, Critic, actor_only_direction, actor_critic_direction

warnings.filterwarnings("ignore")
lams = [1.0, 0.8, 0.6, 0.4, 0.2, 0.0]


def instances(count, S, A, groups, gam, start=0):
    out = []
    for seed in range(start, start + 4000):
        mdp = aliased_mdp(S, A, groups, gam, seed)
        n = mdp.n
        try:
            th, HJ = optimum(mdp, np.zeros(n))
        except Exception:
            continue
        if np.linalg.norm(mdp.grad_J(th)) > 1e-9 or np.abs(th).max() > 6 \
                or np.min(np.linalg.eigvalsh((HJ + HJ.T) / 2)) <= 0:
            continue
        out.append((seed, mdp, th))
        if len(out) == count:
            break
    return out


rows = []
for (S, A, groups, gam, count) in [(5, 2, [0] * 5, 0.9, 25), (6, 2, [0, 0, 0, 1, 1, 1], 0.9, 15),
                                   (6, 3, [0] * 6, 0.8, 15), (8, 2, [0] * 4 + [1] * 4, 0.95, 10),
                                   (4, 2, [0] * 4, 0.5, 15)]:
    for seed, mdp, th in instances(count, S, A, groups, gam):
        _, Gao = actor_only_direction(mdp, th, 1.0, True)
        G = []
        for lam in lams:
            _, Gl = actor_critic_direction(mdp, th, Critic(lam, np.eye(S)), True)
            G.append((Gl + Gl.T) / 2)
        Gao = (Gao + Gao.T) / 2
        dom = np.min(np.linalg.eigvalsh(Gao - G[-1])) / np.max(np.linalg.eigvalsh(Gao))
        mono = min(np.min(np.linalg.eigvalsh(G[i] - G[i + 1])) for i in range(len(lams) - 1)) \
            / np.max(np.linalg.eigvalsh(Gao))
        ratio = np.trace(G[-1]) / np.trace(Gao)
        rows.append((S, A, mdp.n, gam, seed, dom, mono, ratio, np.abs(G[0] - Gao).max()))

rows = np.array(rows, dtype=object)
print(f"{len(rows)} instances")
print("lambda = 1 equals REINFORCE (Theorem 4.1): max |Gamma(1) - Gamma_AO| =",
      f"{max(r[8] for r in rows):.1e}")
dom = np.array([r[5] for r in rows], float)
mono = np.array([r[6] for r in rows], float)
ratio = np.array([r[7] for r in rows], float)
print(f"Loewner Gamma(0) <= Gamma_AO in {np.sum(dom >= -1e-10)}/{len(rows)}; worst normalized min eig {dom.min():.3e}")
print(f"monotone in lambda (Loewner)  in {np.sum(mono >= -1e-10)}/{len(rows)}; worst {mono.min():.3e}")
print(f"trace ratio Gamma(0)/Gamma_AO: median {np.median(ratio):.2f}, range [{ratio.min():.2f}, {ratio.max():.2f}]")
bad = [r for r in rows if r[5] < -1e-10 or r[6] < -1e-10]
for r in bad[:8]:
    print("   counterexample: S=%d A=%d n=%d gamma=%.2f seed=%d  dom=%.2e mono=%.2e ratio=%.2f" % tuple(r[:8]))
