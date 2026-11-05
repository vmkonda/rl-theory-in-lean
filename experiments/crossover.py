"""Finite-time crossover: does the tabular TD(0) critic lose to REINFORCE before the asymptotics?

Theorem 4.5 says that, asymptotically, actor-critic with a tabular TD(0) critic has a smaller
optimal-gain loss than REINFORCE. The critic has |S| + 1 parameters, each tabular entry updated only
when its state is visited, so it may need a long time to settle.

To isolate the size of the critic, we split each state of a fixed 5-state aliased MDP into m copies
with Zipf weights w_j ~ 1/(j+1): the next state's block follows the base MDP and its copy is drawn
from w. The copies are indistinguishable to the actor, so J, H, the REINFORCE noise and (by
Theorem 4.5, since b(s) is the same on copies) the asymptotic actor-critic loss do not depend on m;
only the critic's table grows, to 5m entries, the rarest visited about w_{m-1}/5 of the time.

Both algorithms start from the same point (actor at theta* + 0.5, critic at r = 0), with Polyak
averaging over [K/2, K] and theta projected onto theta* +- 2. We report the normalized loss
(K/2) E[J* - J(thetabar_K)], which tends to the optimal-gain loss l* (Proposition 3.3 with the
averaged covariance Sigma/(K/2)).

Usage: crossover.py m [runs] [log2 steps] [alpha0 ...]
"""
import sys
import time
import warnings

import numpy as np

from ac_rates import MDP, aliased_mdp, optimum, Critic, rate_of, actor_only_direction, \
    actor_critic_direction
from trace_cov import stationary

warnings.filterwarnings("ignore")


BASE_SEED, GAMMA = 147, 0.8      # the best-conditioned 5-state instance found (Sigma_AO = 86)


def split_mdp(base, m):
    w = 1.0 / np.arange(1, m + 1); w /= w.sum()
    S0, A = base.S, base.A
    P = np.einsum('iak,j->iakj', base.P, w).reshape(S0, A, S0 * m)
    P = np.repeat(P, m, axis=0)
    g = np.repeat(base.g, m, axis=0)
    p0 = np.outer(base.p0, w).reshape(-1)
    chi = np.repeat(base.chi, m, axis=0)
    return MDP(P, g, p0, base.gamma, chi)


def instance(m):
    mdp = split_mdp(aliased_mdp(5, 2, [0] * 5, GAMMA, BASE_SEED), m)
    th, HJ = optimum(mdp, np.zeros(1))
    return BASE_SEED, mdp, th, HJ


def simulate(mdp, kind, th0, n_log2, runs, seed, beta0, beta_exp, gam0, gam_exp, k0, box):
    """Returns {K: thetabar over [K/2, K]} at K = 2^j."""
    rng = np.random.default_rng(seed)
    S, gamma = mdp.S, mdp.gamma
    cumP, cum0, g = np.cumsum(mdp.P, axis=2), np.cumsum(mdp.p0), mdp.g
    sig = lambda t: 1 / (1 + np.exp(-t))
    act = lambda t: (rng.random(runs) < sig(t)).astype(int)
    th = np.full(runs, th0)
    rows = np.arange(runs)
    s = (cum0[None, :] < rng.random(runs)[:, None]).sum(1)
    a = act(th)
    w = np.zeros(runs)                  # critic: score weight
    u = np.zeros((runs, S))             # critic: value table
    zw = np.zeros(runs)                 # traces (TD(0): the current features)
    Z = np.zeros(runs)                  # REINFORCE trace
    csum, out, prev, K = np.zeros(runs), {}, np.zeros(runs), 1
    for k in range(1, 2 ** n_log2 + 1):
        beta = beta0 / (k + k0) ** beta_exp
        psi = a - sig(th)
        cont = rng.random(runs) < gamma
        s_step = (cumP[s, a] < rng.random(runs)[:, None]).sum(1)
        s_rest = (cum0[None, :] < rng.random(runs)[:, None]).sum(1)
        s1 = np.where(cont, s_step, s_rest)
        a1 = act(th)
        reward = g[s, a]
        if kind == "ao":
            Z = Z + psi
            th_new = th + beta * reward * Z
            Z = np.where(cont, Z, 0.0)
        else:
            alpha = gam0 / (k + k0) ** gam_exp
            psi1 = a1 - sig(th)
            v, v1 = w * psi + u[rows, s], w * psi1 + u[rows, s1]
            d = reward + cont * v1 - v
            th_new = th + beta * v * psi
            w = w + alpha * d * psi
            u[rows, s] += alpha * d
        th, s, a = np.clip(th_new, box[0], box[1]), s1, a1
        csum += th
        if k == 2 * K or k == 1:
            if k > 1:
                out[k] = (csum - prev) / (k - K)
            prev, K = csum.copy(), k
    return out


if __name__ == "__main__":
    m = int(sys.argv[1])
    runs = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    n_log2 = int(sys.argv[3]) if len(sys.argv) > 3 else 18
    gam0s = [float(x) for x in sys.argv[4:]] or [1.0, 4.0, 16.0]
    seed, mdp, th_opt, HJ = instance(m)
    S = mdp.S
    Jstar = mdp.J(th_opt)
    nu_s = stationary(mdp.chain(th_opt)).reshape(2, S, 2).sum((0, 2))
    if S <= 20:
        ao = rate_of(mdp, lambda t: actor_only_direction(mdp, t, 1.0, True),
                     lambda t: actor_only_direction(mdp, t, 1.0), th_opt, th_opt, HJ, "")
        cr = Critic(0.0, np.eye(S))
        ac = rate_of(mdp, lambda t: actor_critic_direction(mdp, t, cr, True),
                     lambda t: actor_critic_direction(mdp, t, cr), th_opt, th_opt, HJ, "")
        print(f"m={m} S={S} seed={seed} theta*={th_opt[0]:+.3f} S*min nu(s)={S * nu_s.min():.3f} "
              f"predicted l*: REINFORCE {ao.var_term:.4f}, AC TD(0) {ac.var_term:.4f} "
              f"(ratio {ac.var_term / ao.var_term:.3f})", flush=True)
        H = -(actor_only_direction(mdp, th_opt + 1e-5, 1.0) - actor_only_direction(mdp, th_opt - 1e-5, 1.0))[0] / 2e-5
        print(f"  H = {H:.4f} (shared by both methods)", flush=True)
    else:  # the exact covariance needs O((S A)^2 S^2) memory; l* does not depend on m
        print(f"m={m} S={S} seed={seed} theta*={th_opt[0]:+.3f} S*min nu(s)={S * nu_s.min():.3f} "
              f"predicted l*: as for m = 1", flush=True)
        H = -(actor_only_direction(mdp, th_opt + 1e-5, 1.0)
              - actor_only_direction(mdp, th_opt - 1e-5, 1.0))[0] / 2e-5
    th0 = th_opt[0] + 0.5
    common = dict(n_log2=n_log2, runs=runs, seed=7, beta0=1.0, box=(th_opt[0] - 2, th_opt[0] + 2), beta_exp=0.7, gam_exp=0.5, k0=1000)
    cases = [("REINFORCE", "ao", None)] + [(f"AC TD(0), alpha0={g0:g}", "ac", g0) for g0 in gam0s]
    for label, kind, g0 in cases:
        t0 = time.time()
        res = simulate(mdp, kind, th0, gam0=g0 or 0.0, **common)
        Ks = sorted(res)
        loss = [(K // 2) * np.mean([Jstar - mdp.J(np.array([t])) for t in res[K]]) for K in Ks]
        se = [(K // 2) * np.std([Jstar - mdp.J(np.array([t])) for t in res[K]]) / np.sqrt(runs)
              for K in Ks]
        print(f"{label:24s} ({time.time() - t0:.0f}s)", flush=True)
        print("   K: " + " ".join(f"{K:>9d}" for K in Ks[::2]))
        print("   l: " + " ".join(f"{x:9.4f}" for x in loss[::2]))
        print("  se: " + " ".join(f"{x:9.4f}" for x in se[::2]), flush=True)
