"""Simulate actor-only and two-time-scale actor-critic with Polyak averaging, and compare the
empirical n E[(thetabar_n - theta*)^2] with the predicted optimal-gain covariance.

Fully aliased instances (n = 1): chi(s, a) = 1{a = 1}, so pi(1|s) = sigmoid(theta) for all s
and psi(s, a) = 1{a = 1} - sigmoid(theta).
"""

import sys
import time

import numpy as np

from ac_rates import (aliased_mdp, optimum, Critic, rate_of, actor_only_direction,
                      actor_critic_direction, critic_solution)


def simulate(mdp, kind, lam, phibar, th_star, n_steps, runs, seed,
             beta0=1.0, beta_exp=0.75, gam0=1.0, gam_exp=0.55, k0=100):
    rng = np.random.default_rng(seed)
    S, gamma = mdp.S, mdp.gamma
    cumP = np.cumsum(mdp.P, axis=2)
    cum0 = np.cumsum(mdp.p0)
    g = mdp.g
    sig = lambda t: 1 / (1 + np.exp(-t))
    th = np.full(runs, th_star[0])
    extra = 0 if phibar is None else phibar.shape[1]
    m = 1 + extra

    def act(s, t):
        return (rng.random(runs) < sig(t)).astype(int)

    def feats(s, a, t):
        psi = a - sig(t)
        if extra == 0:
            return psi[:, None], psi
        return np.concatenate([psi[:, None], phibar[s]], axis=1), psi

    s = (cum0[None, :] < rng.random(runs)[:, None]).sum(1)
    a = act(s, th)
    if kind == "ac":
        cr = Critic(lam, phibar)
        r = np.tile(critic_solution(mdp, th_star, cr)[-1], (runs, 1))
    z = np.zeros((runs, m if kind == "ac" else 1))
    th_sum = np.zeros(runs)
    burn = n_steps // 10
    for k in range(n_steps):
        beta = beta0 / (k + k0) ** beta_exp
        # current features and trace
        phi, psi = feats(s, a, th)
        if kind == "ao":
            z[:, 0] = z[:, 0] + psi
        else:
            z = z + phi
        # next pair: restart with prob 1 - gamma
        cont = rng.random(runs) < gamma
        s_step = (cumP[s, a] < rng.random(runs)[:, None]).sum(1)
        s_rest = (cum0[None, :] < rng.random(runs)[:, None]).sum(1)
        s1 = np.where(cont, s_step, s_rest)
        a1 = act(s1, th)
        reward = g[s, a]
        if kind == "ao":
            th = th + beta * reward * z[:, 0]
        else:
            gk = gam0 / (k + k0) ** gam_exp
            phi1, _ = feats(s1, a1, th)
            d = reward + cont * np.einsum('ri,ri->r', r, phi1) - np.einsum('ri,ri->r', r, phi)
            th = th + beta * np.einsum('ri,ri->r', r, phi) * psi
            r = r + gk * d[:, None] * z
        if k >= burn:
            th_sum += th
        # decay the trace for the next step (reset at restarts)
        c = np.where(cont, lam, 0.0)
        z = c[:, None] * z
        s, a = s1, a1
    th_bar = th_sum / (n_steps - burn)
    n_eff = n_steps - burn
    return n_eff * np.mean((th_bar - th_star[0]) ** 2), np.mean(th_bar) - th_star[0]


if __name__ == "__main__":
    seed = 2
    mdp = aliased_mdp(6, 2, [0] * 6, 0.9, seed)
    th_opt, HJ = optimum(mdp, np.zeros(1))
    n_steps = int(sys.argv[1]) if len(sys.argv) > 1 else 200_000
    runs = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    cases = [("actor-only lambda_a=1", "ao", 1.0, None),
             ("actor-only lambda_a=0.7", "ao", 0.7, None),
             ("AC tabular, lambda=0.3", "ac", 0.3, np.eye(6)),
             ("AC compatible only, lambda=0.6", "ac", 0.6, None)]
    for label, kind, lam, phibar in cases:
        if kind == "ao":
            pred = rate_of(mdp, lambda t: actor_only_direction(mdp, t, lam, True),
                           lambda t: actor_only_direction(mdp, t, lam), th_opt, th_opt, HJ, "")
        else:
            cr = Critic(lam, phibar)
            pred = rate_of(mdp, lambda t: actor_critic_direction(mdp, t, cr, True),
                           lambda t: actor_critic_direction(mdp, t, cr), th_opt, th_opt, HJ, "")
        t0 = time.time()
        emp, bias = simulate(mdp, kind, lam, phibar, pred.theta, n_steps, runs, seed=11)
        se = emp * np.sqrt(2 / runs)
        print(f"{label:32s} predicted Sigma={pred.Sigma[0, 0]:9.2f}   simulated={emp:9.2f} +- {se:6.2f}"
              f"   mean(thetabar - theta*)={bias:+.4f}   ({time.time() - t0:.0f}s)", flush=True)
