"""Exact test at lambda = 0 of Cov(N_AO, N_AC) = Var(N_AC) for the value-function critic.
With lambda = 0 the critic trace is phi(Y_k), so both noises are affine in the actor-only trace Z
and the exact engine applies to the stacked noise (N_AO, N_AC)."""
import warnings
import numpy as np
from ac_rates import Critic, critic_solution
from explore_value_critic import instances
from trace_cov import long_run_cov

warnings.filterwarnings("ignore")
worst, worst_dom = 0.0, np.inf
cases = instances(15, 5, 2, [0] * 5, 0.9) + instances(10, 6, 2, [0, 0, 0, 1, 1, 1], 0.9) \
    + instances(10, 6, 3, [0] * 6, 0.8)
for seed, mdp, th in cases:
    S = mdp.S
    Q, c, phi, gy, cont, nu, Ac, r = critic_solution(mdp, th, Critic(0.0, np.eye(S)))
    psi = mdp.lift(mdp.psi(th))
    C = np.einsum('y,yn,ym->nm', nu, psi, phi)
    L = -C @ np.linalg.inv(Ac)
    v = phi @ r
    N, n = psi.shape
    d = gy[:, None] + cont[None, :] * v[None, :] - v[:, None]
    eAC = psi[:, None, :] * v[:, None, None] + np.einsum('yz,nm,ym->yzn', d, L, phi)
    eAC -= np.einsum('y,yz,yzn->n', nu, Q, eAC)
    F = np.zeros((N, N, 2 * n, n))
    F[:, :, :n, :] = gy[:, None, None, None] * np.eye(n)[None, None]
    e = np.zeros((N, N, 2 * n))
    e[:, :, n:] = eAC
    cA = np.where(mdp.flags() == 1, 0.0, 1.0)
    G, _ = long_run_cov(Q, cA, psi, F, e)
    GAO, GAC, X = G[:n, :n], G[n:, n:], G[:n, n:]
    worst = max(worst, np.abs(X - GAC).max() / np.abs(GAC).max())
    worst_dom = min(worst_dom, np.min(np.linalg.eigvalsh(GAO - GAC)))
print(f"{len(cases)} instances: max relative |Cov(N_AO, N_AC) - Var(N_AC)| = {worst:.2e}")
print(f"min eigenvalue of Gamma_AO - Gamma_AC: {worst_dom:.3e}")
