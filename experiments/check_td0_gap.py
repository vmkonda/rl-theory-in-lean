"""Theorem 4.6 check: for the TD(0) critic with features (psi, e_s) at theta*,
    Gamma_AO - Gamma_AC = sum_s nu(s) E[delta^2 | s] Cov(c_k Z_{k-1} | s_k = s),
where delta is the TD error of V^pi and Z the REINFORCE trace."""
import warnings
import numpy as np
from ac_rates import Critic, actor_only_direction, actor_critic_direction
from explore_value_critic import instances
from trace_cov import stationary, trace_moments

warnings.filterwarnings("ignore")
worst = 0.0
cases = instances(15, 5, 2, [0] * 5, 0.9) + instances(10, 6, 2, [0, 0, 0, 1, 1, 1], 0.9) \
    + instances(10, 6, 3, [0] * 6, 0.8)
for seed, mdp, th in cases:
    S, A = mdp.S, mdp.A
    _, Gao = actor_only_direction(mdp, th, 1.0, True)
    _, Gac = actor_critic_direction(mdp, th, Critic(0.0, np.eye(S)), True)
    Q = mdp.chain(th); nu = stationary(Q)
    flags = mdp.flags(); cA = np.where(flags == 1, 0.0, 1.0)
    psi = mdp.lift(mdp.psi(th))
    mu, Mz = trace_moments(Q, nu, cA, psi)            # E[Z_k | Y_k], E[Z_k Z_k^T | Y_k]
    # B = c_k Z_{k-1} = Z_k - psi_k
    EB = mu - psi
    EBB = Mz - np.einsum('yi,yj->yij', mu, psi) - np.einsum('yi,yj->yij', psi, mu) \
        + np.einsum('yi,yj->yij', psi, psi)
    V, Qsa, _ = mdp.values(th)
    gy = mdp.lift(mdp.g)
    sidx = np.tile(np.repeat(np.arange(S), A), 2)
    cont = (flags == 0).astype(float)
    Vy = V[sidx]
    delta = gy[:, None] + cont[None, :] * Vy[None, :] - Vy[:, None]   # delta(y, y')
    Ed2 = (Q * delta ** 2).sum(1)                                     # E[delta^2 | y]
    gap = np.zeros_like(Gao)
    for s in range(S):
        w = nu * (sidx == s); ps = w.sum(); w = w / ps
        mB = np.einsum('y,yi->i', w, EB)
        cov = np.einsum('y,yij->ij', w, EBB) - np.outer(mB, mB)
        gap += ps * (w @ Ed2) * cov
    worst = max(worst, np.abs((Gao - Gac) - gap).max() / np.abs(Gao).max())
print(f"{len(cases)} instances: max relative error of the gap formula {worst:.2e}")
