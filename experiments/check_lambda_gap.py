"""For the tabular TD(lambda) critic at theta*, with X_lambda = (z^psi_k - psi_k) - K_lambda z^e_k
(known before the action a_k) and K_lambda the state block of -C A_c^{-1}:
  (a) E[X_lambda | s_k = s] = b(s) = E[c_k Z_{k-1} | s_k = s] for every lambda;
  (b) Gamma(lambda) - Gamma(0) = sum_s nu(s) E[delta^2 | s] Cov(X_lambda | s_k = s);
  (c) is Cov(X_lambda | s) monotone in lambda (Loewner, per state)?"""
import io, contextlib, warnings
import numpy as np
from ac_rates import Critic, critic_solution, actor_critic_direction
with contextlib.redirect_stdout(io.StringIO()):
    from explore_value_critic import instances
from trace_cov import trace_moments

warnings.filterwarnings("ignore")
cases = instances(10, 5, 2, [0] * 5, 0.9) + instances(8, 6, 2, [0, 0, 0, 1, 1, 1], 0.9) \
    + instances(6, 6, 3, [0] * 6, 0.8)
lams = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
ea = eb = 0.0; mono_state = mono_tot = True; worst_state = np.inf
for seed, mdp, th in cases:
    S, A = mdp.S, mdp.A
    flags = mdp.flags(); sidx = np.tile(np.repeat(np.arange(S), A), 2)
    psi = mdp.lift(mdp.psi(th)); n = psi.shape[1]
    _, G0 = actor_critic_direction(mdp, th, Critic(0.0, np.eye(S)), True)
    # b(s) from the REINFORCE carried trace
    Q = mdp.chain(th)
    from trace_cov import stationary
    nu = stationary(Q); cA = np.where(flags == 1, 0.0, 1.0)
    muZ, _ = trace_moments(Q, nu, cA, psi)
    b = np.array([((muZ - psi)[sidx == s] * nu[sidx == s, None]).sum(0) / nu[sidx == s].sum()
                  for s in range(S)])
    V, _, _ = mdp.values(th); gy = mdp.lift(mdp.g); cont = (flags == 0).astype(float)
    Vy = V[sidx]; delta = gy[:, None] + cont[None, :] * Vy[None, :] - Vy[:, None]
    Ed2 = (Q * delta ** 2).sum(1)
    prev = None
    for lam in lams:
        Qc, c, phi, _, _, nuc, Ac, r = critic_solution(mdp, th, Critic(lam, np.eye(S)))
        C = np.einsum('y,yn,ym->nm', nuc, psi, phi)
        Lsel = -C @ np.linalg.inv(Ac)                    # (n, n + S) = (I, -K)
        mu, M = trace_moments(Qc, nuc, c, phi)            # E[z | y], E[z z^T | y]
        # X = Lsel z - psi
        EX = mu @ Lsel.T - psi
        EXX = np.einsum('ni,yij,mj->ynm', Lsel, M, Lsel) - np.einsum('yn,ym->ynm', mu @ Lsel.T, psi) \
            - np.einsum('yn,ym->ynm', psi, mu @ Lsel.T) + np.einsum('yn,ym->ynm', psi, psi)
        gap = np.zeros((n, n)); covs = []
        for s in range(S):
            w = nuc * (sidx == s); ps = w.sum(); w = w / ps
            mX = w @ EX
            ea = max(ea, np.abs(mX - b[s]).max() / (np.abs(b).max() + 1e-12))
            cov = np.einsum('y,ynm->nm', w, EXX) - np.outer(mX, mX)
            covs.append(cov)
            gap += ps * (w @ Ed2) * cov
        _, Gl = actor_critic_direction(mdp, th, Critic(lam, np.eye(S)), True)
        eb = max(eb, np.abs((Gl - G0) - gap).max() / np.abs(G0).max())
        if prev is not None:
            for s in range(S):
                mn = np.min(np.linalg.eigvalsh(covs[s] - prev[s]))
                worst_state = min(worst_state, mn / (np.abs(covs[s]).max() + 1e-12))
        prev = covs
print(f"{len(cases)} instances, lambda in {lams}")
print(f"(a) max relative |E[X_lam | s] - b(s)| = {ea:.2e}")
print(f"(b) max relative error of Gamma(lam) - Gamma(0) = sum_s nu E[d^2|s] Cov(X|s): {eb:.2e}")
print(f"(c) min over states/steps of eig(Cov(X_lam'|s) - Cov(X_lam|s)) / scale: {worst_state:.3e}")
