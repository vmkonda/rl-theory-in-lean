"""Lemma 4.6: the state block of -C A_c^{-1} for the tabular TD(lambda) critic is
K_lambda e_s = -(1 - lambda) b(s), with b(s) = E[c_k Z_{k-1} | s_k = s] the REINFORCE carried trace."""
import io, contextlib, sys, warnings
sys.path.insert(0, ".")
import numpy as np
from ac_rates import Critic, critic_solution
with contextlib.redirect_stdout(io.StringIO()):
    from explore_value_critic import instances
from trace_cov import trace_moments, stationary
warnings.filterwarnings("ignore")
worst = 0
for seed, mdp, th in instances(12, 5, 2, [0] * 5, 0.9) + instances(6, 6, 3, [0] * 6, 0.8):
    S, A = mdp.S, mdp.A
    flags = mdp.flags(); sidx = np.tile(np.repeat(np.arange(S), A), 2)
    psi = mdp.lift(mdp.psi(th)); n = psi.shape[1]
    Q = mdp.chain(th); nu = stationary(Q); cA = np.where(flags == 1, 0.0, 1.0)
    muZ, _ = trace_moments(Q, nu, cA, psi)
    b = np.array([((muZ - psi)[sidx == s] * nu[sidx == s, None]).sum(0) / nu[sidx == s].sum()
                  for s in range(S)])
    for lam in [0.0, 0.3, 0.7, 0.95, 1.0]:
        Qc, c, phi, _, _, nuc, Ac, r = critic_solution(mdp, th, Critic(lam, np.eye(S)))
        C = np.einsum('y,yn,ym->nm', nuc, psi, phi)
        K = (C @ np.linalg.inv(Ac))[:, n:]          # -C A^-1 = (I, -K)  =>  K = (C A^-1)[:, n:]
        worst = max(worst, np.abs(K - (-(1 - lam)) * b.T).max() / np.abs(b).max())
print(f"max relative |K_lambda e_s + (1 - lambda) b(s)| = {worst:.2e}")
