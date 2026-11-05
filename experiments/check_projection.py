"""Is the value-critic noise an orthogonal projection of the REINFORCE noise?
Simulates both effective noises on the same paths at theta* and estimates the long-run
covariances Var(N_AO), Var(N_AC), Cov(N_AO, N_AC) by sums over long stationary stretches."""
import warnings
import numpy as np
from ac_rates import Critic, critic_solution, actor_only_direction, actor_critic_direction
from explore_value_critic import instances
from trace_cov import stationary

warnings.filterwarnings("ignore")
rng = np.random.default_rng(0)
for seed, mdp, th in instances(3, 5, 2, [0] * 5, 0.9):
    for lam in [0.0, 0.5]:
        cr = Critic(lam, np.eye(5))
        Q, c, phi, gy, cont, nu, Ac, r = critic_solution(mdp, th, cr)
        psi = mdp.lift(mdp.psi(th))
        C = np.einsum('y,yn,ym->nm', nu, psi, phi)
        L = -C @ np.linalg.inv(Ac)
        v = phi @ r
        N, m = phi.shape
        n = psi.shape[1]
        runs, T = 4000, 3000
        cum = np.cumsum(Q, 1)
        y = rng.choice(N, size=runs, p=nu)
        z = np.zeros((runs, m)); Z = np.zeros((runs, n))
        z = phi[y].copy(); Z = psi[y].copy()          # start at a restart-free trace approx
        SA = np.zeros((runs, n)); SC = np.zeros((runs, n))
        for k in range(T):
            y1 = (cum[y] < rng.random(runs)[:, None]).sum(1)
            d = gy[y] + cont[y1] * v[y1] - v[y]
            SA += gy[y][:, None] * Z
            SC += psi[y] * v[y][:, None] + (d[:, None] * z) @ L.T
            z = (lam * cont[y1])[:, None] * z + phi[y1]
            Z = cont[y1][:, None] * Z + psi[y1]
            y = y1
        SA -= SA.mean(0); SC -= SC.mean(0)
        vA = (SA.T @ SA)[0, 0] / runs / T; vC = (SC.T @ SC)[0, 0] / runs / T
        cAC = (SA.T @ SC)[0, 0] / runs / T
        _, Gao = actor_only_direction(mdp, th, 1.0, True)
        _, Gac = actor_critic_direction(mdp, th, cr, True)
        print(f"seed {seed} lam {lam}: Var AO {vA:.3f} (exact {Gao[0,0]:.3f})  Var AC {vC:.3f} "
              f"(exact {Gac[0,0]:.3f})  Cov {cAC:.3f}   Cov/VarAC = {cAC / vC:.3f}")
