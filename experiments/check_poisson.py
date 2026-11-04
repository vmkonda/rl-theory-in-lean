"""(a) Gamma = E[M M'] for the Poisson martingale part; (b) beta_k^{-1} E[theta theta'] -> Sigma."""
import numpy as np
from trace_cov import long_run_cov, stationary, trace_moments

rng = np.random.default_rng(0)
N, d = 7, 2
Q = rng.random((N, N)) ** 3; Q /= Q.sum(1, keepdims=True)
nu = stationary(Q)
V = rng.normal(size=(N, N, d))
V -= np.einsum('ab,abp->p', nu[:, None] * Q, V)            # mean zero under stationarity
Z = np.linalg.inv(np.eye(N) - Q + np.outer(np.ones(N), nu))

# (a1) finite chain: M(y,y') = V(y,y') - Vbar(y) + h(y') - (Qh)(y),  h = Z Vbar
Vbar = np.einsum('ab,abp->ap', Q, V); h = Z @ Vbar
Mm = V - Vbar[:, None, :] + h[None, :, :] - (Q @ h)[:, None, :]
EMM = np.einsum('ab,abp,abq->pq', nu[:, None] * Q, Mm, Mm)
G, _ = long_run_cov(Q, np.zeros(N), np.zeros((N, 1)), np.zeros((N, N, d, 1)), V)
print("(a1) finite chain:  |E[MM'] - Gamma| / |Gamma| =", np.abs(EMM - G).max() / np.abs(G).max())

# (a2) trace-driven noise f = F(y,y') z + e(y,y'): Poisson solution H(y,z) = U(y) z + h(y);
#      E[M M'] with M = f - fbar(Y0,z0) + H(Y1,z1) - (KH)(Y0,z0), integrated against the trace law.
m = 3; c = rng.uniform(0, 0.8, size=N); Phi = rng.normal(size=(N, m))
F = rng.normal(size=(N, N, d, m)); e = rng.normal(size=(N, N, d))
mu, Mz = trace_moments(Q, nu, c, Phi)
W01 = nu[:, None] * Q
e -= (np.einsum('ab,abpm,am->p', W01, F, mu) + np.einsum('ab,abp->p', W01, e))  # center
Gt, _ = long_run_cov(Q, c, Phi, F, e)
Fbar = np.einsum('ab,abpm->apm', Q, F); ebar = np.einsum('ab,abp->ap', Q, e)
U = np.linalg.solve(np.eye(N) - Q * c[None, :], Fbar.reshape(N, -1)).reshape(N, d, m)
w = ebar + np.einsum('ab,bpm,bm->ap', Q, U, Phi); hh = Z @ w
# M is affine in z0: M = Mz(y,y') z0 + Mc(y,y'), with z1 = c(y') z0 + phi(y')
KH_z = np.einsum('ab,b,bpm->apm', Q, c, U)                    # coefficient of z0 in KH
KH_c = np.einsum('ab,bpm,bm->ap', Q, U, Phi) + Q @ hh
Mz_ = F + c[None, :, None, None] * U[None, :, :, :] - Fbar[:, None] - KH_z[:, None]
Mc_ = e + np.einsum('bpm,bm->bp', U, Phi)[None, :, :] + hh[None, :, :] - ebar[:, None] - KH_c[:, None]
EMMt = (np.einsum('ab,abpm,amn,abqn->pq', W01, Mz_, Mz, Mz_) + np.einsum('ab,abpm,am,abq->pq', W01, Mz_, mu, Mc_)
        + np.einsum('ab,abp,am,abqm->pq', W01, Mc_, mu, Mz_) + np.einsum('ab,abp,abq->pq', W01, Mc_, Mc_))
print("(a2) trace noise:   |E[MM'] - Gamma| / |Gamma| =", np.abs(EMMt - Gt).max() / np.abs(Gt).max())

# (b) theta_{k+1} = theta_k - beta_k A theta_k + beta_k V(Y_k, Y_{k+1}),  beta_k = alpha/(k + k0)
A = np.array([[1.0, 0.6], [-0.3, 0.8]]); alpha = 2.0; bbar = 1 / alpha
L = np.kron(np.eye(d), A - bbar / 2 * np.eye(d)) + np.kron(A - bbar / 2 * np.eye(d), np.eye(d))
Sigma = np.linalg.solve(L, G.reshape(-1)).reshape(d, d)
runs, K, k0 = 20000, 40000, 50
cum = np.cumsum(Q, 1); y = rng.choice(N, size=runs, p=nu); th = np.zeros((runs, d))
for k in range(K):
    y1 = (cum[y] < rng.random(runs)[:, None]).sum(1)
    beta = alpha / (k + k0)
    th = th - beta * th @ A.T + beta * V[y, y1]
    y = y1
est = (th.T @ th / runs) / beta
print("(b) beta_k^{-1} E[theta theta'] =\n", np.round(est, 3), "\n    predicted Sigma =\n", np.round(Sigma, 3))
