"""Two-time-scale linear SA with Markov noise: beta_k^{-1} E[x x'] -> Sigma_11 (Theorem 2.1 of
docs/two-time-scale-covariance), the covariance of the single-time-scale iteration driven by the
effective noise V - A12 A22^{-1} W."""
import numpy as np
from trace_cov import long_run_cov, stationary

rng = np.random.default_rng(1)
N, d1, d2 = 6, 1, 1
Q = rng.random((N, N)) ** 3; Q /= Q.sum(1, keepdims=True)
nu = stationary(Q)
VW = rng.normal(size=(N, N, d1 + d2))
VW -= np.einsum('ab,abp->p', nu[:, None] * Q, VW)
G, _ = long_run_cov(Q, np.zeros(N), np.zeros((N, 1)), np.zeros((N, N, d1 + d2, 1)), VW)

A11 = np.array([[1.0]]); A12 = np.array([[0.8]]); A21 = np.array([[-0.5]]); A22 = np.array([[1.5]])
Delta = A11 - A12 @ np.linalg.solve(A22, A21)
alpha = 2.0 / Delta[0, 0]; bbar = 1 / alpha                  # beta_k = alpha / (k + k0)
T = np.hstack([np.eye(d1), -A12 @ np.linalg.inv(A22)])       # effective noise V - A12 A22^{-1} W
Gt = T @ G @ T.T
Lop = np.kron(np.eye(d1), Delta - bbar / 2 * np.eye(d1)) + np.kron(Delta - bbar / 2 * np.eye(d1), np.eye(d1))
Sigma11 = np.linalg.solve(Lop, Gt.reshape(-1)).reshape(d1, d1)
naive = np.linalg.solve(Lop, G[:d1, :d1].reshape(-1)).reshape(d1, d1)   # ignoring the critic noise

runs, K, k0, rho = 20000, 100000, 50, 0.7
cum = np.cumsum(Q, 1); y = rng.choice(N, size=runs, p=nu)
x = np.zeros((runs, d1)); r = np.zeros((runs, d2))
for k in range(K):
    y1 = (cum[y] < rng.random(runs)[:, None]).sum(1)
    beta = alpha / (k + k0); gam = 1.0 / (k + k0) ** rho
    n = VW[y, y1]
    x, r = (x - beta * (x @ A11.T + r @ A12.T) + beta * n[:, :d1],
            r - gam * (x @ A21.T + r @ A22.T) + gam * n[:, d1:])
    y = y1
est = (x.T @ x / runs) / beta
print("beta_k^{-1} E[x x'] =", np.round(est, 4))
print("predicted Sigma_11  =", np.round(Sigma11, 4), "  (noise V alone would give", np.round(naive, 4), ")")
