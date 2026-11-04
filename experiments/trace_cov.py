"""Exact long-run covariance of trace-driven noise on a finite Markov chain.

Setting: Y_k is an irreducible aperiodic chain on a finite set with transition matrix Q
and stationary law nu. A trace evolves as
    z_k = c(Y_k) z_{k-1} + phi(Y_k),          0 <= c(y) <= 1, spectral radius of Q diag(c) < 1,
and the noise is affine in the trace:
    f_k = F(Y_k, Y_{k+1}) z_k + e(Y_k, Y_{k+1}),   with E f_k = 0 under stationarity.

Returns Gamma = sum_{l in Z} E[f_0 f_l^T]. The computation uses that functions affine or
quadratic in z are closed under the transition:
    mu(y) = E[z_0 | Y_0 = y],  M(y) = E[z_0 z_0^T | Y_0 = y]   (time-reversed chain),
    H(y, z) = sum_{l>=0} E[f_l | Y_0 = y, z_0 = z] = U(y) z + h(y)   (up to a constant),
with U = Fbar + Q C U and h = Z w (fundamental matrix), w = ebar + Q[U phi].
"""

import numpy as np


def stationary(Q: np.ndarray) -> np.ndarray:
    w, v = np.linalg.eig(Q.T)
    p = np.real(v[:, np.argmin(np.abs(w - 1))])
    return p / p.sum()


def trace_moments(Q, nu, c, Phi):
    """mu(y) = E[z|Y=y] and M(y) = E[z z^T|Y=y] for the stationary trace."""
    N, m = Phi.shape
    Qr = (Q.T * nu[None, :]) / nu[:, None]                    # time reversal
    CQr = c[:, None] * Qr
    mu = np.linalg.solve(np.eye(N) - CQr, Phi)
    mu_prev = Qr @ mu
    Cm = (np.einsum('yi,yj->yij', Phi, Phi)
          + c[:, None, None] * (np.einsum('yi,yj->yij', Phi, mu_prev)
                                + np.einsum('yi,yj->yij', mu_prev, Phi)))
    big = np.eye(N * m * m) - np.kron((c**2)[:, None] * Qr, np.eye(m * m))
    M = np.linalg.solve(big, Cm.reshape(N * m * m)).reshape(N, m, m)
    return mu, M


def long_run_cov(Q, c, Phi, F, e, check=True):
    """Q: (N,N); c: (N,); Phi: (N,m); F: (N,N,p,m); e: (N,N,p). Returns (Gamma, mean)."""
    N, m = Phi.shape
    p = e.shape[-1]
    nu = stationary(Q)
    mu, M = trace_moments(Q, nu, c, Phi)
    W01 = nu[:, None] * Q                                     # joint law of (Y0, Y1)
    mean = np.einsum('ab,abpm,am->p', W01, F, mu) + np.einsum('ab,abp->p', W01, e)
    if check:
        assert np.allclose(mean, 0, atol=1e-8), mean
    Fbar = np.einsum('ab,abpm->apm', Q, F)
    ebar = np.einsum('ab,abp->ap', Q, e)
    # U(y) = Fbar(y) + sum_y' Q(y,y') c(y') U(y')
    QC = Q * c[None, :]
    U = np.linalg.solve(np.eye(N) - QC, Fbar.reshape(N, p * m)).reshape(N, p, m)
    w = ebar + np.einsum('ab,bpm,bm->ap', Q, U, Phi)
    Z = np.linalg.inv(np.eye(N) - Q + np.outer(np.ones(N), nu))
    h = Z @ w
    E0 = (np.einsum('ab,abpm,amn,abqn->pq', W01, F, M, F)
          + np.einsum('ab,abpm,am,abq->pq', W01, F, mu, e)
          + np.einsum('ab,abp,am,abqm->pq', W01, e, mu, F)
          + np.einsum('ab,abp,abq->pq', W01, e, e))
    T = (np.einsum('ab,abpm,amn,b,bqn->pq', W01, F, M, c, U)
         + np.einsum('ab,abpm,am,bn,bqn->pq', W01, F, mu, Phi, U)
         + np.einsum('ab,abpm,am,bq->pq', W01, F, mu, h)
         + np.einsum('ab,abp,b,am,bqm->pq', W01, e, c, mu, U)
         + np.einsum('ab,abp,bm,bqm->pq', W01, e, Phi, U)
         + np.einsum('ab,abp,bq->pq', W01, e, h))
    return E0 + T + T.T, mean
