"""Exact asymptotic rates of TD(lambda) / LSTD(lambda) on finite Markov reward processes.

Setting (discounted, on-policy, Markov samples):
    x_k ~ stationary Markov chain with transition matrix P and stationary law pi,
    z_k = gamma*lam*z_{k-1} + phi(x_k)                      (eligibility trace)
    d_k = g(x_k) + gamma*phi(x_{k+1})'r - phi(x_k)'r        (temporal difference)

TD(lambda) / LSTD(lambda) solve E[d_k z_k] = 0, i.e. A r + b = 0 with
    A = Phi' D (I - gamma lam P)^{-1} (gamma P - I) Phi,   b = Phi' D (I - gamma lam P)^{-1} g.

Figure of merit (Konda 2002, Ch. 6): the *intrinsic variance*
    IV = lim_k k E || Phi (r_k - r*) ||_D^2 = tr(Sigma Phi' D Phi),   Sigma = A^{-1} Gamma A^{-T},
where Gamma is the long-run covariance of the stationary noise f_k = d_k z_k at r = r*.
IV depends only on span(Phi) (thesis Sec. 6.2.1), and recursive TD with steps alpha/k is
never better than LSTD (Thm 6.1(4)).

Gamma is computed exactly: functions of (x, z) that are affine/quadratic in z are closed
under the transition, so the infinite autocovariance series reduce to linear systems
involving the fundamental matrix of P and the time-reversed chain.
"""

from dataclasses import dataclass

import numpy as np


@dataclass
class MRP:
    P: np.ndarray      # (S, S) row-stochastic transition matrix
    g: np.ndarray      # (S,) reward
    gamma: float       # discount factor

    @property
    def S(self) -> int:
        return self.P.shape[0]

    def stationary(self) -> np.ndarray:
        w, v = np.linalg.eig(self.P.T)
        p = np.real(v[:, np.argmin(np.abs(w - 1))])
        return p / p.sum()

    def value(self) -> np.ndarray:
        return np.linalg.solve(np.eye(self.S) - self.gamma * self.P, self.g)


@dataclass
class TDResult:
    lam: float
    r_star: np.ndarray
    A: np.ndarray
    Gamma: np.ndarray
    Sigma: np.ndarray       # asymptotic covariance of sqrt(k)(r_k - r*) for LSTD
    iv: float               # intrinsic variance  tr(Sigma Phi' D Phi)
    bias: float             # || Phi r* - V ||_D
    proj_err: float         # || Pi V - V ||_D  (best possible in span Phi)


def td_lambda_exact(mrp: MRP, Phi: np.ndarray, lam: float) -> TDResult:
    S, m = Phi.shape
    P, g, gam = mrp.P, mrp.g, mrp.gamma
    pi = mrp.stationary()
    D = np.diag(pi)
    I = np.eye(S)
    c = gam * lam

    # steady-state linear system
    Rl = np.linalg.inv(I - c * P)
    A = Phi.T @ D @ Rl @ (gam * P - I) @ Phi
    b = Phi.T @ D @ Rl @ g
    r = -np.linalg.solve(A, b)

    # temporal differences at r*
    v = Phi @ r
    d = g[:, None] + gam * v[None, :] - v[:, None]           # d[x, x']
    dbar = (P * d).sum(axis=1)                                # E[d | x]
    u = Rl @ dbar                                             # sum_j c^j P^j dbar

    # E[f] = Phi' D u must vanish at r*
    W = Phi * u[:, None]                                      # rows phi(x) u(x)
    assert np.allclose(pi @ W, 0, atol=1e-10), pi @ W

    # q = sum_{n>=1} P^n W via the fundamental matrix Z = (I - P + 1 pi)^{-1}
    Z = np.linalg.inv(I - P + np.outer(np.ones(S), pi))
    q = (Z - I) @ W                                           # (S, m)

    # stationary conditional moments of the trace given the current state,
    # using the time-reversed chain Pr(x, y) = pi(y) P(y, x) / pi(x)
    Pr = (P.T * pi[None, :]) / pi[:, None]
    mu = np.linalg.solve(I - c * Pr, Phi)                     # E[z_0 | x_0]
    mu_prev = Pr @ mu                                         # E[z_{-1} | x_0]
    # M(x) = E[z_0 z_0' | x_0 = x] solves M = C + c^2 Pr M
    C = (np.einsum('xi,xj->xij', Phi, Phi)
         + c * (np.einsum('xi,xj->xij', Phi, mu_prev) + np.einsum('xi,xj->xij', mu_prev, Phi)))
    big = np.eye(S * m * m) - c**2 * np.kron(Pr, np.eye(m * m))
    M = np.linalg.solve(big, C.reshape(S * m * m)).reshape(S, m, m)

    # Gamma = E[f0 f0'] + T + T',  T = sum_{l>=1} E[f0 fl']
    w01 = pi[:, None] * P                                     # joint law of (x0, x1)
    E00 = np.einsum('xy,xy,xij->ij', w01, d**2, M)
    T = (np.einsum('xy,xy,y,xij->ij', w01, d, u, c * M)
         + np.einsum('xy,xy,y,xi,yj->ij', w01, d, u, mu, Phi)
         + np.einsum('xy,xy,xi,yj->ij', w01, d, mu, q))
    Gamma = E00 + T + T.T

    Ainv = np.linalg.inv(A)
    Sigma = Ainv @ Gamma @ Ainv.T
    G = Phi.T @ D @ Phi
    iv = float(np.trace(Sigma @ G))

    V = mrp.value()
    proj = Phi @ np.linalg.solve(G, Phi.T @ D @ V)
    norm_D = lambda x: float(np.sqrt(x @ D @ x))
    return TDResult(lam, r, A, Gamma, Sigma, iv, norm_D(v - V), norm_D(proj - V))


def td_recursive_iv(res: TDResult, Phi: np.ndarray, pi: np.ndarray, alpha: float) -> float:
    """Intrinsic variance of recursive TD(lambda) with steps alpha/k.

    sqrt(k)(r_k - r*) has covariance Sigma solving
        (alpha A + I/2) Sigma + Sigma (alpha A + I/2)' + alpha^2 Gamma = 0,
    provided alpha A + I/2 is Hurwitz; returns inf otherwise.
    """
    m = Phi.shape[1]
    K = alpha * res.A + 0.5 * np.eye(m)
    if np.max(np.linalg.eigvals(K).real) >= 0:
        return np.inf
    L = np.kron(np.eye(m), K) + np.kron(K, np.eye(m))
    Sig = np.linalg.solve(L, -(alpha**2) * res.Gamma.reshape(m * m)).reshape(m, m)
    return float(np.trace(Sig @ Phi.T @ np.diag(pi) @ Phi))


# ---------------------------------------------------------------- simulation check

def simulate_lstd_iv(mrp: MRP, Phi: np.ndarray, lam: float, n_steps: int, n_runs: int,
                     r_star: np.ndarray, seed: int = 0) -> float:
    """Monte Carlo estimate of n E||Phi(r_n - r*)||_D^2 for LSTD(lambda)."""
    rng = np.random.default_rng(seed)
    S, m = Phi.shape
    pi = mrp.stationary()
    cum = np.cumsum(mrp.P, axis=1)
    x = rng.choice(S, size=n_runs, p=pi)
    # start the trace from (approximately) its stationary law
    z = np.zeros((n_runs, m))
    for _ in range(200):
        z = mrp.gamma * lam * z + Phi[x]
        x = (cum[x] < rng.random(n_runs)[:, None]).sum(axis=1)
    Ahat = np.zeros((n_runs, m, m))
    bhat = np.zeros((n_runs, m))
    for _ in range(n_steps):
        x1 = (cum[x] < rng.random(n_runs)[:, None]).sum(axis=1)
        Ahat += np.einsum('ri,rj->rij', z, mrp.gamma * Phi[x1] - Phi[x])
        bhat += z * mrp.g[x][:, None]
        x = x1
        z = mrp.gamma * lam * z + Phi[x]
    r_hat = -np.linalg.solve(Ahat, bhat[..., None])[..., 0]
    err = (r_hat - r_star) @ Phi.T                            # (runs, S)
    return float(n_steps * np.mean((err**2) @ pi))


# ---------------------------------------------------------------- example MRPs

def random_mrp(S: int, gamma: float, seed: int) -> MRP:
    rng = np.random.default_rng(seed)
    P = rng.random((S, S)) ** 4                               # skewed, uneven transitions
    P /= P.sum(axis=1, keepdims=True)
    return MRP(P, rng.normal(size=S), gamma)


def ring_mrp(S: int, gamma: float, stay: float, seed: int) -> MRP:
    """Lazy random walk on a cycle: mixes slowly for large S."""
    rng = np.random.default_rng(seed)
    P = np.zeros((S, S))
    for x in range(S):
        P[x, x] = stay
        P[x, (x + 1) % S] += (1 - stay) * 0.6
        P[x, (x - 1) % S] += (1 - stay) * 0.4
    g = np.sin(2 * np.pi * np.arange(S) / S) + 0.3 * rng.normal(size=S)
    return MRP(P, g, gamma)


def fourier_features(S: int, m: int) -> np.ndarray:
    t = 2 * np.pi * np.arange(S) / S
    cols = [np.ones(S)]
    k = 1
    while len(cols) < m:
        cols.append(np.cos(k * t))
        if len(cols) < m:
            cols.append(np.sin(k * t))
        k += 1
    return np.stack(cols, axis=1)


def mixing_factor(P: np.ndarray) -> float:
    """Second largest eigenvalue modulus."""
    return float(sorted(np.abs(np.linalg.eigvals(P)))[-2])
