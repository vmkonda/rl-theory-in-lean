"""Exact asymptotic rates of actor-only and actor-critic methods on finite discounted MDPs.

Sampling: the state-decision chain with restarts. At each step, with probability gamma the
next pair follows the MDP and the current policy; with probability 1-gamma the process
restarts from p0. Its stationary law is the discounted occupancy measure eta_theta, so
expectations of score-weighted quantities give the policy gradient (up to the factor 1-gamma).
The augmented chain Y = (flag, s, a) records whether the pair was reached by a restart.

Actor-only (REINFORCE-type, Konda 2002 Sec. 8.1, per-step form):
    Z_k = c_a(Y_k) Z_{k-1} + psi(Y_k),   c_a = lambda_a, reset to 0 at restarts,
    theta += beta_k g(Y_k) Z_k.
Actor-critic (Konda 2002 Sec. 5.1, actor without traces):
    critic features phi_theta(s,a) = [psi_theta(s,a), phibar(s)]   (compatible + extra),
    z_k = c(Y_k) z_{k-1} + phi(Y_k),   d_k = g(Y_k) + 1{Y_{k+1} not a restart} r'phi(Y_{k+1}) - r'phi(Y_k),
    r += gamma_k d_k z_k        (fast),        theta += beta_k (r'phi(Y_k)) psi(Y_k)   (slow).

Rate figure of merit: the optimal-gain asymptotic covariance Sigma = H^{-1} Gamma H^{-T}
of sqrt(k)(theta_k - theta*), where H = -(Jacobian of the mean direction at its root theta*)
and Gamma is the long-run covariance of the effective noise. Sigma is attained by
Polyak-Ruppert averaging or the optimal matrix gain and is invariant to rescaling the
direction by any invertible matrix. For actor-critic, the two-time-scale reduction
(Konda 2002 Thm 7.8, Konda-Tsitsiklis 2004) makes the effective noise
    N_k = V_k - C A_c^{-1} W_k,
with V_k the actor's own noise, W_k = d_k z_k the critic's noise, C = E[psi phi'] and A_c the
critic's TD matrix.
"""

from dataclasses import dataclass, field

import numpy as np

from trace_cov import long_run_cov, stationary, trace_moments


@dataclass
class MDP:
    P: np.ndarray        # (S, A, S)
    g: np.ndarray        # (S, A)
    p0: np.ndarray       # (S,)
    gamma: float
    chi: np.ndarray      # (S, A, n) softmax policy features

    @property
    def S(self): return self.P.shape[0]

    @property
    def A(self): return self.P.shape[1]

    @property
    def n(self): return self.chi.shape[2]

    # --- policy
    def pi(self, th):
        logits = self.chi @ th
        logits -= logits.max(axis=1, keepdims=True)
        p = np.exp(logits)
        return p / p.sum(axis=1, keepdims=True)

    def psi(self, th):
        p = self.pi(th)
        return self.chi - np.einsum('sa,san->sn', p, self.chi)[:, None, :]

    # --- exact objective and gradient
    def values(self, th):
        p = self.pi(th)
        Ppi = np.einsum('sa,sat->st', p, self.P)
        rpi = (p * self.g).sum(1)
        R = np.linalg.inv(np.eye(self.S) - self.gamma * Ppi)
        V = R @ rpi
        Qsa = self.g + self.gamma * self.P @ V
        d = (1 - self.gamma) * self.p0 @ R
        eta = d[:, None] * p
        return V, Qsa, eta

    def J(self, th):
        return float(self.p0 @ self.values(th)[0])

    def grad_J(self, th):
        _, Qsa, eta = self.values(th)
        return np.einsum('sa,sa,san->n', eta, Qsa, self.psi(th)) / (1 - self.gamma)

    # --- augmented restart chain over y = (flag, s, a)
    def chain(self, th):
        S, A, g = self.S, self.A, self.gamma
        p = self.pi(th)
        step = np.einsum('sat,tb->satb', self.P, p).reshape(S * A, S * A)
        restart = np.outer(np.ones(S * A), (self.p0[:, None] * p).reshape(S * A))
        Q = np.zeros((2 * S * A, 2 * S * A))
        for f in (0, 1):
            rows = slice(f * S * A, (f + 1) * S * A)
            Q[rows, :S * A] = g * step
            Q[rows, S * A:] = (1 - g) * restart
        return Q

    def lift(self, arr):
        """Repeat an (S, A, ...) array over the two flags."""
        flat = arr.reshape((self.S * self.A,) + arr.shape[2:])
        return np.concatenate([flat, flat], axis=0)

    def flags(self):
        return np.repeat([0, 1], self.S * self.A)


@dataclass
class Critic:
    """TD(lam) critic with compatible features plus extra state features phibar (S, k)."""
    lam: float
    phibar: np.ndarray = None
    name: str = ""

    def features(self, mdp, th):
        psi = mdp.psi(th)
        if self.phibar is None or self.phibar.shape[1] == 0:
            return psi
        extra = np.repeat(self.phibar[:, None, :], mdp.A, axis=1)
        return np.concatenate([psi, extra], axis=2)


def actor_only_direction(mdp, th, lam_a, with_noise=False):
    Q = mdp.chain(th)
    flags = mdp.flags()
    c = np.where(flags == 1, 0.0, lam_a)
    psi = mdp.lift(mdp.psi(th))
    gy = mdp.lift(mdp.g)
    nu = stationary(Q)
    mu, _ = trace_moments(Q, nu, c, psi)
    h = np.einsum('y,y,yn->n', nu, gy, mu)
    if not with_noise:
        return h
    N, n = psi.shape
    F = np.broadcast_to((gy[:, None, None] * np.eye(n))[:, None], (N, N, n, n)).copy()
    e = np.broadcast_to(-h, (N, N, n)).copy()
    Gam, _ = long_run_cov(Q, c, psi, F, e)
    return h, Gam


def critic_solution(mdp, th, critic):
    Q = mdp.chain(th)
    flags = mdp.flags()
    c = np.where(flags == 1, 0.0, critic.lam)
    phi = mdp.lift(critic.features(mdp, th))
    gy = mdp.lift(mdp.g)
    cont = (flags == 0).astype(float)
    nu = stationary(Q)
    mu, _ = trace_moments(Q, nu, c, phi)
    nxt = Q @ (cont[:, None] * phi)                          # E[1{cont} phi(Y') | Y]
    Ac = np.einsum('y,yi,yj->ij', nu, mu, nxt - phi)
    bc = np.einsum('y,yi,y->i', nu, mu, gy)
    r = -np.linalg.solve(Ac, bc)
    return Q, c, phi, gy, cont, nu, Ac, r


def actor_critic_direction(mdp, th, critic, with_noise=False):
    Q, c, phi, gy, cont, nu, Ac, r = critic_solution(mdp, th, critic)
    psi = mdp.lift(mdp.psi(th))
    C = np.einsum('y,yn,ym->nm', nu, psi, phi)
    fdir = C @ r
    if not with_noise:
        return fdir
    N, m = phi.shape
    n = psi.shape[1]
    v = phi @ r
    d = gy[:, None] + cont[None, :] * v[None, :] - v[:, None]     # d(y, y')
    L = -C @ np.linalg.inv(Ac)
    F = d[:, :, None, None] * L[None, None]                       # (N, N, n, m)
    V = psi * v[:, None] - fdir                                   # actor noise, function of y
    e = np.broadcast_to(V[:, None, :], (N, N, n)).copy()
    Gam, _ = long_run_cov(Q, c, phi, F, e)
    return fdir, Gam


# ---------------------------------------------------------------- roots and rates

def jacobian(fun, th, eps=1e-5):
    n = th.size
    Jm = np.zeros((n, n))
    for i in range(n):
        dth = np.zeros(n); dth[i] = eps
        Jm[:, i] = (fun(th + dth) - fun(th - dth)) / (2 * eps)
    return Jm


def find_root(fun, th0, tol=1e-12, iters=60):
    th = th0.copy()
    for _ in range(iters):
        f = fun(th)
        if np.linalg.norm(f) < tol:
            break
        step = np.linalg.solve(jacobian(fun, th), f)
        t = 1.0
        while np.linalg.norm(fun(th - t * step)) > np.linalg.norm(f) and t > 1e-4:
            t /= 2
        th = th - t * step
        if np.abs(th).max() > 50:      # running off to a deterministic policy
            break
    return th


@dataclass
class Rate:
    label: str
    theta: np.ndarray
    J: float
    Sigma: np.ndarray
    gap: float = 0.0          # J(theta_opt) - J(theta*)
    var_term: float = 0.0     # tr(H_J Sigma)/2: loss per 1/n
    stable: bool = True


def rate_of(mdp, direction_with_noise, direction, th0, th_opt, HJ, label):
    th = find_root(direction, th0)
    H = -jacobian(direction, th)
    stable = bool(np.all(np.linalg.eigvals(H).real > 0))
    _, Gam = direction_with_noise(th)
    Hi = np.linalg.inv(H)
    Sig = Hi @ Gam @ Hi.T
    r = Rate(label, th, mdp.J(th), Sig, stable=stable)
    r.gap = mdp.J(th_opt) - r.J
    r.var_term = 0.5 * float(np.trace(HJ @ Sig))
    return r


def optimum(mdp, th0):
    th = find_root(mdp.grad_J, th0)
    HJ = -jacobian(mdp.grad_J, th)
    return th, HJ


def random_mdp(S, A, n, gamma, seed, skew=3.0):
    rng = np.random.default_rng(seed)
    P = rng.random((S, A, S)) ** skew
    P /= P.sum(axis=2, keepdims=True)
    return MDP(P, rng.normal(size=(S, A)), np.full(S, 1 / S), gamma, rng.normal(size=(S, A, n)))


def aliased_mdp(S, A, groups, gamma, seed, skew=3.0):
    """Softmax policy whose action preferences are shared by groups of states (aliasing):
    chi(s, a) = e_{group(s), a} for a >= 1, so n = n_groups * (A - 1)."""
    rng = np.random.default_rng(seed)
    P = rng.random((S, A, S)) ** skew
    P /= P.sum(axis=2, keepdims=True)
    G = max(groups) + 1
    chi = np.zeros((S, A, G * (A - 1)))
    for s in range(S):
        for a in range(1, A):
            chi[s, a, groups[s] * (A - 1) + a - 1] = 1.0
    return MDP(P, rng.normal(size=(S, A)), np.full(S, 1 / S), gamma, chi)
