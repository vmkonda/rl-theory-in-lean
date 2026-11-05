"""Is the TD(0) tabular-critic noise an orthogonal projection of the TD(lambda) noise, for every
lambda? Exact test of Cov(N_lambda, N_0) = Var(N_0) at theta*; also tests the same identity
between general pairs lambda' < lambda (which would give monotonicity in lambda)."""
import warnings
import numpy as np
from ac_rates import Critic, critic_solution
from explore_value_critic import instances
from trace_cov import long_run_cov

warnings.filterwarnings("ignore")


def noise_parts(mdp, th, lam):
    S = mdp.S
    Q, c, phi, gy, cont, nu, Ac, r = critic_solution(mdp, th, Critic(lam, np.eye(S)))
    psi = mdp.lift(mdp.psi(th))
    C = np.einsum('y,yn,ym->nm', nu, psi, phi)
    L = -C @ np.linalg.inv(Ac)
    v = phi @ r
    d = gy[:, None] + cont[None, :] * v[None, :] - v[:, None]
    return Q, c, phi, psi, v, d, L, nu


cases = instances(10, 5, 2, [0] * 5, 0.9) + instances(8, 6, 2, [0, 0, 0, 1, 1, 1], 0.9)
pairs = [(0.5, 0.0), (0.9, 0.0), (1.0, 0.0), (0.9, 0.5), (0.5, 0.2), (1.0, 0.5)]
res = {pq: (0.0, np.inf) for pq in pairs}
for seed, mdp, th in cases:
    for lam, lam0 in pairs:
        Q, c, phi, psi, v, d, L, nu = noise_parts(mdp, th, lam)
        _, c0, phi0, _, v0, d0, L0, _ = noise_parts(mdp, th, lam0)
        N, n = psi.shape
        m = phi.shape[1]
        # N_lam = psi v + d L z^lam (trace c, features phi); N_lam0 needs its own trace unless lam0 = 0.
        # Stack both traces: z = (z^lam, z^lam0) requires a common c; so use a joint trace of
        # dimension 2m with per-block discount via the exact engine on a block-diagonal lift.
        if lam0 == 0.0:
            F = np.zeros((N, N, 2 * n, m))
            F[:, :, :n, :] = np.einsum('yz,nm->yznm', d, L)
            e = np.zeros((N, N, 2 * n))
            e[:, :, :n] = psi[:, None, :] * v[:, None, None]
            e[:, :, n:] = psi[:, None, :] * v0[:, None, None] + np.einsum('yz,nm,ym->yzn', d0, L0, phi0)
            e -= np.einsum('y,yz,yzn->n', nu, Q, e)
            G, _ = long_run_cov(Q, c, phi, F, e)
        else:
            # z^lam = sum_j lam^(k-j) phi_j, z^lam0 likewise: both are linear in the "two-rate"
            # trace (z^lam, z^lam0), which is a trace with features (phi, phi) only if the
            # discount is common. Use the exact engine twice via the identity
            # Cov(A, B) = (Var(A + B) - Var(A - B)) / 4 with a joint simulation instead.
            G = None
        if G is None:
            continue
        GA, GB, X = G[:n, :n], G[n:, n:], G[:n, n:]
        rel = np.abs(X - GB).max() / np.abs(GB).max()
        dom = np.min(np.linalg.eigvalsh(GA - GB))
        w, md = res[(lam, lam0)]
        res[(lam, lam0)] = (max(w, rel), min(md, dom))
for (lam, lam0), (w, md) in res.items():
    if np.isfinite(md):
        print(f"lambda={lam:.1f} vs {lam0:.1f}: max rel |Cov(N_lam, N_0) - Var(N_0)| = {w:.2e}, "
              f"min eig Gamma(lam) - Gamma(0) = {md:.3e}")
