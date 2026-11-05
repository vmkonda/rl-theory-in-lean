"""The martingale-increment structure behind Theorem 4.6. With X_lambda = (z^psi_k - psi_k) -
K_lambda z^e_k for the tabular TD(lambda) critic, Theorem 4.6 writes
X_lambda = b(s_k) + sum_i lambda^i Delta_i with orthogonal increments Delta_i given s_k. Hence
  E[X_a X_b^T | s] = E[X_m X_m^T | s] with m = sqrt(a b)              (tested here),
whereas the tower property E[X_a X_b^T | s] = E[X_a X_a^T | s] fails for 0 < a < b.
Joint moments of two traces with different decay rates are computed exactly from
  M(y') = sum_y Q(y,y') [la lb c(y')^2 M(y) + la c(y') mu_a(y) phi(y')^T + lb c(y') phi(y') mu_b(y)^T]
          + nu(y') phi(y') phi(y')^T."""
import io, contextlib, warnings
import numpy as np
from ac_rates import Critic, critic_solution
with contextlib.redirect_stdout(io.StringIO()):
    from explore_value_critic import instances
from trace_cov import trace_moments

warnings.filterwarnings("ignore")


def joint_second(Q, nu, cont, phi, la, lb, mua, mub):
    N, m = phi.shape
    A = np.zeros((N * m * m, N * m * m))
    # linear map M -> sum_y Q(y,y') la lb c(y')^2 M(y)
    for yp in range(N):
        for y in range(N):
            w = Q[y, yp] * la * lb * cont[yp] ** 2
            if w:
                A[yp * m * m:(yp + 1) * m * m, y * m * m:(y + 1) * m * m] += w * np.eye(m * m)
    rhs = np.zeros((N, m, m))
    for yp in range(N):
        ta = np.einsum('y,y,yi->i', Q[:, yp], nu, mua)     # mu are conditional moments E[z | Y=y]
        tb = np.einsum('y,y,yi->i', Q[:, yp], nu, mub)
        rhs[yp] = la * cont[yp] * np.outer(ta, phi[yp]) + lb * cont[yp] * np.outer(phi[yp], tb) \
            + nu[yp] * np.outer(phi[yp], phi[yp])
    M = np.linalg.solve(np.eye(N * m * m) - A, rhs.reshape(-1)).reshape(N, m, m)
    return M


cases = instances(8, 5, 2, [0] * 5, 0.9) + instances(6, 6, 2, [0, 0, 0, 1, 1, 1], 0.9)
pairs = [(0.5, 1.0), (0.2, 0.7), (0.5, 0.9), (0.0, 0.6)]
worst = {pq: 0.0 for pq in pairs}
for seed, mdp, th in cases:
    S, A = mdp.S, mdp.A
    flags = mdp.flags(); sidx = np.tile(np.repeat(np.arange(S), A), 2)
    cont = (flags == 0).astype(float)
    psi = mdp.lift(mdp.psi(th)); n = psi.shape[1]
    for la, lb in pairs:        # la = lambda' < lb = lambda
        sols = {}
        for lam in (la, lb):
            Q, c, phi, _, _, nu, Ac, r = critic_solution(mdp, th, Critic(lam, np.eye(S)))
            C = np.einsum('y,yn,ym->nm', nu, psi, phi)
            Lsel = -C @ np.linalg.inv(Ac)
            mu, _ = trace_moments(Q, nu, lam * cont, phi)
            sols[lam] = (Lsel, mu)
        (La, mua), (Lb, mub) = sols[la], sols[lb]
        Mab = joint_second(Q, nu, cont, phi, la, lb, mua, mub)      # E[z^a z^b^T 1{Y=y}]
        Maa = joint_second(Q, nu, cont, phi, la, la, mua, mua)
        nuy = nu[:, None]
        # E[X_a X_b^T 1{y}] with X = Lsel z - psi
        def cross(Lx, mux, Ly, muy, Mxy):
            return (np.einsum('ni,yij,mj->ynm', Lx, Mxy, Ly)
                    - nu[:, None, None] * np.einsum('yn,ym->ynm', mux @ Lx.T, psi)
                    - nu[:, None, None] * np.einsum('yn,ym->ynm', psi, muy @ Ly.T)
                    + nu[:, None, None] * np.einsum('yn,ym->ynm', psi, psi))
        Xab = cross(La, mua, Lb, mub, Mab)
        mrate = np.sqrt(la * lb)
        Q2, c2, phi2, _, _, nu2, Ac2, _ = critic_solution(mdp, th, Critic(mrate, np.eye(S)))
        Lm = -np.einsum('y,yn,ym->nm', nu2, psi, phi2) @ np.linalg.inv(Ac2)
        mum, _ = trace_moments(Q2, nu2, mrate * cont, phi2)
        Mmm = joint_second(Q, nu, cont, phi, mrate, mrate, mum, mum)
        Xaa = cross(Lm, mum, Lm, mum, Mmm)
        for s in range(S):
            sel = sidx == s
            d = np.abs(Xab[sel].sum(0) - Xaa[sel].sum(0)).max() / (np.abs(Xaa[sel].sum(0)).max() + 1e-12)
            worst[(la, lb)] = max(worst[(la, lb)], d)
for (la, lb), w in worst.items():
    print(f"a={la}, b={lb}: max relative |E[X_a X_b^T | s] - E[X_m X_m^T | s]|, m = sqrt(ab): {w:.2e}")
