"""Numbers for docs/actor-critic-rates.tex.

Loss metric: l = lim n E[J(theta*) - J(theta_n)] = tr(H_J Sigma)/2 with the optimal-gain
asymptotic covariance Sigma = H^{-1} Gamma H^{-T} of the linearized iteration (H the Jacobian of
the mean direction, Gamma the long-run covariance of the effective noise).
(a) Theorem 5.1 (TD(1) critic = actor-only with lambda = 1, for any extra critic features) and
(b) Theorem 5.2 (compatible-only critic with TD(lambda) = actor-only with trace lambda):
    relative differences of H, Gamma and l.
(c) Table of l (unbiased designs) and of the bias gap J* - J(theta_hat) (biased designs).
"""
import warnings
import numpy as np
from ac_rates import random_mdp, aliased_mdp, optimum, Critic, actor_only_direction, \
    actor_critic_direction, jacobian, find_root

warnings.filterwarnings("ignore")


def rate(mdp, HJ, th_opt, dwn, d):
    th = find_root(d, th_opt)
    if np.linalg.norm(d(th)) > 1e-9 or np.abs(th).max() > 8:
        return None
    H = -jacobian(d, th)
    _, Gam = dwn(th)
    Hi = np.linalg.inv(H)
    Sig = Hi @ Gam @ Hi.T
    return dict(th=th, H=H, Gam=Gam, l=0.5 * np.trace(HJ @ Sig), gap=mdp.J(th_opt) - mdp.J(th),
                stable=bool(np.all(np.linalg.eigvals(H).real > 0)))


def AO(mdp, HJ, th, lam):
    return rate(mdp, HJ, th, lambda t: actor_only_direction(mdp, t, lam, True),
                lambda t: actor_only_direction(mdp, t, lam))


def AC(mdp, HJ, th, cr):
    return rate(mdp, HJ, th, lambda t: actor_critic_direction(mdp, t, cr, True),
                lambda t: actor_critic_direction(mdp, t, cr))


def rel(a, b):
    return np.abs(a - b).max() / max(np.abs(b).max(), 1e-300)


instances = []
for seed in range(2000):
    mdp = aliased_mdp(6, 2, [0, 0, 0, 1, 1, 1], 0.9, seed)
    th0 = np.zeros(2)
    try:
        th_opt, HJ = optimum(mdp, th0)
    except Exception:
        continue
    if np.linalg.norm(mdp.grad_J(th_opt)) > 1e-9 or np.min(np.linalg.eigvalsh((HJ + HJ.T) / 2)) <= 0 \
            or np.abs(th_opt).max() > 6:
        continue
    instances.append((seed, mdp, th_opt, HJ))
    if len(instances) == 8:
        break
print(f"{len(instances)} well-posed aliased instances (6 states, 2 actions, 2 groups: 2 policy parameters)")

print("\n(a) TD(1) critic vs actor-only, lambda = 1: max relative differences of H, Gamma, l")
print("\n(b) compatible critic, TD(lambda) vs actor-only, trace lambda")
worst_a, worst_b = 0.0, 0.0
for seed, mdp, th, HJ in instances:
    rng = np.random.default_rng(seed)
    ao1 = AO(mdp, HJ, th, 1.0)
    for extra in [rng.normal(size=(6, 2)), np.eye(6)]:
        ac = AC(mdp, HJ, th, Critic(1.0, extra))
        worst_a = max(worst_a, rel(ac["H"], ao1["H"]), rel(ac["Gam"], ao1["Gam"]), abs(ac["l"] / ao1["l"] - 1))
    for lam in [0.9, 0.6, 0.3, 0.0]:
        ao = AO(mdp, HJ, th, lam)
        if ao is None:
            continue
        ac = AC(mdp, HJ, ao["th"], Critic(lam, None))
        if ac is None:
            continue
        worst_b = max(worst_b, rel(ac["th"], ao["th"]), rel(ac["H"], ao["H"]), rel(ac["Gam"], ao["Gam"]),
                      abs(ac["l"] / ao["l"] - 1))
print(f"   (a) worst relative difference over instances and critic features: {worst_a:.1e}")
print(f"   (b) worst relative difference over instances and lambda:          {worst_b:.1e}")

print("\n(d) critic with tabular state features: fixed point (w, V^pi) and unbiased direction")
from ac_rates import critic_solution
worst_d = 0.0
for seed, mdp, th, HJ in instances:
    for t in [th, th + np.array([0.3, -0.2])]:
        V, Qsa, eta = mdp.values(t)
        psi = mdp.psi(t)
        Psi = np.einsum('sa,san,sam->nm', eta, psi, psi)
        w = np.linalg.solve(Psi, np.einsum('sa,san,sa->n', eta, psi, Qsa - V[:, None]))
        for lam in [0.0, 0.4, 0.8, 1.0]:
            r = critic_solution(mdp, t, Critic(lam, np.eye(6)))[-1]
            d = actor_critic_direction(mdp, t, Critic(lam, np.eye(6)))
            worst_d = max(worst_d, np.abs(r - np.concatenate([w, V])).max(),
                          np.abs(d - (1 - mdp.gamma) * mdp.grad_J(t)).max())
print(f"   worst deviation: {worst_d:.1e}")

print("\n(c) loss metric l (unbiased designs, relative to actor-only lambda = 1) and bias gap")
print("    seed |  AO l=0.9  AO l=0.5 | AC tab l=1  l=0.7  l=0.3  l=0  | AC rand2 l=0.7: gap, l")
for seed, mdp, th, HJ in instances:
    rng = np.random.default_rng(seed + 100)
    base = AO(mdp, HJ, th, 1.0)["l"]
    fmt = lambda r: "   --  " if r is None else (f"{r['l'] / base:7.3f}" if r["gap"] < 1e-10
                                                    else f"{r['l'] / base:5.2f}*")
    row = [fmt(AO(mdp, HJ, th, lam)) for lam in [0.9, 0.5]]
    tab = [fmt(AC(mdp, HJ, th, Critic(lam, np.eye(6)))) for lam in [1.0, 0.7, 0.3, 0.0]]
    rb = AC(mdp, HJ, th, Critic(0.7, rng.normal(size=(6, 2))))
    rbs = "  --" if rb is None else f"{rb['gap']:.2e}, {rb['l'] / base:5.3f}"
    print(f"    {seed:4d} |  {row[0]} {row[1]} |  " + " ".join(tab) + f"  | {rbs}")
print("    (* = biased design: limit differs from theta*, l measured at its own limit)")
