"""Actor-only vs actor-critic with different critics: reward gap and variance term."""
import sys
import numpy as np
from ac_rates import (aliased_mdp, optimum, Critic, rate_of, actor_only_direction,
                      actor_critic_direction)

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2
S = 6
mdp = aliased_mdp(S, 2, [0] * S, 0.9, seed)
th_opt, HJ = optimum(mdp, np.zeros(mdp.n))
V_opt = mdp.values(th_opt)[0]
rng = np.random.default_rng(0)
critics = {
    "compatible only": None,
    "+ constant": np.ones((S, 1)),
    "+ random state feature": rng.normal(size=(S, 1)),
    "+ V at optimum": V_opt[:, None],
    "+ tabular (one-hot)": np.eye(S),
}
print(f"seed {seed}: theta_opt={th_opt}, J*={mdp.J(th_opt):.4f}, H_J={HJ.ravel()}")
print(f"{'method':38s} {'theta*':>8s} {'gap':>9s} {'var term':>10s} {'stable':>6s}")
for lam_a in [1.0, 0.9, 0.7, 0.5]:
    r = rate_of(mdp, lambda th: actor_only_direction(mdp, th, lam_a, True),
                lambda th: actor_only_direction(mdp, th, lam_a), th_opt, th_opt, HJ, "")
    print(f"{'actor-only, lambda_a=%.1f' % lam_a:38s} {r.theta[0]:8.4f} {r.gap:9.2e} {r.var_term:10.3f} {str(r.stable):>6s}")
for name, phibar in critics.items():
    for lam in [1.0, 0.9, 0.6, 0.3, 0.0]:
        cr = Critic(lam, phibar)
        try:
            r = rate_of(mdp, lambda th: actor_critic_direction(mdp, th, cr, True),
                        lambda th: actor_critic_direction(mdp, th, cr), th_opt, th_opt, HJ, "")
            print(f"{'AC ' + name + ', lambda=%.1f' % lam:38s} {r.theta[0]:8.4f} {r.gap:9.2e} {r.var_term:10.3f} {str(r.stable):>6s}")
        except Exception as ex:
            print(f"{'AC ' + name + ', lambda=%.1f' % lam:38s} failed: {ex}")
