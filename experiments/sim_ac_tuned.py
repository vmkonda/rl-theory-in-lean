import sys, time
import numpy as np
from ac_rates import aliased_mdp, optimum, Critic, rate_of, actor_only_direction, actor_critic_direction
from sim_ac import simulate
mdp = aliased_mdp(6, 2, [0] * 6, 0.9, 2)
th_opt, HJ = optimum(mdp, np.zeros(1))
n_steps = int(sys.argv[1]); runs = int(sys.argv[2])
cases = [("actor-only lambda_a=1", "ao", 1.0, None), ("actor-only lambda_a=0.7", "ao", 0.7, None),
         ("AC tabular, lambda=0.3", "ac", 0.3, np.eye(6)), ("AC compatible only, lambda=0.6", "ac", 0.6, None)]
for label, kind, lam, phibar in cases:
    if kind == "ao":
        pred = rate_of(mdp, lambda t: actor_only_direction(mdp, t, lam, True), lambda t: actor_only_direction(mdp, t, lam), th_opt, th_opt, HJ, "")
    else:
        cr = Critic(lam, phibar)
        pred = rate_of(mdp, lambda t: actor_critic_direction(mdp, t, cr, True), lambda t: actor_critic_direction(mdp, t, cr), th_opt, th_opt, HJ, "")
    t0 = time.time()
    emp, bias = simulate(mdp, kind, lam, phibar, pred.theta, n_steps, runs, seed=11,
                         beta0=15.0, beta_exp=0.7, gam0=4.0, gam_exp=0.5, k0=1000)
    print(f"{label:32s} predicted {pred.Sigma[0,0]:8.2f}  simulated {emp:8.2f} +- {emp*np.sqrt(2/runs):6.2f}  ratio {emp/pred.Sigma[0,0]:.3f}  ({time.time()-t0:.0f}s)", flush=True)
