"""Test the conjectured identities on all well-posed aliased instances found earlier."""
import numpy as np
from ac_rates import (aliased_mdp, optimum, Critic, rate_of, actor_only_direction,
                      actor_critic_direction)

def rate(mdp, th_opt, HJ, kind, **kw):
    if kind == "ao":
        lam_a = kw["lam_a"]
        return rate_of(mdp, lambda th: actor_only_direction(mdp, th, lam_a, True),
                       lambda th: actor_only_direction(mdp, th, lam_a), th_opt, th_opt, HJ, "")
    cr = kw["critic"]
    return rate_of(mdp, lambda th: actor_critic_direction(mdp, th, cr, True),
                   lambda th: actor_critic_direction(mdp, th, cr), th_opt, th_opt, HJ, "")

worst = dict(C1=0, C2=0, C3=0)
tab_better = 0; tried = 0
for S, seeds, gam in [(6, [2, 7, 22, 28, 48, 60, 66, 74], 0.9), (8, [13, 17, 37, 51, 59], 0.9),
                      (6, [30, 2, 7], 0.95)]:
    for seed in seeds:
        mdp = aliased_mdp(S, 2, [0] * S, gam, seed)
        th_opt, HJ = optimum(mdp, np.zeros(1))
        rng = np.random.default_rng(seed)
        extras = [None, np.ones((S, 1)), rng.normal(size=(S, 2)), np.eye(S)]
        ao1 = rate(mdp, th_opt, HJ, "ao", lam_a=1.0)
        for ph in extras:          # C1: TD(1) critic == actor-only(1), any extra features
            r = rate(mdp, th_opt, HJ, "ac", critic=Critic(1.0, ph))
            worst["C1"] = max(worst["C1"], abs(r.var_term - ao1.var_term) / ao1.var_term)
        for lam in [0.9, 0.6, 0.3]:   # C2: compatible-only TD(lam) == actor-only(lam_a = lam)
            a = rate(mdp, th_opt, HJ, "ao", lam_a=lam)
            b = rate(mdp, th_opt, HJ, "ac", critic=Critic(lam))
            worst["C2"] = max(worst["C2"], abs(a.var_term - b.var_term) / a.var_term,
                              float(abs(a.theta - b.theta).max()))
            t = rate(mdp, th_opt, HJ, "ac", critic=Critic(lam, np.eye(S)))   # C3: tabular => no bias
            worst["C3"] = max(worst["C3"], float(abs(t.theta - th_opt).max()))
            tried += 1; tab_better += t.var_term < ao1.var_term
print("max relative deviation  C1 (TD(1) critic == actor-only):", f"{worst['C1']:.1e}")
print("max deviation           C2 (compatible TD(lam) == actor-only lam_a=lam):", f"{worst['C2']:.1e}")
print("max |theta* - theta_opt| C3 (tabular state features => unbiased):", f"{worst['C3']:.1e}")
print(f"tabular-critic AC faster than unbiased actor-only in {tab_better}/{tried} (instance, lambda<1) pairs")
