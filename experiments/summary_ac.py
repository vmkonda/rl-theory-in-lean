"""Across well-posed instances: which actor design has the least expected loss gap + var/n?"""
import numpy as np
from ac_rates import aliased_mdp, optimum, Critic, rate_of, actor_only_direction, actor_critic_direction

def safe_rate(mdp, th_opt, HJ, dwn, d):
    try:
        r = rate_of(mdp, dwn, d, th_opt, th_opt, HJ, "")
        return r if (r.stable and abs(r.theta[0]) < 6) else None
    except Exception:
        return None

lams = [1.0, 0.9, 0.7, 0.5, 0.3, 0.0]
ns = [10**3, 10**4, 10**5]
wins = {n: {} for n in ns}
ratio_tab, ratio_rand = [], []
tab_best_lam = []
for S, seeds, gam in [(6, [2, 7, 22, 28, 48, 60, 66, 74], 0.9), (8, [13, 17, 37, 51, 59, 82, 83, 90], 0.9),
                      (6, [30], 0.95)]:
    for seed in seeds:
        mdp = aliased_mdp(S, 2, [0] * S, gam, seed)
        th_opt, HJ = optimum(mdp, np.zeros(1))
        rng = np.random.default_rng(seed)
        designs = {"actor-only": [], "AC +random(2)": [], "AC +tabular": []}
        for lam in lams:
            designs["actor-only"].append(safe_rate(mdp, th_opt, HJ,
                lambda t: actor_only_direction(mdp, t, lam, True), lambda t: actor_only_direction(mdp, t, lam)))
            for name, ph in [("AC +random(2)", rng.normal(size=(S, 2))), ("AC +tabular", np.eye(S))]:
                cr = Critic(lam, ph)
                designs[name].append(safe_rate(mdp, th_opt, HJ,
                    lambda t: actor_critic_direction(mdp, t, cr, True), lambda t: actor_critic_direction(mdp, t, cr)))
        ao1 = designs["actor-only"][0].var_term
        tab = [r for r in designs["AC +tabular"] if r is not None]
        tab_best = min(tab, key=lambda r: r.var_term)
        ratio_tab.append(tab_best.var_term / ao1)
        tab_best_lam.append(lams[[r.var_term if r else np.inf for r in designs["AC +tabular"]].index(tab_best.var_term)])
        for n in ns:
            best = {k: min((r.gap + r.var_term / n for r in v if r is not None), default=np.inf)
                    for k, v in designs.items()}
            w = min(best, key=best.get)
            wins[n][w] = wins[n].get(w, 0) + 1
print("best variance of AC+tabular relative to unbiased actor-only: median %.2f, range [%.2f, %.2f]"
      % (np.median(ratio_tab), min(ratio_tab), max(ratio_tab)))
print("lambda giving the least variance for AC+tabular:", dict(zip(*np.unique(tab_best_lam, return_counts=True))))
for n in ns:
    print(f"n = {n:>6}: design with least loss (each tuned over lambda):", wins[n])
