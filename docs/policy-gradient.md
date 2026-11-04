# Policy Gradients for Discounted Finite MDPs: A Formalized Account

*Vijaymohan Konda · November 2026*

*Generated from the LaTeX source in this directory; the PDF has the same numbering.*

> **Abstract.**
>
> We give a self-contained account of the policy gradient theorem for discounted Markov decision processes with finite state and action spaces, following the formalization in Lean 4 contained in the `rl-theory-in-lean` project. The results are finite-MDP counterparts of the gradient formulas of Chapter 2 of *Actor-Critic Algorithms* (Konda, 2002), and are the first step towards formalizing the convergence of actor-critic algorithms. Every definition, lemma and theorem below has been machine-checked; the name of the corresponding Lean declaration is given after each statement.

## 1 Introduction

Actor-critic algorithms search for a good policy within a parameterized family $`\{\pi_\theta : \theta \in \mathbb{R}^n\}`$ by following an estimate of the gradient of the overall reward with respect to $`\theta`$. The starting point of their analysis is a formula expressing that gradient in terms of quantities that can be estimated from simulation: the stationary (or discounted) distribution of state-decision pairs, the state-decision value function $`Q_\theta`$, and the *score* $`\psi_\theta = \nabla_\theta \log \pi_\theta`$.

This note proves that formula for discounted finite MDPs. Two features of the setting simplify matters considerably compared to the general state spaces of the thesis.

1.  All objects are finite-dimensional, so value functions are obtained by inverting a matrix, and differentiability can be established by elementary means (Cramer’s rule), with no uniform integrability arguments.

2.  We work with *strictly positive* policies. Then the support of the induced Markov chain does not depend on $`\theta`$, so irreducibility and aperiodicity need only be checked at a single parameter value.

The proof of the main theorem (Theorem [6.3](#thm:pg)) avoids differentiating a matrix inverse altogether. Instead we differentiate the Bellman equation and observe that the gradient of the value function solves a Bellman equation of its own, whose unique solution is given by the same resolvent.

##### Organization.

Section [2](#sec:setting) fixes the model. Section [3](#sec:policies) introduces parameterized policies and the softmax family. Section [4](#sec:values) develops the value function of a fixed policy. Section [5](#sec:differentiability) establishes differentiability, and Section [6](#sec:gradient) proves the policy gradient theorem. Section [7](#sec:lean) lists the correspondence with the Lean code and the relation to the thesis.

<a id="sec:setting"></a>

## 2 Setting

Throughout, $`\mathcal{S}`$ and $`\mathcal{A}`$ are finite nonempty sets of states and decisions (actions). A vector $`x \in \mathbb{R}^{\mathcal{S}}`$ is *stochastic* if $`x(s) \ge 0`$ for all $`s`$ and $`\sum_s x(s) = 1`$; a matrix is *row stochastic* if each of its rows is stochastic.

<div id="def:mdp" class="definition">

**Definition 2.1** (Finite MDP). A *finite MDP* consists of

- transition probabilities $`P(s' \mid s, a)`$, such that $`P(\cdot \mid s, a)`$ is stochastic for each $`(s,a) \in \mathcal{S}\times \mathcal{A}`$;

- a one-stage reward $`r : \mathcal{S}\times \mathcal{A}\to \mathbb{R}`$;

- an initial distribution $`p_0`$ on $`\mathcal{S}`$;

- a discount factor $`\gamma \in [0, 1)`$.

*Lean:* `TabularMDP`

</div>

A (randomized stationary) *policy* is a map $`\pi : \mathcal{S}\times \mathcal{A}\to \mathbb{R}`$ such that $`\pi(\cdot \mid s)`$ is stochastic for every $`s`$. A policy induces
``` math
\begin{align*}
  P_\pi(s, s') &= \sum_{a} \pi(a \mid s)\, P(s' \mid s, a)
    && \text{(state transition matrix)}, \\
  r_\pi(s) &= \sum_{a} \pi(a \mid s)\, r(s, a)
    && \text{(expected one-stage reward)}, \\
  \bar P_\pi\big((s,a), (s',a')\big) &= P(s' \mid s, a)\, \pi(a' \mid s')
    && \text{(state-decision transition matrix)}.
\end{align*}
```

*Lean:* `TabularMDP.stateMat, TabularMDP.stateReward, TabularMDP.saMat`

<div id="lem:rowstoch" class="lemma">

**Lemma 2.2**. *If $`\pi`$ is a policy, then $`P_\pi`$ and $`\bar P_\pi`$ are row stochastic.*

</div>

<div class="proof">

*Proof.* Nonnegativity is clear. For the row sums, $`\sum_{s'} P_\pi(s,s') = \sum_a \pi(a\mid s) \sum_{s'} P(s'\mid s,a) = \sum_a \pi(a\mid s) = 1`$, and similarly $`\sum_{s',a'} \bar P_\pi((s,a),(s',a')) = \sum_{s'} P(s'\mid s,a) \sum_{a'} \pi(a'\mid s') = 1`$. ◻

</div>

*Lean:* `TabularMDP.rowStochastic_stateMat, TabularMDP.rowStochastic_saMat`

<div class="remark">

**Remark 2.3**. The existing development in `rl-theory-in-lean` represents an MDP through probability measures and Markov kernels (`MDPSpec`, `FiniteMDP`). The real-valued representation above is equivalent for finite spaces and is far more convenient for calculus. The two are connected: every `MDPSpec` yields a `TabularMDP` (`MDPSpec.toTabular`), and the state-decision chain of a `FiniteMDP` used in the existing TD and Q-learning results is exactly $`\bar P_\pi`$ (`FiniteMDP.MRP_P_eq_saMat`).

</div>

<a id="sec:policies"></a>

## 3 Parameterized policies

<div id="def:family" class="definition">

**Definition 3.1** (Policy family). A *policy family* with $`n`$ parameters is a map $`\theta \mapsto \pi_\theta`$ from $`\mathbb{R}^n`$ to policies such that

1.  $`\pi_\theta(a \mid s) > 0`$ for all $`\theta`$, $`s`$, $`a`$; and

2.  $`\theta \mapsto \pi_\theta(a \mid s)`$ is differentiable for all $`s`$, $`a`$.

The *score* of the family is
``` math
\psi_\theta(s, a) = \nabla_\theta \log \pi_\theta(a \mid s) \in \mathbb{R}^n .
```

*Lean:* `PolicyFamily, PolicyFamily.score`

</div>

<div id="lem:lr" class="lemma">

**Lemma 3.2** (Likelihood ratio). For all $`\theta`$, $`s`$, $`a`$,
``` math
\nabla_\theta\, \pi_\theta(a \mid s) = \pi_\theta(a \mid s)\, \psi_\theta(s,a).
```

</div>

<div class="proof">

*Proof.* Since $`\pi_\theta(a\mid s) > 0`$, the chain rule gives $`\psi_\theta(s,a) = \pi_\theta(a\mid s)^{-1}\, \nabla_\theta \pi_\theta(a\mid s)`$. Multiply by $`\pi_\theta(a\mid s)`$. ◻

</div>

*Lean:* `PolicyFamily.hasGradientAt_pi`

<div id="lem:mean-zero" class="lemma">

**Lemma 3.3** (The score has mean zero). For all $`\theta`$ and $`s`$,
``` math
\sum_{a} \pi_\theta(a \mid s)\, \psi_\theta(s,a) = 0 .
```

</div>

<div class="proof">

*Proof.* By Lemma [3.2](#lem:lr), the left side is $`\nabla_\theta \sum_a \pi_\theta(a\mid s) = \nabla_\theta 1 = 0`$. ◻

</div>

*Lean:* `PolicyFamily.sum_smul_score_eq_zero`

### 3.1 The softmax family

Let $`\phi : \mathcal{S}\times \mathcal{A}\to \mathbb{R}^n`$ be a feature map. The *softmax* (or Gibbs) policy is
``` math
\pi_\theta(a \mid s) =
  \frac{\exp \langle \theta, \phi(s,a)\rangle}{\sum_{b} \exp \langle \theta, \phi(s,b)\rangle} .
```

*Lean:* `softmax, softmaxFamily`

<div id="prop:softmax" class="proposition">

**Proposition 3.4**. The softmax policies form a policy family, and its score is the centered feature:
``` math
\psi_\theta(s,a) = \phi(s,a) - \sum_{b} \pi_\theta(b\mid s)\, \phi(s,b).
```

</div>

<div class="proof">

*Proof.* The denominator $`Z_\theta(s) = \sum_b \exp\langle \theta, \phi(s,b)\rangle`$ is positive, so $`\pi_\theta(a\mid s) > 0`$; the probabilities clearly sum to one; and $`\pi_\theta(a\mid s)`$ is a product of the differentiable functions $`\exp\langle \theta, \phi(s,a)\rangle`$ and $`Z_\theta(s)^{-1}`$. For the score, write $`\log \pi_\theta(a\mid s) = \langle \theta, \phi(s,a)\rangle - \log Z_\theta(s)`$ and note that $`\nabla_\theta Z_\theta(s) = \sum_b \exp\langle \theta, \phi(s,b)\rangle\, \phi(s,b)`$, so that $`\nabla_\theta \log Z_\theta(s) = \sum_b \pi_\theta(b\mid s)\,\phi(s,b)`$. ◻

</div>

*Lean:* `softmax_pos, softmax_stochastic, differentiable_softmax, softmaxFamily_score`

### 3.2 Irreducibility and aperiodicity

Convergence results for simulation-based algorithms require the Markov chain of state-decision pairs to be irreducible and aperiodic for every policy in the family (Assumption 2.4 of the thesis). For strictly positive families it is enough to check this at a single parameter.

<div id="lem:pattern" class="lemma">

**Lemma 3.5**. *Let $`B`$ and $`C`$ be square matrices with nonnegative entries and the same positivity pattern, i.e. $`B_{ij} > 0 \iff C_{ij} > 0`$. Then for every $`m \ge 0`$, $`B^m`$ and $`C^m`$ have the same positivity pattern.*

</div>

<div class="proof">

*Proof.* Induction on $`m`$, the case $`m = 0`$ being trivial. Since all entries are nonnegative, $`(B^{m+1})_{ij} = \sum_k (B^m)_{ik} B_{kj} > 0`$ if and only if there is $`k`$ with $`(B^m)_{ik} > 0`$ and $`B_{kj} > 0`$. By the induction hypothesis and the assumption, the same condition characterizes $`(C^{m+1})_{ij} > 0`$. ◻

</div>

*Lean:* `pow_pos_iff_of_pos_iff`

<div id="prop:support" class="proposition">

**Proposition 3.6**. *Let $`\{\pi_\theta\}`$ be a policy family and $`\theta_0, \theta \in \mathbb{R}^n`$. If $`\bar P_{\pi_{\theta_0}}`$ is irreducible (respectively aperiodic), then so is $`\bar P_{\pi_\theta}`$.*

</div>

<div class="proof">

*Proof.* Since $`\pi_\theta(a'\mid s') > 0`$, the entry $`\bar P_{\pi_\theta}((s,a),(s',a')) = P(s'\mid s,a)\,\pi_\theta(a'\mid s')`$ is positive if and only if $`P(s'\mid s,a) > 0`$, a condition independent of $`\theta`$. By Lemma [3.5](#lem:pattern), all powers of $`\bar P_{\pi_{\theta_0}}`$ and $`\bar P_{\pi_\theta}`$ have the same positivity pattern. Irreducibility (for all $`y, z`$ some power has a positive $`(y,z)`$ entry) and aperiodicity (for each $`y`$ the set of return times $`\{m \ge 1 : (\bar P^m)_{yy} > 0\}`$ has greatest common divisor one) depend only on these patterns. ◻

</div>

*Lean:* `PolicyFamily.saMat_pow_pos_iff, PolicyFamily.irreducible_saMat, PolicyFamily.aperiodic_saMat`

<div class="remark">

**Remark 3.7**. Proposition [3.6](#prop:support) does *not* give mixing rates that are uniform in $`\theta`$; for the softmax family the chain can mix arbitrarily slowly as $`\|\theta\| \to \infty`$. Uniform geometric ergodicity (Assumption 2.5 of the thesis) therefore remains a genuine assumption for the convergence analysis of actor-critic algorithms, to be imposed later.

</div>

<a id="sec:values"></a>

## 4 Value functions of a fixed policy

Fix a policy $`\pi`$ and abbreviate $`P = P_\pi`$. Define the *resolvent*
``` math
R_\pi = (I - \gamma P_\pi)^{-1},
```
and the value functions and objective
``` math
\begin{align*}
  V_\pi &= R_\pi\, r_\pi, \\
  Q_\pi(s,a) &= r(s,a) + \gamma \sum_{s'} P(s' \mid s,a)\, V_\pi(s'), \\
  J(\pi) &= \sum_s p_0(s)\, V_\pi(s).
\end{align*}
```
Finally define the normalized discounted state visitation distribution and the corresponding state-decision occupancy measure
``` math
d_\pi = (1 - \gamma)\, p_0^\top R_\pi, \qquad
  \eta_\pi(s, a) = d_\pi(s)\, \pi(a \mid s).
```

*Lean:* `TabularMDP.resolvent, TabularMDP.V, TabularMDP.Q, TabularMDP.J, TabularMDP.visitation, TabularMDP.occupancy`

Since $`R_\pi = \sum_{k \ge 0} \gamma^k P_\pi^k`$ when the series converges, $`d_\pi(s)`$ is the (normalized) expected discounted number of visits to $`s`$ starting from $`p_0`$. We do not use this series; all properties of $`R_\pi`$ needed below are derived from two maximum/minimum principles.

<div id="lem:invertible" class="lemma">

**Lemma 4.1**. *$`I - \gamma P_\pi`$ is invertible.*

</div>

<div class="proof">

*Proof.* It suffices to show that $`(I - \gamma P)v = 0`$ implies $`v = 0`$. Such a $`v`$ satisfies $`v = \gamma P v`$. Choose $`s_0`$ maximizing $`|v(s)|`$. Since the row $`P(s_0, \cdot)`$ is stochastic,
``` math
|v(s_0)| = \gamma \Big| \sum_{s'} P(s_0,s')\, v(s') \Big|
  \le \gamma \sum_{s'} P(s_0,s')\, |v(s_0)| = \gamma\, |v(s_0)| .
```
As $`\gamma < 1`$, this forces $`|v(s_0)| = 0`$, hence $`v = 0`$. ◻

</div>

*Lean:* `TabularMDP.isUnit_one_sub_smul_stateMat`

Consequently $`(I - \gamma P)R_\pi = R_\pi(I - \gamma P) = I`$, and in particular
``` math
  R_\pi = I + \gamma P_\pi R_\pi .
 \tag{1}
```

*Lean:* `TabularMDP.one_sub_mul_resolvent, TabularMDP.resolvent_mul_one_sub, TabularMDP.resolvent_apply`

<div id="lem:minprinciple" class="lemma">

**Lemma 4.2** (Minimum principle). *If $`u, b \in \mathbb{R}^{\mathcal{S}}`$ satisfy $`u = b + \gamma P_\pi u`$ and $`b \ge 0`$, then $`u \ge 0`$.*

</div>

<div class="proof">

*Proof.* Choose $`s_0`$ minimizing $`u`$. Since $`P(s_0,\cdot)`$ is stochastic, $`u(s_0) \le \sum_{s'} P(s_0,s')\,u(s')`$. Using $`b(s_0) \ge 0`$ and $`\gamma \ge 0`$,
``` math
u(s_0) = b(s_0) + \gamma \sum_{s'} P(s_0,s')\, u(s') \ge \gamma\, u(s_0),
```
so $`(1-\gamma)\,u(s_0) \ge 0`$ and $`u(s_0) \ge 0`$. Hence $`u \ge u(s_0) \ge 0`$. ◻

</div>

*Lean:* `TabularMDP.nonneg_of_eq_add`

<div id="cor:resolvent" class="corollary">

**Corollary 4.3**. The resolvent has nonnegative entries and each of its rows sums to $`(1-\gamma)^{-1}`$:
``` math
R_\pi(s,j) \ge 0, \qquad \sum_j R_\pi(s,j) = \frac{1}{1-\gamma} .
```

</div>

<div class="proof">

*Proof.* For fixed $`j`$, the column $`u = R_\pi(\cdot, j)`$ satisfies $`u = e_j + \gamma P u`$ by [(1)](#eq:resolvent), so $`u \ge 0`$ by Lemma [4.2](#lem:minprinciple). For the row sums, let $`c = (1-\gamma)^{-1}`$, so that $`c = 1 + \gamma c`$. Summing [(1)](#eq:resolvent) over $`j`$ shows that $`w(s) = \sum_j R_\pi(s,j) - c`$ satisfies $`w = \gamma P w`$, using that $`P`$ is row stochastic. Applying Lemma [4.2](#lem:minprinciple) with $`b = 0`$ to both $`w`$ and $`-w`$ gives $`w = 0`$. ◻

</div>

*Lean:* `TabularMDP.resolvent_nonneg, TabularMDP.sum_resolvent`

<div id="prop:bellman" class="proposition">

**Proposition 4.4** (Bellman equation). *$`V_\pi = r_\pi + \gamma P_\pi V_\pi`$, and $`V_\pi(s) = \sum_a \pi(a\mid s)\, Q_\pi(s,a)`$ for every $`s`$.*

</div>

<div class="proof">

*Proof.* $`(I - \gamma P)V_\pi = (I-\gamma P)R_\pi r_\pi = r_\pi`$, which rearranges to the first identity. For the second, $`\sum_a \pi(a\mid s) Q_\pi(s,a) = r_\pi(s) + \gamma \sum_{s'} P_\pi(s,s') V_\pi(s')`$ by the definitions of $`Q_\pi`$ and $`P_\pi`$, which equals $`V_\pi(s)`$ by the first identity. ◻

</div>

*Lean:* `TabularMDP.bellman, TabularMDP.bellman_apply, TabularMDP.V_eq_sum_Q`

<div id="prop:visitation" class="proposition">

**Proposition 4.5**. *$`d_\pi`$ is a probability distribution on $`\mathcal{S}`$ and $`\eta_\pi`$ is a probability distribution on $`\mathcal{S}\times \mathcal{A}`$.*

</div>

<div class="proof">

*Proof.* Nonnegativity follows from Corollary [4.3](#cor:resolvent). For the total mass,
``` math
\sum_{s'} d_\pi(s') = (1-\gamma) \sum_s p_0(s) \sum_{s'} R_\pi(s,s')
  = (1-\gamma)\cdot\frac{1}{1-\gamma}\sum_s p_0(s) = 1,
```
and $`\sum_{s,a}\eta_\pi(s,a) = \sum_s d_\pi(s)\sum_a \pi(a\mid s) = 1`$. ◻

</div>

*Lean:* `TabularMDP.stochastic_visitation, TabularMDP.stochastic_occupancy`

<a id="sec:differentiability"></a>

## 5 Differentiability

From now on $`\{\pi_\theta\}`$ is a policy family, and we write $`P_\theta, r_\theta, R_\theta, V_\theta, Q_\theta, J(\theta), d_\theta, \eta_\theta`$ for the objects of Section [4](#sec:values) associated with $`\pi_\theta`$.

<div id="lem:dPdr" class="lemma">

**Lemma 5.1**. For all $`s, s'`$,
``` math
\nabla_\theta P_\theta(s,s') = \sum_a P(s'\mid s,a)\, \pi_\theta(a\mid s)\,\psi_\theta(s,a),
  \qquad
  \nabla_\theta r_\theta(s) = \sum_a r(s,a)\, \pi_\theta(a\mid s)\,\psi_\theta(s,a).
```

</div>

<div class="proof">

*Proof.* Both are finite sums of $`\pi_\theta(a\mid s)`$ times constants; apply Lemma [3.2](#lem:lr). ◻

</div>

*Lean:* `PolicyFamily.hasGradientAt_stateMat, PolicyFamily.hasGradientAt_stateReward`

<div id="lem:cramer" class="lemma">

**Lemma 5.2** (Cramer’s rule). *Let $`\theta \mapsto B_\theta`$ be a matrix-valued map whose entries are differentiable and with $`\det B_\theta \ne 0`$ for all $`\theta`$. Then every entry of $`\theta \mapsto B_\theta^{-1}`$ is differentiable.*

</div>

<div class="proof">

*Proof.* By the Leibniz formula $`\det B = \sum_\sigma \mathop{\mathrm{sgn}}(\sigma) \prod_i B_{\sigma(i), i}`$, the determinant is a polynomial in the entries, hence $`\theta \mapsto \det B_\theta`$ is differentiable. The entry $`(\mathop{\mathrm{adj}}B)_{ij}`$ of the adjugate is the determinant of the matrix obtained from $`B`$ by replacing its $`j`$-th row with the $`i`$-th unit vector; its entries are entries of $`B`$ or constants, so it is differentiable as well. Finally $`(B^{-1})_{ij} = (\det B)^{-1} (\mathop{\mathrm{adj}}B)_{ij}`$, and $`(\det B_\theta)^{-1}`$ is differentiable because $`\det B_\theta \ne 0`$. ◻

</div>

*Lean:* `differentiable_det_of_entries, differentiable_inv_of_entries`

<div id="cor:diffV" class="corollary">

**Corollary 5.3**. *The maps $`\theta \mapsto R_\theta(s,j)`$, $`\theta \mapsto V_\theta(s)`$ and $`\theta \mapsto J(\theta)`$ are differentiable.*

</div>

<div class="proof">

*Proof.* Apply Lemma [5.2](#lem:cramer) to $`B_\theta = I - \gamma P_\theta`$, whose entries are differentiable by Lemma [5.1](#lem:dPdr) and whose determinant never vanishes by Lemma [4.1](#lem:invertible). Then $`V_\theta(s) = \sum_{s'} R_\theta(s,s')\, r_\theta(s')`$ and $`J(\theta) = \sum_s p_0(s) V_\theta(s)`$ are finite sums of products of differentiable functions. ◻

</div>

*Lean:* `PolicyFamily.differentiable_resolvent, PolicyFamily.differentiable_V, PolicyFamily.differentiable_J`

<a id="sec:gradient"></a>

## 6 The policy gradient theorem

The key observation is that the gradients of the value function satisfy a Bellman equation whose “reward” is $`\sum_a \pi_\theta Q_\theta \psi_\theta`$, and whose solution is therefore again given by the resolvent. We first record the uniqueness statement for vector-valued unknowns.

<div id="lem:vecbellman" class="lemma">

**Lemma 6.1**. Let $`\pi`$ be a policy and let $`G, b : \mathcal{S}\to \mathbb{R}^n`$ satisfy $`G(s) = b(s) + \gamma \sum_{s'} P_\pi(s,s')\, G(s')`$ for all $`s`$. Then
``` math
G(s) = \sum_{s'} R_\pi(s,s')\, b(s') \qquad \text{for all } s.
```

</div>

<div class="proof">

*Proof.* Substituting $`b(s') = G(s') - \gamma\sum_k P_\pi(s',k)\,G(k)`$ and exchanging the order of summation,
``` math
\begin{align*}
  \sum_{s'} R_\pi(s,s')\, b(s')
  &= \sum_k \Big[ R_\pi(s,k) - \gamma \sum_{s'} R_\pi(s,s') P_\pi(s',k) \Big] G(k) \\
  &= \sum_k \big[R_\pi (I - \gamma P_\pi)\big]_{sk}\, G(k) = G(s). 
\end{align*}
```
 ◻

</div>

*Lean:* `TabularMDP.eq_resolvent_smul`

<div id="thm:gradV" class="theorem">

**Theorem 6.2** (Gradient of the value function). For every $`\theta`$ and $`s`$,
``` math
\nabla_\theta V_\theta(s) = \sum_{s'} R_\theta(s,s') \sum_{a}
    \pi_\theta(a\mid s')\, Q_\theta(s',a)\, \psi_\theta(s',a).
```

</div>

<div class="proof">

*Proof.* Write $`G(s) = \nabla_\theta V_\theta(s)`$, which exists by Corollary [5.3](#cor:diffV). The Bellman equation (Proposition [4.4](#prop:bellman)) holds for every value of the parameter:
``` math
V_\theta(s) = r_\theta(s) + \gamma \sum_{s'} P_\theta(s,s')\, V_\theta(s').
```
Differentiating both sides with Lemma [5.1](#lem:dPdr) and the product rule,
``` math
\begin{align*}
  G(s) &= \sum_a r(s,a)\,\pi_\theta(a\mid s)\,\psi_\theta(s,a)
    + \gamma \sum_{s'} V_\theta(s') \sum_a P(s'\mid s,a)\,\pi_\theta(a\mid s)\,\psi_\theta(s,a) \\
  &\qquad + \gamma \sum_{s'} P_\theta(s,s')\, G(s') \\
  &= \sum_a \pi_\theta(a\mid s)\Big[ r(s,a) + \gamma \sum_{s'} P(s'\mid s,a)\, V_\theta(s')\Big]
    \psi_\theta(s,a) \\
  &\qquad + \gamma \sum_{s'} P_\theta(s,s')\, G(s') \\
  &= b(s) + \gamma \sum_{s'} P_\theta(s,s')\, G(s'),
\end{align*}
```
where $`b(s) = \sum_a \pi_\theta(a\mid s)\, Q_\theta(s,a)\, \psi_\theta(s,a)`$. The claim now follows from Lemma [6.1](#lem:vecbellman). ◻

</div>

*Lean:* `PolicyFamily.hasGradientAt_V`

<div id="thm:pg" class="theorem">

**Theorem 6.3** (Policy gradient theorem, discounted reward). For every $`\theta \in \mathbb{R}^n`$,
``` math
\nabla J(\theta) = \frac{1}{1-\gamma} \sum_{s \in \mathcal{S}} \sum_{a \in \mathcal{A}}
    \eta_\theta(s,a)\, Q_\theta(s,a)\, \psi_\theta(s,a).
```
Equivalently, writing $`\langle f, g\rangle_\theta = \sum_{s,a}\eta_\theta(s,a) f(s,a) g(s,a)`$, the $`i`$-th partial derivative is $`\partial_i J(\theta) = (1-\gamma)^{-1}\langle Q_\theta, \psi^i_\theta\rangle_\theta`$.

</div>

<div class="proof">

*Proof.* By Theorem [6.2](#thm:gradV), with $`b`$ as in its proof,
``` math
\nabla J(\theta) = \sum_s p_0(s)\, \nabla_\theta V_\theta(s)
  = \sum_{s'} \Big[\sum_s p_0(s)\, R_\theta(s,s')\Big] b(s')
  = \frac{1}{1-\gamma} \sum_{s'} d_\theta(s')\, b(s'),
```
and $`d_\theta(s')\, b(s') = \sum_a \eta_\theta(s',a)\, Q_\theta(s',a)\, \psi_\theta(s',a)`$. ◻

</div>

*Lean:* `PolicyFamily.hasGradientAt_J`

<div id="cor:baseline" class="corollary">

**Corollary 6.4** (Baselines). For every function $`\beta : \mathcal{S}\to \mathbb{R}`$,
``` math
\nabla J(\theta) = \frac{1}{1-\gamma} \sum_{s,a}
    \eta_\theta(s,a)\, \big(Q_\theta(s,a) - \beta(s)\big)\, \psi_\theta(s,a).
```

</div>

<div class="proof">

*Proof.* The additional term is $`\sum_s d_\theta(s)\,\beta(s) \sum_a \pi_\theta(a\mid s)\,\psi_\theta(s,a)`$, which vanishes by Lemma [3.3](#lem:mean-zero). ◻

</div>

*Lean:* `PolicyFamily.hasGradientAt_J_baseline`

<div class="remark">

**Remark 6.5**. Taking $`\beta = V_\theta`$ and using Proposition [4.4](#prop:bellman) expresses the gradient through the *advantage* $`Q_\theta - V_\theta`$. This is the finite-MDP form of the observation in Chapter 5 of the thesis that the critic need only learn the projection of $`Q_\theta`$ onto the span of the score functions, which is the subject of the next step of the formalization.

</div>

<a id="sec:lean"></a>

## 7 Correspondence with the Lean code and the thesis

### 7.1 Lean declarations

The results above are contained in three files of the `rl-theory-in-lean` project:

- `RLTheory/MarkovDecisionProcess/PolicyFamily.lean`: Sections [2](#sec:setting)–[3](#sec:policies);

- `RLTheory/MarkovDecisionProcess/PolicyGradient.lean`: Sections [4](#sec:values)–[6](#sec:gradient);

- `RLTheory/Analysis/Calculus/Gradient.lean`: sum, product, logarithm and exponential rules for gradients, which Mathlib states only for Fréchet derivatives.

All declarations are in the namespace `ReinforcementLearning`. Gradients are expressed with Mathlib’s `HasGradientAt`, on the parameter space $`\mathbb{R}^n`$ realized as Mathlib’s Euclidean space (abbreviated `E n` in the project). No declaration depends on any axiom beyond the three standard ones (`propext`, `Classical.choice`, `Quot.sound`).

<div class="center">

| Result | Lean declaration |
|:---|:---|
| Definition [2.1](#def:mdp) | `TabularMDP` |
| Definition [3.1](#def:family) | `PolicyFamily`, `PolicyFamily.score` |
| Lemma [3.2](#lem:lr) | `PolicyFamily.hasGradientAt_pi` |
| Lemma [3.3](#lem:mean-zero) | `PolicyFamily.sum_smul_score_eq_zero` |
| Proposition [3.4](#prop:softmax) | `softmaxFamily`, `softmaxFamily_score` |
| Proposition [3.6](#prop:support) | `PolicyFamily.irreducible_saMat`, `PolicyFamily.aperiodic_saMat` |
| Lemma [4.1](#lem:invertible) | `TabularMDP.isUnit_one_sub_smul_stateMat` |
| Lemma [4.2](#lem:minprinciple) | `TabularMDP.nonneg_of_eq_add` |
| Corollary [4.3](#cor:resolvent) | `TabularMDP.resolvent_nonneg`, `TabularMDP.sum_resolvent` |
| Proposition [4.4](#prop:bellman) | `TabularMDP.bellman`, `TabularMDP.V_eq_sum_Q` |
| Proposition [4.5](#prop:visitation) | `TabularMDP.stochastic_visitation`, `TabularMDP.stochastic_occupancy` |
| Lemma [5.2](#lem:cramer) | `differentiable_inv_of_entries` |
| Lemma [6.1](#lem:vecbellman) | `TabularMDP.eq_resolvent_smul` |
| Theorem [6.2](#thm:gradV) | `PolicyFamily.hasGradientAt_V` |
| Theorem [6.3](#thm:pg) | `PolicyFamily.hasGradientAt_J` |
| Corollary [6.4](#cor:baseline) | `PolicyFamily.hasGradientAt_J_baseline` |

</div>

### 7.2 Relation to the thesis

Theorem [6.3](#thm:pg) is the finite-MDP counterpart of the discounted-reward gradient formula of Section 2.4 of the thesis (Theorem 2.13). The differences are the following.

- *State and decision spaces.* The thesis allows general (finite, countable or continuous) spaces, which requires the bounding functions and uniform integrability conditions of Assumptions 2.7–2.9 to justify exchanging differentiation and integration. For finite spaces these conditions are automatic.

- *Positivity and smoothness.* Assumption 2.8 of the thesis requires $`\pi_\theta(a\mid s) > 0`$ and continuous differentiability of $`\theta\mapsto\pi_\theta(a\mid s)`$, together with bounds on the score. We make the same positivity assumption but require only differentiability; the bounds are automatic for finite spaces. The thesis notes that positivity can be weakened to “$`\pi_\theta(a\mid s)`$ is either positive for all $`\theta`$ or zero for all $`\theta`$”; that extension is not formalized here. Positivity is also what yields Proposition [3.6](#prop:support).

- *Method of proof.* The thesis differentiates the Poisson (Bellman) equation after establishing differentiability of a family of solutions via regenerative representations. Here differentiability comes from Cramer’s rule (Lemma [5.2](#lem:cramer)), after which the argument of Theorem [6.2](#thm:gradV) is the same differentiation of the Bellman equation.

### 7.3 Next steps

The remaining steps towards the convergence of actor-critic algorithms are, in order: the average-reward counterpart of Theorem [6.3](#thm:pg) (Theorem 2.10 of the thesis), via the fundamental matrix of the chain; the projection characterization of the gradient and the bias bound of Lemma 5.3; an abstract result that $`\liminf_k \|\nabla J(\theta_k)\| \le \varepsilon`$ for gradient ascent with vanishing noise and bias at most $`\varepsilon`$; and linear stochastic approximation driven by slowly varying Markov chains (Chapter 3), which together yield the convergence theorem for actor-critic algorithms (Theorem 5.5).

# References

- V. R. Konda. *Actor-Critic Algorithms*. PhD thesis, Massachusetts Institute of Technology, 2002. <https://dspace.mit.edu/entities/publication/de41d9e3-f2ba-4327-bdaa-32014dd235ae>.

- S. Zhang. Towards formalizing reinforcement learning theory: a Robbins–Siegmund approach. *Reinforcement Learning Journal*, 2026. <https://arxiv.org/abs/2511.03618>.
