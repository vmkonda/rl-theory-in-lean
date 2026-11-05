# RL Theory in Lean

## Installation

See [https://lean-lang.org/install/](https://lean-lang.org/install/) for a detailed tutorial on setting up Lean.  
Confirm that Lean is set up by ```lake --version```.

```
git clone git@github.com:vmkonda/rl-theory-in-lean.git   # this fork; upstream: ShangtongZhang/rl-theory-in-lean
cd rl-theory-in-lean
lake exe cache get
lake build
```

It is recommended to use this project with the Lean 4 extension of VSCode. 

## Paper
[Towards Formalizing Reinforcement Learning Theory](https://arxiv.org/abs/2511.03618)  
```bibtex
@article{zhang2026towards,
    title={Towards Formalizing Reinforcement Learning Theory: A Robbins-Siegmund Approach},
    author={Shangtong Zhang},
    journal={Reinforcement Learning Journal},
    year={2026}
}
```

## Rates of convergence of actor-critic (this fork)

This fork extends the library toward the convergence-rate theory of actor-critic methods on finite
discounted MDPs: how fast actor-critic converges, for different critic features and trace parameters
λ in TD(λ), compared with actor-only (REINFORCE) methods. The mathematics is written up in
[`docs/`](docs/README.md) as theorem–proof chapters, each with LaTeX source and a GitHub-readable
Markdown version; every formalized statement there names its Lean counterpart. Everything below
builds with no `sorry` and depends only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

Main results, by chapter:

- **Policy gradients** ([policy-gradient.md](docs/policy-gradient.md))
  - [PolicyFamily.lean](RLTheory/MarkovDecisionProcess/PolicyFamily.lean), [PolicyGradient.lean](RLTheory/MarkovDecisionProcess/PolicyGradient.lean) — **`PolicyFamily.hasGradientAt_J`**: the discounted policy gradient theorem.
  - [PolicyGradientLipschitz.lean](RLTheory/MarkovDecisionProcess/PolicyGradientLipschitz.lean) — **`PolicyFamily.Regular.isLip_gradJ`**: the gradient is Lipschitz; **`softmaxFamily_regular`**.
  - [GradientAscent.lean](RLTheory/StochasticApproximation/GradientAscent.lean) — **`frequently_norm_grad_lt_of_tendsto_bias`**: pathwise convergence of biased gradient ascent.
- **Asymptotic covariance of linear SA with Markov noise** ([markov-sa-covariance.md](docs/markov-sa-covariance.md))
  - [CovarianceRecursion.lean](RLTheory/StochasticApproximation/CovarianceRecursion.lean), [MarkovNoiseCovariance.lean](RLTheory/StochasticApproximation/MarkovNoiseCovariance.lean) — **`tendsto_secondMoment_of_markov_noise`**: `β_k⁻¹ E[θ_k θ_kᵀ]` converges to the solution of the Lyapunov equation.
  - [PoissonNoise.lean](RLTheory/StochasticApproximation/PoissonNoise.lean), [TraceMoments.lean](RLTheory/StochasticApproximation/TraceMoments.lean) — finite-chain and trace-driven noise (**`tendsto_secondMoment_of_trace_noise_stationary`**).
  - [MultiplicativeNoiseCovariance.lean](RLTheory/StochasticApproximation/MultiplicativeNoiseCovariance.lean) — multiplicative Markov noise.
- **Two-time-scale SA** ([two-time-scale-covariance.md](docs/two-time-scale-covariance.md))
  - [TwoTimeScaleRecursion.lean](RLTheory/StochasticApproximation/TwoTimeScaleRecursion.lean), [TwoTimeScaleCovariance.lean](RLTheory/StochasticApproximation/TwoTimeScaleCovariance.lean) — **`tendsto_two_time_scale_covariance`**, **`tendsto_tts_perturbed`**.
  - [TwoTimeScaleMultiplicative.lean](RLTheory/StochasticApproximation/TwoTimeScaleMultiplicative.lean), [TwoTimeScaleTrace.lean](RLTheory/StochasticApproximation/TwoTimeScaleTrace.lean) — multiplicative and trace-driven noise.
- **Actor-critic versus actor-only** ([actor-critic-rates.md](docs/actor-critic-rates.md))
  - Linearization (Assumption 2.2 from the nonlinear iteration):
    - [Linearization.lean](RLTheory/StochasticApproximation/Linearization.lean) — **`hasFDerivAt_implicit`** (Lemma 2.1), **`tendsto_secondMoment_of_dissipative_markov`**.
    - [TwoTimeScaleNonlinear.lean](RLTheory/StochasticApproximation/TwoTimeScaleNonlinear.lean), [TwoTimeScaleMoments.lean](RLTheory/StochasticApproximation/TwoTimeScaleMoments.lean), [TwoTimeScaleMarkov.lean](RLTheory/StochasticApproximation/TwoTimeScaleMarkov.lean) — **`tendsto_tts_taylor`**, fourth-moment bounds **`moment_bounds_tts_markov`**, **`tendsto_tts_dissipative_markov`**.
  - θ-dependent sampling:
    - [ParamMarkovNoise.lean](RLTheory/StochasticApproximation/ParamMarkovNoise.lean) — the noise decomposition with a lagged parameter.
    - [DoeblinPoisson.lean](RLTheory/StochasticApproximation/DoeblinPoisson.lean) — Lipschitz Poisson pairs for Doeblin chains.
    - [DoeblinCovariance.lean](RLTheory/StochasticApproximation/DoeblinCovariance.lean) — law and covariance convergence under a moving kernel, **`tendsto_secondMoment_of_doeblin_chain_auto`**.
    - [TwoTimeScaleParam.lean](RLTheory/StochasticApproximation/TwoTimeScaleParam.lean) — the two-time-scale version, **`tendsto_tts_param_chain_doeblin`**.
  - The loss in expected reward: [RateComparison.lean](RLTheory/StochasticApproximation/RateComparison.lean) — **`tendsto_quadLoss`**, **`optLoss_mono`** (comparison principle).
  - Critics:
    - [CriticTheorems.lean](RLTheory/MarkovDecisionProcess/CriticTheorems.lean) — TD(1), compatible and value-function critics, and the gains of the tabular TD(0) and TD(λ) critics (**`ScoreChain.td0_gain`**, **`ScoreChain.tdlam_gain`**).
    - [OrthogonalNoise.lean](RLTheory/StochasticApproximation/OrthogonalNoise.lean), [RestartProcess.lean](RLTheory/MarkovDecisionProcess/RestartProcess.lean) — the martingale step: the restart chain is state-driven before the action, and orthogonal noises add their covariances.
    - [LookbackMonotone.lean](RLTheory/StochasticApproximation/LookbackMonotone.lean) — the centered critic trace and Loewner monotonicity of its covariance in λ.
    - [LambdaMonotone.lean](RLTheory/MarkovDecisionProcess/LambdaMonotone.lean) — **`ScoreChain.restart_actor_loss_mono`**: Theorem 4.7, shorter traces give a smaller actor covariance and loss, end to end for the restart chain. TD(0) is the best tabular critic, and TD(1) (REINFORCE) the worst.

Not formalized: replacing global dissipativity by a localization argument, existence of Poisson
solutions for general irreducible chains, and the numerical observations in
[`experiments/`](experiments/README.md).

## Main Results 

> This project is organized by mirroring the structure of Mathlib so the counterparts can be upstreamed to Mathlib easily. Below are some main results.

- Algorithm
  - [LinearTD.lean](RLTheory/Algorithm/LinearTD.lean)
    - **`[LinearTDIterates]`** - linear TD algorithm.
    - **`[DecreaseAlong]`** - $\ell_2$ norm qualifies a Lyapunov function for linear TD.
    - **`ae_tendsto_of_linearTD_iid`** — almost sure convergence of linear TD with i.i.d. samples.
    - **`ae_tendsto_of_linearTD_markov`** — almost sure convergence of linear TD with Markovian samples.
  - [QLearning.lean](RLTheory/Algorithm/QLearning.lean)
    - **`[QLearningIterates]`** — Q-learning algorithm.
    - **`[DecreaseAlong]`** - $\ell_p$ norm with a sufficiently large $p$ qualifies a Lyapunov function for Q-learning.
    - **`ae_tendsto_of_QLearning_iid`** — almost sure convergence of Q-learning with i.i.d. samples.
    - **`ae_tendsto_of_QLearning_markov`** — almost sure convergence of Q-learning with Markovian samples.
- StochasticApproximation
  - [Iterates.lean](RLTheory/StochasticApproximation/Iterates.lean) - stochastic approximation (SA) iterates and non-uniform bounds.
    - **`[Iterates]`** — a general form of SA iterates with Martingale difference noise and additional noise.
    - **`[IteratesOfResidual]`** — a specific form of SA iterates driven by residual of an operator.
    - **`[AdaptedOnSamplePath]`** — SA iterates are  completely determined by available information until current time step on every sample path.
  - [CondExp.lean](RLTheory/StochasticApproximation/CondExp.lean) 
    - **`condExp_iterates_update`** — computes the conditional expectation of SA iterates in the Ionescu-Tulcea probability space.
  - [Lyapunov.lean](RLTheory/StochasticApproximation/Lyapunov.lean) 
    - **`[LyapunovFunction]`** — desired properties for a function to be used as a Lyapunov function to analyze SA iterates.
  - [LpSpace.lean](RLTheory/StochasticApproximation/LpSpace.lean) - squared $\ell_p$ norm qualifies a Lyapunov function 
    - **`smooth_half_sq_Lp`** — squared $\ell_p$ norm is $p - 1$ smooth.
  - [Pathwise.lean](RLTheory/StochasticApproximation/Pathwise.lean) 
    - **`fundamental_inequality`** — recursive bounds of errors based on a Lyapunov function on an individual sample path.
  - [DiscreteGronwall.lean](RLTheory/StochasticApproximation/DiscreteGronwall.lean) — discrete Gronwall inequalities.
  - [MartingaleDifference.lean](RLTheory/StochasticApproximation/MartingaleDifference.lean)
    - **`ae_tendsto_of_iterates_mds_noise`** — convergence of SA iterates with Martingale difference noise.
  - [IIDSamples.lean](RLTheory/StochasticApproximation/IIDSamples.lean) 
    - **`ae_tendsto_of_iterates_iid_samples`** — convergence of SA iterates with i.i.d. samples.
  - [StepSize.lean](RLTheory/StochasticApproximation/StepSize.lean) 
    - **`anchors_of_inv_poly`** — inverse polynomial step size qualifies the [skeleton iterates](https://arxiv.org/abs/2411.13711) technique that can convert Markov noise to Martingale difference noise.
  - [MarkovSamples.lean](RLTheory/StochasticApproximation/MarkovSamples.lean)
    - **`ae_tendsto_of_iterates_markov_samples`** — convergence of SA iterates with Markovian samples.
    - **`ae_tendsto_of_iterates_markov_samples_of_inv_poly`** — specializes to inverse polynomial step size schedules.
- Data
  - [Int/GCD.lean](RLTheory/Data/Int/GCD.lean) 
    - **`all_but_finite_of_closed_under_add_and_gcd_one`** — if a set has gcd 1 and is close under addition, it then contains all large enough integers.
  - [Matrix/PosDef.lean](RLTheory/Data/Matrix/PosDef.lean) — positive definiteness (p.d.) for asymmetric real matrices.
    - **`posDefAsymm_iff'`** — a lower bound for the quadratic form of a p.d. matrix.
  - [Matrix/Stochastic.lean](RLTheory/Data/Matrix/Stochastic.lean) — stochastic vectors and row stochastic matrices.
    - **`smat_minorizable_with_large_pow`** — an irreducible and aperiodic stochastic matrix is Doeblin minorizable after sufficient powers.
    - **`smat_contraction_in_simplex`** - Doeblin minorization implies contraction in simplex 
    - **`stationary_distribution_exists`** - produces one stationary distribution via Cesaro limit.
    - **`stationary_distribution_uniquely_exists`** — stationary distribution uniquely exists under irreducibility and aperiodicity.
    - **`[GeometricMixing]`** - geometric mixing under irreducibility and aperiodicity.
- Probability
  - [MarkovChain/Defs.lean](RLTheory/Probability/MarkovChain/Defs.lean) — basics of time homogeneous Markov chains.
  - [MarkovChain/Finite/Defs.lean](RLTheory/Probability/MarkovChain/Finite/Defs.lean) — matrix representation of finite Markov chains 
  - [MarkovChain/Trajectory.lean](RLTheory/Probability/MarkovChain/Trajectory.lean) 
    - **`traj_prob`** — constructs the sample path space probability measure for Markov chains by the Ionescu-Tulcea theorem.
  - [Martingale/Convergence.lean](RLTheory/Probability/Martingale/Convergence.lean) 
    - **`ae_tendsto_zero_of_almost_supermartingale`** — Robbins-Siegmund theorem for the convergence of almost supermartingales.
- MarkovDecisionProcess
  - [MarkovRewardProcess.lean](RLTheory/MarkovDecisionProcess/MarkovRewardProcess.lean) — basics of finite MRPs.
    - **`[NegDefAsymm MRP.K]`** — negative definiteness of the matrix $D(\gamma P - I)$ 
  - [MarkovDecisionProcess.lean](RLTheory/MarkovDecisionProcess/MarkovDecisionProcess.lean) — basics of finite MDPs.
