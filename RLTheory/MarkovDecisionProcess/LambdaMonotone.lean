/-
SPDX-License-Identifier: MIT
-/
import RLTheory.MarkovDecisionProcess.CriticTheorems
import RLTheory.MarkovDecisionProcess.RestartProcess
import RLTheory.StochasticApproximation.LookbackMonotone

/-!
# Theorem 4.7 for the restart chain

Shorter traces give a smaller actor-critic noise, from the model alone. The sampling chain is
described twice, by the same process:
* `TwoStageChain`: given the history before the action, the action is drawn from the policy, and
  then the next flag and state from `kap`. This gives the conditional law of the next observation
  given the pre-action filtration (`TwoStageChain.stateDriven`).
* `FiniteMarkov` for the pairs `Y_k = (f_k, s_k, a_k)`: this gives the convergence of the law to
  a stationary `ν` (`tendsto_law_restart`).

The critic runs the tabular TD(`λ`) traces `z^ψ`, `z^e`, started at `z^ψ_0 = ψ_0`,
`z^e_0 = e_{s_0}`. With `b` the stationary conditional mean of the REINFORCE carried trace
(`carryMean`), the centered critic trace is
`W_k = (z^ψ_k - ψ_k) + (1 - λ) Σ_t z^e_k(t) b(t) - b(s_k)`, and the TD(`λ`) noise is the TD(0)
noise plus `δ W_k` (`tdlam_noise_split`, with the gain of `tdlam_gain`).

* `restart_centered_trace`: `W` steps by `W' = λ (ε' + c' W)`, is known before the action, and
  is bounded.
* `restart_lambda_covariance_mono`: for `0 ≤ λ₁ ≤ λ₂ ≤ 1`, the extra covariances
  `Γ_D(λ) = lim E[δ² W Wᵀ]` exist and satisfy `0 ≼ Γ_D(λ₁) ≼ Γ_D(λ₂)`.
-/

open Finset Real Filter Topology MeasureTheory RLTheory Matrix

namespace StochasticApproximation

namespace ScoreChain

variable {S Ac : Type*} [Fintype S] [Fintype Ac] [DecidableEq S] [DecidableEq Ac]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace Ac] [DiscreteMeasurableSpace Ac]
  (M : ScoreChain S Ac)

/-- The centered critic trace `W_k = (z^ψ_k - ψ_k) + (1 - λ) Σ_t z^e_k(t) b(t) - b(s_k)`. -/
noncomputable def centeredTrace {Ω : Type*} {n : ℕ} (lam : ℝ) (ψ : S → Ac → E n) (b : S → E n)
    (zψ : ℕ → Ω → E n) (ze : ℕ → Ω → S → ℝ) (fs : ℕ → Ω → Bool × S) (a : ℕ → Ω → Ac) (k : ℕ)
    (ω : Ω) : E n :=
  ((zψ k ω - ψ (fs k ω).2 (a k ω)) + (1 - lam) • ∑ t, ze k ω t • b t) - b (fs k ω).2

/-- The first lookback increment `ε(s₀, a, f', s') = c(f', s') (ψ(s₀, a) + b(s₀)) - b(s')`. -/
noncomputable def lookbackInc {n : ℕ} (ψ : S → Ac → E n) (b : S → E n) (x : S × Ac × (Bool × S)) : E n :=
  M.c x.2.2.1 x.2.2.2 • (ψ x.1 x.2.1 + b x.1) - b x.2.2.2

section Process

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq Ac] [IsProbabilityMeasure μ] in
set_option maxHeartbeats 4000000 in
/-- **The centered critic trace along the restart chain.** If the TD(`λ`) traces step by
`z^ψ_{k+1} = ψ_{k+1} + λ c_{k+1} z^ψ_k` and `z^e_{k+1} = e_{s_{k+1}} + λ c_{k+1} z^e_k` from
`z^ψ_0 = ψ_0`, `z^e_0 = e_{s_0}`, with `0 ≤ λ c ≤ 1`, then the centered trace `W` steps by
`W_{k+1} = λ (ε(ξ_{k+1}) + c(ξ_{k+1}) W_k)`, is known before the action `a_k`, and is bounded. -/
theorem restart_centered_trace {𝒢 ℋ : MeasureTheory.Filtration ℕ m0} {fs : ℕ → Ω → Bool × S}
    {a : ℕ → Ω → Ac} (hc : TwoStageChain μ 𝒢 ℋ fs a M.pol M.kap)
    (hc0 : ∀ s, M.c true s = 0) (hcf0 : ∀ s, 0 ≤ M.c false s) (hcf1 : ∀ s, M.c false s ≤ 1)
    {n : ℕ} (ψ : S → Ac → E n) (b : S → E n) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    {zψ : ℕ → Ω → E n} {ze : ℕ → Ω → S → ℝ}
    (hz0 : ∀ ω, zψ 0 ω = ψ (fs 0 ω).2 (a 0 ω))
    (hze0 : ∀ ω t, ze 0 ω t = if (fs 0 ω).2 = t then 1 else 0)
    (hzψ : ∀ k ω, zψ (k + 1) ω = ψ (fs (k + 1) ω).2 (a (k + 1) ω)
      + (lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) • zψ k ω)
    (hze : ∀ k ω t, ze (k + 1) ω t = (if (fs (k + 1) ω).2 = t then 1 else 0)
      + lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 * ze k ω t) :
    (∀ k ω, centeredTrace lam ψ b zψ ze fs a (k + 1) ω =
      lam • (M.lookbackInc ψ b ((fs k ω).2, a k ω, fs (k + 1) ω)
        + M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 • centeredTrace lam ψ b zψ ze fs a k ω)) ∧
    (∀ k, StronglyMeasurable[𝒢 k] (centeredTrace lam ψ b zψ ze fs a k)) ∧
    (∀ k, ∃ C, ∀ ω, ‖centeredTrace lam ψ b zψ ze fs a k ω‖ ≤ C) := by
  -- the discount `λ c` is in `[0, 1]`
  have hcY : ∀ f s, 0 ≤ M.c f s ∧ M.c f s ≤ 1 := fun f s => by
    cases f
    · exact ⟨hcf0 s, hcf1 s⟩
    · rw [hc0 s]; exact ⟨le_rfl, zero_le_one⟩
  have hlc : ∀ f s, |lam * M.c f s| ≤ 1 := fun f s => by
    rw [abs_of_nonneg (mul_nonneg hl0 (hcY f s).1)]
    nlinarith [(hcY f s).1, (hcY f s).2]
  -- measurability of functions of the flag, state and action
  have hfsm : ∀ k, Measurable[𝒢 k] (fs k) := hc.meas_fs
  have hpairm : ∀ k, Measurable[ℋ k] (fun ω => ((fs k ω).2, a k ω)) := fun k =>
    ((measurable_snd.comp (hfsm k)).mono (hc.le₁ k) le_rfl).prodMk (hc.meas_a k)
  have hψm : ∀ k, StronglyMeasurable[ℋ k] (fun ω => ψ (fs k ω).2 (a k ω)) := fun k =>
    (StronglyMeasurable.of_discrete (f := fun p : S × Ac => ψ p.1 p.2)).comp_measurable (hpairm k)
  have hcm : ∀ k, StronglyMeasurable[𝒢 k] (fun ω => M.c (fs k ω).1 (fs k ω).2) := fun k =>
    (StronglyMeasurable.of_discrete (f := fun p : Bool × S => M.c p.1 p.2)).comp_measurable (hfsm k)
  have hbm : ∀ k, StronglyMeasurable[𝒢 k] (fun ω => b (fs k ω).2) := fun k =>
    (StronglyMeasurable.of_discrete (f := b)).comp_measurable (measurable_snd.comp (hfsm k))
  have hindm : ∀ k t, StronglyMeasurable[𝒢 k] (fun ω => if (fs k ω).2 = t then (1 : ℝ) else 0) :=
    fun k t => (StronglyMeasurable.of_discrete
      (f := fun s : S => if s = t then (1 : ℝ) else 0)).comp_measurable (measurable_snd.comp (hfsm k))
  -- the traces
  have hzm : ∀ k, StronglyMeasurable[ℋ k] (zψ k) := by
    intro k
    induction k with
    | zero =>
      rw [show zψ 0 = fun ω => ψ (fs 0 ω).2 (a 0 ω) from funext hz0]
      exact hψm 0
    | succ k ih =>
      rw [show zψ (k + 1) = fun ω => ψ (fs (k + 1) ω).2 (a (k + 1) ω)
        + (lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) • zψ k ω from funext (hzψ k)]
      have := (hψm (k + 1)).add ((((hcm (k + 1)).mono (hc.le₁ (k + 1))).const_mul lam).smul
        (ih.mono ((hc.le₂ k).trans (hc.le₁ (k + 1)))))
      exact this
  have hzem : ∀ k t, StronglyMeasurable[𝒢 k] (fun ω => ze k ω t) := by
    intro k
    induction k with
    | zero =>
      intro t
      rw [show (fun ω => ze 0 ω t) = fun ω => if (fs 0 ω).2 = t then (1 : ℝ) else 0 from
        funext fun ω => hze0 ω t]
      exact hindm 0 t
    | succ k ih =>
      intro t
      rw [show (fun ω => ze (k + 1) ω t) = fun ω => (if (fs (k + 1) ω).2 = t then (1 : ℝ) else 0)
        + lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 * ze k ω t from funext fun ω => hze k ω t]
      have := (hindm (k + 1) t).add (((hcm (k + 1)).const_mul lam).mul
        ((ih t).mono (𝒢.mono (Nat.le_succ k))))
      exact this
  set Cψ := ∑ s, ∑ a, ‖ψ s a‖ with hCψ
  have hψb : ∀ s a', ‖ψ s a'‖ ≤ Cψ := fun s a' =>
    (single_le_sum (f := fun a => ‖ψ s a‖) (fun _ _ => norm_nonneg _) (mem_univ a')).trans
      (single_le_sum (f := fun s => ∑ a, ‖ψ s a‖) (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)
        (mem_univ s))
  have hCψ0 : 0 ≤ Cψ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have hzb : ∀ k ω, ‖zψ k ω‖ ≤ (k + 1) * Cψ := by
    intro k
    induction k with
    | zero => intro ω; rw [hz0]; simpa using hψb _ _
    | succ k ih =>
      intro ω
      rw [hzψ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      have h1 := mul_le_mul (hlc (fs (k + 1) ω).1 (fs (k + 1) ω).2) (ih ω) (norm_nonneg _)
        zero_le_one
      have h2 := hψb (fs (k + 1) ω).2 (a (k + 1) ω)
      push_cast
      linarith
  have hzeb : ∀ k ω t, |ze k ω t| ≤ k + 1 := by
    intro k
    induction k with
    | zero => intro ω t; rw [hze0]; split_ifs <;> simp
    | succ k ih =>
      intro ω t
      rw [hze]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have h1 := mul_le_mul (hlc (fs (k + 1) ω).1 (fs (k + 1) ω).2) (ih ω t) (abs_nonneg _)
        zero_le_one
      have h2 : |(if (fs (k + 1) ω).2 = t then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      push_cast
      linarith
  refine ⟨fun k ω => ?_, fun k => ?_, fun k => ?_⟩
  · -- the recursion
    simp only [centeredTrace, lookbackInc]
    exact centered_trace_step lam (M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) (zψ k ω) (zψ (k + 1) ω)
      (ψ (fs k ω).2 (a k ω)) (ψ (fs (k + 1) ω).2 (a (k + 1) ω)) (ze k ω) (ze (k + 1) ω) b
      (fs k ω).2 (fs (k + 1) ω).2 (hzψ k ω) (hze k ω)
  · -- known before the action
    have hR : StronglyMeasurable[𝒢 k] (fun ω => zψ k ω - ψ (fs k ω).2 (a k ω)) := by
      cases k with
      | zero =>
        rw [show (fun ω => zψ 0 ω - ψ (fs 0 ω).2 (a 0 ω)) = fun _ => 0 from
          funext fun ω => by rw [hz0, sub_self]]
        exact stronglyMeasurable_const
      | succ k =>
        rw [show (fun ω => zψ (k + 1) ω - ψ (fs (k + 1) ω).2 (a (k + 1) ω)) = fun ω =>
          (lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) • zψ k ω from
            funext fun ω => by rw [hzψ]; abel]
        have := ((hcm (k + 1)).const_mul lam).smul ((hzm k).mono (hc.le₂ k))
        exact this
    have hS : StronglyMeasurable[𝒢 k] (fun ω => ∑ t, ze k ω t • b t) :=
      Finset.stronglyMeasurable_sum _ fun t _ => (hzem k t).smul_const (b t)
    have := ((hR.add (hS.const_smul (1 - lam))).sub (hbm k))
    exact this
  · -- bounded
    set Cb := ∑ t, ‖b t‖ with hCb
    have hbb : ∀ t, ‖b t‖ ≤ Cb := fun t =>
      single_le_sum (f := fun t => ‖b t‖) (fun _ _ => norm_nonneg _) (mem_univ t)
    refine ⟨(k + 1) * Cψ + Cψ + |1 - lam| * ((k + 1) * Cb) + Cb, fun ω => ?_⟩
    have hsum : ‖∑ t, ze k ω t • b t‖ ≤ (k + 1) * Cb := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ t, ‖ze k ω t • b t‖ = ∑ t, |ze k ω t| * ‖b t‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ t, (k + 1) * ‖b t‖ := sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_right (hzeb k ω t) (norm_nonneg _)
        _ = (k + 1) * Cb := by rw [← mul_sum]
    simp only [centeredTrace]
    have t1 := norm_sub_le (zψ k ω) (ψ (fs k ω).2 (a k ω))
    have t2 := norm_add_le (zψ k ω - ψ (fs k ω).2 (a k ω)) ((1 - lam) • ∑ t, ze k ω t • b t)
    have t3 := norm_sub_le ((zψ k ω - ψ (fs k ω).2 (a k ω)) + (1 - lam) • ∑ t, ze k ω t • b t)
      (b (fs k ω).2)
    have t4 : ‖(1 - lam) • ∑ t, ze k ω t • b t‖ ≤ |1 - lam| * ((k + 1) * Cb) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    have := hzb k ω
    have := hψb (fs k ω).2 (a k ω)
    have := hbb (fs k ω).2
    linarith

omit [DecidableEq S] [DecidableEq Ac] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Ac] [DiscreteMeasurableSpace Ac] [IsProbabilityMeasure μ] in
/-- **The REINFORCE trace moments exist.** For a restart chain the `TraceMoment` recursion with
`λ = 1` has a solution, for any law `ν`. -/
theorem exists_traceMoment_restart (hkap : ∀ y f s, 0 ≤ M.kap y f s)
    (hpol0 : ∀ s a, 0 ≤ M.pol s a) (hpol : ∀ s, ∑ a, M.pol s a = 1) (hc0 : ∀ s, M.c true s = 0)
    (hc1 : ∀ s, |M.c false s| ≤ 1) {γ : ℝ} (hγ1 : γ < 1)
    (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) (ν : Bool × S × Ac → ℝ) {p : ℕ}
    (φ : Bool × S × Ac → E p) : ∃ m, M.TraceMoment ν 1 φ m := by
  have hρ := M.restart_contraction hkap hpol hc0 hc1 hγ 1
  have hρ1 : |(1 : ℝ)| * γ < 1 := by rw [abs_one, one_mul]; exact hγ1
  have h1 : ∀ a, ∃ xl : Bool × S × Ac → ℝ,
      ∀ y', xl y' = transfer M.Q (fun y => 1 * M.cY y) xl y' + φ y' a * ν y' := fun a =>
    exists_transfer_fixed (M.Q_nonneg hkap hpol0) hρ hρ1 _
  choose m₁ hm₁ using h1
  refine ⟨fun y => (fun a => m₁ a y : E p), fun y' => ?_⟩
  ext a
  show m₁ a y' = _
  rw [hm₁ a y']
  simp only [transfer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, euclid_sum_apply']
  rw [mul_sum]
  ring_nf

omit [DecidableEq S] [DecidableEq Ac] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Ac] [DiscreteMeasurableSpace Ac] [IsProbabilityMeasure μ] in
/-- **Every state is visited.** If restarts reach every state, the stationary state law is
positive. -/
theorem stateSum_ne_zero_restart {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    (hν0 : ∀ y, 0 ≤ ν y) (hνm : ∑ y, ν y = 1) (hpol : ∀ s, ∑ a, M.pol s a = 1)
    (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s) (hpos : ∀ y s, 0 < M.kap y true s)
    (s : S) : stateSum ν s ≠ 0 := by
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ)
    (show ∑ a, M.pol s a ≠ 0 by rw [hpol]; exact one_ne_zero)
  have hrow : ∀ a, ν (true, s, a) = M.kap (true, s, a₀) true s * M.pol s a := fun a => by
    rw [← hν (true, s, a)]
    simp only [Q]
    rw [show ∑ y, ν y * (M.kap y true s * M.pol s a) =
      ∑ y, ν y * (M.kap (true, s, a₀) true s * M.pol s a) from
        sum_congr rfl fun y _ => by rw [hrest y (true, s, a₀) s], ← sum_mul, hνm, one_mul]
  have h1 : ∑ a, ν (true, s, a) ≤ stateSum ν s := by
    unfold stateSum
    rw [Fintype.sum_bool]
    have : 0 ≤ ∑ a, ν (false, s, a) := sum_nonneg fun a _ => hν0 _
    linarith
  have h2 : ∑ a, ν (true, s, a) = M.kap (true, s, a₀) true s := by
    rw [sum_congr rfl fun a _ => hrow a, ← mul_sum, hpol, mul_one]
  have := hpos (true, s, a₀) s
  linarith

/-- The law of the state converges to the state marginal of `ν`. -/
theorem tendsto_stateLaw {ℱ : MeasureTheory.Filtration ℕ m0} {fs : ℕ → Ω → Bool × S}
    {a : ℕ → Ω → Ac}
    (hY : FiniteMarkov μ ℱ (fun k ω => ((fs k ω).1, (fs k ω).2, a k ω)) M.Q)
    {ν : Bool × S × Ac → ℝ}
    (hlaw : ∀ y, Tendsto (fun k => momAt μ (fun k ω => ((fs k ω).1, (fs k ω).2, a k ω))
      (fun _ _ => 1) k y) atTop (𝓝 (ν y))) (s : S) :
    Tendsto (fun k => ∫ ω, {ω | (fs k ω).2 = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ) atTop
      (𝓝 (stateSum ν s)) := by
  set Y : ℕ → Ω → Bool × S × Ac := fun k ω => ((fs k ω).1, (fs k ω).2, a k ω) with hYd
  have hint : ∀ k y, Integrable ({ω | Y k ω = y}.indicator fun _ => (1 : ℝ)) μ := fun k y =>
    (integrable_const (1 : ℝ)).indicator (ℱ.le k _ (hY.measurableSet_eq k y))
  have e : ∀ k, ∫ ω, {ω | (fs k ω).2 = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ =
      ∑ f, ∑ a', momAt μ Y (fun _ _ => 1) k (f, s, a') := fun k => by
    simp only [momAt]
    calc ∫ ω, {ω | (fs k ω).2 = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ
        = ∫ ω, ∑ f, ∑ a', {ω | Y k ω = (f, s, a')}.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [Set.indicator_apply, Set.mem_setOf_eq, hYd, Prod.mk.injEq]
          by_cases h : (fs k ω).2 = s
          · rw [if_pos h, Finset.sum_eq_single (fs k ω).1 (fun f _ hf => by simp [Ne.symm hf])
              (by simp), Finset.sum_eq_single (a k ω) (fun a' _ ha => by simp [Ne.symm ha])
              (by simp)]
            simp [h]
          · simp [h]
      _ = ∑ f, ∫ ω, ∑ a', {ω | Y k ω = (f, s, a')}.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
          integral_finset_sum _ fun f _ => integrable_finset_sum _ fun a' _ => hint k (f, s, a')
      _ = _ := sum_congr rfl fun f _ => integral_finset_sum _ fun a' _ => hint k (f, s, a')
  simp only [e]
  unfold stateSum
  exact tendsto_finset_sum _ fun f _ => tendsto_finset_sum _ fun a' _ => hlaw (f, s, a')


omit [DecidableEq Ac] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace Ac]
  [DiscreteMeasurableSpace Ac] [IsProbabilityMeasure μ] in
/-- Sums against the pre-action kernel `P(s, (s₀, a, f', s')) = 1{s₀ = s} π(a | s) κ((·, s, a), f', s')`. -/
lemma sum_preaction_kernel (s : S) (G : S × Ac × (Bool × S) → ℝ) :
    ∑ x, (if x.1 = s then 1 else 0) * (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2)
      * G x = ∑ a, ∑ f, ∑ s', M.pol s a * M.kap (false, s, a) f s' * G (s, a, (f, s')) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s (fun s₀ _ h => by simp [h]) (by simp)]
  simp

set_option maxHeartbeats 8000000 in
/-- **Theorem 4.7 for the restart chain: shorter traces give smaller noise.** Let the sampling
chain be the restart chain, described by its two stages (`TwoStageChain`) and as a Markov chain
on pairs (`FiniteMarkov`), with:
* restarts that reach every state and do not depend on the current pair;
* a continuation probability at most `γ < 1`;
* a trace discount `c` with `c(restart) = 0` and `0 ≤ c ≤ 1`;
* a step law that does not depend on the flag.

Let the critic run the tabular TD(`λ`) traces for `0 ≤ λ₁ ≤ λ₂ ≤ 1`. Then the law of the pairs
converges to a stationary `ν`, the REINFORCE trace moments `m_Z` exist, and with
`b = carryMean ν ψ m_Z` the extra noise covariances
`Γ_D(λ) = lim E[δ² W_λ W_λᵀ]` of the centered critic traces exist and satisfy
`0 ≼ Γ_D(λ₁) ≼ Γ_D(λ₂)`. With the gain `K_λ e_s = -(1 - λ) b(s)` of `tdlam_gain` and the noise
splitting `tdlam_noise_split`, this is the monotonicity of `Γ̃(λ) = Γ̃(0) + Γ_D(λ)`. -/
theorem restart_lambda_covariance_mono {𝒢 ℋ : MeasureTheory.Filtration ℕ m0}
    {fs : ℕ → Ω → Bool × S} {a : ℕ → Ω → Ac} (hc : TwoStageChain μ 𝒢 ℋ fs a M.pol M.kap)
    (hY : FiniteMarkov μ ℋ (fun k ω => ((fs k ω).1, (fs k ω).2, a k ω)) M.Q)
    (hkap0 : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    (hpos : ∀ y s, 0 < M.kap y true s)
    (hflag : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a))
    (hc0 : ∀ s, M.c true s = 0) (hcf0 : ∀ s, 0 ≤ M.c false s) (hcf1 : ∀ s, M.c false s ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ)
    {n : ℕ} (ψ : S → Ac → E n) (δ : S × Ac × (Bool × S) → ℝ)
    {l₁ l₂ : ℝ} (hl0 : 0 ≤ l₁) (hl12 : l₁ ≤ l₂) (hl2 : l₂ ≤ 1)
    {zψ₁ zψ₂ : ℕ → Ω → E n} {ze₁ ze₂ : ℕ → Ω → S → ℝ}
    (hz0₁ : ∀ ω, zψ₁ 0 ω = ψ (fs 0 ω).2 (a 0 ω))
    (hze0₁ : ∀ ω t, ze₁ 0 ω t = if (fs 0 ω).2 = t then 1 else 0)
    (hzψ₁ : ∀ k ω, zψ₁ (k + 1) ω = ψ (fs (k + 1) ω).2 (a (k + 1) ω)
      + (l₁ * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) • zψ₁ k ω)
    (hze₁ : ∀ k ω t, ze₁ (k + 1) ω t = (if (fs (k + 1) ω).2 = t then 1 else 0)
      + l₁ * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 * ze₁ k ω t)
    (hz0₂ : ∀ ω, zψ₂ 0 ω = ψ (fs 0 ω).2 (a 0 ω))
    (hze0₂ : ∀ ω t, ze₂ 0 ω t = if (fs 0 ω).2 = t then 1 else 0)
    (hzψ₂ : ∀ k ω, zψ₂ (k + 1) ω = ψ (fs (k + 1) ω).2 (a (k + 1) ω)
      + (l₂ * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) • zψ₂ k ω)
    (hze₂ : ∀ k ω t, ze₂ (k + 1) ω t = (if (fs (k + 1) ω).2 = t then 1 else 0)
      + l₂ * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 * ze₂ k ω t) :
    ∃ ν : Bool × S × Ac → ℝ, (∀ y', ∑ y, ν y * M.Q y y' = ν y') ∧ ∑ y, ν y = 1 ∧
      ∃ mZ : Bool × S × Ac → E n, M.TraceMoment ν 1 (fun y => ψ y.2.1 y.2.2) mZ ∧
      ∃ Γ₁ Γ₂ : Mat n,
        Tendsto (fun k => secondMoment μ fun ω => δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
          centeredTrace l₁ ψ (carryMean ν (fun y => ψ y.2.1 y.2.2) mZ) zψ₁ ze₁ fs a k ω) atTop
          (𝓝 Γ₁) ∧
        Tendsto (fun k => secondMoment μ fun ω => δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
          centeredTrace l₂ ψ (carryMean ν (fun y => ψ y.2.1 y.2.2) mZ) zψ₂ ze₂ fs a k ω) atTop
          (𝓝 Γ₂) ∧
        ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * Γ₁ (i, j) ∧
          ∑ i, ∑ j, v i * v j * Γ₁ (i, j) ≤ ∑ i, ∑ j, v i * v j * Γ₂ (i, j) := by
  obtain ⟨ν, hν, hνm, hlaw⟩ := M.tendsto_law_restart hY hkap0 hpol0 hpol hrest hγ0 hγ1 hγ
  have hν0 : ∀ y, 0 ≤ ν y := fun y => ge_of_tendsto' (hlaw y) fun k =>
    integral_nonneg fun ω => by simp only [Set.indicator_apply]; split_ifs <;> norm_num
  have hc1 : ∀ s, |M.c false s| ≤ 1 := fun s => by rw [abs_of_nonneg (hcf0 s)]; exact hcf1 s
  set ψY : Bool × S × Ac → E n := fun y => ψ y.2.1 y.2.2 with hψY
  obtain ⟨mZ, hmZ⟩ := M.exists_traceMoment_restart hkap0 hpol0 hpol hc0 hc1 hγ1 hγ ν ψY
  have hνS := M.stateSum_ne_zero_restart hν hν0 hνm hpol hrest hpos
  set b := carryMean ν ψY mZ with hb
  have hσ := hc.stateDriven hflag
  have hcY : ∀ f s, 0 ≤ M.c f s ∧ M.c f s ≤ 1 := fun f s => by
    cases f
    · exact ⟨hcf0 s, hcf1 s⟩
    · rw [hc0 s]; exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨hW₁r, hW₁m, hW₁B⟩ := M.restart_centered_trace hc hc0 hcf0 hcf1 ψ b hl0
    (hl12.trans hl2) hz0₁ hze0₁ hzψ₁ hze₁
  obtain ⟨hW₂r, hW₂m, hW₂B⟩ := M.restart_centered_trace hc hc0 hcf0 hcf1 ψ b (hl0.trans hl12)
    hl2 hz0₂ hze0₂ hzψ₂ hze₂
  -- the kernel
  have hP0 : ∀ s (x : S × Ac × (Bool × S)), 0 ≤ (if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2) := fun s x =>
    mul_nonneg (by split_ifs <;> norm_num) (mul_nonneg (hpol0 _ _) (hkap0 _ _ _))
  have hρ : ∀ s, ∑ x : S × Ac × (Bool × S), (if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2) * M.c x.2.2.1 x.2.2.2 ≤ γ :=
    fun s => by
      rw [M.sum_preaction_kernel s (fun x => M.c x.2.2.1 x.2.2.2)]
      calc ∑ a', ∑ f, ∑ s', M.pol s a' * M.kap (false, s, a') f s' * M.c f s'
          = ∑ a', M.pol s a' * ∑ s', M.kap (false, s, a') false s' * M.c false s' := by
            refine sum_congr rfl fun a' _ => ?_
            rw [Fintype.sum_bool]
            simp only [hc0, mul_zero, sum_const_zero, zero_add, mul_sum]
            exact sum_congr rfl fun s' _ => by ring
        _ ≤ ∑ a', M.pol s a' * γ := sum_le_sum fun a' _ => mul_le_mul_of_nonneg_left
            ((sum_le_sum fun s' _ => mul_le_of_le_one_right (hkap0 _ _ _) (hcf1 s')).trans
              (hγ _)) (hpol0 _ _)
        _ = γ := by rw [← sum_mul, hpol, one_mul]
  -- the centering
  have hcent : ∀ s j, ∑ s', stateSum ν s' * ∑ x : S × Ac × (Bool × S),
      (if x.1 = s' then 1 else 0) * (M.pol s' x.2.1 * M.kap (false, s', x.2.1) x.2.2.1 x.2.2.2) *
        ((if x.2.2.2 = s then 1 else 0) * M.lookbackInc ψ b x j) = 0 := fun s j => by
    have h := congrArg (fun v : E n => v j)
      (M.carryMean_step_centered hν hmZ hpol hνS hflag (fun _ _ _ _ => rfl) s)
    simp only [euclid_sum_apply', PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h
    refine Eq.trans ?_ h
    refine sum_congr rfl fun s' _ => ?_
    rw [M.sum_preaction_kernel s' (fun x => (if x.2.2.2 = s then 1 else 0) * M.lookbackInc ψ b x j),
      mul_sum]
    refine sum_congr rfl fun a' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun f _ => ?_
    rw [Finset.sum_eq_single s (fun s'' _ h => by simp [h]) (by simp)]
    simp only [if_true, one_mul, lookbackInc, hψY]
    ring
  obtain ⟨Γ₁, Γ₂, h1, h2, h3⟩ := hσ.lookback_covariance_mono (ŝ := fun x => x.2.2.2)
    (ĉ := fun x => M.c x.2.2.1 x.2.2.2) (ε := M.lookbackInc ψ b) (ν := stateSum ν) δ
    (fun k ω => rfl) hP0 (fun x => (hcY _ _).1) (fun x => (hcY _ _).2) hρ hγ0 hγ1
    (M.tendsto_stateLaw hY hlaw) hcent hl0 hl12 hl2 hW₁r hW₁m hW₁B hW₂r hW₂m hW₂B
  exact ⟨ν, hν, hνm, mZ, hmZ, Γ₁, Γ₂, h1, h2, h3⟩


end Process

end ScoreChain

end StochasticApproximation
