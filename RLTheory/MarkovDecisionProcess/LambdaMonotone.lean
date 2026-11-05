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
* `stationary_unique_restart`: the stationary law of the restart chain is unique.
* `restart_actor_one`, `restart_actor_covariance_mono`: the merged theorem. The linearized actor
  with the TD(`λ`) critic noise has `β_k⁻¹ E[θ_k θ_kᵀ] → Σ_λ`, the Lyapunov solution for
  `Γ̃(λ) = Γ_M + Γ_D(λ)`, and `Γ̃(λ₁) ≼ Γ̃(λ₂)`.
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

omit [DecidableEq Ac] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace Ac]
  [DiscreteMeasurableSpace Ac] [IsProbabilityMeasure μ] in
/-- The continuation weight of the pre-action kernel is at most `γ`. -/
lemma preaction_contraction (hkap0 : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hc0 : ∀ s, M.c true s = 0) (hcf1 : ∀ s, M.c false s ≤ 1)
    {γ : ℝ} (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) (s : S) :
    ∑ x : S × Ac × (Bool × S), (if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2) * M.c x.2.2.1 x.2.2.2 ≤ γ := by
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

omit [DecidableEq Ac] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace Ac]
  [DiscreteMeasurableSpace Ac] [IsProbabilityMeasure μ] in
/-- The stationary centering of the lookback increment, in the form of the pre-action kernel. -/
lemma preaction_centered {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    {n : ℕ} (ψ : S → Ac → E n) {mZ : Bool × S × Ac → E n}
    (hmZ : M.TraceMoment ν 1 (fun y => ψ y.2.1 y.2.2) mZ) (hpol : ∀ s, ∑ a, M.pol s a = 1)
    (hνS : ∀ s, stateSum ν s ≠ 0) (hflag : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a))
    (s : S) (j : Fin n) :
    ∑ s', stateSum ν s' * ∑ x : S × Ac × (Bool × S),
      (if x.1 = s' then 1 else 0) * (M.pol s' x.2.1 * M.kap (false, s', x.2.1) x.2.2.1 x.2.2.2) *
        ((if x.2.2.2 = s then 1 else 0) *
          M.lookbackInc ψ (carryMean ν (fun y => ψ y.2.1 y.2.2) mZ) x j) = 0 := by
  set b := carryMean ν (fun y => ψ y.2.1 y.2.2) mZ with hb
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
  simp only [if_true, one_mul, lookbackInc]
  ring


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
  have hP0 : ∀ s (x : S × Ac × (Bool × S)), 0 ≤ (if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2) := fun s x =>
    mul_nonneg (by split_ifs <;> norm_num) (mul_nonneg (hpol0 _ _) (hkap0 _ _ _))
  have hρ := M.preaction_contraction hkap0 hpol0 hpol hc0 hcf1 hγ
  have hcent := M.preaction_centered hν ψ hmZ hpol hνS hflag
  obtain ⟨Γ₁, Γ₂, h1, h2, h3⟩ := hσ.lookback_covariance_mono (ŝ := fun x => x.2.2.2)
    (ĉ := fun x => M.c x.2.2.1 x.2.2.2) (ε := M.lookbackInc ψ b) (ν := stateSum ν) δ
    (fun k ω => rfl) hP0 (fun x => (hcY _ _).1) (fun x => (hcY _ _).2) hρ hγ0 hγ1
    (M.tendsto_stateLaw hY hlaw) hcent hl0 hl12 hl2 hW₁r hW₁m hW₁B hW₂r hW₂m hW₂B
  exact ⟨ν, hν, hνm, mZ, hmZ, Γ₁, Γ₂, h1, h2, h3⟩


omit [DecidableEq S] [DecidableEq Ac] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Ac] [DiscreteMeasurableSpace Ac] [IsProbabilityMeasure μ] in
/-- **The stationary law of the restart chain is unique.** Two stationary laws of mass one solve
the same contracting affine equation. -/
theorem stationary_unique_restart (hpol : ∀ s, ∑ a, M.pol s a = 1)
    (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s) {γ : ℝ} (hγ1 : γ < 1)
    (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {ν ν' : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') (hνm : ∑ y, ν y = 1)
    (hν' : ∀ y', ∑ y, ν' y * M.Q y y' = ν' y') (hνm' : ∑ y, ν' y = 1) : ν = ν' := by
  set cc : Bool × S × Ac → ℝ := fun y => if y.1 then 0 else 1 with hcc
  set bb : Bool × S × Ac → ℝ := fun y => if y.1 then M.Q y y else 0 with hb
  have hQr : ∀ y s a, M.Q y (true, s, a) = M.Q (true, s, a) (true, s, a) := fun y s a => by
    simp only [Q, hrest y (true, s, a) s]
  have hsplit : ∀ (x : Bool × S × Ac → ℝ) (y' : Bool × S × Ac),
      ∑ y, M.Q y y' * x y = transfer M.Q cc x y' + bb y' * ∑ y, x y := by
    rintro x ⟨f, s, a⟩
    cases f
    · simp [transfer, hcc, hb]
    · simp only [transfer, hcc, hb, if_true, zero_mul, mul_sum, sum_const_zero, zero_add]
      exact sum_congr rfl fun y _ => by rw [hQr y s a]
  have hρ : ∀ y, ∑ y', M.Q y y' * |cc y'| ≤ γ := fun y => by
    rw [sum_prod3, Fintype.sum_bool]
    simp only [hcc, if_true, abs_zero, mul_zero, sum_const_zero, zero_add, Bool.false_eq_true,
      if_false, abs_one, mul_one, Q]
    refine le_trans (le_of_eq ?_) (hγ y)
    exact sum_congr rfl fun s _ => by rw [← mul_sum, hpol, mul_one]
  have hfix : ∀ (x : Bool × S × Ac → ℝ), (∀ y', ∑ y, x y * M.Q y y' = x y') → ∑ y, x y = 1 →
      ∀ y', x y' = transfer M.Q cc x y' + bb y' := fun x hx hxm y' => by
    calc x y' = ∑ y, x y * M.Q y y' := (hx y').symm
      _ = ∑ y, M.Q y y' * x y := sum_congr rfl fun y _ => mul_comm _ _
      _ = _ := by rw [hsplit, hxm, mul_one]
  set dd : Bool × S × Ac → ℝ := fun y => ν y - ν' y with hdd
  have hd : ∀ y', dd y' = transfer M.Q cc dd y' := fun y' => by
    simp only [hdd]
    rw [hfix ν hν hνm y', hfix ν' hν' hνm' y']
    simp only [transfer, mul_sub, sum_sub_distrib]
    ring
  have hl1 := l1_transfer_le (M.Q_nonneg hkap hpol0) hρ dd
  have hsum : ∑ y, |dd y| ≤ γ * ∑ y, |dd y| := by
    calc ∑ y, |dd y| = ∑ y', |transfer M.Q cc dd y'| := sum_congr rfl fun y _ => by rw [← hd y]
      _ ≤ _ := hl1
  have h0 : ∑ y, |dd y| = 0 := by
    have := sum_nonneg fun y (_ : y ∈ univ) => abs_nonneg (dd y)
    nlinarith
  funext y
  have := abs_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun y _ => abs_nonneg (dd y)).mp h0 y
    (mem_univ y))
  simp only [hdd] at this
  linarith

set_option maxHeartbeats 8000000 in
/-- **One actor iteration with the TD(`λ`) critic.** The linearized actor
`θ_{k+1} = θ_k - β_k A θ_k + β_k (V(s_k) ψ_k + δ_{k+1} (z^ψ_k - K_λ z^e_k))`, with the gain
`K_λ e_t = -(1 - λ) b(t)`, and the TD(0) noise `V ψ + δ (ψ + b(s)) = Φ(s_k, ξ_{k+1}) + h_k - h_{k+1}`
with `Φ` a martingale part. If the second moments of the centered critic trace converge and its
state-conditioned means vanish, then `β_k⁻¹ E[θ_k θ_kᵀ]` converges to the solution of the Lyapunov
equation with `Γ_M + Γ_D(λ)`. -/
theorem restart_actor_one {𝒢 ℋ : MeasureTheory.Filtration ℕ m0}
    {fs : ℕ → Ω → Bool × S} {a : ℕ → Ω → Ac} (hc : TwoStageChain μ 𝒢 ℋ fs a M.pol M.kap)
    (hflag : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a))
    (hc0 : ∀ s, M.c true s = 0) (hcf0 : ∀ s, 0 ≤ M.c false s) (hcf1 : ∀ s, M.c false s ≤ 1)
    {n : ℕ} (ψ : S → Ac → E n) (b : S → E n) (V : S → ℝ) (δ : S × Ac × (Bool × S) → ℝ)
    (Φ : S → S × Ac × (Bool × S) → E n)
    (hΦ : ∀ s, ∑ x : S × Ac × (Bool × S), ((if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2)) • Φ s x = 0)
    (hδ : ∀ s, ∑ x : S × Ac × (Bool × S), ((if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2)) * δ x = 0)
    {h : ℕ → Ω → E n} (hh : ∀ k, StronglyMeasurable[𝒢 k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
    (hN0 : ∀ k ω, V (fs k ω).2 • ψ (fs k ω).2 (a k ω) + δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
      (ψ (fs k ω).2 (a k ω) + b (fs k ω).2) =
        Φ (fs k ω).2 ((fs k ω).2, a k ω, fs (k + 1) ω) + h k ω - h (k + 1) ω)
    {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar) (A : Matrix (Fin n) (Fin n) ℝ) {η : ℝ}
    (hη : 0 < η) (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {zψ : ℕ → Ω → E n} {ze : ℕ → Ω → S → ℝ}
    (hz0 : ∀ ω, zψ 0 ω = ψ (fs 0 ω).2 (a 0 ω))
    (hze0 : ∀ ω t, ze 0 ω t = if (fs 0 ω).2 = t then 1 else 0)
    (hzψ : ∀ k ω, zψ (k + 1) ω = ψ (fs (k + 1) ω).2 (a (k + 1) ω)
      + (lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2) • zψ k ω)
    (hze : ∀ k ω t, ze (k + 1) ω t = (if (fs (k + 1) ω).2 = t then 1 else 0)
      + lam * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 * ze k ω t)
    {θ : ℕ → Ω → E n} (hθ0 : StronglyMeasurable[𝒢 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω) + β k •
      (V (fs k ω).2 • ψ (fs k ω).2 (a k ω) + δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
        (zψ k ω - ∑ t, ze k ω t • (-(1 - lam) • b t))))
    {ΓM ΓD : Mat n}
    (hΓM : Tendsto (fun k => secondMoment μ fun ω =>
      Φ (fs k ω).2 ((fs k ω).2, a k ω, fs (k + 1) ω)) atTop (𝓝 ΓM))
    (hm0 : ∀ s j, Tendsto (fun k => ∫ ω, {ω | (fs k ω).2 = s}.indicator
      (fun ω => centeredTrace lam ψ b zψ ze fs a k ω j) ω ∂μ) atTop (𝓝 0))
    {C : S → Fin n → Fin n → ℝ}
    (hconv : ∀ s i j, Tendsto (fun k => ∫ ω, {ω | (fs k ω).2 = s}.indicator
      (fun ω => centeredTrace lam ψ b zψ ze fs a k ω i * centeredTrace lam ψ b zψ ze fs a k ω j)
        ω ∂μ) atTop (𝓝 (C s i j)))
    (hΓD : Tendsto (fun k => secondMoment μ fun ω => δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
      centeredTrace lam ψ b zψ ze fs a k ω) atTop (𝓝 ΓD)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = ΓM + ΓD ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  have hσ := hc.stateDriven hflag
  obtain ⟨-, hWm, hWB⟩ := M.restart_centered_trace hc hc0 hcf0 hcf1 ψ b hl0 hl1 hz0 hze0 hzψ hze
  set W := centeredTrace lam ψ b zψ ze fs a with hW
  set B : ℕ → Ω → E n := fun k ω => W k ω + b (fs k ω).2 with hB
  have hBW : ∀ k ω, B k ω - b (fs k ω).2 = W k ω := fun k ω => by simp only [hB, add_sub_cancel_right]
  have hθ' : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω) + β k •
      (Φ (fs k ω).2 ((fs k ω).2, a k ω, fs (k + 1) ω)
        + δ ((fs k ω).2, a k ω, fs (k + 1) ω) • (B k ω - b (fs k ω).2) + h k ω - h (k + 1) ω) :=
    fun k ω => by
      rw [hθ k ω, tdlam_noise_split, hN0 k ω, hBW k ω]
      simp only [hW, centeredTrace]
      abel
  have hbm : ∀ k, StronglyMeasurable[𝒢 k] (fun ω => b (fs k ω).2) := fun k =>
    (StronglyMeasurable.of_discrete (f := b)).comp_measurable (measurable_snd.comp (hc.meas_fs k))
  have hBm : ∀ k, StronglyMeasurable[𝒢 k] (B k) := fun k => by
    have := (hWm k).add (hbm k); exact this
  set Cb := ∑ t, ‖b t‖ with hCb
  have hbb : ∀ t, ‖b t‖ ≤ Cb := fun t =>
    single_le_sum (f := fun t => ‖b t‖) (fun _ _ => norm_nonneg _) (mem_univ t)
  have hCb0 : 0 ≤ Cb := sum_nonneg fun _ _ => norm_nonneg _
  have hBB : ∀ k, ∃ C, ∀ ω, ‖B k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC⟩ := hWB k
    exact ⟨C + Cb, fun ω => (norm_add_le _ _).trans (add_le_add (hC ω) (hbb _))⟩
  -- the uniform second-moment bound
  have hB2 : ∃ C', ∀ k, ∫ ω, ‖B k ω‖ ^ 2 ∂μ ≤ C' := by
    have hu := tendsto_finset_sum (univ : Finset (Fin n)) fun i _ =>
      tendsto_finset_sum (univ : Finset S) fun s _ => hconv s i i
    obtain ⟨U, hU⟩ := hu.bddAbove_range
    refine ⟨2 * U + 2 * Cb ^ 2, fun k => ?_⟩
    have hcoord : ∀ i, StronglyMeasurable[𝒢 k] fun ω => W k ω i := fun i =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_stronglyMeasurable (hWm k)
    obtain ⟨CW, hCW⟩ := hWB k
    have hWi : ∀ i ω, |W k ω i| ≤ CW := fun i ω => by
      rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le _ i).trans (hCW ω)
    have hset : ∀ s, MeasurableSet[𝒢 k] {ω | (fs k ω).2 = s} := fun s =>
      (measurable_snd.comp (hc.meas_fs k)) (measurableSet_singleton s)
    have hint : ∀ i s, Integrable ({ω | (fs k ω).2 = s}.indicator
        fun ω => W k ω i * W k ω i) μ := fun i s =>
      (memLp_top_of_bound ((((hcoord i).mul (hcoord i)).indicator (hset s)).mono
        (𝒢.le k)).aestronglyMeasurable (CW * CW) (Eventually.of_forall fun ω =>
          (norm_indicator_le_norm_self _ ω).trans (by
            show ‖W k ω i * W k ω i‖ ≤ _
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (hWi i ω) (hWi i ω) (abs_nonneg _)
              ((abs_nonneg _).trans (hWi i ω))))).integrable le_top
    have hWsq : ∫ ω, ‖W k ω‖ ^ 2 ∂μ = ∑ i, ∑ s, ∫ ω, {ω | (fs k ω).2 = s}.indicator
        (fun ω => W k ω i * W k ω i) ω ∂μ := by
      have e : ∀ ω, ‖W k ω‖ ^ 2 = ∑ i, ∑ s, {ω | (fs k ω).2 = s}.indicator
          (fun ω => W k ω i * W k ω i) ω := fun ω => by
        rw [EuclideanSpace.norm_sq_eq]
        refine sum_congr rfl fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs, sq]
        have := sum_indicator_mul (σ := fun k ω => (fs k ω).2) (k := k) ω
          (fun _ ω => W k ω i * W k ω i) (fun _ => (1 : ℝ))
        simp only [mul_one] at this
        exact this.symm
      rw [integral_congr_ae (Eventually.of_forall e),
        integral_finset_sum _ fun i _ => integrable_finset_sum _ fun s _ => hint i s]
      exact sum_congr rfl fun i _ => integral_finset_sum _ fun s _ => hint i s
    have hWsqU : ∫ ω, ‖W k ω‖ ^ 2 ∂μ ≤ U := by
      rw [hWsq]; exact hU ⟨k, rfl⟩
    have iW : Integrable (fun ω => ‖W k ω‖ ^ 2) μ :=
      (memLp_top_of_bound (((hWm k).mono (𝒢.le k)).aestronglyMeasurable.norm.pow 2) (CW ^ 2)
        (Eventually.of_forall fun ω => by
          show ‖‖W k ω‖ ^ 2‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hCW ω) 2)).integrable le_top
    have iB : Integrable (fun ω => ‖B k ω‖ ^ 2) μ := by
      obtain ⟨C, hC⟩ := hBB k
      exact (memLp_top_of_bound (((hBm k).mono (𝒢.le k)).aestronglyMeasurable.norm.pow 2) (C ^ 2)
        (Eventually.of_forall fun ω => by
          show ‖‖B k ω‖ ^ 2‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2)).integrable le_top
    have hpt : ∀ ω, ‖B k ω‖ ^ 2 ≤ 2 * ‖W k ω‖ ^ 2 + 2 * Cb ^ 2 := fun ω => by
      have h1 := norm_add_le (W k ω) (b (fs k ω).2)
      have h2 := hbb (fs k ω).2
      have h3 : ‖B k ω‖ ≤ ‖W k ω‖ + Cb := h1.trans (add_le_add_left h2 _)
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [sq_nonneg (‖W k ω‖ - Cb), norm_nonneg (W k ω)]
    have i2 : Integrable (fun ω => 2 * ‖W k ω‖ ^ 2 + 2 * Cb ^ 2) μ :=
      (iW.const_mul 2).add (integrable_const _)
    calc ∫ ω, ‖B k ω‖ ^ 2 ∂μ ≤ ∫ ω, (2 * ‖W k ω‖ ^ 2 + 2 * Cb ^ 2) ∂μ := integral_mono iB i2 hpt
      _ = 2 * ∫ ω, ‖W k ω‖ ^ 2 ∂μ + 2 * Cb ^ 2 := by
          rw [integral_add (iW.const_mul 2) (integrable_const _), integral_const_mul]; simp
      _ ≤ 2 * U + 2 * Cb ^ 2 := by linarith
  -- the centering hypothesis
  have hcent : ∀ s j, Tendsto (fun k => ∫ ω, {ω | (fs k ω).2 = s}.indicator
      (fun ω => B k ω j - b s j) ω ∂μ) atTop (𝓝 0) := fun s j => by
    refine (hm0 s j).congr fun k => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with hs
    · rw [← hs, ← hBW k ω]; simp
    · rfl
  have hΓD' : Tendsto (fun k => secondMoment μ fun ω => δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
      (B k ω - b (fs k ω).2)) atTop (𝓝 ΓD) := by
    simpa only [hBW] using hΓD
  exact hσ.tendsto_secondMoment_of_centered_split hβ A hη hA Φ δ b hθ' hθ0 hθ0L hh hhL hhB hΦ hδ
    hBm hBB hB2 hcent hΓM hΓD'


set_option maxHeartbeats 16000000 in
/-- **Theorem 4.7, merged: shorter traces give a smaller actor covariance.** For the restart chain
(hypotheses as in `restart_lambda_covariance_mono`), let `ν` be its stationary law and `m_Z` the
REINFORCE trace moments, so that `b = carryMean ν ψ m_Z`. Let the TD(0) actor-critic noise split as
`V ψ + δ (ψ + b(s)) = Φ(s_k, ξ_{k+1}) + h_k - h_{k+1}`, with `Φ` and `δ` centered given the state.
For `0 ≤ λ₁ ≤ λ₂ ≤ 1`, run the linearized actor with the TD(`λ_l`) critic noise,
`θ_{k+1} = θ_k - β_k A θ_k + β_k (V(s_k) ψ_k + δ_{k+1} (z^ψ_k - K_λ z^e_k))` with
`K_λ e_t = -(1 - λ) b(t)`. Then `β_k⁻¹ E[θ^{(l)}_k θ^{(l)ᵀ}_k] → Σ_l`, where `Σ_l` solves the
Lyapunov equation with `Γ̃(λ_l) = Γ_M + Γ_D(λ_l)`, and `Γ_D(λ₁) ≼ Γ_D(λ₂)`, so
`Γ̃(λ₁) ≼ Γ̃(λ₂)`. -/
theorem restart_actor_covariance_mono {𝒢 ℋ : MeasureTheory.Filtration ℕ m0}
    {fs : ℕ → Ω → Bool × S} {a : ℕ → Ω → Ac} (hc : TwoStageChain μ 𝒢 ℋ fs a M.pol M.kap)
    (hY : FiniteMarkov μ ℋ (fun k ω => ((fs k ω).1, (fs k ω).2, a k ω)) M.Q)
    (hkap0 : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    (hpos : ∀ y s, 0 < M.kap y true s)
    (hflag : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a))
    (hc0 : ∀ s, M.c true s = 0) (hcf0 : ∀ s, 0 ≤ M.c false s) (hcf1 : ∀ s, M.c false s ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ)
    {n : ℕ} (ψ : S → Ac → E n) (V : S → ℝ) (δ : S × Ac × (Bool × S) → ℝ)
    {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') (hνm : ∑ y, ν y = 1)
    {mZ : Bool × S × Ac → E n} (hmZ : M.TraceMoment ν 1 (fun y => ψ y.2.1 y.2.2) mZ)
    (Φ : S → S × Ac × (Bool × S) → E n)
    (hΦ : ∀ s, ∑ x : S × Ac × (Bool × S), ((if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2)) • Φ s x = 0)
    (hδ : ∀ s, ∑ x : S × Ac × (Bool × S), ((if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2)) * δ x = 0)
    {h : ℕ → Ω → E n} (hh : ∀ k, StronglyMeasurable[𝒢 k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
    (hN0 : ∀ k ω, V (fs k ω).2 • ψ (fs k ω).2 (a k ω) + δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
      (ψ (fs k ω).2 (a k ω) + carryMean ν (fun y => ψ y.2.1 y.2.2) mZ (fs k ω).2) =
        Φ (fs k ω).2 ((fs k ω).2, a k ω, fs (k + 1) ω) + h k ω - h (k + 1) ω)
    {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar) (A : Matrix (Fin n) (Fin n) ℝ) {η : ℝ}
    (hη : 0 < η) (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
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
      + l₂ * M.c (fs (k + 1) ω).1 (fs (k + 1) ω).2 * ze₂ k ω t)
    {θ₁ θ₂ : ℕ → Ω → E n}
    (hθ0₁ : StronglyMeasurable[𝒢 0] (θ₁ 0)) (hθ0L₁ : MemLp (θ₁ 0) 2 μ)
    (hθ₁ : ∀ k ω, θ₁ (k + 1) ω = θ₁ k ω - β k • matCLM A (θ₁ k ω) + β k •
      (V (fs k ω).2 • ψ (fs k ω).2 (a k ω) + δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
        (zψ₁ k ω - ∑ t, ze₁ k ω t • (-(1 - l₁) • carryMean ν (fun y => ψ y.2.1 y.2.2) mZ t))))
    (hθ0₂ : StronglyMeasurable[𝒢 0] (θ₂ 0)) (hθ0L₂ : MemLp (θ₂ 0) 2 μ)
    (hθ₂ : ∀ k ω, θ₂ (k + 1) ω = θ₂ k ω - β k • matCLM A (θ₂ k ω) + β k •
      (V (fs k ω).2 • ψ (fs k ω).2 (a k ω) + δ ((fs k ω).2, a k ω, fs (k + 1) ω) •
        (zψ₂ k ω - ∑ t, ze₂ k ω t • (-(1 - l₂) • carryMean ν (fun y => ψ y.2.1 y.2.2) mZ t)))) :
    ∃ ΓM Γ₁ Γ₂ Sig₁ Sig₂ : Mat n,
      lyapOp (A - (βbar / 2) • 1) Sig₁ = ΓM + Γ₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ₁ k)) atTop (𝓝 Sig₁) ∧
      lyapOp (A - (βbar / 2) • 1) Sig₂ = ΓM + Γ₂ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ₂ k)) atTop (𝓝 Sig₂) ∧
      ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * Γ₁ (i, j) ∧
        ∑ i, ∑ j, v i * v j * Γ₁ (i, j) ≤ ∑ i, ∑ j, v i * v j * Γ₂ (i, j) := by
  obtain ⟨ν', hν', hνm', hlaw'⟩ := M.tendsto_law_restart hY hkap0 hpol0 hpol hrest hγ0 hγ1 hγ
  have hνeq : ν' = ν := M.stationary_unique_restart hpol hkap0 hpol0 hrest hγ1 hγ hν' hνm' hν hνm
  rw [hνeq] at hlaw'
  have hν0 : ∀ y, 0 ≤ ν y := fun y => ge_of_tendsto' (hlaw' y) fun k =>
    integral_nonneg fun ω => by simp only [Set.indicator_apply]; split_ifs <;> norm_num
  have hνS := M.stateSum_ne_zero_restart hν hν0 hνm hpol hrest hpos
  set b := carryMean ν (fun y => ψ y.2.1 y.2.2) mZ with hb
  have hσ := hc.stateDriven hflag
  have hcY : ∀ f s, 0 ≤ M.c f s ∧ M.c f s ≤ 1 := fun f s => by
    cases f
    · exact ⟨hcf0 s, hcf1 s⟩
    · rw [hc0 s]; exact ⟨le_rfl, zero_le_one⟩
  have hP0 : ∀ s (x : S × Ac × (Bool × S)), 0 ≤ (if x.1 = s then 1 else 0) *
      (M.pol s x.2.1 * M.kap (false, s, x.2.1) x.2.2.1 x.2.2.2) := fun s x =>
    mul_nonneg (by split_ifs <;> norm_num) (mul_nonneg (hpol0 _ _) (hkap0 _ _ _))
  have hρ := M.preaction_contraction hkap0 hpol0 hpol hc0 hcf1 hγ
  have hcent := M.preaction_centered hν ψ hmZ hpol hνS hflag
  have hstate := M.tendsto_stateLaw hY hlaw'
  obtain ⟨hW₁r, hW₁m, hW₁B⟩ := M.restart_centered_trace hc hc0 hcf0 hcf1 ψ b hl0
    (hl12.trans hl2) hz0₁ hze0₁ hzψ₁ hze₁
  obtain ⟨hW₂r, hW₂m, hW₂B⟩ := M.restart_centered_trace hc hc0 hcf0 hcf1 ψ b (hl0.trans hl12)
    hl2 hz0₂ hze0₂ hzψ₂ hze₂
  obtain ⟨hm0₁, C₁, -, hconv₁⟩ := hσ.tendsto_lookback_moments (ŝ := fun x => x.2.2.2)
    (ĉ := fun x => M.c x.2.2.1 x.2.2.2) (ε := M.lookbackInc ψ b) (ν := stateSum ν)
    (fun k ω => rfl) hP0 (fun x => (hcY _ _).1) (fun x => (hcY _ _).2) hρ hγ0 hγ1 hl0
    (hl12.trans hl2) hW₁r hW₁m hW₁B hstate hcent
  obtain ⟨hm0₂, C₂, -, hconv₂⟩ := hσ.tendsto_lookback_moments (ŝ := fun x => x.2.2.2)
    (ĉ := fun x => M.c x.2.2.1 x.2.2.2) (ε := M.lookbackInc ψ b) (ν := stateSum ν)
    (fun k ω => rfl) hP0 (fun x => (hcY _ _).1) (fun x => (hcY _ _).2) hρ hγ0 hγ1
    (hl0.trans hl12) hl2 hW₂r hW₂m hW₂B hstate hcent
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hmono⟩ := hσ.lookback_covariance_mono (ŝ := fun x => x.2.2.2)
    (ĉ := fun x => M.c x.2.2.1 x.2.2.2) (ε := M.lookbackInc ψ b) (ν := stateSum ν) δ
    (fun k ω => rfl) hP0 (fun x => (hcY _ _).1) (fun x => (hcY _ _).2) hρ hγ0 hγ1
    hstate hcent hl0 hl12 hl2 hW₁r hW₁m hW₁B hW₂r hW₂m hW₂B
  have hΓM := hσ.tendsto_secondMoment_pair Φ hstate
  obtain ⟨Sig₁, hS₁, hT₁⟩ := M.restart_actor_one hc hflag hc0 hcf0 hcf1 ψ b V δ Φ hΦ hδ hh hhL
    hhB hN0 hβ A hη hA hl0 (hl12.trans hl2) hz0₁ hze0₁ hzψ₁ hze₁ hθ0₁ hθ0L₁ hθ₁ hΓM hm0₁ hconv₁
    hΓ₁
  obtain ⟨Sig₂, hS₂, hT₂⟩ := M.restart_actor_one hc hflag hc0 hcf0 hcf1 ψ b V δ Φ hΦ hδ hh hhL
    hhB hN0 hβ A hη hA (hl0.trans hl12) hl2 hz0₂ hze0₂ hzψ₂ hze₂ hθ0₂ hθ0L₂ hθ₂ hΓM hm0₂ hconv₂
    hΓ₂
  exact ⟨_, Γ₁, Γ₂, Sig₁, Sig₂, hS₁, hT₁, hS₂, hT₂, hmono⟩


end Process

end ScoreChain

end StochasticApproximation
