/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.DoeblinPoisson
import RLTheory.StochasticApproximation.OrthogonalNoise

/-!
# The noise covariance under θ-dependent Doeblin sampling

`tendsto_secondMoment_of_param_chain` assumes that the covariance of the martingale part
`M_{k+1} = U_{θ_k}(ξ_{k+1}) - V_{θ_k}(ξ_k)` converges. This file derives it.

* `tendsto_integral_norm_of_four`: `E‖X_k‖⁴ = O(β_k²)` gives `E‖X_k‖ → 0`.
* `tendsto_law_moving`: if the kernel at the limit `θ*` is Doeblin,
  `P_{θ*} = α ν + (1 - α) Q`, and the kernels are Lipschitz in `θ` in total variation, then the law
  of `ξ_k` converges to the stationary law `π` of `P_{θ*}`, even though the chain moves by
  `P_{θ_k}`. Under `P_{θ*}` the difference of two laws contracts by `1 - α`, and the kernels drift
  by `O(E‖θ_k - θ*‖)`.
* `tendsto_secondMoment_paramM`: then `E[M_{k+1} M_{k+1}ᵀ] = E[g(θ_k, ξ_k)]`, with `g` bounded and
  Lipschitz in `θ`, converges to `Σ_s π(s) g(θ*, s)`.
* `tendsto_secondMoment_of_param_chain_doeblin`, `tendsto_secondMoment_of_doeblin_chain_auto`:
  Assumption 2.2 for θ-dependent sampling with no hypothesis on the noise covariance.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Fourth moments control the mean.** If `E‖X_k‖⁴ ≤ W β_k²` with `β_k → 0`, then
`E‖X_k‖ → 0`, from `‖x‖ ≤ e + ‖x‖⁴ / e³`. -/
lemma tendsto_integral_norm_of_four {X : ℕ → Ω → E d} {β : ℕ → ℝ}
    (hβ0 : Tendsto β atTop (𝓝 0)) {W : ℝ} (hXi : ∀ k, Integrable (fun ω => ‖X k ω‖) μ)
    (hX4i : ∀ k, Integrable (fun ω => ‖X k ω‖ ^ 4) μ)
    (hX4 : ∀ k, ∫ ω, ‖X k ω‖ ^ 4 ∂μ ≤ W * β k ^ 2) :
    Tendsto (fun k => ∫ ω, ‖X k ω‖ ∂μ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 2 with he
  have he0 : 0 < e := by positivity
  have hpt : ∀ a : ℝ, 0 ≤ a → a ≤ e + a ^ 4 / e ^ 3 := fun a ha => by
    by_cases hae : a ≤ e
    · have : 0 ≤ a ^ 4 / e ^ 3 := by positivity
      linarith
    · push_neg at hae
      have h1 : a ≤ a ^ 4 / e ^ 3 := by
        rw [le_div_iff₀ (by positivity)]
        have h2 : e ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ he0.le hae.le 3
        nlinarith [pow_pos he0 3]
      linarith
  have hβ2 : Tendsto (fun k => W * β k ^ 2 / e ^ 3) atTop (𝓝 0) := by
    have := ((hβ0.pow 2).const_mul W).div_const (e ^ 3)
    simpa using this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hβ2) e he0
  refine ⟨N, fun k hk => ?_⟩
  have hint : ∫ ω, ‖X k ω‖ ∂μ ≤ e + (∫ ω, ‖X k ω‖ ^ 4 ∂μ) / e ^ 3 := by
    calc ∫ ω, ‖X k ω‖ ∂μ ≤ ∫ ω, (e + ‖X k ω‖ ^ 4 / e ^ 3) ∂μ :=
          integral_mono (hXi k) ((integrable_const e).add ((hX4i k).div_const _))
            fun ω => hpt _ (norm_nonneg _)
      _ = e + (∫ ω, ‖X k ω‖ ^ 4 ∂μ) / e ^ 3 := by
          rw [integral_add (integrable_const e) ((hX4i k).div_const _), integral_const,
            integral_div]
          simp
  have h1 : (∫ ω, ‖X k ω‖ ^ 4 ∂μ) / e ^ 3 ≤ W * β k ^ 2 / e ^ 3 :=
    div_le_div_of_nonneg_right (hX4 k) (by positivity)
  have h2 := hN k hk
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  have h3 : 0 ≤ ∫ ω, ‖X k ω‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  rw [abs_of_nonneg h3]
  have h4 := (le_abs_self _).trans_lt h2
  linarith

section Law

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq S] in
/-- **The law converges under a moving Doeblin kernel.** -/
theorem tendsto_law_moving (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d}
    {ξ : ℕ → Ω → S} (hξm : ∀ k, Measurable[ℱ k] (ξ k)) {P : E d → S → S → ℝ}
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (θ k ω) (ξ k ω) s)
    {θh : E d} {LP α : ℝ} {ν : S → ℝ} {Q : S → S → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hQ0 : ∀ s s', 0 ≤ Q s s') (hQ1 : ∀ s, ∑ s', Q s s' = 1)
    (hPh : ∀ s s', P θh s s' = α * ν s' + (1 - α) * Q s s')
    (hPL : ∀ t s, ∑ s', |P t s s' - P θh s s'| ≤ LP * ‖t - θh‖)
    {pst : S → ℝ} (hpst : ∀ s', ∑ s, pst s * P θh s s' = pst s') (hpst1 : ∑ s, pst s = 1)
    (hθi : ∀ k, Integrable (fun ω => ‖θ k ω - θh‖) μ)
    (hθc : Tendsto (fun k => ∫ ω, ‖θ k ω - θh‖ ∂μ) atTop (𝓝 0)) (s : S) :
    Tendsto (fun k => ∫ ω, {ω | ξ k ω = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ) atTop
      (𝓝 (pst s)) := by
  set L : ℕ → S → ℝ := fun k s => ∫ ω, {ω | ξ k ω = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ
    with hL
  have hset : ∀ k s, MeasurableSet[ℱ k] {ω | ξ k ω = s} := fun k s =>
    hξm k (measurableSet_singleton s)
  have hIi : ∀ k s, Integrable ({ω | ξ k ω = s}.indicator fun _ => (1 : ℝ)) μ := fun k s =>
    (integrable_const (1 : ℝ)).indicator (ℱ.le k _ (hset k s))
  -- `F(ξ_k) = Σ_s 1{ξ_k = s} F(s)`
  have hdec : ∀ k (F : S → ℝ) ω, F (ξ k ω) =
      ∑ s, {ω | ξ k ω = s}.indicator (fun _ => (1 : ℝ)) ω * F s := fun k F ω => by
    rw [sum_indicator_mul (σ := ξ) (k := k) ω (fun _ _ => 1) F, one_mul]
  have hFint : ∀ k (F : S → ℝ), ∫ ω, F (ξ k ω) ∂μ = ∑ s, F s * L k s := fun k F => by
    rw [integral_congr_ae (Eventually.of_forall (hdec k F)),
      integral_finset_sum _ fun s _ => (hIi k s).mul_const _]
    exact sum_congr rfl fun s _ => by rw [integral_mul_const, mul_comm]
  have hmass : ∀ k, ∑ s, L k s = 1 := fun k => by
    have := hFint k (fun _ => 1)
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_univ_eq_one, one_mul] at this
    exact this.symm
  -- one step of the law
  have hPi : ∀ k s', Integrable (fun ω => P (θ k ω) (ξ k ω) s') μ := fun k s' =>
    integrable_condExp.congr (hlaw k s')
  have hstep : ∀ k s', L (k + 1) s' = ∫ ω, P (θ k ω) (ξ k ω) s' ∂μ := fun k s' => by
    simp only [hL]
    rw [← integral_condExp (ℱ.le k)]
    exact integral_congr_ae (hlaw k s')
  set e : ℕ → S → ℝ := fun k s' => L (k + 1) s' - ∑ s, P θh s s' * L k s with he
  have hPhi : ∀ k s', Integrable (fun ω => P θh (ξ k ω) s') μ := fun k s' =>
    (memLp_top_of_bound ((StronglyMeasurable.of_discrete (f := fun s => P θh s s')).comp_measurable
      ((hξm k).mono (ℱ.le k) le_rfl)).aestronglyMeasurable (∑ s, |P θh s s'|)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact single_le_sum (f := fun s => |P θh s s'|) (fun _ _ => abs_nonneg _)
          (mem_univ _))).integrable le_top
  have he_eq : ∀ k s', e k s' = ∫ ω, (P (θ k ω) (ξ k ω) s' - P θh (ξ k ω) s') ∂μ := fun k s' => by
    simp only [he]
    rw [integral_sub (hPi k s') (hPhi k s'), hstep k s', hFint k (fun s => P θh s s')]
  have hesum : ∀ k, ∑ s', |e k s'| ≤ LP * ∫ ω, ‖θ k ω - θh‖ ∂μ := fun k => by
    calc ∑ s', |e k s'| ≤ ∑ s', ∫ ω, |P (θ k ω) (ξ k ω) s' - P θh (ξ k ω) s'| ∂μ :=
          sum_le_sum fun s' _ => by rw [he_eq]; exact abs_integral_le_integral_abs
      _ = ∫ ω, ∑ s', |P (θ k ω) (ξ k ω) s' - P θh (ξ k ω) s'| ∂μ :=
          (integral_finset_sum _ fun s' _ => ((hPi k s').sub (hPhi k s')).abs).symm
      _ ≤ ∫ ω, LP * ‖θ k ω - θh‖ ∂μ :=
          integral_mono (integrable_finset_sum _ fun s' _ => ((hPi k s').sub (hPhi k s')).abs)
            ((hθi k).const_mul LP) fun ω => hPL _ _
      _ = LP * ∫ ω, ‖θ k ω - θh‖ ∂μ := integral_const_mul _ _
  -- the deviation from `pst` contracts
  set dd : ℕ → S → ℝ := fun k s => L k s - pst s with hdd
  have hd0 : ∀ k, ∑ s, dd k s = 0 := fun k => by
    simp only [hdd, sum_sub_distrib, hmass, hpst1, sub_self]
  have hdrec : ∀ k s', dd (k + 1) s' = (1 - α) * ∑ s, Q s s' * dd k s + e k s' := fun k s' => by
    have h1 : ∑ s, P θh s s' * dd k s = (1 - α) * ∑ s, Q s s' * dd k s := by
      simp only [hPh, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
      rw [hd0 k, mul_zero, mul_zero, zero_add]
    have h2 : pst s' = ∑ s, P θh s s' * pst s := by
      rw [← hpst s']; exact sum_congr rfl fun s _ => mul_comm _ _
    have h3 : dd (k + 1) s' = ∑ s, P θh s s' * dd k s + e k s' := by
      simp only [hdd, he, mul_sub, sum_sub_distrib]
      rw [← h2]
      ring
    rw [h3, h1]
  set u : ℕ → ℝ := fun k => ∑ s, |dd k s| with hu
  have hrec : ∀ k, u (k + 1) ≤ (1 - α) * u k + LP * ∫ ω, ‖θ k ω - θh‖ ∂μ := fun k => by
    have h1 : ∀ s', |dd (k + 1) s'| ≤ (1 - α) * ∑ s, Q s s' * |dd k s| + |e k s'| := fun s' => by
      rw [hdrec k s']
      refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - α)]
      refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
        (le_of_eq (sum_congr rfl fun s _ => by rw [abs_mul, abs_of_nonneg (hQ0 s s')])))
        (by linarith)
    calc u (k + 1) ≤ ∑ s', ((1 - α) * ∑ s, Q s s' * |dd k s| + |e k s'|) :=
          sum_le_sum fun s' _ => h1 s'
      _ = (1 - α) * ∑ s, (∑ s', Q s s') * |dd k s| + ∑ s', |e k s'| := by
          rw [sum_add_distrib, ← mul_sum, sum_comm]
          congr 2
          exact sum_congr rfl fun s _ => by rw [sum_mul]
      _ ≤ (1 - α) * u k + LP * ∫ ω, ‖θ k ω - θh‖ ∂μ := by
          simp only [hQ1, one_mul]
          linarith [hesum k]
  have hu0 : ∀ k, 0 ≤ u k := fun k => sum_nonneg fun _ _ => abs_nonneg _
  have hut := tendsto_zero_of_le_contract (by linarith) (by linarith) hu0 hrec
    (by simpa using hθc.const_mul LP)
  have hds : Tendsto (fun k => dd k s) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) hut
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun s => |dd k s|) (fun _ _ => abs_nonneg _) (mem_univ s)
  have := hds.add_const (pst s)
  simp only [hdd, sub_add_cancel, zero_add] at this
  exact this

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure μ] in
/-- The conditional second moment `g(t, s₀) = Σ_s P_t(s₀, s) (U_t s - V_t s₀)_i (U_t s - V_t s₀)_j`
is Lipschitz in `t` at `θ*`. -/
lemma abs_condCov_sub_le {P : E d → S → S → ℝ} {U V : E d → S → E d} {θh t : E d} (s₀ : S)
    (i j : Fin d) {CU CV LU LV LP : ℝ} (hCU : 0 ≤ CU) (hCV : 0 ≤ CV)
    (hUb : ∀ t s, ‖U t s‖ ≤ CU) (hVb : ∀ t s, ‖V t s‖ ≤ CV)
    (hUL : ∀ t s, ‖U t s - U θh s‖ ≤ LU * ‖t - θh‖) (hVL : ∀ t s, ‖V t s - V θh s‖ ≤ LV * ‖t - θh‖)
    (hP0 : ∀ s s', 0 ≤ P θh s s') (hP1 : ∀ s, ∑ s', P θh s s' = 1)
    (hPL : ∀ t s, ∑ s', |P t s s' - P θh s s'| ≤ LP * ‖t - θh‖) :
    |∑ s, P t s₀ s * ((U t s - V t s₀) i * (U t s - V t s₀) j)
      - ∑ s, P θh s₀ s * ((U θh s - V θh s₀) i * (U θh s - V θh s₀) j)| ≤
      (LP * (CU + CV) ^ 2 + 2 * (CU + CV) * (LU + LV)) * ‖t - θh‖ := by
  set δ := ‖t - θh‖ with hδ
  set Ca := CU + CV
  have hCa : 0 ≤ Ca := add_nonneg hCU hCV
  have ha : ∀ t' s (l : Fin d), |(U t' s - V t' s₀) l| ≤ Ca := fun t' s l => by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ l).trans ((norm_sub_le _ _).trans (add_le_add (hUb _ _) (hVb _ _)))
  have hda : ∀ s (l : Fin d), |(U t s - V t s₀) l - (U θh s - V θh s₀) l| ≤ (LU + LV) * δ :=
    fun s l => by
      rw [← Real.norm_eq_abs, show (U t s - V t s₀) l - (U θh s - V θh s₀) l =
        ((U t s - U θh s) - (V t s₀ - V θh s₀)) l by simp; ring]
      refine (PiLp.norm_apply_le _ l).trans ((norm_sub_le _ _).trans ?_)
      have := hUL t s; have := hVL t s₀
      linarith
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hLa : 0 ≤ (LU + LV) * δ := (abs_nonneg _).trans (hda s₀ i)
  rw [← sum_sub_distrib]
  have hterm : ∀ s, |P t s₀ s * ((U t s - V t s₀) i * (U t s - V t s₀) j)
      - P θh s₀ s * ((U θh s - V θh s₀) i * (U θh s - V θh s₀) j)| ≤
      |P t s₀ s - P θh s₀ s| * Ca ^ 2 + P θh s₀ s * (2 * Ca * ((LU + LV) * δ)) := fun s => by
    set a := (U t s - V t s₀) i
    set b := (U t s - V t s₀) j
    set a' := (U θh s - V θh s₀) i
    set b' := (U θh s - V θh s₀) j
    have e : P t s₀ s * (a * b) - P θh s₀ s * (a' * b') =
        (P t s₀ s - P θh s₀ s) * (a * b) + P θh s₀ s * (a * (b - b') + b' * (a - a')) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul]
      have := ha t s i; have := ha t s j
      exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg a, abs_nonneg b]) (abs_nonneg _)
    · rw [abs_mul, abs_of_nonneg (hP0 _ _)]
      refine mul_le_mul_of_nonneg_left ?_ (hP0 _ _)
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 := mul_le_mul (ha t s i) (hda s j) (abs_nonneg _) hCa
      have h2 := mul_le_mul (ha θh s j) (hda s i) (abs_nonneg _) hCa
      linarith
  calc |∑ s, (P t s₀ s * ((U t s - V t s₀) i * (U t s - V t s₀) j)
        - P θh s₀ s * ((U θh s - V θh s₀) i * (U θh s - V θh s₀) j))|
      ≤ ∑ s, (|P t s₀ s - P θh s₀ s| * Ca ^ 2 + P θh s₀ s * (2 * Ca * ((LU + LV) * δ))) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => hterm s)
    _ = (∑ s, |P t s₀ s - P θh s₀ s|) * Ca ^ 2 + (∑ s, P θh s₀ s) * (2 * Ca * ((LU + LV) * δ)) := by
        rw [sum_add_distrib, sum_mul, sum_mul]
    _ ≤ (LP * δ) * Ca ^ 2 + 1 * (2 * Ca * ((LU + LV) * δ)) := by
        rw [hP1]
        exact add_le_add_right (mul_le_mul_of_nonneg_right (hPL t s₀) (sq_nonneg _)) _
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **The noise covariance converges.** Under a moving Doeblin kernel, with `U`, `V` bounded,
continuous, and Lipschitz at `θ*`, the kernels Lipschitz at `θ*` in total variation, the law of
`ξ_k` converging to `π`, and `E‖θ_k - θ*‖ → 0`, the second moment of
`M_{k+1} = U_{θ_k}(ξ_{k+1}) - V_{θ_k}(ξ_k)` converges to
`Γ* = Σ_{s₀} π(s₀) Σ_s P_{θ*}(s₀, s) (U_{θ*} s - V_{θ*} s₀)(U_{θ*} s - V_{θ*} s₀)ᵀ`. -/
theorem tendsto_secondMoment_paramM (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d}
    {ξ : ℕ → Ω → S} (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    {P : E d → S → S → ℝ}
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (θ k ω) (ξ k ω) s)
    {U V : E d → S → E d} {θh : E d} {CU CV LU LV LP : ℝ} (hCU : 0 ≤ CU) (hCV : 0 ≤ CV)
    (hUc : ∀ s, Continuous fun t => U t s) (hVc : ∀ s, Continuous fun t => V t s)
    (hUb : ∀ t s, ‖U t s‖ ≤ CU) (hVb : ∀ t s, ‖V t s‖ ≤ CV)
    (hUL : ∀ t s, ‖U t s - U θh s‖ ≤ LU * ‖t - θh‖) (hVL : ∀ t s, ‖V t s - V θh s‖ ≤ LV * ‖t - θh‖)
    (hP0 : ∀ s s', 0 ≤ P θh s s') (hP1 : ∀ s, ∑ s', P θh s s' = 1)
    (hPL : ∀ t s, ∑ s', |P t s s' - P θh s s'| ≤ LP * ‖t - θh‖) {pst : S → ℝ}
    (hlawc : ∀ s, Tendsto (fun k => ∫ ω, {ω | ξ k ω = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ)
      atTop (𝓝 (pst s)))
    (hθi : ∀ k, Integrable (fun ω => ‖θ k ω - θh‖) μ)
    (hθc : Tendsto (fun k => ∫ ω, ‖θ k ω - θh‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => secondMoment μ (paramM U V θ ξ (k + 1))) atTop
      (𝓝 ((EuclideanSpace.equiv (Fin d × Fin d) ℝ).symm fun ij => ∑ s₀, pst s₀ *
        ∑ s, P θh s₀ s * ((U θh s - V θh s₀) ij.1 * (U θh s - V θh s₀) ij.2))) := by
  refine tendsto_euclid_of_coord fun ij => ?_
  obtain ⟨i, j⟩ := ij
  set Lg := LP * (CU + CV) ^ 2 + 2 * (CU + CV) * (LU + LV)
  have hset : ∀ k s, MeasurableSet[ℱ k] {ω | ξ k ω = s} := fun k s =>
    hξm k (measurableSet_singleton s)
  have hIi : ∀ k s, Integrable ({ω | ξ k ω = s}.indicator fun _ => (1 : ℝ)) μ := fun k s =>
    (integrable_const (1 : ℝ)).indicator (ℱ.le k _ (hset k s))
  have hcoordb : ∀ t s s₀ (l : Fin d), |(U t s - V t s₀) l| ≤ CU + CV := fun t s s₀ l => by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ l).trans ((norm_sub_le _ _).trans (add_le_add (hUb _ _) (hVb _ _)))
  -- the entry is `E[g(θ_k, ξ_k)]`
  have hentry : ∀ k, Integrable (fun ω => ∑ s, P (θ k ω) (ξ k ω) s *
      ((U (θ k ω) s - V (θ k ω) (ξ k ω)) i * (U (θ k ω) s - V (θ k ω) (ξ k ω)) j)) μ ∧
      (secondMoment μ (paramM U V θ ξ (k + 1))) (i, j) =
      ∫ ω, ∑ s, P (θ k ω) (ξ k ω) s * ((U (θ k ω) s - V (θ k ω) (ξ k ω)) i *
        (U (θ k ω) s - V (θ k ω) (ξ k ω)) j) ∂μ := fun k => by
    have hMm : StronglyMeasurable[ℱ (k + 1)] (paramM U V θ ξ (k + 1)) := by
      show StronglyMeasurable[ℱ (k + 1)] fun ω => U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω)
      exact (stronglyMeasurable_comp_finite ((hθm k).mono (ℱ.mono k.le_succ)) (hξm (k + 1))
        hUc).sub ((stronglyMeasurable_comp_finite (hθm k) (hξm k) hVc).mono (ℱ.mono k.le_succ))
    have hML : MemLp (paramM U V θ ξ (k + 1)) 2 μ :=
      MemLp.of_bound (hMm.mono (ℱ.le (k + 1))).aestronglyMeasurable (CU + CV)
        (Eventually.of_forall fun ω => by
          show ‖U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω)‖ ≤ _
          exact (norm_sub_le _ _).trans (add_le_add (hUb _ _) (hVb _ _)))
    rw [secondMoment, crossMoment_apply hML hML]
    have hGm : ∀ s, StronglyMeasurable[ℱ k] (fun ω => (U (θ k ω) s - V (θ k ω) (ξ k ω)) i *
        (U (θ k ω) s - V (θ k ω) (ξ k ω)) j) := fun s => by
      have hW : StronglyMeasurable[ℱ k] (fun ω => U (θ k ω) s - V (θ k ω) (ξ k ω)) :=
        ((hUc s).comp_stronglyMeasurable (hθm k)).sub
          (stronglyMeasurable_comp_finite (hθm k) (hξm k) hVc)
      exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_stronglyMeasurable hW).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_stronglyMeasurable hW)
    have hmix := condExp_finite_mix (μ := μ) ℱ k ((hξm (k + 1)).mono (ℱ.le (k + 1)) le_rfl)
      (hlaw k) (G := fun s ω => (U (θ k ω) s - V (θ k ω) (ξ k ω)) i *
        (U (θ k ω) s - V (θ k ω) (ξ k ω)) j) hGm
      (fun s => ⟨(CU + CV) * (CU + CV), fun ω => by
        show |(U (θ k ω) s - V (θ k ω) (ξ k ω)) i * (U (θ k ω) s - V (θ k ω) (ξ k ω)) j| ≤ _
        rw [abs_mul]
        exact mul_le_mul (hcoordb (θ k ω) s (ξ k ω) i) (hcoordb (θ k ω) s (ξ k ω) j)
          (abs_nonneg _) (add_nonneg hCU hCV)⟩)
    refine ⟨integrable_condExp.congr hmix, ?_⟩
    calc ∫ ω, paramM U V θ ξ (k + 1) ω i * paramM U V θ ξ (k + 1) ω j ∂μ
        = ∫ ω, (fun ω => (U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω)) i *
            (U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω)) j) ω ∂μ := by
          rfl
      _ = ∫ ω, (μ[fun ω => (U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω)) i *
            (U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω)) j | ℱ k]) ω ∂μ :=
          (integral_condExp (ℱ.le k)).symm
      _ = _ := integral_congr_ae hmix
  set gs : S → ℝ := fun s₀ => ∑ s, P θh s₀ s * ((U θh s - V θh s₀) i * (U θh s - V θh s₀) j)
    with hgs
  have hgsi : ∀ k, Integrable (fun ω => gs (ξ k ω)) μ := fun k =>
    (memLp_top_of_bound ((StronglyMeasurable.of_discrete (f := gs)).comp_measurable
      ((hξm k).mono (ℱ.le k) le_rfl)).aestronglyMeasurable (∑ s, |gs s|)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact single_le_sum (f := fun s => |gs s|) (fun _ _ => abs_nonneg _)
          (mem_univ _))).integrable le_top
  have hgs_eq : ∀ k, ∫ ω, gs (ξ k ω) ∂μ =
      ∑ s₀, gs s₀ * ∫ ω, {ω | ξ k ω = s₀}.indicator (fun _ => (1 : ℝ)) ω ∂μ := fun k => by
    have e : ∀ ω, gs (ξ k ω) = ∑ s₀, {ω | ξ k ω = s₀}.indicator (fun _ => (1 : ℝ)) ω * gs s₀ :=
      fun ω => by rw [sum_indicator_mul (σ := ξ) (k := k) ω (fun _ _ => 1) gs, one_mul]
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_finset_sum _ fun s₀ _ => (hIi k s₀).mul_const _]
    exact sum_congr rfl fun s₀ _ => by rw [integral_mul_const, mul_comm]
  have hgs_t : Tendsto (fun k => ∫ ω, gs (ξ k ω) ∂μ) atTop (𝓝 (∑ s₀, pst s₀ * gs s₀)) := by
    have h := tendsto_finset_sum (univ : Finset S) fun s₀ _ => (hlawc s₀).const_mul (gs s₀)
    rw [show ∑ s₀, gs s₀ * pst s₀ = ∑ s₀, pst s₀ * gs s₀ from
      sum_congr rfl fun _ _ => mul_comm _ _] at h
    exact h.congr fun k => (hgs_eq k).symm
  have hdiff : ∀ k, |(∫ ω, ∑ s, P (θ k ω) (ξ k ω) s * ((U (θ k ω) s - V (θ k ω) (ξ k ω)) i *
      (U (θ k ω) s - V (θ k ω) (ξ k ω)) j) ∂μ) - ∫ ω, gs (ξ k ω) ∂μ| ≤
      Lg * ∫ ω, ‖θ k ω - θh‖ ∂μ := fun k => by
    rw [← integral_sub (hentry k).1 (hgsi k), ← integral_const_mul]
    refine abs_integral_le_integral_abs.trans (integral_mono ((hentry k).1.sub (hgsi k)).abs
      ((hθi k).const_mul Lg) fun ω => ?_)
    exact abs_condCov_sub_le (ξ k ω) i j hCU hCV hUb hVb hUL hVL hP0 hP1 hPL
  have h0 : Tendsto (fun k => (∫ ω, ∑ s, P (θ k ω) (ξ k ω) s * ((U (θ k ω) s - V (θ k ω) (ξ k ω)) i
      * (U (θ k ω) s - V (θ k ω) (ξ k ω)) j) ∂μ) - ∫ ω, gs (ξ k ω) ∂μ) atTop (𝓝 0) :=
    squeeze_zero_norm (a := fun k => Lg * ∫ ω, ‖θ k ω - θh‖ ∂μ)
      (fun k => (Real.norm_eq_abs _).trans_le (hdiff k)) (by simpa using hθc.const_mul Lg)
  have := h0.add hgs_t
  simp only [sub_add_cancel, zero_add] at this
  refine this.congr fun k => ?_
  exact ((hentry k).2).symm


end Law

section Chain

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

set_option maxHeartbeats 8000000 in
/-- **Assumption 2.2 for θ-dependent sampling, with the covariance derived.** As
`tendsto_secondMoment_of_param_chain`, without the hypothesis on the noise covariance. Instead:
* the kernel at `θ*` is Doeblin, `P_{θ*} = α ν + (1 - α) Q`, with stationary law `π`;
* the kernels are Lipschitz at `θ*` in total variation;
* `U` is Lipschitz at `θ*`.

The covariance is then `Γ* = Σ_{s₀} π(s₀) Σ_s P_{θ*}(s₀, s) (U_{θ*} s - V_{θ*} s₀)(·)ᵀ`. -/
theorem tendsto_secondMoment_of_param_chain_doeblin {β : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hA : ∀ x, η₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d} {ξ : ℕ → Ω → S} {θh : E d}
    {f : E d → E d} {H U V : E d → S → E d} {P : E d → S → S → ℝ}
    {η K L CU CV LU LV CH LP α : ℝ} (h2η : βbar < 2 * η) (hK0 : 0 ≤ K) (hL : 0 ≤ L)
    (hdis : ∀ x, ⟪x - θh, f x⟫_ℝ ≤ -η * ‖x - θh‖ ^ 2) (hlin : ∀ x, ‖f x‖ ≤ K * ‖x - θh‖)
    (hf : ∀ x, ‖f x + matCLM A (x - θh)‖ ≤ L * ‖x - θh‖ ^ 2) (hfc : Continuous f)
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • H (θ k ω) (ξ (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    (hθ0 : ∃ C, ∀ ω, ‖θ 0 ω - θh‖ ≤ C)
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (θ k ω) (ξ k ω) s)
    (hpois : ∀ t s, U t s - V t s = H t s - f t) (hV : ∀ t s, V t s = ∑ s', P t s s' • U t s')
    (hCU : 0 ≤ CU) (hCV : 0 ≤ CV)
    (hUc : ∀ s, Continuous fun t => U t s) (hUb : ∀ t s, ‖U t s‖ ≤ CU)
    (hUL : ∀ t s, ‖U t s - U θh s‖ ≤ LU * ‖t - θh‖)
    (hVb : ∀ t s, ‖V t s‖ ≤ CV) (hVL : ∀ t t' s, ‖V t s - V t' s‖ ≤ LV * ‖t - t'‖)
    (hHb : ∀ t s, ‖H t s‖ ≤ CH)
    {ν : S → ℝ} {Q : S → S → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hQ0 : ∀ s s', 0 ≤ Q s s') (hQ1 : ∀ s, ∑ s', Q s s' = 1)
    (hPh : ∀ s s', P θh s s' = α * ν s' + (1 - α) * Q s s')
    (hP0 : ∀ s s', 0 ≤ P θh s s') (hP1 : ∀ s, ∑ s', P θh s s' = 1)
    (hPL : ∀ t s, ∑ s', |P t s s' - P θh s s'| ≤ LP * ‖t - θh‖)
    {pst : S → ℝ} (hpst : ∀ s', ∑ s, pst s * P θh s s' = pst s') (hpst1 : ∑ s, pst s = 1) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig =
        (EuclideanSpace.equiv (Fin d × Fin d) ℝ).symm (fun ij => ∑ s₀, pst s₀ *
          ∑ s, P θh s₀ s * ((U θh s - V θh s₀) ij.1 * (U θh s - V θh s₀) ij.2)) ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (fun ω => θ k ω - θh)) atTop (𝓝 Sig) := by
  obtain ⟨hθ', hhm, hrm, ⟨Cr, hrb⟩, hMm, hMb, hmart⟩ := param_chain_decomp (μ := μ) hβ ℱ hθ hθm
    hξm hlaw hpois hV hUc hUb hVb hVL hHb
  obtain ⟨hbd, W₄, h4⟩ := moment_bounds_of_dissipative_markov hβ ℱ h2η hK0 hdis hlin hfc hθ'
    hθm hθ0 hhm (fun k ω => hVb _ _) hrm hrb hMm hMb hmart
  have hθsm : ∀ k, StronglyMeasurable[ℱ k] (fun ω => θ k ω - θh) := fun k =>
    (hθm k).sub stronglyMeasurable_const
  have hθi : ∀ k, Integrable (fun ω => ‖θ k ω - θh‖) μ := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    exact (memLp_top_of_bound (((hθsm k).mono (ℱ.le k)).aestronglyMeasurable.norm) C
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hC ω)).integrable le_top
  have hθ4i : ∀ k, Integrable (fun ω => ‖θ k ω - θh‖ ^ 4) μ := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    exact (memLp_top_of_bound (((hθsm k).mono (ℱ.le k)).aestronglyMeasurable.norm.pow 4) (C ^ 4)
      (Eventually.of_forall fun ω => by
        show ‖‖θ k ω - θh‖ ^ 4‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) 4)).integrable le_top
  have hθc := tendsto_integral_norm_of_four (X := fun k ω => θ k ω - θh) hβ.tendsto_zero hθi
    hθ4i h4
  have hVc : ∀ s, Continuous fun t => V t s := fun s =>
    continuous_of_lipschitz_bound (fun t t' => hVL t t' s)
  have hlawc := tendsto_law_moving (μ := μ) ℱ hξm hlaw hα0 hα1 hQ0 hQ1 hPh hPL hpst hpst1 hθi hθc
  have hΓ := tendsto_secondMoment_paramM (μ := μ) ℱ hθm hξm hlaw hCU hCV hUc hVc hUb hVb hUL
    (fun t s => hVL t θh s) hP0 hP1 hPL hlawc hθi hθc
  exact tendsto_secondMoment_of_dissipative_markov hβ A hη₀ hA ℱ h2η hK0 hL hdis hlin hf hfc hθ'
    hθm hθ0 hhm (fun k ω => hVb _ _) hrm hrb hMm hMb hmart hΓ

set_option maxHeartbeats 8000000 in
/-- **Assumption 2.2 for θ-dependent Doeblin sampling, from the model.** As
`tendsto_secondMoment_of_doeblin_chain`, without the hypothesis on the noise covariance: the
covariance of the martingale part converges to
`Γ* = Σ_{s₀} π_{θ*}(s₀) Σ_s P_{θ*}(s₀, s) (U_{θ*} s - V_{θ*} s₀)(·)ᵀ`, for the Poisson pair
`doeblinU`, `doeblinV`. -/
theorem tendsto_secondMoment_of_doeblin_chain_auto {β : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hA : ∀ x, η₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d} {ξ : ℕ → Ω → S} {θh : E d}
    {f : E d → E d} {H : E d → S → E d} {α : ℝ} {ν : E d → S → ℝ} {Q : E d → S → S → ℝ}
    {ρ : E d → S → ℝ} {η K L CH LH LQ Lν : ℝ} (h2η : βbar < 2 * η) (hK0 : 0 ≤ K) (hL : 0 ≤ L)
    (hdis : ∀ x, ⟪x - θh, f x⟫_ℝ ≤ -η * ‖x - θh‖ ^ 2) (hlin : ∀ x, ‖f x‖ ≤ K * ‖x - θh‖)
    (hf : ∀ x, ‖f x + matCLM A (x - θh)‖ ≤ L * ‖x - θh‖ ^ 2) (hfc : Continuous f)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (hν0 : ∀ t s, 0 ≤ ν t s) (hν1 : ∀ t, ∑ s, ν t s = 1)
    (hCH : 0 ≤ CH) (hLH : 0 ≤ LH) (hLQ : 0 ≤ LQ) (hLν : 0 ≤ Lν)
    (hHb : ∀ t s, ‖H t s‖ ≤ CH) (hHL : ∀ t t' s, ‖H t s - H t' s‖ ≤ LH * ‖t - t'‖)
    (hQL : ∀ t t' s, ∑ s', |Q t s s' - Q t' s s'| ≤ LQ * ‖t - t'‖)
    (hνL : ∀ t t', ∑ s, |ν t s - ν t' s| ≤ Lν * ‖t - t'‖)
    (hρ : ∀ t s', ∑ s, ρ t s * (α * ν t s' + (1 - α) * Q t s s') = ρ t s')
    (hρ1 : ∀ t, ∑ s, ρ t s = 1) (hfρ : ∀ t, f t = ∑ s, ρ t s • H t s)
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • H (θ k ω) (ξ (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    (hθ0 : ∃ C, ∀ ω, ‖θ 0 ω - θh‖ ≤ C)
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => α * ν (θ k ω) s + (1 - α) * Q (θ k ω) (ξ k ω) s) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig =
        (EuclideanSpace.equiv (Fin d × Fin d) ℝ).symm (fun ij => ∑ s₀, ρ θh s₀ *
          ∑ s, (α * ν θh s + (1 - α) * Q θh s₀ s) *
            ((doeblinU α Q H θh s - doeblinV α ν Q H θh s₀) ij.1 *
              (doeblinU α Q H θh s - doeblinV α ν Q H θh s₀) ij.2)) ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (fun ω => θ k ω - θh)) atTop (𝓝 Sig) := by
  have hfeq : ∀ t, doeblinF α ν Q H t = f t := fun t => by
    rw [hfρ t]; exact doeblinF_eq_mean hα0 hα1 hQ0 hQ1 t (hρ t) (hρ1 t)
  have hUL := norm_doeblinU_sub_le (H := H) hα0 hα1 hQ0 hQ1 hCH hLH hLQ hHb hHL hQL
  have hPL : ∀ t s, ∑ s', |(α * ν t s' + (1 - α) * Q t s s') - (α * ν θh s' + (1 - α) * Q θh s s')|
      ≤ (α * Lν + (1 - α) * LQ) * ‖t - θh‖ := fun t s => by
    have h1 : ∀ s', |(α * ν t s' + (1 - α) * Q t s s') - (α * ν θh s' + (1 - α) * Q θh s s')| ≤
        α * |ν t s' - ν θh s'| + (1 - α) * |Q t s s' - Q θh s s'| := fun s' => by
      rw [show (α * ν t s' + (1 - α) * Q t s s') - (α * ν θh s' + (1 - α) * Q θh s s') =
        α * (ν t s' - ν θh s') + (1 - α) * (Q t s s' - Q θh s s') by ring]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
        rw [abs_mul, abs_of_nonneg (by linarith)]
    calc _ ≤ ∑ s', (α * |ν t s' - ν θh s'| + (1 - α) * |Q t s s' - Q θh s s'|) :=
          sum_le_sum fun s' _ => h1 s'
      _ = α * ∑ s', |ν t s' - ν θh s'| + (1 - α) * ∑ s', |Q t s s' - Q θh s s'| := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ α * (Lν * ‖t - θh‖) + (1 - α) * (LQ * ‖t - θh‖) :=
          add_le_add (mul_le_mul_of_nonneg_left (hνL t θh) hα0.le)
            (mul_le_mul_of_nonneg_left (hQL t θh s) (by linarith))
      _ = _ := by ring
  refine tendsto_secondMoment_of_param_chain_doeblin hβ A hη₀ hA ℱ (U := doeblinU α Q H)
    (V := doeblinV α ν Q H) (P := fun t s s' => α * ν t s' + (1 - α) * Q t s s')
    h2η hK0 hL hdis hlin hf hfc hθ hθm hξm hθ0 hlaw ?_ (doeblinV_eq hα0 hα1 hQ0 hQ1)
    (div_nonneg hCH hα0.le) (by positivity)
    (fun s => continuous_of_lipschitz_bound (F := fun t => doeblinU α Q H t s)
      (fun t t' => (norm_le_pi_norm (doeblinU α Q H t - doeblinU α Q H t') s).trans (hUL t t')))
    (fun t s => (norm_le_pi_norm _ s).trans (norm_doeblinU_le hα0 hα1 hQ0 hQ1 hCH hHb t))
    (fun t s => (norm_le_pi_norm (doeblinU α Q H t - doeblinU α Q H θh) s).trans (hUL t θh))
    (norm_doeblinV_le hα0 hα1 hQ0 hQ1 hν0 hν1 hCH hHb)
    (norm_doeblinV_sub_le hα0 hα1 hQ0 hQ1 hν0 hν1 hCH hLH hLQ hLν hHb hHL hQL hνL) hHb
    (ν := ν θh) (Q := Q θh) hα0 hα1 (hQ0 θh) (hQ1 θh) (fun s s' => rfl)
    (fun s s' => add_nonneg (mul_nonneg hα0.le (hν0 _ _)) (mul_nonneg (by linarith) (hQ0 _ _ _)))
    (fun s => by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hν1, hQ1]; ring) hPL (hρ θh) (hρ1 θh)
  intro t s
  rw [doeblinV, hfeq]
  abel

end Chain

end StochasticApproximation
