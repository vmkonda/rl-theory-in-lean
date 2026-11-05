/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.OrthogonalNoise

/-!
# Shorter traces give smaller noise: the second moments of the centered trace

Theorem 4.7 of `docs/actor-critic-rates.md`. With the tabular TD(`λ`) critic, the actor-critic
noise is `N(0) + δ_{k+1} W_k`, where `W_k = X_{λ,k} - b(s_k)` is the centered critic trace. It
satisfies the one-step recursion
`W_{k+1} = λ (ε_{k+1} + c_{k+1} W_k)`, with `ε_{k+1} = c_{k+1}(ψ_k + b(s_k)) - b(s_{k+1})`
a function of the next observation: the first increment of the lookback martingale.

With respect to the pre-action filtration, the law of the next observation depends on the past
only through the state (`StateDriven`). Then:
* the state-conditioned first moments `E[W_k 1{s_k = s}]` tend to `0`, when `b` is the stationary
  conditional mean of the carried trace;
* the state-conditioned second moments `C_k(s) = E[W_k W_kᵀ 1{s_k = s}]` converge to a solution of
  `C = λ² (Ē + 𝒯 C)`, where `Ē(s) = E[ε εᵀ 1{s_k = s}]` and
  `(𝒯 C)(s) = Σ_{s'} E[c² 1{s_{k+1} = s} | s_k = s'] C(s')` (`tendsto_lookback_moments`);
* such solutions are positive semidefinite and nondecreasing in `λ` in the Loewner order
  (`nonneg_of_fixed`, `mono_of_fixed`): unrolled, `C = Σ_n λ^{2(n+1)} 𝒯ⁿ Ē`, the sum
  `Σ_i λ^{2i} Δ_i` of Theorem 4.7.

So the extra noise covariance `Γ_D(λ) = Σ_s E[δ² | s] C_λ(s)` is nondecreasing in `λ`
(`lookback_covariance_mono`).
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory

namespace StochasticApproximation

/-! ### Positivity and monotonicity of the fixed point -/

section Fixed

variable {S : Type*} [Fintype S]

/-- **Positivity.** If `q = κ 𝒯 q + f` with `f ≥ 0`, `𝒯 ≥ 0` with row sums at most `ρ < 1`, and
`0 ≤ κ ≤ 1`, then `q ≥ 0`. The negative parts satisfy `N ≤ κ ρ N`. -/
lemma nonneg_of_fixed {p : S → S → ℝ} {ρ κ : ℝ} (hp : ∀ s t, 0 ≤ p s t)
    (hρ : ∀ s, ∑ t, p s t ≤ ρ) (hρ1 : ρ < 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {q f : S → ℝ}
    (hf : ∀ t, 0 ≤ f t) (hq : ∀ t, q t = κ * ∑ s, p s t * q s + f t) (t : S) : 0 ≤ q t := by
  set N := ∑ t, max (-q t) 0 with hN
  have h1 : ∀ t, max (-q t) 0 ≤ κ * ∑ s, p s t * max (-q s) 0 := fun t => by
    have hR : 0 ≤ κ * ∑ s, p s t * max (-q s) 0 :=
      mul_nonneg hκ0 (sum_nonneg fun s _ => mul_nonneg (hp s t) (le_max_right _ _))
    refine max_le ?_ hR
    have h2 : -(∑ s, p s t * q s) ≤ ∑ s, p s t * max (-q s) 0 := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun s _ => by
        have := mul_le_mul_of_nonneg_left (le_max_left (-q s) 0) (hp s t)
        linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hκ0
    rw [hq t]
    linarith [hf t]
  have hN0 : 0 ≤ N := sum_nonneg fun _ _ => le_max_right _ _
  have hrow : 0 ≤ ∑ s, (∑ t, p s t) * max (-q s) 0 :=
    sum_nonneg fun s _ => mul_nonneg (sum_nonneg fun t _ => hp s t) (le_max_right _ _)
  have h4 : N ≤ ρ * N := by
    calc N ≤ ∑ t, κ * ∑ s, p s t * max (-q s) 0 := sum_le_sum fun t _ => h1 t
      _ = κ * ∑ s, (∑ t, p s t) * max (-q s) 0 := by
          rw [← mul_sum, sum_comm]
          exact congrArg _ (sum_congr rfl fun s _ => by rw [sum_mul])
      _ ≤ 1 * ∑ s, (∑ t, p s t) * max (-q s) 0 := mul_le_mul_of_nonneg_right hκ1 hrow
      _ ≤ ∑ s, ρ * max (-q s) 0 := by
          rw [one_mul]
          exact sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hρ s) (le_max_right _ _)
      _ = ρ * N := by rw [← mul_sum]
  have hN' : N = 0 := by nlinarith
  have h5 := (sum_eq_zero_iff_of_nonneg fun t _ => le_max_right (-q t) 0).mp hN' t (mem_univ t)
  have h6 := le_max_left (-q t) 0
  linarith

/-- **Monotonicity in `λ`.** If `q_i = λ_i² (e + 𝒯 q_i)` with `e ≥ 0` and `0 ≤ λ₁ ≤ λ₂ ≤ 1`, then
`0 ≤ q₁ ≤ q₂`. The difference solves the same equation with forcing
`(λ₂² - λ₁²)(e + 𝒯 q₂) ≥ 0`. -/
lemma mono_of_fixed {p : S → S → ℝ} {ρ : ℝ} (hp : ∀ s t, 0 ≤ p s t)
    (hρ : ∀ s, ∑ t, p s t ≤ ρ) (hρ1 : ρ < 1) {e q₁ q₂ : S → ℝ} {l₁ l₂ : ℝ} (hl0 : 0 ≤ l₁)
    (hl12 : l₁ ≤ l₂) (hl2 : l₂ ≤ 1) (he : ∀ t, 0 ≤ e t)
    (h₁ : ∀ t, q₁ t = l₁ ^ 2 * (e t + ∑ s, p s t * q₁ s))
    (h₂ : ∀ t, q₂ t = l₂ ^ 2 * (e t + ∑ s, p s t * q₂ s)) (t : S) :
    0 ≤ q₁ t ∧ q₁ t ≤ q₂ t := by
  have hl₁1 : l₁ ^ 2 ≤ 1 := by nlinarith
  have hl₂1 : l₂ ^ 2 ≤ 1 := by nlinarith
  have hq₂ : ∀ t, 0 ≤ q₂ t := nonneg_of_fixed hp hρ hρ1 (sq_nonneg l₂) hl₂1
    (f := fun t => l₂ ^ 2 * e t) (fun t => mul_nonneg (sq_nonneg _) (he t))
    (fun t => by rw [h₂ t]; ring)
  have hq₁ : 0 ≤ q₁ t := nonneg_of_fixed hp hρ hρ1 (sq_nonneg l₁) hl₁1
    (f := fun t => l₁ ^ 2 * e t) (fun t => mul_nonneg (sq_nonneg _) (he t))
    (fun t => by rw [h₁ t]; ring) t
  have hsq : l₁ ^ 2 ≤ l₂ ^ 2 := pow_le_pow_left₀ hl0 hl12 2
  have hD := nonneg_of_fixed hp hρ hρ1 (sq_nonneg l₁) hl₁1 (q := fun t => q₂ t - q₁ t)
    (f := fun t => (l₂ ^ 2 - l₁ ^ 2) * (e t + ∑ s, p s t * q₂ s))
    (fun t => mul_nonneg (by linarith)
      (add_nonneg (he t) (sum_nonneg fun s _ => mul_nonneg (hp s t) (hq₂ s))))
    (fun t => by
      simp only
      rw [h₁ t, h₂ t]
      simp only [mul_sub, sum_sub_distrib]
      ring) t
  exact ⟨hq₁, by linarith⟩

end Fixed

/-! ### The moments of the centered trace along the process -/

section Process

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : MeasureTheory.Filtration ℕ m0}
  {S X : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  {σ : ℕ → Ω → S} {ξ : ℕ → Ω → X} {P : S → X → ℝ}

omit [DecidableEq S] in
/-- A bounded known weight against a function of the next observation:
`E[w F(ξ_{k+1})] = Σ_s (Σ_x P(s, x) F(x)) E[w 1{σ_k = s}]`. -/
lemma StateDriven.integral_weight_obs (hσ : StateDriven μ ℱ σ ξ P) {k : ℕ} {w : Ω → ℝ}
    (hw : StronglyMeasurable[ℱ k] w) (hwB : ∃ C, ∀ ω, |w ω| ≤ C) (F : X → ℝ) :
    ∫ ω, w ω * F (ξ (k + 1) ω) ∂μ =
      ∑ s, (∑ x, P s x * F x) * ∫ ω, {ω | σ k ω = s}.indicator w ω ∂μ := by
  obtain ⟨C, hC⟩ := hwB
  rw [hσ.integral_mul hw ⟨C, hC⟩ F]
  have e : ∀ ω, w ω * ∑ x, P (σ k ω) x * F x =
      ∑ s, {ω | σ k ω = s}.indicator w ω * (∑ x, P s x * F x) := fun ω =>
    (sum_indicator_mul (σ := σ) ω (fun _ => w) (fun s => ∑ x, P s x * F x)).symm
  rw [integral_congr_ae (Eventually.of_forall e)]
  have hset : ∀ s, MeasurableSet[ℱ k] {ω | σ k ω = s} := fun s =>
    hσ.state k (measurableSet_singleton s)
  have hIi : ∀ s, Integrable ({ω | σ k ω = s}.indicator w) μ := fun s =>
    (memLp_top_of_bound (((hw.indicator (hset s)).mono (ℱ.le k)).aestronglyMeasurable) C
      (Eventually.of_forall fun ω => (norm_indicator_le_norm_self w ω).trans
        (by rw [Real.norm_eq_abs]; exact hC ω))).integrable le_top
  rw [integral_finset_sum _ fun s _ => (hIi s).mul_const _]
  exact sum_congr rfl fun s _ => by rw [integral_mul_const, mul_comm]

set_option maxHeartbeats 4000000 in
/-- **The moments of the centered trace.** Let `W_{k+1} = λ (ε(ξ_{k+1}) + c(ξ_{k+1}) W_k)` with
`W_k` bounded and known at time `k`, the state `σ_{k+1} = ŝ(ξ_{k+1})`, `0 ≤ c ≤ 1`, and
`Σ_x P(s, x) c(x) ≤ ρ < 1`. Suppose the law of the state converges to `ν`, and `ε` is centered
in stationarity: `Σ_{s'} ν(s') E[ε 1{ŝ = s} | s'] = 0`. Then:
* `E[W_k 1{σ_k = s}] → 0`;
* `E[W_k W_kᵀ 1{σ_k = s}] → C(s)`, where `C = λ² (Ē + 𝒯 C)` with
  `Ē(s) = Σ_{s'} ν(s') E[ε εᵀ 1{ŝ = s} | s']` and `𝒯(s', s) = E[c² 1{ŝ = s} | s']`. -/
theorem StateDriven.tendsto_lookback_moments (hσ : StateDriven μ ℱ σ ξ P)
    {n : ℕ} {ŝ : X → S} {ĉ : X → ℝ} {ε : X → E n} {lam ρ : ℝ} {W : ℕ → Ω → E n} {ν : S → ℝ}
    (hσξ : ∀ k ω, σ (k + 1) ω = ŝ (ξ (k + 1) ω))
    (hP0 : ∀ s x, 0 ≤ P s x) (hc0 : ∀ x, 0 ≤ ĉ x) (hc1 : ∀ x, ĉ x ≤ 1)
    (hρ : ∀ s, ∑ x, P s x * ĉ x ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1)
    (hW : ∀ k ω, W (k + 1) ω = lam • (ε (ξ (k + 1) ω) + ĉ (ξ (k + 1) ω) • W k ω))
    (hWm : ∀ k, StronglyMeasurable[ℱ k] (W k)) (hWB : ∀ k, ∃ C, ∀ ω, ‖W k ω‖ ≤ C)
    (hlaw : ∀ s, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ)
      atTop (𝓝 (ν s)))
    (hcent : ∀ s j, ∑ s', ν s' * ∑ x, P s' x * ((if ŝ x = s then 1 else 0) * ε x j) = 0) :
    (∀ s j, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator (fun ω => W k ω j) ω ∂μ) atTop
      (𝓝 0)) ∧
    ∃ C : S → Fin n → Fin n → ℝ,
      (∀ s i j, C s i j = lam ^ 2 * (∑ s', ν s' * ∑ x, P s' x *
          ((if ŝ x = s then 1 else 0) * (ε x i * ε x j))
        + ∑ s', (∑ x, P s' x * ((if ŝ x = s then 1 else 0) * ĉ x ^ 2)) * C s' i j)) ∧
      ∀ s i j, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator
        (fun ω => W k ω i * W k ω j) ω ∂μ) atTop (𝓝 (C s i j)) := by
  set ind : S → X → ℝ := fun s x => if ŝ x = s then 1 else 0 with hind
  have hind_sum : ∀ x, ∑ s, ind s x = 1 := fun x => by simp [hind]
  have hsumind : ∀ (g : X → ℝ) s', ∑ s, ∑ x, P s' x * (ind s x * g x) = ∑ x, P s' x * g x :=
    fun g s' => by
      rw [sum_comm]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_sum, ← sum_mul, hind_sum, one_mul]
  -- the indicator at `k + 1` is a function of the observation
  have hsucc : ∀ k s (g : Ω → ℝ), ∫ ω, {ω | σ (k + 1) ω = s}.indicator g ω ∂μ =
      ∫ ω, ind s (ξ (k + 1) ω) * g ω ∂μ := fun k s g => by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hind, Set.indicator_apply, Set.mem_setOf_eq, hσξ k ω]
    split_ifs <;> simp
  have hcoord : ∀ k j, StronglyMeasurable[ℱ k] fun ω => W k ω j := fun k j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_stronglyMeasurable (hWm k)
  have hcb : ∀ k j, ∃ C, ∀ ω, |W k ω j| ≤ C := fun k j => by
    obtain ⟨C, hC⟩ := hWB k
    exact ⟨C, fun ω => by rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le _ j).trans (hC ω)⟩
  have hcb2 : ∀ k i j, ∃ C, ∀ ω, |W k ω i * W k ω j| ≤ C := fun k i j => by
    obtain ⟨C₁, hC₁⟩ := hcb k i
    obtain ⟨C₂, hC₂⟩ := hcb k j
    exact ⟨C₁ * C₂, fun ω => by
      rw [abs_mul]; exact mul_le_mul (hC₁ ω) (hC₂ ω) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ ω))⟩
  have hone : ∀ k, StronglyMeasurable[ℱ k] (fun _ : Ω => (1 : ℝ)) := fun _ =>
    stronglyMeasurable_const
  have hone_b : ∃ C, ∀ ω : Ω, |(fun _ : Ω => (1 : ℝ)) ω| ≤ C := ⟨1, fun _ => by simp⟩
  have hInt : ∀ k (w : Ω → ℝ) (F : X → ℝ), StronglyMeasurable[ℱ k] w → (∃ C, ∀ ω, |w ω| ≤ C) →
      Integrable (fun ω => w ω * F (ξ (k + 1) ω)) μ := fun k w F hw ⟨C, hC⟩ =>
    (hσ.integrable_obs F k).bdd_mul (hw.mono (ℱ.le k)).aestronglyMeasurable
      ⟨C, fun ω => by rw [Real.norm_eq_abs]; exact hC ω⟩
  have hWj : ∀ k ω j, W (k + 1) ω j = lam * (ε (ξ (k + 1) ω) j + ĉ (ξ (k + 1) ω) * W k ω j) :=
    fun k ω j => by rw [hW k ω]; simp [smul_eq_mul]
  -- the moments
  set νk : ℕ → S → ℝ := fun k s => ∫ ω, {ω | σ k ω = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ
    with hνk
  set m : ℕ → Fin n → S → ℝ := fun k j s =>
    ∫ ω, {ω | σ k ω = s}.indicator (fun ω => W k ω j) ω ∂μ with hm
  set p₁ : S → S → ℝ := fun s' s => ∑ x, P s' x * (ind s x * ĉ x) with hp₁
  set p₂ : S → S → ℝ := fun s' s => ∑ x, P s' x * (ind s x * ĉ x ^ 2) with hp₂
  have hind0 : ∀ s x, 0 ≤ ind s x := fun s x => by simp only [hind]; split_ifs <;> norm_num
  have hp₁0 : ∀ s' s, 0 ≤ p₁ s' s := fun s' s =>
    sum_nonneg fun x _ => mul_nonneg (hP0 _ _) (mul_nonneg (hind0 _ _) (hc0 x))
  have hp₂0 : ∀ s' s, 0 ≤ p₂ s' s := fun s' s =>
    sum_nonneg fun x _ => mul_nonneg (hP0 _ _) (mul_nonneg (hind0 _ _) (sq_nonneg _))
  have hPc0 : ∀ s', 0 ≤ ∑ x, P s' x * ĉ x := fun s' =>
    sum_nonneg fun x _ => mul_nonneg (hP0 _ _) (hc0 x)
  have hp₁ρ : ∀ s', ∑ s, p₁ s' s * |(fun _ : S => lam) s| ≤ ρ := fun s' => by
    simp only [abs_of_nonneg hlam0]
    rw [← sum_mul, hsumind ĉ s']
    calc (∑ x, P s' x * ĉ x) * lam ≤ (∑ x, P s' x * ĉ x) * 1 :=
          mul_le_mul_of_nonneg_left hlam1 (hPc0 s')
      _ ≤ ρ := by rw [mul_one]; exact hρ s'
  have hp₂ρ : ∀ s', ∑ s, p₂ s' s * |(fun _ : S => lam ^ 2) s| ≤ ρ := fun s' => by
    simp only [abs_of_nonneg (sq_nonneg lam)]
    rw [← sum_mul, hsumind (fun x => ĉ x ^ 2) s']
    have h1 : ∑ x, P s' x * ĉ x ^ 2 ≤ ∑ x, P s' x * ĉ x := sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (by nlinarith [hc0 x, hc1 x]) (hP0 _ _)
    have h2 : lam ^ 2 ≤ 1 := by nlinarith
    have h3 : 0 ≤ ∑ x, P s' x * ĉ x ^ 2 :=
      sum_nonneg fun x _ => mul_nonneg (hP0 _ _) (sq_nonneg _)
    calc (∑ x, P s' x * ĉ x ^ 2) * lam ^ 2 ≤ (∑ x, P s' x * ĉ x ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ ρ := by rw [mul_one]; linarith [hρ s']
  -- first moments: `m_{k+1} = λ 𝒯₁ m_k + λ (forcing)`
  have hrec₁ : ∀ j k s, m (k + 1) j s = transfer p₁ (fun _ => lam) (m k j) s
      + lam * ∑ s', (∑ x, P s' x * (ind s x * ε x j)) * νk k s' := fun j k s => by
    have e1 : ∫ ω, {ω | σ (k + 1) ω = s}.indicator (fun ω => W (k + 1) ω j) ω ∂μ =
        ∫ ω, (lam * (ind s (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j)
          + lam * (W k ω j * (ind s (ξ (k + 1) ω) * ĉ (ξ (k + 1) ω)))) ∂μ := by
      rw [hsucc]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hWj]
      ring
    have A1 : Integrable (fun ω => lam * (ind s (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j)) μ :=
      (hσ.integrable_obs (fun x => ind s x * ε x j) k).const_mul lam
    have A2 : Integrable (fun ω => lam * (W k ω j * (ind s (ξ (k + 1) ω) * ĉ (ξ (k + 1) ω)))) μ :=
      (hInt k _ (fun x => ind s x * ĉ x) (hcoord k j) (hcb k j)).const_mul lam
    have w1 : ∫ ω, ind s (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j ∂μ =
        ∑ s', (∑ x, P s' x * (ind s x * ε x j)) * νk k s' :=
      (integral_congr_ae (Eventually.of_forall fun ω => by simp only [one_mul])).trans
        (hσ.integral_weight_obs (hone k) hone_b (fun x => ind s x * ε x j))
    have w2 : ∫ ω, W k ω j * (ind s (ξ (k + 1) ω) * ĉ (ξ (k + 1) ω)) ∂μ =
        ∑ s', (∑ x, P s' x * (ind s x * ĉ x)) * m k j s' :=
      hσ.integral_weight_obs (hcoord k j) (hcb k j) (fun x => ind s x * ĉ x)
    show ∫ ω, {ω | σ (k + 1) ω = s}.indicator (fun ω => W (k + 1) ω j) ω ∂μ = _
    rw [e1, integral_add A1 A2, integral_const_mul, integral_const_mul, w1, w2]
    simp only [transfer, hp₁]
    ring
  have hm0 : ∀ s j, Tendsto (fun k => m k j s) atTop (𝓝 0) := by
    intro s j
    have hb : ∀ s, Tendsto (fun k => lam * ∑ s', (∑ x, P s' x * (ind s x * ε x j)) * νk k s')
        atTop (𝓝 (lam * ∑ s', (∑ x, P s' x * (ind s x * ε x j)) * ν s')) := fun s =>
      (tendsto_finset_sum _ fun s' _ => (hlaw s').const_mul _).const_mul _
    obtain ⟨xl, hxl, hconv⟩ := tendsto_affine_transfer hp₁0 hp₁ρ hρ0 hρ1
      (x := fun k s => m k j s) (fun k s => hrec₁ j k s) hb
    have hbl : ∀ s, lam * ∑ s', (∑ x, P s' x * (ind s x * ε x j)) * ν s' = 0 := fun s => by
      have := hcent s j
      rw [show ∑ s', (∑ x, P s' x * (ind s x * ε x j)) * ν s' =
        ∑ s', ν s' * ∑ x, P s' x * ((if ŝ x = s then 1 else 0) * ε x j) from
          sum_congr rfl fun s' _ => mul_comm _ _, this, mul_zero]
    have hfix : ∀ y', xl y' = transfer p₁ (fun _ => lam) xl y' := fun y' => by
      rw [hxl y', hbl y', add_zero]
    have hl1 := l1_transfer_le hp₁0 hp₁ρ xl
    have hsum : ∑ y, |xl y| ≤ ρ * ∑ y, |xl y| := by
      calc ∑ y, |xl y| = ∑ y', |transfer p₁ (fun _ => lam) xl y'| :=
            sum_congr rfl fun y _ => by rw [← hfix y]
        _ ≤ _ := hl1
    have h0 : ∑ y, |xl y| = 0 := by
      have := sum_nonneg fun y (_ : y ∈ univ) => abs_nonneg (xl y)
      nlinarith
    have hxs : xl s = 0 :=
      abs_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun y _ => abs_nonneg (xl y)).mp h0 s
        (mem_univ s))
    simpa [hxs] using hconv s
  refine ⟨hm0, ?_⟩
  -- second moments: `c_{k+1} = λ² 𝒯₂ c_k + λ² (forcing)`
  set c2 : Fin n → Fin n → ℕ → S → ℝ := fun i j k s =>
    ∫ ω, {ω | σ k ω = s}.indicator (fun ω => W k ω i * W k ω j) ω ∂μ with hc2
  have hrec₂ : ∀ i j k s, c2 i j (k + 1) s = transfer p₂ (fun _ => lam ^ 2) (c2 i j k) s
      + lam ^ 2 * (∑ s', (∑ x, P s' x * (ind s x * (ε x i * ε x j))) * νk k s'
        + ∑ s', (∑ x, P s' x * (ind s x * (ĉ x * ε x j))) * m k i s'
        + ∑ s', (∑ x, P s' x * (ind s x * (ĉ x * ε x i))) * m k j s') := fun i j k s => by
    have e1 : ∫ ω, {ω | σ (k + 1) ω = s}.indicator (fun ω => W (k + 1) ω i * W (k + 1) ω j) ω ∂μ
        = ∫ ω, (lam ^ 2 * (ind s (ξ (k + 1) ω) * (ε (ξ (k + 1) ω) i * ε (ξ (k + 1) ω) j))
          + lam ^ 2 * (W k ω i * (ind s (ξ (k + 1) ω) * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j)))
          + lam ^ 2 * (W k ω j * (ind s (ξ (k + 1) ω) * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) i)))
          + lam ^ 2 * (W k ω i * W k ω j * (ind s (ξ (k + 1) ω) * ĉ (ξ (k + 1) ω) ^ 2))) ∂μ := by
      rw [hsucc]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hWj]
      ring
    have B1 : Integrable (fun ω => lam ^ 2 * (ind s (ξ (k + 1) ω)
        * (ε (ξ (k + 1) ω) i * ε (ξ (k + 1) ω) j))) μ :=
      (hσ.integrable_obs (fun x => ind s x * (ε x i * ε x j)) k).const_mul _
    have B2 : Integrable (fun ω => lam ^ 2 * (W k ω i * (ind s (ξ (k + 1) ω)
        * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j)))) μ :=
      (hInt k _ (fun x => ind s x * (ĉ x * ε x j)) (hcoord k i) (hcb k i)).const_mul _
    have B3 : Integrable (fun ω => lam ^ 2 * (W k ω j * (ind s (ξ (k + 1) ω)
        * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) i)))) μ :=
      (hInt k _ (fun x => ind s x * (ĉ x * ε x i)) (hcoord k j) (hcb k j)).const_mul _
    have B4 : Integrable (fun ω => lam ^ 2 * (W k ω i * W k ω j
        * (ind s (ξ (k + 1) ω) * ĉ (ξ (k + 1) ω) ^ 2))) μ :=
      (hInt k _ (fun x => ind s x * ĉ x ^ 2) ((hcoord k i).mul (hcoord k j))
        (hcb2 k i j)).const_mul _
    have B12 : Integrable (fun ω => lam ^ 2 * (ind s (ξ (k + 1) ω)
        * (ε (ξ (k + 1) ω) i * ε (ξ (k + 1) ω) j)) + lam ^ 2 * (W k ω i * (ind s (ξ (k + 1) ω)
        * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j)))) μ := B1.add B2
    have B123 : Integrable (fun ω => lam ^ 2 * (ind s (ξ (k + 1) ω)
        * (ε (ξ (k + 1) ω) i * ε (ξ (k + 1) ω) j)) + lam ^ 2 * (W k ω i * (ind s (ξ (k + 1) ω)
        * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j))) + lam ^ 2 * (W k ω j * (ind s (ξ (k + 1) ω)
        * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) i)))) μ := B12.add B3
    have w1 : ∫ ω, ind s (ξ (k + 1) ω) * (ε (ξ (k + 1) ω) i * ε (ξ (k + 1) ω) j) ∂μ =
        ∑ s', (∑ x, P s' x * (ind s x * (ε x i * ε x j))) * νk k s' :=
      (integral_congr_ae (Eventually.of_forall fun ω => by simp only [one_mul])).trans
        (hσ.integral_weight_obs (hone k) hone_b (fun x => ind s x * (ε x i * ε x j)))
    have w2 : ∫ ω, W k ω i * (ind s (ξ (k + 1) ω) * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) j)) ∂μ =
        ∑ s', (∑ x, P s' x * (ind s x * (ĉ x * ε x j))) * m k i s' :=
      hσ.integral_weight_obs (hcoord k i) (hcb k i) (fun x => ind s x * (ĉ x * ε x j))
    have w3 : ∫ ω, W k ω j * (ind s (ξ (k + 1) ω) * (ĉ (ξ (k + 1) ω) * ε (ξ (k + 1) ω) i)) ∂μ =
        ∑ s', (∑ x, P s' x * (ind s x * (ĉ x * ε x i))) * m k j s' :=
      hσ.integral_weight_obs (hcoord k j) (hcb k j) (fun x => ind s x * (ĉ x * ε x i))
    have w4 : ∫ ω, W k ω i * W k ω j * (ind s (ξ (k + 1) ω) * ĉ (ξ (k + 1) ω) ^ 2) ∂μ =
        ∑ s', (∑ x, P s' x * (ind s x * ĉ x ^ 2)) * c2 i j k s' :=
      hσ.integral_weight_obs ((hcoord k i).mul (hcoord k j)) (hcb2 k i j)
        (fun x => ind s x * ĉ x ^ 2)
    show ∫ ω, {ω | σ (k + 1) ω = s}.indicator (fun ω => W (k + 1) ω i * W (k + 1) ω j) ω ∂μ = _
    rw [e1, integral_add B123 B4, integral_add B12 B3, integral_add B1 B2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, w1, w2, w3,
      w4]
    simp only [transfer, hp₂]
    ring
  have hlim : ∀ i j, ∃ xl : S → ℝ, (∀ s, xl s = transfer p₂ (fun _ => lam ^ 2) xl s
      + lam ^ 2 * ∑ s', ν s' * ∑ x, P s' x * (ind s x * (ε x i * ε x j))) ∧
      ∀ s, Tendsto (fun k => c2 i j k s) atTop (𝓝 (xl s)) := fun i j => by
    have hb : ∀ s, Tendsto (fun k => lam ^ 2 * (∑ s', (∑ x, P s' x * (ind s x * (ε x i * ε x j)))
        * νk k s' + ∑ s', (∑ x, P s' x * (ind s x * (ĉ x * ε x j))) * m k i s'
        + ∑ s', (∑ x, P s' x * (ind s x * (ĉ x * ε x i))) * m k j s')) atTop
        (𝓝 (lam ^ 2 * ∑ s', ν s' * ∑ x, P s' x * (ind s x * (ε x i * ε x j)))) := fun s => by
      have t1 := tendsto_finset_sum (univ : Finset S) fun s' _ =>
        (hlaw s').const_mul (∑ x, P s' x * (ind s x * (ε x i * ε x j)))
      have t2 := tendsto_finset_sum (univ : Finset S) fun s' _ =>
        (hm0 s' i).const_mul (∑ x, P s' x * (ind s x * (ĉ x * ε x j)))
      have t3 := tendsto_finset_sum (univ : Finset S) fun s' _ =>
        (hm0 s' j).const_mul (∑ x, P s' x * (ind s x * (ĉ x * ε x i)))
      have := (((t1.add t2).add t3).const_mul (lam ^ 2))
      simp only [mul_zero, sum_const_zero, add_zero] at this
      convert this using 2
      exact congrArg _ (sum_congr rfl fun s' _ => mul_comm _ _)
    exact tendsto_affine_transfer hp₂0 hp₂ρ hρ0 hρ1 (x := fun k s => c2 i j k s)
      (fun k s => hrec₂ i j k s) hb
  choose xl hxl hconv using hlim
  refine ⟨fun s i j => xl i j s, fun s i j => ?_, fun s i j => hconv i j s⟩
  show xl i j s = _
  rw [hxl i j s]
  simp only [transfer, hp₂, hind]
  ring

omit [IsProbabilityMeasure μ] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace X] [DiscreteMeasurableSpace X] in
lemma sum4_comm {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (f : ι → κ → α → β → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f i j a b :=
        sum_congr rfl fun i _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b := sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := sum_congr rfl fun a _ => sum_comm

omit [IsProbabilityMeasure μ] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace X] [DiscreteMeasurableSpace X] in
lemma sum3_comm {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α] (f : ι → κ → α → ℝ) :
    ∑ i, ∑ j, ∑ a, f i j a = ∑ a, ∑ i, ∑ j, f i j a := by
  calc ∑ i, ∑ j, ∑ a, f i j a = ∑ i, ∑ a, ∑ j, f i j a := sum_congr rfl fun i _ => sum_comm
    _ = _ := sum_comm

set_option maxHeartbeats 4000000 in
/-- **Theorem 4.7: shorter traces give smaller noise.** Let `W^{(1)}, W^{(2)}` be the centered traces
for trace parameters `0 ≤ λ₁ ≤ λ₂ ≤ 1`, as in `tendsto_lookback_moments`, and let
`Γ_l = lim E[(δ W^{(l)}) (δ W^{(l)})ᵀ]` be the extra noise covariances, with `δ = δ(ξ_{k+1})` the TD
error. Then `0 ≼ Γ₁ ≼ Γ₂` in the Loewner order. -/
theorem StateDriven.lookback_covariance_mono (hσ : StateDriven μ ℱ σ ξ P)
    {n : ℕ} {ŝ : X → S} {ĉ : X → ℝ} {ε : X → E n} {ρ : ℝ} {ν : S → ℝ} (δ : X → ℝ)
    (hσξ : ∀ k ω, σ (k + 1) ω = ŝ (ξ (k + 1) ω))
    (hP0 : ∀ s x, 0 ≤ P s x) (hc0 : ∀ x, 0 ≤ ĉ x) (hc1 : ∀ x, ĉ x ≤ 1)
    (hρ : ∀ s, ∑ x, P s x * ĉ x ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hlaw : ∀ s, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator (fun _ => (1 : ℝ)) ω ∂μ)
      atTop (𝓝 (ν s)))
    (hcent : ∀ s j, ∑ s', ν s' * ∑ x, P s' x * ((if ŝ x = s then 1 else 0) * ε x j) = 0)
    {l₁ l₂ : ℝ} (hl0 : 0 ≤ l₁) (hl12 : l₁ ≤ l₂) (hl2 : l₂ ≤ 1) {W₁ W₂ : ℕ → Ω → E n}
    (hW₁ : ∀ k ω, W₁ (k + 1) ω = l₁ • (ε (ξ (k + 1) ω) + ĉ (ξ (k + 1) ω) • W₁ k ω))
    (hW₁m : ∀ k, StronglyMeasurable[ℱ k] (W₁ k)) (hW₁B : ∀ k, ∃ C, ∀ ω, ‖W₁ k ω‖ ≤ C)
    (hW₂ : ∀ k ω, W₂ (k + 1) ω = l₂ • (ε (ξ (k + 1) ω) + ĉ (ξ (k + 1) ω) • W₂ k ω))
    (hW₂m : ∀ k, StronglyMeasurable[ℱ k] (W₂ k)) (hW₂B : ∀ k, ∃ C, ∀ ω, ‖W₂ k ω‖ ≤ C)
    {Γ₁ Γ₂ : Mat n}
    (hΓ₁ : Tendsto (fun k => secondMoment μ fun ω => δ (ξ (k + 1) ω) • W₁ k ω) atTop (𝓝 Γ₁))
    (hΓ₂ : Tendsto (fun k => secondMoment μ fun ω => δ (ξ (k + 1) ω) • W₂ k ω) atTop (𝓝 Γ₂))
    (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * v j * Γ₁ (i, j) ∧
      ∑ i, ∑ j, v i * v j * Γ₁ (i, j) ≤ ∑ i, ∑ j, v i * v j * Γ₂ (i, j) := by
  obtain ⟨-, C₁, hC₁, hconv₁⟩ := hσ.tendsto_lookback_moments hσξ hP0 hc0 hc1 hρ hρ0 hρ1 hl0
    (hl12.trans hl2) hW₁ hW₁m hW₁B hlaw hcent
  obtain ⟨-, C₂, hC₂, hconv₂⟩ := hσ.tendsto_lookback_moments hσξ hP0 hc0 hc1 hρ hρ0 hρ1
    (hl0.trans hl12) hl2 hW₂ hW₂m hW₂B hlaw hcent
  set σ2 : S → ℝ := fun s => ∑ x, P s x * δ x ^ 2 with hσ2
  have hσ20 : ∀ s, 0 ≤ σ2 s := fun s => sum_nonneg fun x _ => mul_nonneg (hP0 _ _) (sq_nonneg _)
  -- the covariance is the `σ²`-weighted limit second moment
  have key : ∀ (W : ℕ → Ω → E n) (Γ : Mat n) (C : S → Fin n → Fin n → ℝ),
      (∀ k, StronglyMeasurable[ℱ k] (W k)) → (∀ k, ∃ C, ∀ ω, ‖W k ω‖ ≤ C) →
      Tendsto (fun k => secondMoment μ fun ω => δ (ξ (k + 1) ω) • W k ω) atTop (𝓝 Γ) →
      (∀ s i j, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator
        (fun ω => W k ω i * W k ω j) ω ∂μ) atTop (𝓝 (C s i j))) →
      ∀ i j, Γ (i, j) = ∑ s, σ2 s * C s i j := by
    intro W Γ C hWm hWB hΓ hconv i j
    have h1 : Tendsto (fun k => (secondMoment μ fun ω => δ (ξ (k + 1) ω) • W k ω) (i, j)) atTop
        (𝓝 (Γ (i, j))) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, j)).continuous.tendsto _).comp hΓ
    have hL : ∀ k, MemLp (fun ω => δ (ξ (k + 1) ω) • W k ω) 2 μ := fun k => by
      obtain ⟨C, hC⟩ := hWB k
      refine MemLp.of_bound (((hσ.stronglyMeasurable_obs δ k).smul
        ((hWm k).mono (ℱ.mono k.le_succ))).mono (ℱ.le (k + 1))).aestronglyMeasurable
        ((∑ x, |δ x|) * C) (Eventually.of_forall fun ω => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (single_le_sum (f := fun x => |δ x|) (fun _ _ => abs_nonneg _)
        (mem_univ _)) (hC ω) (norm_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
    have h2 : ∀ k, (secondMoment μ fun ω => δ (ξ (k + 1) ω) • W k ω) (i, j) =
        ∑ s, σ2 s * ∫ ω, {ω | σ k ω = s}.indicator (fun ω => W k ω i * W k ω j) ω ∂μ := by
      intro k
      rw [secondMoment, crossMoment_apply (hL k) (hL k)]
      have := hσ.integral_sq_centered_eq (hWm k) (hWB k) 0 δ i j
      simp only [Pi.zero_apply, sub_zero, PiLp.zero_apply] at this
      exact this
    have h3 : Tendsto (fun k => ∑ s, σ2 s * ∫ ω, {ω | σ k ω = s}.indicator
        (fun ω => W k ω i * W k ω j) ω ∂μ) atTop (𝓝 (∑ s, σ2 s * C s i j)) :=
      tendsto_finset_sum _ fun s _ => (hconv s i j).const_mul _
    exact tendsto_nhds_unique (h1.congr h2) h3
  have hΓ₁e := key W₁ Γ₁ C₁ hW₁m hW₁B hΓ₁ hconv₁
  have hΓ₂e := key W₂ Γ₂ C₂ hW₂m hW₂B hΓ₂ hconv₂
  -- quadratic forms
  set qf : (S → Fin n → Fin n → ℝ) → S → ℝ := fun C s => ∑ i, ∑ j, v i * v j * C s i j with hqf
  have hquad : ∀ (Γ : Mat n) (C : S → Fin n → Fin n → ℝ), (∀ i j, Γ (i, j) = ∑ s, σ2 s * C s i j)
      → ∑ i, ∑ j, v i * v j * Γ (i, j) = ∑ s, σ2 s * qf C s := fun Γ C hΓ => by
    simp only [hΓ, hqf, mul_sum]
    rw [sum3_comm]
    exact sum_congr rfl fun s _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  set ind : S → X → ℝ := fun s x => if ŝ x = s then 1 else 0 with hind
  set p₂ : S → S → ℝ := fun s' s => ∑ x, P s' x * (ind s x * ĉ x ^ 2) with hp₂
  set e : S → ℝ := fun s => ∑ i, ∑ j, v i * v j * (∑ s', ν s' * ∑ x, P s' x *
    (ind s x * (ε x i * ε x j))) with he
  have hν0 : ∀ s, 0 ≤ ν s := fun s => ge_of_tendsto' (hlaw s) fun k =>
    integral_nonneg fun ω => by
      simp only [Set.indicator_apply]; split_ifs <;> norm_num
  have hind0 : ∀ s x, 0 ≤ ind s x := fun s x => by simp only [hind]; split_ifs <;> norm_num
  have he0 : ∀ s, 0 ≤ e s := fun s => by
    have e1 : e s = ∑ s', ∑ x, ∑ i, ∑ j, (ν s' * (P s' x * ind s x)) *
        ((v i * ε x i) * (v j * ε x j)) := by
      simp only [he, mul_sum]
      refine (sum4_comm _).trans ?_
      exact sum_congr rfl fun s' _ => sum_congr rfl fun x _ =>
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    have e2 : ∀ s' x, ∑ i, ∑ j, (ν s' * (P s' x * ind s x)) * ((v i * ε x i) * (v j * ε x j)) =
        (ν s' * (P s' x * ind s x)) * ((∑ i, v i * ε x i) * (∑ j, v j * ε x j)) := fun s' x => by
      rw [sum_mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by rw [mul_sum]
    rw [e1]
    exact sum_nonneg fun s' _ => sum_nonneg fun x _ => by
      rw [e2]
      exact mul_nonneg (mul_nonneg (hν0 s') (mul_nonneg (hP0 _ _) (hind0 _ _))) (mul_self_nonneg _)
  have hfix : ∀ (l : ℝ) (C : S → Fin n → Fin n → ℝ),
      (∀ s i j, C s i j = l ^ 2 * (∑ s', ν s' * ∑ x, P s' x *
          ((if ŝ x = s then 1 else 0) * (ε x i * ε x j))
        + ∑ s', (∑ x, P s' x * ((if ŝ x = s then 1 else 0) * ĉ x ^ 2)) * C s' i j)) →
      ∀ s, qf C s = l ^ 2 * (e s + ∑ s', p₂ s' s * qf C s') := fun l C hC s => by
    have e1 : qf C s = ∑ i, ∑ j, v i * v j * (l ^ 2 * (∑ s', ν s' * ∑ x, P s' x *
        (ind s x * (ε x i * ε x j)) + ∑ s', p₂ s' s * C s' i j)) :=
      sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hC s i j]
    rw [e1]
    have e2 : ∑ s', p₂ s' s * qf C s' = ∑ i, ∑ j, v i * v j * ∑ s', p₂ s' s * C s' i j := by
      simp only [hqf, mul_sum]
      refine Eq.trans ?_ (sum3_comm _).symm
      exact sum_congr rfl fun s' _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [e2, he, mul_add, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hp₂0 : ∀ s' s, 0 ≤ p₂ s' s := fun s' s =>
    sum_nonneg fun x _ => mul_nonneg (hP0 _ _) (mul_nonneg (hind0 _ _) (sq_nonneg _))
  have hp₂ρ : ∀ s', ∑ s, p₂ s' s ≤ ρ := fun s' => by
    have h1 : ∑ s, p₂ s' s = ∑ x, P s' x * ĉ x ^ 2 := by
      simp only [hp₂]
      rw [sum_comm]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_sum, ← sum_mul]
      simp [hind]
    rw [h1]
    refine le_trans (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hP0 s' x)) (hρ s')
    nlinarith [hc0 x, hc1 x]
  have hm := fun s => mono_of_fixed hp₂0 hp₂ρ hρ1 hl0 hl12 hl2 he0 (hfix l₁ C₁ hC₁)
    (hfix l₂ C₂ hC₂) s
  rw [hquad Γ₁ C₁ hΓ₁e, hquad Γ₂ C₂ hΓ₂e]
  exact ⟨sum_nonneg fun s _ => mul_nonneg (hσ20 s) (hm s).1,
    sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hm s).2 (hσ20 s)⟩

end Process

/-! ### The critic's traces -/

section Traces

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- **The centered critic trace steps by `W' = λ (ε' + c' W)`.** Let the TD(`λ`) traces step by
`z^ψ' = ψ' + λ c' z^ψ` and `z^e'(t) = 1{s' = t} + λ c' z^e(t)`, and let
`X = (z^ψ - ψ) + (1 - λ) Σ_t z^e(t) b(t)`, the critic's carried trace after the gain
`K_λ e_t = -(1 - λ) b(t)`. Then `W = X - b(s)` satisfies
`W' = λ (c' (ψ + b(s)) - b(s') + c' W)`. -/
lemma centered_trace_step (lam c' : ℝ) (zψ zψ' ψ ψ' : E n) (ze ze' : S → ℝ) (b : S → E n)
    (s s' : S) (hzψ : zψ' = ψ' + (lam * c') • zψ)
    (hze : ∀ t, ze' t = (if s' = t then 1 else 0) + lam * c' * ze t) :
    ((zψ' - ψ') + (1 - lam) • ∑ t, ze' t • b t) - b s' =
      lam • ((c' • (ψ + b s) - b s') + c' • (((zψ - ψ) + (1 - lam) • ∑ t, ze t • b t) - b s)) := by
  have h1 : ∑ t, ze' t • b t = b s' + (lam * c') • ∑ t, ze t • b t := by
    simp only [hze, add_smul, sum_add_distrib, ite_smul, one_smul, zero_smul, sum_ite_eq,
      mem_univ, if_true, smul_sum, smul_smul]
  rw [h1, hzψ]
  module

omit [DecidableEq S] in
/-- **The noise splits.** With the gain `K_λ e_t = -(1 - λ) b(t)`, the TD(`λ`) actor-critic noise
`V ψ + δ (z^ψ - K_λ z^e)` is the TD(0) noise `V ψ + δ (ψ + b(s))` plus `δ W`, with `W` the
centered critic trace. -/
lemma tdlam_noise_split (V δ : ℝ) (lam : ℝ) (zψ ψ : E n) (ze : S → ℝ) (b : S → E n) (s : S) :
    V • ψ + δ • (zψ - ∑ t, ze t • (-(1 - lam) • b t)) =
      (V • ψ + δ • (ψ + b s)) + δ • (((zψ - ψ) + (1 - lam) • ∑ t, ze t • b t) - b s) := by
  have : ∑ t, ze t • (-(1 - lam) • b t) = -((1 - lam) • ∑ t, ze t • b t) := by
    rw [smul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun t _ => by module
  rw [this]
  module

end Traces

end StochasticApproximation
