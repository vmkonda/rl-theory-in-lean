/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TwoTimeScaleMoments

/-!
# Moment bounds for two time scales with Markov noise

The fourth-moment hypotheses of `tendsto_tts_taylor` for the iteration
`x_{k+1} = x_k + β_k (F₁(x_k, y_k) + M₁_{k+1} + r₁_k + h_k - h_{k+1})`,
`y_{k+1} = y_k + γ_k (F₂(x_k, y_k) + M₂_{k+1} + r₂_k + g_k - g_{k+1})`,
where `h, g` are bounded Poisson shifts and `r₁ = O(β)`, `r₂ = O(γ)` are sampling remainders.

The proof shifts both components, `e_k = x_k + β_{k-1} h_k` and `ŷ_k = y_k + γ_{k-1} g_k`, so
that each step is a part known at time `k` plus a martingale term. With Lipschitz drifts the known
part is the dissipative step at `(e_k, ŷ_k)` up to an error of size `βγ` (slow) or `γ²` (fast),
which `tts_moments_of_steps` absorbs at the cost of half the margin `η - c₀`.

* `moment_bounds_tts_markov`: `E‖x_k‖⁴, E‖y_k‖⁴ = O(γ_k²)`.
* `tendsto_tts_dissipative_markov`: the end-to-end two-time-scale linearization with Markov noise.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

section Helpers

variable {n : ℕ}

/-- A step size at `k - 1` is comparable to the step at `k`, and consecutive steps differ by
`O(β_k²)`. -/
lemma StepSizeRate.prev_le {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar) :
    ∃ R C, 1 ≤ R ∧ 0 ≤ C ∧ ∀ k, β (k - 1) ≤ R * β k ∧ |β k - β (k - 1)| ≤ C * β k ^ 2 := by
  obtain ⟨CΔ, hCΔ0, hCΔ⟩ := hβ.abs_sub_le
  obtain ⟨R, hR1, hR⟩ : ∃ R, 1 ≤ R ∧ ∀ k, β (k - 1) ≤ R * β k := by
    have h := hβ.tendsto_ratio.inv₀ one_ne_zero
    simp only [inv_one] at h
    obtain ⟨R₀, hR₀⟩ := h.bddAbove_range
    refine ⟨max R₀ 1, le_max_right _ _, fun k => ?_⟩
    cases k with
    | zero => simpa using (le_mul_of_one_le_left (hβ.pos 0).le (le_max_right R₀ 1))
    | succ j =>
      have hj := hR₀ ⟨j, rfl⟩
      simp only [inv_div] at hj
      have hb := hβ.pos (j + 1)
      simp only [Nat.add_sub_cancel]
      calc β j = β j / β (j + 1) * β (j + 1) := by field_simp
        _ ≤ max R₀ 1 * β (j + 1) :=
            mul_le_mul_of_nonneg_right (hj.trans (le_max_left _ _)) hb.le
  refine ⟨R, CΔ * R ^ 2, hR1, by positivity, fun k => ⟨hR k, ?_⟩⟩
  cases k with
  | zero => simp; positivity
  | succ j =>
    simp only [Nat.add_sub_cancel]
    have h1 := hCΔ j
    have h2 : β j ^ 2 ≤ (R * β (j + 1)) ^ 2 :=
      pow_le_pow_left₀ (hβ.pos j).le (by simpa using hR (j + 1)) 2
    calc |β (j + 1) - β j| ≤ CΔ * β j ^ 2 := h1
      _ ≤ CΔ * (R * β (j + 1)) ^ 2 := mul_le_mul_of_nonneg_left h2 hCΔ0
      _ = CΔ * R ^ 2 * β (j + 1) ^ 2 := by ring

lemma pow_four_add_le {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), mul_nonneg _ha _hb, sq_nonneg (a + b)]

lemma norm_add_sq_le' (p ε : E n) : ‖p + ε‖ ^ 2 ≤ ‖p‖ ^ 2 + 2 * ‖p‖ * ‖ε‖ + ‖ε‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le p ε) 2
  nlinarith [h]

lemma norm_add_three_le (a b c : E n) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have := norm_add_le (a + b) c; have := norm_add_le a b; linarith

lemma norm_add_six_le (a b c d e f : E n) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have := norm_add_le (a + b + c + d + e) f; have := norm_add_le (a + b + c + d) e
  have := norm_add_le (a + b + c) d; have := norm_add_le (a + b) c; have := norm_add_le a b
  linarith

lemma norm_add_four_sub_le (a b c d e : E n) :
    ‖a + b + c + d - e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have := norm_sub_le (a + b + c + d) e; have := norm_add_le (a + b + c) d
  have := norm_add_le (a + b) c; have := norm_add_le a b
  linarith

lemma norm_smul_le_of_le {s c : ℝ} {v : E n} (hs : 0 ≤ s) (hv : ‖v‖ ≤ c) : ‖s • v‖ ≤ s * c := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left hv hs

/-- **The perturbed slow step, scalar form.** A dissipative slow step `p` perturbed by `ε` of size
`E₁ β γ` still contracts at rate `η - θ`, with an additive `O(β²)` when `γ² = O(β)`. -/
lemma slow_perturb_scalar {E W Pn U εn β γ η θ K E₁ Bβ Bγ Bgb : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hθ : 0 < θ) (hE : 0 ≤ E) (hW : 0 ≤ W) (hεn0 : 0 ≤ εn) (hK : 0 ≤ K) (_hE₁ : 0 ≤ E₁)
    (hP2 : Pn ^ 2 ≤ (1 - η * β + 2 * K ^ 2 * β ^ 2) * E ^ 2
      + (K ^ 2 / η + 2 * K ^ 2 * β) * β * W ^ 2)
    (hPn : Pn ≤ E + β * K * (E + W)) (hεn : εn ≤ E₁ * β * γ)
    (hU : U ≤ Pn ^ 2 + 2 * Pn * εn + εn ^ 2)
    (hβB : β ≤ Bβ) (hγB : γ ≤ Bγ) (hgb : γ ^ 2 ≤ Bgb * β) :
    U ≤ (1 - (η - θ) * β + (3 * K ^ 2 + (η - θ) ^ 2 / 4) * β ^ 2) * E ^ 2
      + (K ^ 2 / η + 3 * K ^ 2 * Bβ) * β * W ^ 2
      + (E₁ ^ 2 * Bgb / θ + 3 * E₁ ^ 2 * Bγ ^ 2) * β ^ 2 := by
  have s1 : 2 * Pn * εn ≤ 2 * ((E + β * K * (E + W)) * (E₁ * β * γ)) := by
    have := mul_le_mul hPn hεn hεn0 (by positivity)
    linarith
  have s2 : 2 * E * (E₁ * β * γ) ≤ θ * β * E ^ 2 + E₁ ^ 2 * β * γ ^ 2 / θ := by
    have h0 : 0 ≤ β * (θ * E - E₁ * γ) ^ 2 / θ := by positivity
    have e : β * (θ * E - E₁ * γ) ^ 2 / θ =
        θ * β * E ^ 2 - 2 * E * (E₁ * β * γ) + E₁ ^ 2 * β * γ ^ 2 / θ := by
      field_simp; ring
    linarith
  have s3 : 2 * (β * K * E) * (E₁ * β * γ) ≤ β ^ 2 * K ^ 2 * E ^ 2 + E₁ ^ 2 * β ^ 2 * γ ^ 2 := by
    nlinarith [sq_nonneg (β * K * E - E₁ * β * γ)]
  have s4 : 2 * (β * K * W) * (E₁ * β * γ) ≤ β ^ 2 * K ^ 2 * W ^ 2 + E₁ ^ 2 * β ^ 2 * γ ^ 2 := by
    nlinarith [sq_nonneg (β * K * W - E₁ * β * γ)]
  have s5 : εn ^ 2 ≤ E₁ ^ 2 * β ^ 2 * γ ^ 2 := by
    have := pow_le_pow_left₀ hεn0 hεn 2
    have e : (E₁ * β * γ) ^ 2 = E₁ ^ 2 * β ^ 2 * γ ^ 2 := by ring
    linarith
  have s6 : E₁ ^ 2 * β * γ ^ 2 / θ ≤ E₁ ^ 2 * Bgb / θ * β ^ 2 := by
    have := mul_le_mul_of_nonneg_left hgb (by positivity : 0 ≤ E₁ ^ 2 * β / θ)
    have e1 : E₁ ^ 2 * β / θ * γ ^ 2 = E₁ ^ 2 * β * γ ^ 2 / θ := by ring
    have e2 : E₁ ^ 2 * β / θ * (Bgb * β) = E₁ ^ 2 * Bgb / θ * β ^ 2 := by ring
    linarith
  have s7 : E₁ ^ 2 * β ^ 2 * γ ^ 2 ≤ E₁ ^ 2 * Bγ ^ 2 * β ^ 2 := by
    have h1 := pow_le_pow_left₀ hγ.le hγB 2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ E₁ ^ 2 * β ^ 2)
    linarith
  have s8 : β ^ 2 * K ^ 2 * W ^ 2 + 2 * K ^ 2 * β * β * W ^ 2 ≤ 3 * K ^ 2 * Bβ * β * W ^ 2 := by
    have := mul_le_mul_of_nonneg_left hβB (by positivity : 0 ≤ 3 * K ^ 2 * β * W ^ 2)
    linarith
  have s9 : 0 ≤ (η - θ) ^ 2 / 4 * β ^ 2 * E ^ 2 := by positivity
  have e : 2 * ((E + β * K * (E + W)) * (E₁ * β * γ)) = 2 * E * (E₁ * β * γ)
      + 2 * (β * K * E) * (E₁ * β * γ) + 2 * (β * K * W) * (E₁ * β * γ) := by ring
  linarith

/-- **The perturbed fast step, scalar form.** A dissipative fast step `p` perturbed by `ε` of
size `E₂ γ²` still contracts at rate `η - θ`, with an additive `O(γ²)`. -/
lemma fast_perturb_scalar {E W Pn V εn β γ η θ K₂ c₂ E₂ Bγ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hθ : 0 < θ) (hE : 0 ≤ E) (hW : 0 ≤ W) (hεn0 : 0 ≤ εn) (hK₂ : 0 ≤ K₂) (_hE₂ : 0 ≤ E₂)
    (hP2 : Pn ^ 2 ≤ (1 - η * γ + c₂ * (γ ^ 2 + β ^ 2 / γ)) * W ^ 2
      + c₂ * (γ ^ 2 + β ^ 2 / γ) * E ^ 2)
    (hPn : Pn ≤ W + K₂ * γ * (E + W)) (hεn : εn ≤ E₂ * γ ^ 2)
    (hV : V ≤ Pn ^ 2 + 2 * Pn * εn + εn ^ 2) (hγB : γ ≤ Bγ) :
    V ≤ (1 - (η - θ) * γ + (c₂ + K₂ ^ 2) * (γ ^ 2 + β ^ 2 / γ)) * W ^ 2
      + (c₂ + K₂ ^ 2) * (γ ^ 2 + β ^ 2 / γ) * E ^ 2
      + (E₂ ^ 2 * Bγ / θ + 3 * E₂ ^ 2 * Bγ ^ 2) * γ ^ 2 := by
  have s1 : 2 * Pn * εn ≤ 2 * ((W + K₂ * γ * (E + W)) * (E₂ * γ ^ 2)) := by
    have := mul_le_mul hPn hεn hεn0 (by positivity)
    linarith
  have s2 : 2 * W * (E₂ * γ ^ 2) ≤ θ * γ * W ^ 2 + E₂ ^ 2 * γ ^ 3 / θ := by
    have h0 : 0 ≤ γ * (θ * W - E₂ * γ) ^ 2 / θ := by positivity
    have e : γ * (θ * W - E₂ * γ) ^ 2 / θ =
        θ * γ * W ^ 2 - 2 * W * (E₂ * γ ^ 2) + E₂ ^ 2 * γ ^ 3 / θ := by
      field_simp; ring
    linarith
  have s3 : 2 * (K₂ * γ * E) * (E₂ * γ ^ 2) ≤ K₂ ^ 2 * γ ^ 2 * E ^ 2 + E₂ ^ 2 * γ ^ 4 := by
    nlinarith [sq_nonneg (K₂ * γ * E - E₂ * γ ^ 2)]
  have s4 : 2 * (K₂ * γ * W) * (E₂ * γ ^ 2) ≤ K₂ ^ 2 * γ ^ 2 * W ^ 2 + E₂ ^ 2 * γ ^ 4 := by
    nlinarith [sq_nonneg (K₂ * γ * W - E₂ * γ ^ 2)]
  have s5 : εn ^ 2 ≤ E₂ ^ 2 * γ ^ 4 := by
    have := pow_le_pow_left₀ hεn0 hεn 2
    have e : (E₂ * γ ^ 2) ^ 2 = E₂ ^ 2 * γ ^ 4 := by ring
    linarith
  have s6 : E₂ ^ 2 * γ ^ 3 / θ ≤ E₂ ^ 2 * Bγ / θ * γ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hγB (by positivity : 0 ≤ E₂ ^ 2 * γ ^ 2 / θ)
    have e1 : E₂ ^ 2 * γ ^ 2 / θ * γ = E₂ ^ 2 * γ ^ 3 / θ := by ring
    have e2 : E₂ ^ 2 * γ ^ 2 / θ * Bγ = E₂ ^ 2 * Bγ / θ * γ ^ 2 := by ring
    linarith
  have s7 : E₂ ^ 2 * γ ^ 4 ≤ E₂ ^ 2 * Bγ ^ 2 * γ ^ 2 := by
    have h1 := pow_le_pow_left₀ hγ.le hγB 2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ E₂ ^ 2 * γ ^ 2)
    have e : E₂ ^ 2 * γ ^ 2 * γ ^ 2 = E₂ ^ 2 * γ ^ 4 := by ring
    linarith
  have hτ : 0 ≤ β ^ 2 / γ := by positivity
  have s8 : 0 ≤ K₂ ^ 2 * (β ^ 2 / γ) * E ^ 2 := by positivity
  have s9 : 0 ≤ K₂ ^ 2 * (β ^ 2 / γ) * W ^ 2 := by positivity
  have e : 2 * ((W + K₂ * γ * (E + W)) * (E₂ * γ ^ 2)) = 2 * W * (E₂ * γ ^ 2)
      + 2 * (K₂ * γ * E) * (E₂ * γ ^ 2) + 2 * (K₂ * γ * W) * (E₂ * γ ^ 2) := by ring
  linarith

end Helpers

section Main

variable {d₁ d₂ : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

set_option maxHeartbeats 8000000 in
/-- **Fourth moments for two time scales with Markov noise.** Let
`x_{k+1} = x_k + β_k (F₁(x_k, y_k) + M₁_{k+1} + r₁_k + h_k - h_{k+1})` and
`y_{k+1} = y_k + γ_k (F₂(x_k, y_k) + M₂_{k+1} + r₂_k + g_k - g_{k+1})`, and write `z = y + D x`.
Suppose:
* `⟨x, F₁⟩ ≤ -η‖x‖² + K‖x‖‖z‖`, `⟨z, F₂⟩ ≤ -η‖z‖²`, `‖F_i‖ ≤ K(‖x‖ + ‖z‖)`, and the `F_i` are
  `L_F`-Lipschitz;
* `M₁, M₂` are bounded martingale differences, the Poisson shifts `h, g` are bounded and known at
  time `k`, `‖r₁_k‖ ≤ C β_k`, `‖r₂_k‖ ≤ C γ_k`, and the start is bounded;
* `β/γ → 0`, `γ²/β → 0` and eventually `γ_k / γ_{k+1} ≤ 1 + c₀ β_k` with `0 ≤ c₀ < η`.

Then each iterate is bounded and `E‖x_k‖⁴, E‖y_k‖⁴ ≤ W γ_k²`. -/
theorem moment_bounds_tts_markov {β γ : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar)
    (hγ : StepSizeRate γ 0) (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0)) {η c₀ K LF CM Ch Cr : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η) (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k)
    (hK : 0 ≤ K) (hLF : 0 ≤ LF) (ℱ : MeasureTheory.Filtration ℕ m0)
    {x M₁ h r₁ : ℕ → Ω → E d₁} {y M₂ g r₂ : ℕ → Ω → E d₂} (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {F₁ : E d₁ → E d₂ → E d₁} {F₂ : E d₁ → E d₂ → E d₂}
    (hF₁in : ∀ u w, ⟪u, F₁ u w⟫_ℝ ≤ -η * ‖u‖ ^ 2 + K * ‖u‖ * ‖w + matCLM D u‖)
    (hF₁g : ∀ u w, ‖F₁ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₂in : ∀ u w, ⟪w + matCLM D u, F₂ u w⟫_ℝ ≤ -η * ‖w + matCLM D u‖ ^ 2)
    (hF₂g : ∀ u w, ‖F₂ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₁L : ∀ u w u' w', ‖F₁ u w - F₁ u' w'‖ ≤ LF * (‖u - u'‖ + ‖w - w'‖))
    (hF₂L : ∀ u w u' w', ‖F₂ u w - F₂ u' w'‖ ≤ LF * (‖u - u'‖ + ‖w - w'‖))
    (hF₁c : Continuous fun p : E d₁ × E d₂ => F₁ p.1 p.2)
    (hF₂c : Continuous fun p : E d₁ × E d₂ => F₂ p.1 p.2)
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • (F₁ (x k ω) (y k ω) + M₁ (k + 1) ω + r₁ k ω
      + h k ω - h (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • (F₂ (x k ω) (y k ω) + M₂ (k + 1) ω + r₂ k ω
      + g k ω - g (k + 1) ω))
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hym : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hx0 : ∃ C, ∀ ω, ‖x 0 ω‖ ≤ C) (hy0 : ∃ C, ∀ ω, ‖y 0 ω‖ ≤ C)
    (hhm : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhb : ∀ k ω, ‖h k ω‖ ≤ Ch)
    (hgm : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgb : ∀ k ω, ‖g k ω‖ ≤ Ch)
    (hr₁m : ∀ k, StronglyMeasurable[ℱ k] (r₁ k)) (hr₁b : ∀ k ω, ‖r₁ k ω‖ ≤ Cr * β k)
    (hr₂m : ∀ k, StronglyMeasurable[ℱ k] (r₂ k)) (hr₂b : ∀ k ω, ‖r₂ k ω‖ ≤ Cr * γ k)
    (hM₁ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₁ (k + 1))) (hM₁b : ∀ k ω, ‖M₁ (k + 1) ω‖ ≤ CM)
    (hmart₁ : ∀ k j, μ[fun ω => M₁ (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hM₂ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₂ (k + 1))) (hM₂b : ∀ k ω, ‖M₂ (k + 1) ω‖ ≤ CM)
    (hmart₂ : ∀ k j, μ[fun ω => M₂ (k + 1) ω j | ℱ k] =ᵐ[μ] 0) :
    (∀ k, ∃ C, ∀ ω, ‖x k ω‖ ≤ C ∧ ‖y k ω‖ ≤ C) ∧
      ∃ W, ∀ k, ∫ ω, ‖x k ω‖ ^ 4 ∂μ ≤ W * γ k ^ 2 ∧ ∫ ω, ‖y k ω‖ ^ 4 ∂μ ≤ W * γ k ^ 2 := by
  have hη : 0 < η := by linarith
  -- constants
  set CM₀ := max CM 0
  set Ch₀ := max Ch 0
  set Cr₀ := max Cr 0
  have hCM₀ : 0 ≤ CM₀ := le_max_right _ _
  have hCh₀ : 0 ≤ Ch₀ := le_max_right _ _
  have hCr₀ : 0 ≤ Cr₀ := le_max_right _ _
  have hM₁b' : ∀ k ω, ‖M₁ (k + 1) ω‖ ≤ CM₀ := fun k ω => (hM₁b k ω).trans (le_max_left _ _)
  have hM₂b' : ∀ k ω, ‖M₂ (k + 1) ω‖ ≤ CM₀ := fun k ω => (hM₂b k ω).trans (le_max_left _ _)
  have hhb' : ∀ k ω, ‖h k ω‖ ≤ Ch₀ := fun k ω => (hhb k ω).trans (le_max_left _ _)
  have hgb' : ∀ k ω, ‖g k ω‖ ≤ Ch₀ := fun k ω => (hgb k ω).trans (le_max_left _ _)
  have hr₁b' : ∀ k ω, ‖r₁ k ω‖ ≤ Cr₀ * β k := fun k ω =>
    (hr₁b k ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hβ.pos k).le)
  have hr₂b' : ∀ k ω, ‖r₂ k ω‖ ≤ Cr₀ * γ k := fun k ω =>
    (hr₂b k ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hγ.pos k).le)
  obtain ⟨Bβ, hBβ⟩ := hβ.tendsto_zero.bddAbove_range
  obtain ⟨Bγ, hBγ⟩ := hγ.tendsto_zero.bddAbove_range
  obtain ⟨Bq, hBq⟩ := hβγ.bddAbove_range
  obtain ⟨Bg, hBg⟩ := hγβ.bddAbove_range
  have hβB : ∀ k, β k ≤ Bβ := fun k => hBβ ⟨k, rfl⟩
  have hγB : ∀ k, γ k ≤ Bγ := fun k => hBγ ⟨k, rfl⟩
  have hqB : ∀ k, β k / γ k ≤ Bq := fun k => hBq ⟨k, rfl⟩
  have hBβ0 : 0 ≤ Bβ := (hβ.pos 0).le.trans (hβB 0)
  have hBγ0 : 0 ≤ Bγ := (hγ.pos 0).le.trans (hγB 0)
  have hBq0 : 0 ≤ Bq := (div_nonneg (hβ.pos 0).le (hγ.pos 0).le).trans (hqB 0)
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have := hqB k; rwa [div_le_iff₀ (hγ.pos k)] at this
  have hgbq : ∀ k, γ k ^ 2 ≤ Bg * β k := fun k => by
    have : γ k ^ 2 / β k ≤ Bg := hBg ⟨k, rfl⟩
    rwa [div_le_iff₀ (hβ.pos k)] at this
  have hBg0 : 0 ≤ Bg := (div_nonneg (sq_nonneg (γ 0)) (hβ.pos 0).le).trans (hBg ⟨0, rfl⟩)
  have hββ : ∀ k, β k ^ 2 ≤ Bq ^ 2 * γ k ^ 2 := fun k => by
    have := pow_le_pow_left₀ (hβ.pos k).le (hbq k) 2; rw [mul_pow] at this; exact this
  have hβγ' : ∀ k, β k * β k ≤ Bq * (β k * γ k) := fun k => by
    have := mul_le_mul_of_nonneg_left (hbq k) (hβ.pos k).le; linarith
  have hβγ2 : ∀ k, β k * γ k ≤ Bq * γ k ^ 2 := fun k => by
    have := mul_le_mul_of_nonneg_right (hbq k) (hγ.pos k).le; nlinarith
  obtain ⟨Rβ, CΔβ, hRβ1, hCΔβ, hRβ⟩ := hβ.prev_le
  obtain ⟨Rγ, CΔγ, hRγ1, hCΔγ, hRγ⟩ := hγ.prev_le
  have hRβ0 : 0 ≤ Rβ := by linarith
  have hRγ0 : 0 ≤ Rγ := by linarith
  set nD := ‖matCLM D‖
  have hnD : 0 ≤ nD := norm_nonneg _
  -- each iterate is bounded
  have hF₁b : ∀ u w, ‖F₁ u w‖ ≤ K * ((2 + nD) * (max ‖u‖ ‖w‖)) := fun u w => by
    refine (hF₁g u w).trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h1 : ‖w + matCLM D u‖ ≤ ‖w‖ + nD * ‖u‖ :=
      (norm_add_le _ _).trans (add_le_add_left ((matCLM D).le_opNorm _) _)
    have := le_max_left ‖u‖ ‖w‖; have := le_max_right ‖u‖ ‖w‖
    nlinarith
  have hF₂b : ∀ u w, ‖F₂ u w‖ ≤ K * ((2 + nD) * (max ‖u‖ ‖w‖)) := fun u w => by
    refine (hF₂g u w).trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h1 : ‖w + matCLM D u‖ ≤ ‖w‖ + nD * ‖u‖ :=
      (norm_add_le _ _).trans (add_le_add_left ((matCLM D).le_opNorm _) _)
    have := le_max_left ‖u‖ ‖w‖; have := le_max_right ‖u‖ ‖w‖
    nlinarith
  have hbd0 : ∀ k, ∃ C, 0 ≤ C ∧ ∀ ω, ‖x k ω‖ ≤ C ∧ ‖y k ω‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      obtain ⟨Cx, hCx⟩ := hx0
      obtain ⟨Cy, hCy⟩ := hy0
      refine ⟨max (max Cx Cy) 0, le_max_right _ _, fun ω => ⟨?_, ?_⟩⟩
      · exact (hCx ω).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hCy ω).trans ((le_max_right _ _).trans (le_max_left _ _))
    | succ k ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      have hb := hβ.pos k
      have hg := hγ.pos k
      set S := K * ((2 + nD) * C) + CM₀ + Cr₀ * (β k + γ k) + 2 * Ch₀ with hS
      have hS0 : 0 ≤ S := by positivity
      have hmax : ∀ ω, max ‖x k ω‖ ‖y k ω‖ ≤ C := fun ω => max_le (hC ω).1 (hC ω).2
      refine ⟨C + (β k + γ k) * S, by positivity, fun ω => ⟨?_, ?_⟩⟩
      · rw [hx k ω]
        have t := norm_add_four_sub_le (F₁ (x k ω) (y k ω)) (M₁ (k + 1) ω) (r₁ k ω) (h k ω)
          (h (k + 1) ω)
        have t1 := (hF₁b (x k ω) (y k ω)).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hmax ω) (by positivity)) hK)
        have t2 : ‖F₁ (x k ω) (y k ω) + M₁ (k + 1) ω + r₁ k ω + h k ω - h (k + 1) ω‖ ≤ S := by
          have := hM₁b' k ω; have := hr₁b' k ω; have := hhb' k ω; have := hhb' (k + 1) ω
          have : Cr₀ * β k ≤ Cr₀ * (β k + γ k) := mul_le_mul_of_nonneg_left (by linarith) hCr₀
          simp only [hS]; linarith
        have t3 := norm_smul_le_of_le hb.le t2
        have := norm_add_le (x k ω) (β k • (F₁ (x k ω) (y k ω) + M₁ (k + 1) ω + r₁ k ω
          + h k ω - h (k + 1) ω))
        have : 0 ≤ γ k * S := by positivity
        nlinarith [(hC ω).1]
      · rw [hy k ω]
        have t := norm_add_four_sub_le (F₂ (x k ω) (y k ω)) (M₂ (k + 1) ω) (r₂ k ω) (g k ω)
          (g (k + 1) ω)
        have t1 := (hF₂b (x k ω) (y k ω)).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hmax ω) (by positivity)) hK)
        have t2 : ‖F₂ (x k ω) (y k ω) + M₂ (k + 1) ω + r₂ k ω + g k ω - g (k + 1) ω‖ ≤ S := by
          have := hM₂b' k ω; have := hr₂b' k ω; have := hgb' k ω; have := hgb' (k + 1) ω
          have : Cr₀ * γ k ≤ Cr₀ * (β k + γ k) := mul_le_mul_of_nonneg_left (by linarith) hCr₀
          simp only [hS]; linarith
        have t3 := norm_smul_le_of_le hg.le t2
        have := norm_add_le (y k ω) (γ k • (F₂ (x k ω) (y k ω) + M₂ (k + 1) ω + r₂ k ω
          + g k ω - g (k + 1) ω))
        have : 0 ≤ β k * S := by positivity
        nlinarith [(hC ω).2]
  refine ⟨fun k => by obtain ⟨C, -, hC⟩ := hbd0 k; exact ⟨C, hC⟩, ?_⟩
  -- the shifted coordinates
  set e : ℕ → Ω → E d₁ := fun k ω => x k ω + β (k - 1) • h k ω with he
  set yh : ℕ → Ω → E d₂ := fun k ω => y k ω + γ (k - 1) • g k ω with hyh
  set w : ℕ → Ω → E d₂ := fun k ω => yh k ω + matCLM D (e k ω) with hw
  set f₁ : ℕ → Ω → E d₁ := fun k ω => F₁ (e k ω) (yh k ω) with hf₁
  set f₂ : ℕ → Ω → E d₂ := fun k ω => F₂ (e k ω) (yh k ω) with hf₂
  set Δ₁ : ℕ → Ω → E d₁ := fun k ω => F₁ (x k ω) (y k ω) - f₁ k ω with hΔ₁
  set Δ₂ : ℕ → Ω → E d₂ := fun k ω => F₂ (x k ω) (y k ω) - f₂ k ω with hΔ₂
  set ε₁ : ℕ → Ω → E d₁ := fun k ω => (β k - β (k - 1)) • h k ω + β k • r₁ k ω
    + β k • Δ₁ k ω with hε₁
  set ε₂ : ℕ → Ω → E d₂ := fun k ω => (γ k - γ (k - 1)) • g k ω
    + (β k - β (k - 1)) • matCLM D (h k ω) + γ k • r₂ k ω + β k • matCLM D (r₁ k ω)
    + γ k • Δ₂ k ω + β k • matCLM D (Δ₁ k ω) with hε₂
  set u : ℕ → Ω → E d₁ := fun k ω => e k ω + β k • f₁ k ω + ε₁ k ω with hu
  set v : ℕ → Ω → E d₂ := fun k ω => w k ω + γ k • f₂ k ω + β k • matCLM D (f₁ k ω)
    + ε₂ k ω with hv
  set Mt : ℕ → Ω → E d₂ := fun n ω => M₂ n ω + (β (n - 1) / γ (n - 1)) • matCLM D (M₁ n ω)
    with hMt
  have hxstep : ∀ k ω, e (k + 1) ω = u k ω + β k • M₁ (k + 1) ω := fun k ω => by
    simp only [he, hu, hε₁, hΔ₁, hf₁, hx k ω, Nat.add_sub_cancel]
    module
  have hzstep : ∀ k ω, w (k + 1) ω = v k ω + γ k • Mt (k + 1) ω := fun k ω => by
    have hg := (hγ.pos k).ne'
    have key : γ k • Mt (k + 1) ω = γ k • M₂ (k + 1) ω + β k • matCLM D (M₁ (k + 1) ω) := by
      simp only [hMt, Nat.add_sub_cancel, smul_add, smul_smul]
      rw [mul_div_cancel₀ _ hg]
    rw [key]
    simp only [hw, hyh, he, hv, hε₂, hΔ₁, hΔ₂, hf₁, hf₂, hx k ω, hy k ω, Nat.add_sub_cancel,
      map_add, map_sub, map_smul]
    module
  -- measurability
  have hDm : ∀ k {f : Ω → E d₁}, StronglyMeasurable[ℱ k] f →
      StronglyMeasurable[ℱ k] (fun ω => matCLM D (f ω)) := fun k _ hf =>
    (matCLM D).continuous.comp_stronglyMeasurable hf
  have hem : ∀ k, StronglyMeasurable[ℱ k] (e k) := fun k => by
    have := (hxm k).add ((hhm k).const_smul (β (k - 1))); exact this
  have hyhm : ∀ k, StronglyMeasurable[ℱ k] (yh k) := fun k => by
    have := (hym k).add ((hgm k).const_smul (γ (k - 1))); exact this
  have hwm : ∀ k, StronglyMeasurable[ℱ k] (w k) := fun k => by
    have := (hyhm k).add (hDm k (hem k)); exact this
  have hf₁m : ∀ k, StronglyMeasurable[ℱ k] (f₁ k) := fun k =>
    hF₁c.comp_stronglyMeasurable ((hem k).prodMk (hyhm k))
  have hf₂m : ∀ k, StronglyMeasurable[ℱ k] (f₂ k) := fun k =>
    hF₂c.comp_stronglyMeasurable ((hem k).prodMk (hyhm k))
  have hF₁m : ∀ k, StronglyMeasurable[ℱ k] (fun ω => F₁ (x k ω) (y k ω)) := fun k =>
    hF₁c.comp_stronglyMeasurable ((hxm k).prodMk (hym k))
  have hF₂m : ∀ k, StronglyMeasurable[ℱ k] (fun ω => F₂ (x k ω) (y k ω)) := fun k =>
    hF₂c.comp_stronglyMeasurable ((hxm k).prodMk (hym k))
  have hΔ₁m : ∀ k, StronglyMeasurable[ℱ k] (Δ₁ k) := fun k => by
    have := (hF₁m k).sub (hf₁m k); exact this
  have hΔ₂m : ∀ k, StronglyMeasurable[ℱ k] (Δ₂ k) := fun k => by
    have := (hF₂m k).sub (hf₂m k); exact this
  have hε₁m : ∀ k, StronglyMeasurable[ℱ k] (ε₁ k) := fun k => by
    have := (((hhm k).const_smul (β k - β (k - 1))).add ((hr₁m k).const_smul (β k))).add
      ((hΔ₁m k).const_smul (β k))
    exact this
  have hε₂m : ∀ k, StronglyMeasurable[ℱ k] (ε₂ k) := fun k => by
    have := (((((((hgm k).const_smul (γ k - γ (k - 1))).add
      ((hDm k (hhm k)).const_smul (β k - β (k - 1)))).add
      ((hr₂m k).const_smul (γ k))).add ((hDm k (hr₁m k)).const_smul (β k))).add
      ((hΔ₂m k).const_smul (γ k))).add ((hDm k (hΔ₁m k)).const_smul (β k)))
    exact this
  have hum : ∀ k, StronglyMeasurable[ℱ k] (u k) := fun k => by
    have := ((hem k).add ((hf₁m k).const_smul (β k))).add (hε₁m k); exact this
  have hvm : ∀ k, StronglyMeasurable[ℱ k] (v k) := fun k => by
    have := (((hwm k).add ((hf₂m k).const_smul (γ k))).add
      ((hDm k (hf₁m k)).const_smul (β k))).add (hε₂m k)
    exact this
  -- the fast noise
  have hMtm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Mt (k + 1)) := fun k => by
    have := (hM₂ k).add (((matCLM D).continuous.comp_stronglyMeasurable (hM₁ k)).const_smul
      (β k / γ k))
    exact this
  set CMt := CM₀ + Bq * nD * CM₀ with hCMt
  have hMtb : ∀ k ω, ‖Mt (k + 1) ω‖ ≤ CMt := fun k ω => by
    simp only [hMt, Nat.add_sub_cancel]
    refine (norm_add_le _ _).trans (add_le_add (hM₂b' k ω) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hβ.pos k).le (hγ.pos k).le)]
    have h1 : ‖matCLM D (M₁ (k + 1) ω)‖ ≤ nD * CM₀ :=
      ((matCLM D).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM₁b' k ω) hnD)
    calc β k / γ k * ‖matCLM D (M₁ (k + 1) ω)‖ ≤ Bq * (nD * CM₀) :=
          mul_le_mul (hqB k) h1 (norm_nonneg _) hBq0
      _ = Bq * nD * CM₀ := by ring
  have hMtmart : ∀ k j, μ[fun ω => Mt (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j => by
    have hM₁L : MemLp (M₁ (k + 1)) 2 μ := MemLp.of_bound
      ((hM₁ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM₀ (Eventually.of_forall (hM₁b' k))
    have hM₂L : MemLp (M₂ (k + 1)) 2 μ := MemLp.of_bound
      ((hM₂ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM₀ (Eventually.of_forall (hM₂b' k))
    have h2 := condExp_matCLM_eq_zero (μ := μ) (ℱ := ℱ k) D hM₁L (hmart₁ k) j
    have i1 := (memLp_apply hM₂L j).integrable one_le_two
    have i2 : Integrable (fun ω => matCLM D (M₁ (k + 1) ω) j) μ :=
      (memLp_apply ((matCLM D).comp_memLp' hM₁L) j).integrable one_le_two
    have e : (fun ω => Mt (k + 1) ω j) = (fun ω => M₂ (k + 1) ω j)
        + (β k / γ k) • fun ω => matCLM D (M₁ (k + 1) ω) j := by
      funext ω; simp [hMt]
    rw [e]
    filter_upwards [condExp_add i1 (i2.smul (β k / γ k)) (ℱ k),
      condExp_smul (β k / γ k) (fun ω => matCLM D (M₁ (k + 1) ω) j) (ℱ k), hmart₂ k j, h2]
      with ω h1 h3 h4 h5
    rw [h1, Pi.add_apply, h3, Pi.smul_apply, h4, h5]
    simp
  -- the shifted coordinates are bounded
  have hshift : ∀ k ω, ‖x k ω - e k ω‖ ≤ Rβ * Ch₀ * β k ∧ ‖y k ω - yh k ω‖ ≤ Rγ * Ch₀ * γ k :=
    fun k ω => by
      constructor
      · have e1 : x k ω - e k ω = -(β (k - 1) • h k ω) := by simp only [he]; abel
        rw [e1, norm_neg]
        refine (norm_smul_le_of_le (hβ.pos _).le (hhb' k ω)).trans ?_
        have := mul_le_mul_of_nonneg_right (hRβ k).1 hCh₀
        linarith
      · have e1 : y k ω - yh k ω = -(γ (k - 1) • g k ω) := by simp only [hyh]; abel
        rw [e1, norm_neg]
        refine (norm_smul_le_of_le (hγ.pos _).le (hgb' k ω)).trans ?_
        have := mul_le_mul_of_nonneg_right (hRγ k).1 hCh₀
        linarith
  have hbd : ∀ k, ∃ C, 0 ≤ C ∧ ∀ ω, ‖e k ω‖ ≤ C ∧ ‖w k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd0 k
    set Ce := C + Rβ * Ch₀ * β k
    set Cy := C + Rγ * Ch₀ * γ k
    have hb := (hβ.pos k).le
    have hg := (hγ.pos k).le
    have hee : ∀ ω, ‖e k ω‖ ≤ Ce := fun ω => by
      have := norm_sub_le_norm_sub_add_norm_sub (e k ω) (x k ω) 0
      have h1 := (hshift k ω).1
      rw [norm_sub_rev] at h1
      simp only [sub_zero] at this
      linarith [(hC ω).1]
    have hyy : ∀ ω, ‖yh k ω‖ ≤ Cy := fun ω => by
      have := norm_sub_le_norm_sub_add_norm_sub (yh k ω) (y k ω) 0
      have h1 := (hshift k ω).2
      rw [norm_sub_rev] at h1
      simp only [sub_zero] at this
      linarith [(hC ω).2]
    refine ⟨Ce + Cy + nD * Ce, by positivity, fun ω => ⟨?_, ?_⟩⟩
    · have := hee ω; have : 0 ≤ Cy + nD * Ce := by positivity
      linarith
    · have h1 : ‖w k ω‖ ≤ ‖yh k ω‖ + nD * ‖e k ω‖ :=
        (norm_add_le _ _).trans (add_le_add_left ((matCLM D).le_opNorm _) _)
      have := mul_le_mul_of_nonneg_left (hee ω) hnD
      have := hyy ω; have : 0 ≤ Ce := by positivity
      linarith
  have hubd : ∀ k, ∃ C, ∀ ω, ‖u k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd (k + 1)
    refine ⟨C + β k * CM₀, fun ω => ?_⟩
    have e1 : u k ω = e (k + 1) ω - β k • M₁ (k + 1) ω := by rw [hxstep k ω]; abel
    rw [e1]
    exact (norm_sub_le _ _).trans (add_le_add (hC ω).1
      (norm_smul_le_of_le (hβ.pos k).le (hM₁b' k ω)))
  have hvbd : ∀ k, ∃ C, ∀ ω, ‖v k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd (k + 1)
    refine ⟨C + γ k * CMt, fun ω => ?_⟩
    have e1 : v k ω = w (k + 1) ω - γ k • Mt (k + 1) ω := by rw [hzstep k ω]; abel
    rw [e1]
    exact (norm_sub_le _ _).trans (add_le_add (hC ω).2
      (norm_smul_le_of_le (hγ.pos k).le (hMtb k ω)))
  -- the perturbations
  set Λ := LF * Ch₀ * (Rβ * Bq + Rγ) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΔb : ∀ k ω, ‖Δ₁ k ω‖ ≤ Λ * γ k ∧ ‖Δ₂ k ω‖ ≤ Λ * γ k := fun k ω => by
    have hs := hshift k ω
    have hb := hbq k
    have hdev : LF * (‖x k ω - e k ω‖ + ‖y k ω - yh k ω‖) ≤ Λ * γ k := by
      have h1 : ‖x k ω - e k ω‖ + ‖y k ω - yh k ω‖ ≤ Ch₀ * (Rβ * Bq + Rγ) * γ k := by
        have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ Rβ * Ch₀)
        nlinarith [hs.1, hs.2]
      have := mul_le_mul_of_nonneg_left h1 hLF
      simp only [hΛ]; linarith
    exact ⟨(hF₁L _ _ _ _).trans hdev, (hF₂L _ _ _ _).trans hdev⟩
  set E₁ := CΔβ * Ch₀ * Bq + Cr₀ * Bq + Λ with hE₁
  have hE₁0 : 0 ≤ E₁ := by positivity
  have hε₁b : ∀ k ω, ‖ε₁ k ω‖ ≤ E₁ * β k * γ k := fun k ω => by
    have hb := hβ.pos k
    have t1 : ‖(β k - β (k - 1)) • h k ω‖ ≤ CΔβ * β k ^ 2 * Ch₀ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hRβ k).2 (hhb' k ω) (norm_nonneg _) (by positivity)
    have t2 := norm_smul_le_of_le hb.le (hr₁b' k ω)
    have t3 := norm_smul_le_of_le hb.le (hΔb k ω).1
    have t := norm_add_three_le ((β k - β (k - 1)) • h k ω) (β k • r₁ k ω) (β k • Δ₁ k ω)
    have s1 := mul_le_mul_of_nonneg_left (hβγ' k) (by positivity : 0 ≤ CΔβ * Ch₀)
    have s2 := mul_le_mul_of_nonneg_left (hβγ' k) hCr₀
    have e1 : E₁ * β k * γ k = CΔβ * Ch₀ * (Bq * (β k * γ k)) + Cr₀ * (Bq * (β k * γ k))
        + β k * (Λ * γ k) := by simp only [hE₁]; ring
    have e2 : CΔβ * β k ^ 2 * Ch₀ = CΔβ * Ch₀ * (β k * β k) := by ring
    have e3 : β k * (Cr₀ * β k) = Cr₀ * (β k * β k) := by ring
    show ‖(β k - β (k - 1)) • h k ω + β k • r₁ k ω + β k • Δ₁ k ω‖ ≤ _
    linarith
  set E₂ := CΔγ * Ch₀ + CΔβ * Bq ^ 2 * nD * Ch₀ + Cr₀ + nD * Cr₀ * Bq ^ 2 + Λ + nD * Λ * Bq
    with hE₂
  have hE₂0 : 0 ≤ E₂ := by positivity
  have hε₂b : ∀ k ω, ‖ε₂ k ω‖ ≤ E₂ * γ k ^ 2 := fun k ω => by
    have hb := hβ.pos k
    have hg := hγ.pos k
    have hDn : ∀ {c : ℝ} (f : E d₁), ‖f‖ ≤ c → ‖matCLM D f‖ ≤ nD * c := fun f hf =>
      ((matCLM D).le_opNorm f).trans (mul_le_mul_of_nonneg_left hf hnD)
    have t1 : ‖(γ k - γ (k - 1)) • g k ω‖ ≤ CΔγ * γ k ^ 2 * Ch₀ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hRγ k).2 (hgb' k ω) (norm_nonneg _) (by positivity)
    have t2 : ‖(β k - β (k - 1)) • matCLM D (h k ω)‖ ≤ CΔβ * β k ^ 2 * (nD * Ch₀) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hRβ k).2 (hDn _ (hhb' k ω)) (norm_nonneg _) (by positivity)
    have t3 := norm_smul_le_of_le hg.le (hr₂b' k ω)
    have t4 := norm_smul_le_of_le hb.le (hDn _ (hr₁b' k ω))
    have t5 := norm_smul_le_of_le hg.le (hΔb k ω).2
    have t6 := norm_smul_le_of_le hb.le (hDn _ (hΔb k ω).1)
    have t := norm_add_six_le ((γ k - γ (k - 1)) • g k ω) ((β k - β (k - 1)) • matCLM D (h k ω))
      (γ k • r₂ k ω) (β k • matCLM D (r₁ k ω)) (γ k • Δ₂ k ω) (β k • matCLM D (Δ₁ k ω))
    have s1 := mul_le_mul_of_nonneg_left (hββ k) (by positivity : 0 ≤ CΔβ * nD * Ch₀)
    have s2 := mul_le_mul_of_nonneg_left (hββ k) (by positivity : 0 ≤ nD * Cr₀)
    have s3 := mul_le_mul_of_nonneg_left (hβγ2 k) (by positivity : 0 ≤ nD * Λ)
    have e1 : E₂ * γ k ^ 2 = CΔγ * γ k ^ 2 * Ch₀ + CΔβ * nD * Ch₀ * (Bq ^ 2 * γ k ^ 2)
        + γ k * (Cr₀ * γ k) + nD * Cr₀ * (Bq ^ 2 * γ k ^ 2) + γ k * (Λ * γ k)
        + nD * Λ * (Bq * γ k ^ 2) := by simp only [hE₂]; ring
    have e2 : CΔβ * β k ^ 2 * (nD * Ch₀) = CΔβ * nD * Ch₀ * β k ^ 2 := by ring
    have e3 : β k * (nD * (Cr₀ * β k)) = nD * Cr₀ * β k ^ 2 := by ring
    have e4 : β k * (nD * (Λ * γ k)) = nD * Λ * (β k * γ k) := by ring
    show ‖(γ k - γ (k - 1)) • g k ω + (β k - β (k - 1)) • matCLM D (h k ω) + γ k • r₂ k ω
      + β k • matCLM D (r₁ k ω) + γ k • Δ₂ k ω + β k • matCLM D (Δ₁ k ω)‖ ≤ _
    linarith
  -- the pointwise drift bounds
  set θ := (η - c₀) / 2 with hθ
  have hθ0 : 0 < θ := by simp only [hθ]; linarith
  set c₁ := K ^ 2 / η + 3 * K ^ 2 * Bβ with hc₁
  set K₂ := (1 + Bq * nD) * K with hK₂
  set c₂ := 4 * K ^ 2 + 4 * (nD * K) ^ 2 / η + K₂ ^ 2 with hc₂
  set G := (E₁ ^ 2 * Bg / θ + 3 * E₁ ^ 2 * Bγ ^ 2) + (E₂ ^ 2 * Bγ / θ + 3 * E₂ ^ 2 * Bγ ^ 2)
    with hG
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hu2 : ∀ k ω, ‖u k ω‖ ^ 2 ≤ (1 - (η - θ) * β k + (3 * K ^ 2 + (η - θ) ^ 2 / 4) * β k ^ 2)
      * ‖e k ω‖ ^ 2 + c₁ * β k * ‖w k ω‖ ^ 2 + G * β k ^ 2 := fun k ω => by
    have hb := hβ.pos k
    have hP2 := slow_step_bound (x := e k ω) (f := f₁ k ω) (zn := ‖w k ω‖) hη hb.le
      (norm_nonneg _) (hF₁in _ _) (hF₁g _ _) hK
    have hPn : ‖e k ω + β k • f₁ k ω‖ ≤ ‖e k ω‖ + β k * K * (‖e k ω‖ + ‖w k ω‖) := by
      have := norm_smul_le_of_le hb.le (hF₁g (e k ω) (yh k ω))
      have := norm_add_le (e k ω) (β k • f₁ k ω)
      have e1 : β k * (K * (‖e k ω‖ + ‖yh k ω + matCLM D (e k ω)‖)) =
          β k * K * (‖e k ω‖ + ‖w k ω‖) := by ring
      linarith
    have hU := norm_add_sq_le' (e k ω + β k • f₁ k ω) (ε₁ k ω)
    have h := slow_perturb_scalar (Bβ := Bβ) (Bγ := Bγ) (Bgb := Bg) (θ := θ) hb (hγ.pos k) hθ0
      (norm_nonneg (e k ω)) (norm_nonneg (w k ω)) (norm_nonneg _) hK hE₁0 hP2 hPn (hε₁b k ω) hU
      (hβB k) (hγB k) (hgbq k)
    have : (E₁ ^ 2 * Bg / θ + 3 * E₁ ^ 2 * Bγ ^ 2) * β k ^ 2 ≤ G * β k ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      simp only [hG]; have : 0 ≤ E₂ ^ 2 * Bγ / θ + 3 * E₂ ^ 2 * Bγ ^ 2 := by positivity
      linarith
    show ‖e k ω + β k • f₁ k ω + ε₁ k ω‖ ^ 2 ≤ _
    linarith
  have hηγ : ∀ᶠ k in atTop, η * γ k ≤ 1 := by
    have h := hγ.tendsto_zero.const_mul η
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have hv2 : ∀ᶠ k in atTop, ∀ ω, ‖v k ω‖ ^ 2 ≤
      (1 - (η - θ) * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖w k ω‖ ^ 2
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖e k ω‖ ^ 2 + G * γ k ^ 2 := by
    filter_upwards [hηγ] with k hk ω
    have hb := hβ.pos k
    have hg := hγ.pos k
    have hDf : ‖matCLM D (f₁ k ω)‖ ≤ nD * K * (‖e k ω‖ + ‖w k ω‖) := by
      have := ((matCLM D).le_opNorm (f₁ k ω)).trans
        (mul_le_mul_of_nonneg_left (hF₁g (e k ω) (yh k ω)) hnD)
      linarith [show nD * (K * (‖e k ω‖ + ‖w k ω‖)) = nD * K * (‖e k ω‖ + ‖w k ω‖) by ring]
    have hP2 := fast_step_bound (z := w k ω) (f₂ := f₂ k ω) (w := matCLM D (f₁ k ω))
      (xn := ‖e k ω‖) (K := K) (K' := nD * K) (β := β k) hη hg hk hb.le (norm_nonneg _) hK
      (by positivity) (hF₂in _ _) (hF₂g _ _) hDf
    have hPn : ‖w k ω + γ k • f₂ k ω + β k • matCLM D (f₁ k ω)‖ ≤
        ‖w k ω‖ + K₂ * γ k * (‖e k ω‖ + ‖w k ω‖) := by
      have t1 := norm_smul_le_of_le hg.le (hF₂g (e k ω) (yh k ω))
      have t2 := norm_smul_le_of_le hb.le hDf
      have t := norm_add_three_le (w k ω) (γ k • f₂ k ω) (β k • matCLM D (f₁ k ω))
      have hS : 0 ≤ nD * K * (‖e k ω‖ + ‖w k ω‖) := by positivity
      have t3 := mul_le_mul_of_nonneg_right (hbq k) hS
      have e1 : K₂ * γ k * (‖e k ω‖ + ‖w k ω‖) = γ k * (K * (‖e k ω‖ + ‖w k ω‖))
          + Bq * γ k * (nD * K * (‖e k ω‖ + ‖w k ω‖)) := by simp only [hK₂]; ring
      have e2 : γ k * (K * (‖e k ω‖ + ‖yh k ω + matCLM D (e k ω)‖)) =
          γ k * (K * (‖e k ω‖ + ‖w k ω‖)) := rfl
      linarith
    have hV := norm_add_sq_le' (w k ω + γ k • f₂ k ω + β k • matCLM D (f₁ k ω)) (ε₂ k ω)
    have h := fast_perturb_scalar (θ := θ) (Bγ := Bγ) hb hg hθ0 (norm_nonneg (e k ω))
      (norm_nonneg (w k ω)) (norm_nonneg _) (by positivity) hE₂0 hP2 hPn (hε₂b k ω) hV (hγB k)
    have : (E₂ ^ 2 * Bγ / θ + 3 * E₂ ^ 2 * Bγ ^ 2) * γ k ^ 2 ≤ G * γ k ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      simp only [hG]; have : 0 ≤ E₁ ^ 2 * Bg / θ + 3 * E₁ ^ 2 * Bγ ^ 2 := by positivity
      linarith
    show ‖w k ω + γ k • f₂ k ω + β k • matCLM D (f₁ k ω) + ε₂ k ω‖ ^ 2 ≤ _
    simp only [hc₂]
    linarith
  have hq : ∀ k, 0 ≤ 1 - (η - θ) * β k + (3 * K ^ 2 + (η - θ) ^ 2 / 4) * β k ^ 2 := fun k => by
    nlinarith [sq_nonneg (1 - (η - θ) * β k / 2), sq_nonneg (K * β k)]
  have hc₀η' : c₀ < η - θ := by simp only [hθ]; linarith
  obtain ⟨W, hW⟩ := tts_moments_of_steps (μ := μ) (η := η - θ) hβ.pos hγ.pos hβ.tendsto_zero
    hγ.tendsto_zero hβγ hc₀ hc₀η' hratio hc₁0 hc₂0 hG0 hq ℱ hem hwm hum hvm hbd hubd hvbd hM₁
    hM₁b' hmart₁ hMtm hMtb hMtmart hxstep hzstep hu2 hv2
  -- back to `x` and `y`
  have hbI : ∀ (f : Ω → ℝ), AEStronglyMeasurable f μ → (∃ C, ∀ ω, |f ω| ≤ C) →
      Integrable f μ := fun f hf ⟨C, hC⟩ => (memLp_top_of_bound hf C
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top
  have ipow : ∀ {n : ℕ} (f : Ω → E n), AEStronglyMeasurable f μ →
      (∃ C, ∀ ω, ‖f ω‖ ≤ C) → Integrable (fun ω => ‖f ω‖ ^ 4) μ := by
    intro n f hf ⟨C, hC⟩
    refine hbI _ (hf.norm.pow 4) ⟨max C 0 ^ 4, fun ω => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hC ω).trans (le_max_left _ _)) 4
  have ie : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, -, hC⟩ := hbd k
    exact ipow _ ((hem k).mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => (hC ω).1⟩
  have iw : ∀ k, Integrable (fun ω => ‖w k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, -, hC⟩ := hbd k
    exact ipow _ ((hwm k).mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => (hC ω).2⟩
  have ix : ∀ k, Integrable (fun ω => ‖x k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, -, hC⟩ := hbd0 k
    exact ipow _ ((hxm k).mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => (hC ω).1⟩
  have iy : ∀ k, Integrable (fun ω => ‖y k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, -, hC⟩ := hbd0 k
    exact ipow _ ((hym k).mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => (hC ω).2⟩
  set W₀ := max W 0
  have hW₀ : 0 ≤ W₀ := le_max_right _ _
  have hW' : ∀ k, ∫ ω, ‖e k ω‖ ^ 4 ∂μ ≤ W₀ * γ k ^ 2 ∧ ∫ ω, ‖w k ω‖ ^ 4 ∂μ ≤ W₀ * γ k ^ 2 :=
    fun k => ⟨(hW k).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)),
      (hW k).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
  -- the shifts are `O(γ)`
  set Cs := Rβ * Ch₀ * Bq + Rγ * Ch₀ with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hsh : ∀ k ω, ‖x k ω - e k ω‖ ≤ Cs * γ k ∧ ‖y k ω - yh k ω‖ ≤ Cs * γ k := fun k ω => by
    have h1 := (hshift k ω).1
    have h2 := (hshift k ω).2
    have h3 := mul_le_mul_of_nonneg_left (hbq k) (by positivity : 0 ≤ Rβ * Ch₀)
    have h4 : 0 ≤ Rγ * Ch₀ * γ k := by have := hγ.pos k; positivity
    have h5 : 0 ≤ Rβ * Ch₀ * Bq * γ k := by have := hγ.pos k; positivity
    constructor <;> nlinarith
  have hγ4 : ∀ k, (Cs * γ k) ^ 4 ≤ Cs ^ 4 * Bγ ^ 2 * γ k ^ 2 := fun k => by
    have hg := hγ.pos k
    have h1 := pow_le_pow_left₀ hg.le (hγB k) 2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Cs ^ 4 * γ k ^ 2)
    have e1 : (Cs * γ k) ^ 4 = Cs ^ 4 * γ k ^ 2 * γ k ^ 2 := by ring
    linarith
  have hint : ∀ (f : Ω → ℝ), Integrable f μ → ∀ c : ℝ,
      ∫ ω, (8 * f ω + c) ∂μ = 8 * ∫ ω, f ω ∂μ + c := fun f hf c => by
    rw [integral_add (hf.const_mul 8) (integrable_const c), integral_const_mul]
    simp
  refine ⟨8 * W₀ + 8 * Cs ^ 4 * Bγ ^ 2 + 8 * (8 * W₀ + 8 * (nD ^ 4 * W₀)
    + 8 * Cs ^ 4 * Bγ ^ 2 * (1 + 8 * nD ^ 4)), fun k => ⟨?_, ?_⟩⟩
  · have hpt : ∀ ω, ‖x k ω‖ ^ 4 ≤ 8 * ‖e k ω‖ ^ 4 + 8 * (Cs ^ 4 * Bγ ^ 2 * γ k ^ 2) := fun ω => by
      have h1 : ‖x k ω‖ ≤ ‖e k ω‖ + Cs * γ k := by
        have := norm_sub_le_norm_sub_add_norm_sub (x k ω) (e k ω) 0
        simp only [sub_zero] at this
        have := (hsh k ω).1
        linarith
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      have h3 := pow_four_add_le (norm_nonneg (e k ω))
        (by have := hγ.pos k; positivity : 0 ≤ Cs * γ k)
      have := hγ4 k
      linarith
    have i8 : Integrable (fun ω => 8 * ‖e k ω‖ ^ 4 + 8 * (Cs ^ 4 * Bγ ^ 2 * γ k ^ 2)) μ :=
      ((ie k).const_mul 8).add (integrable_const _)
    have := integral_mono (ix k) i8 hpt
    rw [hint _ (ie k)] at this
    have h1 := (hW' k).1
    have : 0 ≤ 8 * (8 * W₀ + 8 * (nD ^ 4 * W₀) + 8 * Cs ^ 4 * Bγ ^ 2 * (1 + 8 * nD ^ 4))
        * γ k ^ 2 := by positivity
    nlinarith
  · -- `y = yh - γ' g` and `yh = w - D e`
    have hpt : ∀ ω, ‖y k ω‖ ^ 4 ≤ 8 * (8 * ‖w k ω‖ ^ 4 + 8 * (nD ^ 4 * ‖e k ω‖ ^ 4))
        + 8 * (Cs ^ 4 * Bγ ^ 2 * γ k ^ 2) := fun ω => by
      have hyw : ‖yh k ω‖ ≤ ‖w k ω‖ + nD * ‖e k ω‖ := by
        have e1 : yh k ω = w k ω - matCLM D (e k ω) := by simp only [hw]; abel
        rw [e1]
        exact (norm_sub_le _ _).trans (add_le_add_left ((matCLM D).le_opNorm _) _)
      have h1 : ‖y k ω‖ ≤ ‖yh k ω‖ + Cs * γ k := by
        have := norm_sub_le_norm_sub_add_norm_sub (y k ω) (yh k ω) 0
        simp only [sub_zero] at this
        have := (hsh k ω).2
        linarith
      have hp : 0 ≤ nD * ‖e k ω‖ := by positivity
      have hq' : 0 ≤ Cs * γ k := by have := hγ.pos k; positivity
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (h1.trans (add_le_add_right hyw _)) 4
      have h3 := pow_four_add_le (add_nonneg (norm_nonneg (w k ω)) hp) hq'
      have h4 := pow_four_add_le (norm_nonneg (w k ω)) hp
      have e1 : (nD * ‖e k ω‖) ^ 4 = nD ^ 4 * ‖e k ω‖ ^ 4 := by ring
      have := hγ4 k
      nlinarith
    have iwe : Integrable (fun ω => 8 * ‖w k ω‖ ^ 4 + 8 * (nD ^ 4 * ‖e k ω‖ ^ 4)) μ :=
      ((iw k).const_mul 8).add (((ie k).const_mul _).const_mul 8)
    have i8 : Integrable (fun ω => 8 * (8 * ‖w k ω‖ ^ 4 + 8 * (nD ^ 4 * ‖e k ω‖ ^ 4))
        + 8 * (Cs ^ 4 * Bγ ^ 2 * γ k ^ 2)) μ := (iwe.const_mul 8).add (integrable_const _)
    have := integral_mono (iy k) i8 hpt
    rw [hint _ iwe] at this
    have e2 : ∫ ω, (8 * ‖w k ω‖ ^ 4 + 8 * (nD ^ 4 * ‖e k ω‖ ^ 4)) ∂μ =
        8 * ∫ ω, ‖w k ω‖ ^ 4 ∂μ + 8 * (nD ^ 4 * ∫ ω, ‖e k ω‖ ^ 4 ∂μ) := by
      rw [integral_add ((iw k).const_mul 8) (((ie k).const_mul _).const_mul 8),
        integral_const_mul, integral_const_mul, integral_const_mul]
    rw [e2] at this
    have h1 := (hW' k).1
    have h2 := (hW' k).2
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ nD ^ 4)
    have p1 : 0 ≤ W₀ * γ k ^ 2 := by positivity
    have p2 : 0 ≤ Cs ^ 4 * Bγ ^ 2 * (1 + 8 * nD ^ 4) * γ k ^ 2 := by positivity
    linarith

set_option maxHeartbeats 8000000 in
/-- **Assumption 2.2 for two time scales with Markov noise.** The iteration of
`moment_bounds_tts_markov`, with drifts linear to first order,
`F(x, y) = -A(x, y) + O(‖x‖² + ‖y‖²)` with `A₂₂ D = A₂₁`, and martingale covariances within
`δ_k + C(R + R²)` of `Γ`, has the asymptotic covariances of its linearization. -/
theorem tendsto_tts_dissipative_markov {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0)) {η c₀ K L LF CM Ch Cr : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η) (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hLF : 0 ≤ LF)
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η' : ℝ} (hη' : 0 < η')
    (hΔ : ∀ x, η' * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η' * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x M₁ h r₁ : ℕ → Ω → E d₁} {y M₂ g r₂ : ℕ → Ω → E d₂}
    {F₁ : E d₁ → E d₂ → E d₁} {F₂ : E d₁ → E d₂ → E d₂}
    (hF₁in : ∀ u w, ⟪u, F₁ u w⟫_ℝ ≤ -η * ‖u‖ ^ 2 + K * ‖u‖ * ‖w + matCLM D u‖)
    (hF₁g : ∀ u w, ‖F₁ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₂in : ∀ u w, ⟪w + matCLM D u, F₂ u w⟫_ℝ ≤ -η * ‖w + matCLM D u‖ ^ 2)
    (hF₂g : ∀ u w, ‖F₂ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₁L : ∀ u w u' w', ‖F₁ u w - F₁ u' w'‖ ≤ LF * (‖u - u'‖ + ‖w - w'‖))
    (hF₂L : ∀ u w u' w', ‖F₂ u w - F₂ u' w'‖ ≤ LF * (‖u - u'‖ + ‖w - w'‖))
    (hF₁ : ∀ u w, ‖F₁ u w + (matCLM A₁₁ u + matCLM A₁₂ w)‖ ≤ L * (‖u‖ ^ 2 + ‖w‖ ^ 2))
    (hF₂ : ∀ u w, ‖F₂ u w + (matCLM A₂₁ u + matCLM A₂₂ w)‖ ≤ L * (‖u‖ ^ 2 + ‖w‖ ^ 2))
    (hF₁c : Continuous fun p : E d₁ × E d₂ => F₁ p.1 p.2)
    (hF₂c : Continuous fun p : E d₁ × E d₂ => F₂ p.1 p.2)
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • (F₁ (x k ω) (y k ω) + M₁ (k + 1) ω + r₁ k ω
      + h k ω - h (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • (F₂ (x k ω) (y k ω) + M₂ (k + 1) ω + r₂ k ω
      + g k ω - g (k + 1) ω))
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hym : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hx0 : ∃ C, ∀ ω, ‖x 0 ω‖ ≤ C) (hy0 : ∃ C, ∀ ω, ‖y 0 ω‖ ≤ C)
    (hhm : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhb : ∀ k ω, ‖h k ω‖ ≤ Ch)
    (hgm : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgb : ∀ k ω, ‖g k ω‖ ≤ Ch)
    (hr₁m : ∀ k, StronglyMeasurable[ℱ k] (r₁ k)) (hr₁b : ∀ k ω, ‖r₁ k ω‖ ≤ Cr * β k)
    (hr₂m : ∀ k, StronglyMeasurable[ℱ k] (r₂ k)) (hr₂b : ∀ k ω, ‖r₂ k ω‖ ≤ Cr * γ k)
    (hM₁ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₁ (k + 1))) (hM₁b : ∀ k ω, ‖M₁ (k + 1) ω‖ ≤ CM)
    (hmart₁ : ∀ k j, μ[fun ω => M₁ (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hM₂ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₂ (k + 1))) (hM₂b : ∀ k ω, ‖M₂ (k + 1) ω‖ ≤ CM)
    (hmart₂ : ∀ k j, μ[fun ω => M₂ (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 ≤ C) {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂} {δ₁ δ₂ δ₃ : ℕ → ℝ}
    (hδ₁0 : ∀ k, 0 ≤ δ₁ k) (hδ₂0 : ∀ k, 0 ≤ δ₂ k) (hδ₃0 : ∀ k, 0 ≤ δ₃ k)
    (hδ₁ : Tendsto δ₁ atTop (𝓝 0)) (hδ₂ : Tendsto δ₂ atTop (𝓝 0)) (hδ₃ : Tendsto δ₃ atTop (𝓝 0))
    (dev₁ : ∀ k, ‖secondMoment μ (M₁ (k + 1)) - Γ₁₁‖ ≤
      δ₁ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₂ : ∀ k, ‖crossMoment μ (M₁ (k + 1)) (M₂ (k + 1)) - Γ₁₂‖ ≤
      δ₂ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₃ : ∀ k, ‖secondMoment μ (M₂ (k + 1)) - Γ₂₂‖ ≤
      δ₃ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  obtain ⟨hbd, W, hW⟩ := moment_bounds_tts_markov (μ := μ) hβ hγ hβγ hγβ hc₀ hc₀η hratio hK
    hLF ℱ D hF₁in hF₁g hF₂in hF₂g hF₁L hF₂L hF₁c hF₂c hx hy hxm hym hx0 hy0 hhm hhb hgm hgb
    hr₁m hr₁b hr₂m hr₂b hM₁ hM₁b hmart₁ hM₂ hM₂b hmart₂
  set B₀ := max (max CM 0) (max Ch 0)
  have hB₀ : 0 ≤ B₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCMB : CM ≤ B₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hChB : Ch ≤ B₀ := (le_max_left _ _).trans (le_max_right _ _)
  set C' := max C B₀
  have hC' : 0 ≤ C' := le_trans hC (le_max_left _ _)
  have hxL : ∀ k, MemLp (x k) 2 μ := fun k => by
    obtain ⟨B, hB⟩ := hbd k
    exact MemLp.of_bound ((hxm k).mono (ℱ.le k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => (hB ω).1)
  have hyL : ∀ k, MemLp (y k) 2 μ := fun k => by
    obtain ⟨B, hB⟩ := hbd k
    exact MemLp.of_bound ((hym k).mono (ℱ.le k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => (hB ω).2)
  have hhL : ∀ k, MemLp (h k) 2 μ := fun k =>
    MemLp.of_bound ((hhm k).mono (ℱ.le k)).aestronglyMeasurable Ch (Eventually.of_forall (hhb k))
  have hgL : ∀ k, MemLp (g k) 2 μ := fun k =>
    MemLp.of_bound ((hgm k).mono (ℱ.le k)).aestronglyMeasurable Ch (Eventually.of_forall (hgb k))
  have hM₁L : ∀ k, MemLp (M₁ (k + 1)) 2 μ := fun k =>
    MemLp.of_bound ((hM₁ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM
      (Eventually.of_forall (hM₁b k))
  have hM₂L : ∀ k, MemLp (M₂ (k + 1)) 2 μ := fun k =>
    MemLp.of_bound ((hM₂ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM
      (Eventually.of_forall (hM₂b k))
  have hR0 : ∀ k, 0 ≤ rms μ (x k) + rms μ (y k) := fun k => add_nonneg (rms_nonneg _) (rms_nonneg _)
  have rB : ∀ {n : ℕ} (f : Ω → E n) {c : ℝ}, (∀ ω, ‖f ω‖ ≤ c) → c ≤ B₀ → rms μ f ≤ C' := by
    intro n f c hb hc
    have h1 : rms μ f ≤ B₀ := by
      unfold rms
      refine Real.sqrt_le_iff.mpr ⟨hB₀, ?_⟩
      calc ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ ∫ _ω, B₀ ^ 2 ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
              (integrable_const _) (Eventually.of_forall fun ω =>
                pow_le_pow_left₀ (norm_nonneg _) ((hb ω).trans hc) 2)
        _ = B₀ ^ 2 := by simp
    exact h1.trans (le_max_right _ _)
  have rM : ∀ {n : ℕ} (M : Ω → E n), (∀ ω, ‖M ω‖ ≤ CM) → ∀ k,
      rms μ M ≤ C' * (1 + (rms μ (x k) + rms μ (y k))) := fun M hb k => by
    have := rB M hb hCMB
    have := hR0 k
    nlinarith
  have hup : ∀ t : ℝ, 0 ≤ t → C * t ≤ C' * t := fun t ht =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) ht
  refine tendsto_tts_taylor hβ hγ hβγ hγβ A₁₁ A₁₂ A₂₁ A₂₂ D hD hη' hΔ hA₂₂ ℱ
    (Cr := Cr) (C₄ := W) hL hF₁ hF₂ hF₁c hF₂c hx hy hxm hym (hxL 0) (hyL 0)
    hhm hhL hgm hgL hM₁ hM₁L hM₂ hM₂L (fun k => (hr₁m k).mono (ℱ.mono k.le_succ)) hr₁b
    (fun k => (hr₂m k).mono (ℱ.mono k.le_succ)) hr₂b ?_ ?_
    (fun k => (hW k).1) (fun k => (hW k).2) hmart₁ hmart₂ hC'
    (fun k => rB _ (hhb k) hChB) (fun k => rB _ (hgb k) hChB)
    (fun k => rM _ (hM₁b k) k) (fun k => rM _ (hM₂b k) k)
    hδ₁0 hδ₂0 hδ₃0 hδ₁ hδ₂ hδ₃
    (fun k => (dev₁ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₂ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₃ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
  · intro k
    obtain ⟨B, hB⟩ := hbd k
    refine (memLp_top_of_bound (((hxm k).mono (ℱ.le k)).aestronglyMeasurable.norm.pow 4) (B ^ 4)
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    show ‖‖x k ω‖ ^ 4‖ ≤ B ^ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB ω).1 4
  · intro k
    obtain ⟨B, hB⟩ := hbd k
    refine (memLp_top_of_bound (((hym k).mono (ℱ.le k)).aestronglyMeasurable.norm.pow 4) (B ^ 4)
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    show ‖‖y k ω‖ ^ 4‖ ≤ B ^ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB ω).2 4

end Main

end StochasticApproximation
