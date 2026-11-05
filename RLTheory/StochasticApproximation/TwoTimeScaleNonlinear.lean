/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TwoTimeScaleMultiplicative

/-!
# Two time scales: linearization

Assumption 2.2 of `docs/actor-critic-rates.md` for the two-time-scale (actor-critic) iteration.

* `tendsto_tts_nonlinear`: the linear two-time-scale theorem with a remainder in the drift.
  The slow iterate `x` and the fast iterate `y` follow the linear recursion plus remainders
  `ρ₁, ρ₂` with `rms ρ_i ≤ C γ_k (1 + rms x_k + rms y_k)`, plus martingale differences
  `m, m'` (which may depend on the iterates, with covariances close to `Γ` when the iterates are
  small) and bounded Poisson shifts `h, g`. The conclusions of Theorem 2.1 of the
  two-time-scale note hold.
* `tendsto_tts_taylor`: the remainder is a Taylor remainder `O(‖x‖² + ‖y‖²)` of the drift plus a
  remainder of order `β_k` (slow) and `γ_k` (fast), from sampling under the current parameter.
  It is controlled by fourth moments `E‖x_k‖⁴ = O(γ_k²)` and `E‖y_k‖⁴ = O(γ_k²)`.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory

namespace StochasticApproximation

variable {d₁ d₂ : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The root mean square of one step of a linear recursion with additive terms. -/
lemma rms_lin_step {n p q : ℕ} {s : ℝ} (hs : 0 ≤ s) (A : Matrix (Fin n) (Fin p) ℝ)
    (A' : Matrix (Fin n) (Fin q) ℝ) {xn xn1 v₁ v₂ v₃ v₄ : Ω → E n} {u : Ω → E p} {w : Ω → E q}
    (hxL : MemLp xn 2 μ) (huL : MemLp u 2 μ) (hwL : MemLp w 2 μ) (h1 : MemLp v₁ 2 μ)
    (h2 : MemLp v₂ 2 μ) (h3 : MemLp v₃ 2 μ) (h4 : MemLp v₄ 2 μ)
    (hrec : ∀ ω, xn1 ω = xn ω - s • (matCLM A (u ω) + matCLM A' (w ω))
      + s • (v₁ ω + v₂ ω + v₃ ω - v₄ ω)) :
    rms μ xn1 ≤ rms μ xn + s * (‖matCLM A‖ * rms μ u + ‖matCLM A'‖ * rms μ w
      + (rms μ v₁ + rms μ v₂ + rms μ v₃ + rms μ v₄)) := by
  have hAu : MemLp (fun ω => matCLM A (u ω)) 2 μ := (matCLM A).comp_memLp' huL
  have hAw : MemLp (fun ω => matCLM A' (w ω)) 2 μ := (matCLM A').comp_memLp' hwL
  have hlin : MemLp (fun ω => matCLM A (u ω) + matCLM A' (w ω)) 2 μ := hAu.add hAw
  have h12 : MemLp (fun ω => v₁ ω + v₂ ω) 2 μ := h1.add h2
  have h123 : MemLp (fun ω => v₁ ω + v₂ ω + v₃ ω) 2 μ := h12.add h3
  have hv : MemLp (fun ω => v₁ ω + v₂ ω + v₃ ω - v₄ ω) 2 μ := h123.sub h4
  have e : xn1 = fun ω => (xn ω - s • (matCLM A (u ω) + matCLM A' (w ω)))
      + s • (v₁ ω + v₂ ω + v₃ ω - v₄ ω) := funext hrec
  have hsL : MemLp (fun ω => s • (matCLM A (u ω) + matCLM A' (w ω))) 2 μ := hlin.const_smul s
  have hsv : MemLp (fun ω => s • (v₁ ω + v₂ ω + v₃ ω - v₄ ω)) 2 μ := hv.const_smul s
  have hd : MemLp (fun ω => xn ω - s • (matCLM A (u ω) + matCLM A' (w ω))) 2 μ := hxL.sub hsL
  rw [e]
  refine (rms_add_le' hd hsv).trans ?_
  have t1 := rms_sub_le' (μ := μ) hxL hsL
  rw [rms_smul, abs_of_nonneg hs] at t1
  rw [rms_smul, abs_of_nonneg hs]
  have t2 := (rms_add_le' (μ := μ) hAu hAw).trans (add_le_add (rms_matCLM_le A huL)
    (rms_matCLM_le A' hwL))
  have t3 := (rms_sub_le' (μ := μ) h123 h4).trans (add_le_add_right ((rms_add_le' h12 h3).trans
    (add_le_add_right (rms_add_le' h1 h2) _)) _)
  have := mul_le_mul_of_nonneg_left t2 hs
  have := mul_le_mul_of_nonneg_left t3 hs
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Two time scales with a remainder in the drift.** Let
`x_{k+1} = x_k - β_k (A₁₁ x_k + A₁₂ y_k) + β_k (m_{k+1} + ρ₁_k + h_k - h_{k+1})` and
`y_{k+1} = y_k - γ_k (A₂₁ x_k + A₂₂ y_k) + γ_k (m'_{k+1} + ρ₂_k + g_k - g_{k+1})`, with martingale
differences `m, m'` (of size `C(1 + R_k)`, covariances within `δ + C(R + R²)` of `Γ`), bounded
shifts `h, g` and remainders with `rms ρ_i ≤ C γ_k (1 + R_k)`, where `R_k = rms x_k + rms y_k`.
Then the conclusions of the linear two-time-scale theorem hold. -/
theorem tendsto_tts_nonlinear [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x m ρ₁ h : ℕ → Ω → E d₁} {y m' ρ₂ g : ℕ → Ω → E d₂}
    (hx : ∀ k ω, x (k + 1) ω = x k ω - β k • (matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω))
      + β k • (m (k + 1) ω + ρ₁ k ω + h k ω - h (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω - γ k • (matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω))
      + γ k • (m' (k + 1) ω + ρ₂ k ω + g k ω - g (k + 1) ω))
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
    (hhm : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hgm : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
    (hmm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (m (k + 1))) (hmL : ∀ k, MemLp (m (k + 1)) 2 μ)
    (hm'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (m' (k + 1)))
    (hm'L : ∀ k, MemLp (m' (k + 1)) 2 μ)
    (hρ₁m : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ρ₁ k)) (hρ₁L : ∀ k, MemLp (ρ₁ k) 2 μ)
    (hρ₂m : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ρ₂ k)) (hρ₂L : ∀ k, MemLp (ρ₂ k) 2 μ)
    (hmart : ∀ k j, μ[fun ω => m (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hmart' : ∀ k j, μ[fun ω => m' (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 ≤ C) (rh : ∀ k, rms μ (h k) ≤ C) (rg : ∀ k, rms μ (g k) ≤ C)
    (rm : ∀ k, rms μ (m (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rm' : ∀ k, rms μ (m' (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rρ₁ : ∀ k, rms μ (ρ₁ k) ≤ C * γ k * (1 + (rms μ (x k) + rms μ (y k))))
    (rρ₂ : ∀ k, rms μ (ρ₂ k) ≤ C * γ k * (1 + (rms μ (x k) + rms μ (y k))))
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂} {δ₁ δ₂ δ₃ : ℕ → ℝ}
    (hδ₁0 : ∀ k, 0 ≤ δ₁ k) (hδ₂0 : ∀ k, 0 ≤ δ₂ k) (hδ₃0 : ∀ k, 0 ≤ δ₃ k)
    (hδ₁ : Tendsto δ₁ atTop (𝓝 0)) (hδ₂ : Tendsto δ₂ atTop (𝓝 0)) (hδ₃ : Tendsto δ₃ atTop (𝓝 0))
    (dev₁ : ∀ k, ‖secondMoment μ (m (k + 1)) - Γ₁₁‖ ≤
      δ₁ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₂ : ∀ k, ‖crossMoment μ (m (k + 1)) (m' (k + 1)) - Γ₁₂‖ ≤
      δ₂ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₃ : ∀ k, ‖secondMoment μ (m' (k + 1)) - Γ₂₂‖ ≤
      δ₃ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  -- step-size bounds
  obtain ⟨Bb, hBb⟩ := hβ.tendsto_zero.bddAbove_range
  obtain ⟨Bg, hBg⟩ := hγ.tendsto_zero.bddAbove_range
  obtain ⟨Bq₀, hBq₀⟩ := hβγ.bddAbove_range
  have hβB : ∀ k, β k ≤ Bb := fun k => hBb ⟨k, rfl⟩
  have hγB : ∀ k, γ k ≤ Bg := fun k => hBg ⟨k, rfl⟩
  have hBb0 : 0 ≤ Bb := (hβ.pos 0).le.trans (hβB 0)
  have hBg0 : 0 ≤ Bg := (hγ.pos 0).le.trans (hγB 0)
  set Bq := max Bq₀ 0
  have hBq0 : 0 ≤ Bq := le_max_right _ _
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have h1 : β k / γ k ≤ Bq := (hBq₀ ⟨k, rfl⟩).trans (le_max_left _ _)
    rwa [div_le_iff₀ (hγ.pos k)] at h1
  -- the iterates are in `L²`
  have hxyL : ∀ k, MemLp (x k) 2 μ ∧ MemLp (y k) 2 μ := by
    intro k
    induction k with
    | zero => exact ⟨hx0L, hy0L⟩
    | succ k ih =>
      obtain ⟨hxk, hyk⟩ := ih
      have hAx : MemLp (fun ω => matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω)) 2 μ :=
        ((matCLM A₁₁).comp_memLp' hxk).add ((matCLM A₁₂).comp_memLp' hyk)
      have hAy : MemLp (fun ω => matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω)) 2 μ :=
        ((matCLM A₂₁).comp_memLp' hxk).add ((matCLM A₂₂).comp_memLp' hyk)
      have hvx : MemLp (fun ω => m (k + 1) ω + ρ₁ k ω + h k ω - h (k + 1) ω) 2 μ :=
        (((hmL k).add (hρ₁L k)).add (hhL k)).sub (hhL (k + 1))
      have hvy : MemLp (fun ω => m' (k + 1) ω + ρ₂ k ω + g k ω - g (k + 1) ω) 2 μ :=
        (((hm'L k).add (hρ₂L k)).add (hgL k)).sub (hgL (k + 1))
      refine ⟨?_, ?_⟩
      · rw [show x (k + 1) = _ from funext (hx k)]
        exact (hxk.sub (hAx.const_smul (β k))).add (hvx.const_smul (β k))
      · rw [show y (k + 1) = _ from funext (hy k)]
        exact (hyk.sub (hAy.const_smul (γ k))).add (hvy.const_smul (γ k))
  have hxL := fun k => (hxyL k).1
  have hyL := fun k => (hxyL k).2
  set R : ℕ → ℝ := fun k => rms μ (x k) + rms μ (y k) with hR
  have hR0 : ∀ k, 0 ≤ R k := fun k => add_nonneg (rms_nonneg _) (rms_nonneg _)
  -- the constants
  set a := ‖matCLM A₁₁‖ + ‖matCLM A₁₂‖ + ‖matCLM A₂₁‖ + ‖matCLM A₂₂‖ with ha
  have ha0 : 0 ≤ a := by positivity
  set K₁ := 2 + (Bb + Bg) * (a + 3 * C + C * Bg) with hK₁
  set nD := ‖matCLM D‖
  set K₂ := 1 + nD + Bq * C * (1 + 2 * nD) + C with hK₂
  set Cs := C + K₁ + K₂ with hCs
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hCCs : C ≤ Cs := by linarith
  -- one step
  have hR1 : ∀ k, rms μ (x (k + 1)) + rms μ (y (k + 1)) ≤ Cs * (1 + (rms μ (x k) + rms μ (y k))) := by
    intro k
    have hb := hβ.pos k
    have hg := hγ.pos k
    have sx := rms_lin_step (μ := μ) hb.le A₁₁ A₁₂ (hxL k) (hxL k) (hyL k) (hmL k) (hρ₁L k)
      (hhL k) (hhL (k + 1)) (hx k)
    have sy := rms_lin_step (μ := μ) hg.le A₂₁ A₂₂ (hyL k) (hxL k) (hyL k) (hm'L k) (hρ₂L k)
      (hgL k) (hgL (k + 1)) (hy k)
    have hrx : ‖matCLM A₁₁‖ * rms μ (x k) + ‖matCLM A₁₂‖ * rms μ (y k) ≤ a * R k := by
      have := rms_nonneg (μ := μ) (x k); have := rms_nonneg (μ := μ) (y k)
      simp only [ha, hR]; nlinarith [norm_nonneg (matCLM A₂₁), norm_nonneg (matCLM A₂₂),
        norm_nonneg (matCLM A₁₁), norm_nonneg (matCLM A₁₂)]
    have hry : ‖matCLM A₂₁‖ * rms μ (x k) + ‖matCLM A₂₂‖ * rms μ (y k) ≤ a * R k := by
      have := rms_nonneg (μ := μ) (x k); have := rms_nonneg (μ := μ) (y k)
      simp only [ha, hR]; nlinarith [norm_nonneg (matCLM A₂₁), norm_nonneg (matCLM A₂₂),
        norm_nonneg (matCLM A₁₁), norm_nonneg (matCLM A₁₂)]
    have hvb : ∀ (r₁ r₂ r₃ r₄ : ℝ), r₁ ≤ C * (1 + R k) → r₂ ≤ C * γ k * (1 + R k) → r₃ ≤ C →
        r₄ ≤ C → r₁ + r₂ + r₃ + r₄ ≤ (3 * C + C * Bg) * (1 + R k) := by
      intro r₁ r₂ r₃ r₄ h1 h2 h3 h4
      have h5 : C * γ k * (1 + R k) ≤ C * Bg * (1 + R k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hγB k) hC) (by linarith [hR0 k])
      nlinarith [hR0 k]
    have vx := hvb _ _ _ _ (rm k) (rρ₁ k) (rh k) (rh (k + 1))
    have vy := hvb _ _ _ _ (rm' k) (rρ₂ k) (rg k) (rg (k + 1))
    have hsx : rms μ (x (k + 1)) ≤ R k + Bb * ((a + 3 * C + C * Bg) * (1 + R k)) := by
      have : β k * (‖matCLM A₁₁‖ * rms μ (x k) + ‖matCLM A₁₂‖ * rms μ (y k)
          + (rms μ (m (k + 1)) + rms μ (ρ₁ k) + rms μ (h k) + rms μ (h (k + 1)))) ≤
          Bb * ((a + 3 * C + C * Bg) * (1 + R k)) := by
        refine mul_le_mul (hβB k) ?_ (by
          have := rms_nonneg (μ := μ) (x k); have := rms_nonneg (μ := μ) (y k)
          have := rms_nonneg (μ := μ) (m (k + 1)); have := rms_nonneg (μ := μ) (ρ₁ k)
          have := rms_nonneg (μ := μ) (h k); have := rms_nonneg (μ := μ) (h (k + 1))
          positivity) hBb0
        nlinarith [hR0 k]
      have := rms_nonneg (μ := μ) (y k)
      simp only [hR] at this ⊢
      linarith
    have hsy : rms μ (y (k + 1)) ≤ R k + Bg * ((a + 3 * C + C * Bg) * (1 + R k)) := by
      have : γ k * (‖matCLM A₂₁‖ * rms μ (x k) + ‖matCLM A₂₂‖ * rms μ (y k)
          + (rms μ (m' (k + 1)) + rms μ (ρ₂ k) + rms μ (g k) + rms μ (g (k + 1)))) ≤
          Bg * ((a + 3 * C + C * Bg) * (1 + R k)) := by
        refine mul_le_mul (hγB k) ?_ (by
          have := rms_nonneg (μ := μ) (x k); have := rms_nonneg (μ := μ) (y k)
          have := rms_nonneg (μ := μ) (m' (k + 1)); have := rms_nonneg (μ := μ) (ρ₂ k)
          have := rms_nonneg (μ := μ) (g k); have := rms_nonneg (μ := μ) (g (k + 1))
          positivity) hBg0
        nlinarith [hR0 k]
      have := rms_nonneg (μ := μ) (x k)
      simp only [hR] at this ⊢
      linarith
    have : rms μ (x (k + 1)) + rms μ (y (k + 1)) ≤ K₁ * (1 + R k) := by
      simp only [hK₁]; nlinarith [hR0 k]
    have h2 : K₁ * (1 + R k) ≤ Cs * (1 + R k) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hR0 k])
    simp only [hR] at this h2
    linarith
  -- the iterates are controlled by the shifted iterates
  have hinv : ∀ k, rms μ (x k) + rms μ (y k) ≤
      Cs * (rms μ (ttsX β x h k) + rms μ (ttsY D β γ x h y g k) + γ k) := by
    intro k
    have hb := hβ.pos k
    have hg := hγ.pos k
    have hXL : MemLp (ttsX β x h k) 2 μ := (hxL k).add ((hhL k).const_smul (β k))
    have hDx : MemLp (fun ω => matCLM D (x k ω)) 2 μ := (matCLM D).comp_memLp' (hxL k)
    have hDh : MemLp (fun ω => matCLM D (h k ω)) 2 μ := (matCLM D).comp_memLp' (hhL k)
    have hYL : MemLp (ttsY D β γ x h y g k) 2 μ :=
      (((hyL k).add hDx).add ((hgL k).const_smul (γ k))).add (hDh.const_smul (β k))
    -- the slow iterate
    have ex : x k = fun ω => ttsX β x h k ω - β k • h k ω := by
      funext ω; simp only [ttsX]; abel
    have hβh : MemLp (fun ω => β k • h k ω) 2 μ := (hhL k).const_smul (β k)
    have hγg : MemLp (fun ω => γ k • g k ω) 2 μ := (hgL k).const_smul (γ k)
    have hβDh : MemLp (fun ω => β k • matCLM D (h k ω)) 2 μ := hDh.const_smul (β k)
    have rx : rms μ (x k) ≤ rms μ (ttsX β x h k) + Bq * γ k * C := by
      have t := rms_sub_le' (μ := μ) hXL hβh
      rw [rms_smul, abs_of_pos hb] at t
      rw [ex]
      refine t.trans (add_le_add_left ?_ _)
      calc β k * rms μ (h k) ≤ (Bq * γ k) * C := mul_le_mul (hbq k) (rh k) (rms_nonneg _)
            (by positivity)
        _ = Bq * γ k * C := rfl
    -- the fast iterate
    have hS : MemLp (fun ω => matCLM D (x k ω) + γ k • g k ω) 2 μ := hDx.add hγg
    have hS2 : MemLp (fun ω => matCLM D (x k ω) + γ k • g k ω + β k • matCLM D (h k ω)) 2 μ :=
      hS.add hβDh
    have ey : y k = fun ω => ttsY D β γ x h y g k ω
        - (matCLM D (x k ω) + γ k • g k ω + β k • matCLM D (h k ω)) := by
      funext ω; simp only [ttsY]; abel
    have ry : rms μ (y k) ≤ rms μ (ttsY D β γ x h y g k) + nD * rms μ (x k) + γ k * C
        + Bq * γ k * (nD * C) := by
      rw [ey]
      refine (rms_sub_le' hYL hS2).trans ?_
      have t1 := (rms_add_le' (μ := μ) hS hβDh).trans (add_le_add_right
        (rms_add_le' (μ := μ) hDx hγg) _)
      rw [rms_smul, abs_of_pos hg, rms_smul, abs_of_pos hb] at t1
      have t2 := rms_matCLM_le (μ := μ) D (hxL k)
      have t3 : γ k * rms μ (g k) ≤ γ k * C := mul_le_mul_of_nonneg_left (rg k) hg.le
      have t4 : β k * rms μ (fun ω => matCLM D (h k ω)) ≤ Bq * γ k * (nD * C) :=
        mul_le_mul (hbq k) ((rms_matCLM_le (μ := μ) D (hhL k)).trans
          (mul_le_mul_of_nonneg_left (rh k) (norm_nonneg _))) (rms_nonneg _) (by positivity)
      linarith
    have hX0 := rms_nonneg (μ := μ) (ttsX β x h k)
    have hY0 := rms_nonneg (μ := μ) (ttsY D β γ x h y g k)
    have hnD : 0 ≤ nD := norm_nonneg _
    have key : rms μ (x k) + rms μ (y k) ≤ K₂ * (rms μ (ttsX β x h k)
        + rms μ (ttsY D β γ x h y g k) + γ k) := by
      have h1 := mul_le_mul_of_nonneg_left rx hnD
      simp only [hK₂]
      nlinarith [mul_nonneg hBq0 hC, mul_nonneg (mul_nonneg hBq0 hC) hnD, hg.le]
    exact key.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  -- the hypotheses with the common constant
  have hCs0 : 0 ≤ Cs := by linarith
  have hup : ∀ (_k : ℕ) (t : ℝ), 0 ≤ t → C * t ≤ Cs * t := fun _ t ht =>
    mul_le_mul_of_nonneg_right hCCs ht
  have rneg₁ : ∀ k, rms μ (fun ω => -ρ₁ k ω) = rms μ (ρ₁ k) := fun k => by
    have : (fun ω => -ρ₁ k ω) = fun ω => (-1 : ℝ) • ρ₁ k ω := by funext ω; simp
    rw [this, rms_smul]; simp
  have rneg₂ : ∀ k, rms μ (fun ω => -ρ₂ k ω) = rms μ (ρ₂ k) := fun k => by
    have : (fun ω => -ρ₂ k ω) = fun ω => (-1 : ℝ) • ρ₂ k ω := by funext ω; simp
    rw [this, rms_smul]; simp
  exact tendsto_tts_perturbed hβ hγ hβγ hγβ A₁₁ A₁₂ A₂₁ A₂₂ D hD hη hΔ hA₂₂ ℱ
    (Mx := fun n ω => m n ω + ρ₁ (n - 1) ω) (ηp := h) (m := m) (ρ := fun k ω => -ρ₁ k ω)
    (My := fun n ω => m' n ω + ρ₂ (n - 1) ω) (ζ := g) (m' := m') (ρ' := fun k ω => -ρ₂ k ω)
    ⟨fun k ω => hx k ω, fun k ω => hy k ω⟩
    (fun k ω => (sub_neg_eq_add _ _).symm) (fun k ω => (sub_neg_eq_add _ _).symm)
    hx0 hx0L hy0 hy0L hhm hhL hgm hgL hmm hmL hm'm hm'L
    (fun k => (hρ₁m k).neg) (fun k => (hρ₁L k).neg) (fun k => (hρ₂m k).neg)
    (fun k => (hρ₂L k).neg) hmart hmart' hCs0
    (fun k => (rh k).trans (by nlinarith [hR0 k]))
    (fun k => (rg k).trans (by nlinarith [hR0 k]))
    (fun k => (rm k).trans (hup k _ (by linarith [hR0 k])))
    (fun k => (rm' k).trans (hup k _ (by linarith [hR0 k])))
    (fun k => by
      rw [rneg₁]
      refine (rρ₁ k).trans ?_
      have := mul_le_mul_of_nonneg_right hCCs (mul_nonneg (hγ.pos k).le (by linarith [hR0 k] :
        (0 : ℝ) ≤ 1 + R k))
      simp only [hR] at this ⊢
      nlinarith)
    (fun k => by
      rw [rneg₂]
      refine (rρ₂ k).trans ?_
      have := mul_le_mul_of_nonneg_right hCCs (mul_nonneg (hγ.pos k).le (by linarith [hR0 k] :
        (0 : ℝ) ≤ 1 + R k))
      simp only [hR] at this ⊢
      nlinarith)
    hR1 hinv hδ₁0 hδ₂0 hδ₃0 hδ₁ hδ₂ hδ₃
    (fun k => (dev₁ k).trans (add_le_add_left (hup k _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₂ k).trans (add_le_add_left (hup k _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₃ k).trans (add_le_add_left (hup k _ (by nlinarith [hR0 k])) _))

/-- The size of a Taylor remainder: if `‖ρ‖ ≤ L (‖x‖² + ‖y‖²) + c` pointwise, with
`E‖x‖⁴ ≤ C₄ s²`, `E‖y‖⁴ ≤ C₄ t²`, then `rms ρ ≤ √(4L²C₄ (s² + t²) + 2c²)`. -/
lemma rms_taylor_le [IsProbabilityMeasure μ] {n p q : ℕ} {ρ : Ω → E n} {x : Ω → E p} {y : Ω → E q}
    {L c C₄ s t : ℝ} (hρL : MemLp ρ 2 μ) (hx4 : Integrable (fun ω => ‖x ω‖ ^ 4) μ)
    (hy4 : Integrable (fun ω => ‖y ω‖ ^ 4) μ) (hL : 0 ≤ L) (_hc : 0 ≤ c)
    (hb : ∀ ω, ‖ρ ω‖ ≤ L * (‖x ω‖ ^ 2 + ‖y ω‖ ^ 2) + c)
    (hx : ∫ ω, ‖x ω‖ ^ 4 ∂μ ≤ C₄ * s ^ 2) (hy : ∫ ω, ‖y ω‖ ^ 4 ∂μ ≤ C₄ * t ^ 2) :
    rms μ ρ ≤ √(4 * L ^ 2 * C₄ * (s ^ 2 + t ^ 2) + 2 * c ^ 2) := by
  unfold rms
  refine Real.sqrt_le_sqrt ?_
  have hpt : ∀ ω, ‖ρ ω‖ ^ 2 ≤ 4 * L ^ 2 * ‖x ω‖ ^ 4 + 4 * L ^ 2 * ‖y ω‖ ^ 4 + 2 * c ^ 2 :=
    fun ω => by
      have h0 := norm_nonneg (ρ ω)
      have h1 := pow_le_pow_left₀ h0 (hb ω) 2
      have hxy : 0 ≤ L * (‖x ω‖ ^ 2 + ‖y ω‖ ^ 2) := by positivity
      nlinarith [sq_nonneg (L * (‖x ω‖ ^ 2 + ‖y ω‖ ^ 2) - c), sq_nonneg (‖x ω‖ ^ 2 - ‖y ω‖ ^ 2),
        sq_nonneg L]
  have hi : Integrable (fun ω => 4 * L ^ 2 * ‖x ω‖ ^ 4 + 4 * L ^ 2 * ‖y ω‖ ^ 4 + 2 * c ^ 2) μ :=
    ((hx4.const_mul _).add (hy4.const_mul _)).add (integrable_const _)
  have hi2 : Integrable (fun ω => 4 * L ^ 2 * ‖x ω‖ ^ 4 + 4 * L ^ 2 * ‖y ω‖ ^ 4) μ :=
    (hx4.const_mul _).add (hy4.const_mul _)
  have heq : ∫ ω, (4 * L ^ 2 * ‖x ω‖ ^ 4 + 4 * L ^ 2 * ‖y ω‖ ^ 4 + 2 * c ^ 2) ∂μ =
      4 * L ^ 2 * ∫ ω, ‖x ω‖ ^ 4 ∂μ + 4 * L ^ 2 * ∫ ω, ‖y ω‖ ^ 4 ∂μ + 2 * c ^ 2 := by
    rw [integral_add hi2 (integrable_const _), integral_add (hx4.const_mul _) (hy4.const_mul _),
      integral_const_mul, integral_const_mul]
    simp
  refine (integral_mono (memLp_sq_integrable hρL) hi hpt).trans ?_
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 4 * L ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 4 * L ^ 2)
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **Assumption 2.2 for two time scales.** The actor-critic iteration
`x_{k+1} = x_k + β_k (F₁(x_k, y_k) + m_{k+1} + r₁_k + h_k - h_{k+1})`,
`y_{k+1} = y_k + γ_k (F₂(x_k, y_k) + m'_{k+1} + r₂_k + g_k - g_{k+1})` (in the deviations from the
root), with a drift that is linear to first order, `F(x, y) = -A (x, y) + O(‖x‖² + ‖y‖²)`, sampling
remainders `‖r₁_k‖ ≤ C_r β_k`, `‖r₂_k‖ ≤ C_r γ_k`, and fourth moments `E‖x_k‖⁴ = O(γ_k²)`,
`E‖y_k‖⁴ = O(γ_k²)`, has the asymptotic covariances of its linearization: the conclusions of the
linear two-time-scale theorem hold. -/
theorem tendsto_tts_taylor [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x m r₁ h : ℕ → Ω → E d₁} {y m' r₂ g : ℕ → Ω → E d₂}
    {F₁ : E d₁ → E d₂ → E d₁} {F₂ : E d₁ → E d₂ → E d₂} {L Cr C₄ : ℝ} (hL : 0 ≤ L)
    (hF₁ : ∀ u v, ‖F₁ u v + (matCLM A₁₁ u + matCLM A₁₂ v)‖ ≤ L * (‖u‖ ^ 2 + ‖v‖ ^ 2))
    (hF₂ : ∀ u v, ‖F₂ u v + (matCLM A₂₁ u + matCLM A₂₂ v)‖ ≤ L * (‖u‖ ^ 2 + ‖v‖ ^ 2))
    (hF₁c : Continuous fun p : E d₁ × E d₂ => F₁ p.1 p.2)
    (hF₂c : Continuous fun p : E d₁ × E d₂ => F₂ p.1 p.2)
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • (F₁ (x k ω) (y k ω) + m (k + 1) ω + r₁ k ω
      + h k ω - h (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • (F₂ (x k ω) (y k ω) + m' (k + 1) ω + r₂ k ω
      + g k ω - g (k + 1) ω))
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hym : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hx0L : MemLp (x 0) 2 μ) (hy0L : MemLp (y 0) 2 μ)
    (hhm : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hgm : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
    (hmm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (m (k + 1))) (hmL : ∀ k, MemLp (m (k + 1)) 2 μ)
    (hm'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (m' (k + 1)))
    (hm'L : ∀ k, MemLp (m' (k + 1)) 2 μ)
    (hr₁m : ∀ k, StronglyMeasurable[ℱ (k + 1)] (r₁ k)) (hr₁b : ∀ k ω, ‖r₁ k ω‖ ≤ Cr * β k)
    (hr₂m : ∀ k, StronglyMeasurable[ℱ (k + 1)] (r₂ k)) (hr₂b : ∀ k ω, ‖r₂ k ω‖ ≤ Cr * γ k)
    (h4xi : ∀ k, Integrable (fun ω => ‖x k ω‖ ^ 4) μ)
    (h4yi : ∀ k, Integrable (fun ω => ‖y k ω‖ ^ 4) μ)
    (h4x : ∀ k, ∫ ω, ‖x k ω‖ ^ 4 ∂μ ≤ C₄ * γ k ^ 2) (h4y : ∀ k, ∫ ω, ‖y k ω‖ ^ 4 ∂μ ≤ C₄ * γ k ^ 2)
    (hmart : ∀ k j, μ[fun ω => m (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hmart' : ∀ k j, μ[fun ω => m' (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 ≤ C) (rh : ∀ k, rms μ (h k) ≤ C) (rg : ∀ k, rms μ (g k) ≤ C)
    (rm : ∀ k, rms μ (m (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rm' : ∀ k, rms μ (m' (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂} {δ₁ δ₂ δ₃ : ℕ → ℝ}
    (hδ₁0 : ∀ k, 0 ≤ δ₁ k) (hδ₂0 : ∀ k, 0 ≤ δ₂ k) (hδ₃0 : ∀ k, 0 ≤ δ₃ k)
    (hδ₁ : Tendsto δ₁ atTop (𝓝 0)) (hδ₂ : Tendsto δ₂ atTop (𝓝 0)) (hδ₃ : Tendsto δ₃ atTop (𝓝 0))
    (dev₁ : ∀ k, ‖secondMoment μ (m (k + 1)) - Γ₁₁‖ ≤
      δ₁ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₂ : ∀ k, ‖crossMoment μ (m (k + 1)) (m' (k + 1)) - Γ₁₂‖ ≤
      δ₂ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₃ : ∀ k, ‖secondMoment μ (m' (k + 1)) - Γ₂₂‖ ≤
      δ₃ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  set C₄' := max C₄ 0
  set Cr' := max Cr 0
  have hC₄' : 0 ≤ C₄' := le_max_right _ _
  have hCr' : 0 ≤ Cr' := le_max_right _ _
  have h4x' : ∀ k, ∫ ω, ‖x k ω‖ ^ 4 ∂μ ≤ C₄' * γ k ^ 2 := fun k =>
    (h4x k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have h4y' : ∀ k, ∫ ω, ‖y k ω‖ ^ 4 ∂μ ≤ C₄' * γ k ^ 2 := fun k =>
    (h4y k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have hr₁b' : ∀ k ω, ‖r₁ k ω‖ ≤ Cr' * β k := fun k ω =>
    (hr₁b k ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hβ.pos k).le)
  have hr₂b' : ∀ k ω, ‖r₂ k ω‖ ≤ Cr' * γ k := fun k ω =>
    (hr₂b k ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hγ.pos k).le)
  obtain ⟨Bq₀, hBq₀⟩ := hβγ.bddAbove_range
  set Bq := max Bq₀ 0
  have hBq0 : 0 ≤ Bq := le_max_right _ _
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have h1 : β k / γ k ≤ Bq := (hBq₀ ⟨k, rfl⟩).trans (le_max_left _ _)
    rwa [div_le_iff₀ (hγ.pos k)] at h1
  -- the remainders
  set ρ₁ : ℕ → Ω → E d₁ := fun k ω => F₁ (x k ω) (y k ω) + (matCLM A₁₁ (x k ω)
    + matCLM A₁₂ (y k ω)) + r₁ k ω with hρ₁
  set ρ₂ : ℕ → Ω → E d₂ := fun k ω => F₂ (x k ω) (y k ω) + (matCLM A₂₁ (x k ω)
    + matCLM A₂₂ (y k ω)) + r₂ k ω with hρ₂
  have hb₁ : ∀ k ω, ‖ρ₁ k ω‖ ≤ L * (‖x k ω‖ ^ 2 + ‖y k ω‖ ^ 2) + Cr' * β k := fun k ω =>
    (norm_add_le _ _).trans (add_le_add (hF₁ _ _) (hr₁b' k ω))
  have hb₂ : ∀ k ω, ‖ρ₂ k ω‖ ≤ L * (‖x k ω‖ ^ 2 + ‖y k ω‖ ^ 2) + Cr' * γ k := fun k ω =>
    (norm_add_le _ _).trans (add_le_add (hF₂ _ _) (hr₂b' k ω))
  have hρ₁m : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ρ₁ k) := fun k => by
    have hmono := ℱ.mono (Nat.le_succ k)
    have hp := ((hxm k).mono hmono).prodMk ((hym k).mono hmono)
    exact ((hF₁c.comp_stronglyMeasurable hp).add
      (((matCLM A₁₁).continuous.comp_stronglyMeasurable ((hxm k).mono hmono)).add
        ((matCLM A₁₂).continuous.comp_stronglyMeasurable ((hym k).mono hmono)))).add (hr₁m k)
  have hρ₂m : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ρ₂ k) := fun k => by
    have hmono := ℱ.mono (Nat.le_succ k)
    have hp := ((hxm k).mono hmono).prodMk ((hym k).mono hmono)
    exact ((hF₂c.comp_stronglyMeasurable hp).add
      (((matCLM A₂₁).continuous.comp_stronglyMeasurable ((hxm k).mono hmono)).add
        ((matCLM A₂₂).continuous.comp_stronglyMeasurable ((hym k).mono hmono)))).add (hr₂m k)
  have hρL : ∀ {n : ℕ} (k : ℕ) (ρ : Ω → E n) (c : ℝ), StronglyMeasurable[ℱ (k + 1)] ρ →
      (∀ ω, ‖ρ ω‖ ≤ L * (‖x k ω‖ ^ 2 + ‖y k ω‖ ^ 2) + c) → MemLp ρ 2 μ := by
    intro n k ρ c hm hb
    have hma : AEStronglyMeasurable ρ μ := (hm.mono (ℱ.le (k + 1))).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hma]
    refine ((((h4xi k).const_mul (4 * L ^ 2)).add ((h4yi k).const_mul (4 * L ^ 2))).add
      (integrable_const (2 * c ^ 2))).mono' (hma.norm.pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    show ‖ρ ω‖ ^ 2 ≤ 4 * L ^ 2 * ‖x k ω‖ ^ 4 + 4 * L ^ 2 * ‖y k ω‖ ^ 4 + 2 * c ^ 2
    set A := L * (‖x k ω‖ ^ 2 + ‖y k ω‖ ^ 2) with hA
    have h0 := norm_nonneg (ρ ω)
    have h1 : ‖ρ ω‖ ^ 2 ≤ (A + c) ^ 2 := pow_le_pow_left₀ h0 (hb ω) 2
    have h2 : (A + c) ^ 2 ≤ 2 * A ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (A - c)]
    have h3 : A ^ 2 ≤ 2 * L ^ 2 * ‖x k ω‖ ^ 4 + 2 * L ^ 2 * ‖y k ω‖ ^ 4 := by
      have e : A ^ 2 = L ^ 2 * (‖x k ω‖ ^ 2 + ‖y k ω‖ ^ 2) ^ 2 := by simp only [hA]; ring
      have h4 : (‖x k ω‖ ^ 2 + ‖y k ω‖ ^ 2) ^ 2 ≤ 2 * ‖x k ω‖ ^ 4 + 2 * ‖y k ω‖ ^ 4 := by
        nlinarith [sq_nonneg (‖x k ω‖ ^ 2 - ‖y k ω‖ ^ 2)]
      have := mul_le_mul_of_nonneg_left h4 (sq_nonneg L)
      rw [e]; linarith
    linarith
  have hρ₁L : ∀ k, MemLp (ρ₁ k) 2 μ := fun k => hρL k (ρ₁ k) (Cr' * β k) (hρ₁m k) (hb₁ k)
  have hρ₂L : ∀ k, MemLp (ρ₂ k) 2 μ := fun k => hρL k (ρ₂ k) (Cr' * γ k) (hρ₂m k) (hb₂ k)
  -- their sizes
  set Kρ := 8 * L ^ 2 * C₄' + 2 * Cr' ^ 2 * (Bq ^ 2 + 1) with hKρ
  have hKρ0 : 0 ≤ Kρ := by positivity
  have rρ₁ : ∀ k, rms μ (ρ₁ k) ≤ √Kρ * γ k := fun k => by
    have hg := hγ.pos k
    refine (rms_taylor_le (ρ := ρ₁ k) (x := x k) (y := y k) (hρ₁L k) (h4xi k) (h4yi k) hL (mul_nonneg hCr' (hβ.pos k).le) (hb₁ k)
      (h4x' k) (h4y' k)).trans ?_
    rw [show √Kρ * γ k = √(Kρ * γ k ^ 2) by
      rw [Real.sqrt_mul hKρ0, Real.sqrt_sq hg.le]]
    refine Real.sqrt_le_sqrt ?_
    have hb2 : β k ^ 2 ≤ Bq ^ 2 * γ k ^ 2 := by
      have := pow_le_pow_left₀ (hβ.pos k).le (hbq k) 2; rwa [mul_pow] at this
    have t2 := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 2 * Cr' ^ 2)
    have t3 : 0 ≤ 2 * Cr' ^ 2 * γ k ^ 2 := by positivity
    have e1 : 4 * L ^ 2 * C₄' * (γ k ^ 2 + γ k ^ 2) + 2 * (Cr' * β k) ^ 2 =
        8 * L ^ 2 * C₄' * γ k ^ 2 + 2 * Cr' ^ 2 * β k ^ 2 := by ring
    have e2 : Kρ * γ k ^ 2 = 8 * L ^ 2 * C₄' * γ k ^ 2 + 2 * Cr' ^ 2 * (Bq ^ 2 * γ k ^ 2)
        + 2 * Cr' ^ 2 * γ k ^ 2 := by simp only [hKρ]; ring
    linarith
  have rρ₂ : ∀ k, rms μ (ρ₂ k) ≤ √Kρ * γ k := fun k => by
    have hg := hγ.pos k
    refine (rms_taylor_le (ρ := ρ₂ k) (x := x k) (y := y k) (hρ₂L k) (h4xi k) (h4yi k) hL (mul_nonneg hCr' hg.le) (hb₂ k)
      (h4x' k) (h4y' k)).trans ?_
    rw [show √Kρ * γ k = √(Kρ * γ k ^ 2) by
      rw [Real.sqrt_mul hKρ0, Real.sqrt_sq hg.le]]
    refine Real.sqrt_le_sqrt ?_
    have hb2 : β k ^ 2 ≤ Bq ^ 2 * γ k ^ 2 := by
      have := pow_le_pow_left₀ (hβ.pos k).le (hbq k) 2; rwa [mul_pow] at this
    have t3 : 0 ≤ 2 * Cr' ^ 2 * (Bq ^ 2 * γ k ^ 2) := by positivity
    have e1 : 4 * L ^ 2 * C₄' * (γ k ^ 2 + γ k ^ 2) + 2 * (Cr' * γ k) ^ 2 =
        8 * L ^ 2 * C₄' * γ k ^ 2 + 2 * Cr' ^ 2 * γ k ^ 2 := by ring
    have e2 : Kρ * γ k ^ 2 = 8 * L ^ 2 * C₄' * γ k ^ 2 + 2 * Cr' ^ 2 * (Bq ^ 2 * γ k ^ 2)
        + 2 * Cr' ^ 2 * γ k ^ 2 := by simp only [hKρ]; ring
    linarith
  -- apply the reduction
  set C' := C + √Kρ with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hCC' : C ≤ C' := by simp only [hC']; linarith [Real.sqrt_nonneg Kρ]
  have hR0 : ∀ k, 0 ≤ rms μ (x k) + rms μ (y k) := fun k => add_nonneg (rms_nonneg _) (rms_nonneg _)
  have hup : ∀ t : ℝ, 0 ≤ t → C * t ≤ C' * t := fun t ht => mul_le_mul_of_nonneg_right hCC' ht
  have rbound : ∀ k (r : ℝ), r ≤ √Kρ * γ k →
      r ≤ C' * γ k * (1 + (rms μ (x k) + rms μ (y k))) := fun k r hr => by
    have hg := hγ.pos k
    have h1 : √Kρ * γ k ≤ C' * γ k := mul_le_mul_of_nonneg_right (by simp only [hC']; linarith)
      hg.le
    have h2 : C' * γ k ≤ C' * γ k * (1 + (rms μ (x k) + rms μ (y k))) := by
      have := hR0 k
      nlinarith [mul_nonneg hC'0 hg.le]
    linarith
  exact tendsto_tts_nonlinear hβ hγ hβγ hγβ A₁₁ A₁₂ A₂₁ A₂₂ D hD hη hΔ hA₂₂ ℱ (ρ₁ := ρ₁)
    (ρ₂ := ρ₂)
    (fun k ω => by simp only [hρ₁, hx k ω]; module)
    (fun k ω => by simp only [hρ₂, hy k ω]; module)
    (hxm 0) hx0L (hym 0) hy0L hhm hhL hgm hgL hmm hmL hm'm hm'L hρ₁m hρ₁L hρ₂m hρ₂L hmart hmart'
    hC'0 (fun k => (rh k).trans hCC') (fun k => (rg k).trans hCC')
    (fun k => (rm k).trans (hup _ (by linarith [hR0 k])))
    (fun k => (rm' k).trans (hup _ (by linarith [hR0 k])))
    (fun k => rbound k _ (rρ₁ k)) (fun k => rbound k _ (rρ₂ k))
    hδ₁0 hδ₂0 hδ₃0 hδ₁ hδ₂ hδ₃
    (fun k => (dev₁ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₂ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₃ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))

end StochasticApproximation
