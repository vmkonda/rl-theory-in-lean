/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TwoTimeScaleMultiplicative
import RLTheory.StochasticApproximation.TraceMoments

/-!
# Two time scales with trace-driven noise

The two-time-scale theorems of `TwoTimeScaleMultiplicative.lean` take the limits of the
covariances of the additive martingale parts as hypotheses. For additive noise driven by a
finite Markov chain and an eligibility trace (both time scales driven by the same chain and
trace, as for an actor and its critic), this file discharges them: the martingale parts come from
the Poisson solutions of Lemma 4.4, and the three limits `Γ₁₁`, `Γ₁₂`, `Γ₂₂` are computed from
the stationary first and second moments of the trace (`traceGamma`, `traceCross`).

* `tendsto_mtts_slow_trace`: Corollary 2.2 of `docs/two-time-scale-covariance.md` (the slow
  iterate has the covariance of the single-time-scale iteration with effective noise
  `V - A₁₂ A₂₂⁻¹ W`) for trace-driven additive noise. The multiplicative noise is the abstract
  bounded structure `TTSMatrixNoise`.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory

namespace StochasticApproximation

variable {d₁ d₂ : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → S} {Q : S → S → ℝ}
  {p : ℕ} {z : ℕ → Ω → E p} {c : S → ℝ} {φ : S → E p}

/-- **Corollary 2.2 for trace-driven noise.** Two time scales, with additive noise
`F₁(Y_k, Y_{k+1}) z_k + e₁(Y_k, Y_{k+1})` on the slow iterate and
`F₂(Y_k, Y_{k+1}) z_k + e₂(Y_k, Y_{k+1})` on the fast one, driven by one finite chain whose law
converges and one trace with `|c| ≤ 1`, `Σ_{y'} Q y y' |c y'| ≤ ρ < 1` and a bounded start, plus
bounded multiplicative noise `W`. The slow iterate satisfies `β_k⁻¹ E[x_k x_kᵀ] → Σ`, where `Σ`
solves the Lyapunov equation of the effective noise with
`Γ₁₁ = traceGamma (G₁, g₁)`, `Γ₁₂ = traceCross (G₁, g₁) (G₂, g₂)`, `Γ₂₂ = traceGamma (G₂, g₂)`
and `G_i y y' = F_i y y' + c y' U_i y' - U_i y`, `g_i y y' = e_i y y' + U_i y' φ y' + ĥ_i y' - ĥ_i y`
from the Poisson solutions. -/
theorem tendsto_mtts_slow_trace {βbar : ℝ} {β γ : ℕ → ℝ}
    {A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ} {A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ}
    {A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ} {A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (Ginv : Matrix (Fin d₂) (Fin d₂) ℝ) (hG : Ginv * A₂₂ = 1) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * (Ginv * A₂₁) - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (hY : FiniteMarkov μ ℱ Y Q) (hQ : ∀ y y', 0 ≤ Q y y') {ρ : ℝ}
    (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc1 : ∀ y, |c y| ≤ 1)
    {ν : S → ℝ} (hlaw : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y)))
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hz0 : ∃ C, ∀ ω, ‖z 0 ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω))
    (F₁ : S → S → E p →L[ℝ] E d₁) (e₁ : S → S → E d₁) (U₁ : S → E p →L[ℝ] E d₁)
    (hh₁ : S → E d₁) (hU₁ : ∀ y, U₁ y = ∑ y', Q y y' • (F₁ y y' + c y' • U₁ y'))
    (hhh₁ : ∀ y, hh₁ y = ∑ y', Q y y' • (e₁ y y' + U₁ y' (φ y') + hh₁ y'))
    (F₂ : S → S → E p →L[ℝ] E d₂) (e₂ : S → S → E d₂) (U₂ : S → E p →L[ℝ] E d₂)
    (hh₂ : S → E d₂) (hU₂ : ∀ y, U₂ y = ∑ y', Q y y' • (F₂ y y' + c y' • U₂ y'))
    (hhh₂ : ∀ y, hh₂ y = ∑ y', Q y y' • (e₂ y y' + U₂ y' (φ y') + hh₂ y'))
    (W : TTSMatrixNoise μ ℱ d₁ d₂) {x : ℕ → Ω → E d₁} {y : ℕ → Ω → E d₂}
    (hx : ∀ k ω, x (k + 1) ω = x k ω - β k • (matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω))
      - β k • ((W.N₁₁ (k + 1) ω + W.G₁₁ k ω - W.G₁₁ (k + 1) ω) (x k ω)
        + (W.N₁₂ (k + 1) ω + W.G₁₂ k ω - W.G₁₂ (k + 1) ω) (y k ω))
      + β k • traceNoise F₁ e₁ Y z k ω)
    (hy : ∀ k ω, y (k + 1) ω = y k ω - γ k • (matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω))
      - γ k • ((W.N₂₁ (k + 1) ω + W.G₂₁ k ω - W.G₂₁ (k + 1) ω) (x k ω)
        + (W.N₂₂ (k + 1) ω + W.G₂₂ k ω - W.G₂₂ (k + 1) ω) (y k ω))
      + γ k • traceNoise F₂ e₂ Y z k ω)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ) :
    ∃ (m₁ : Fin p → S → ℝ) (m₂ : Fin p → Fin p → S → ℝ),
      (∀ a y', m₁ a y' = transfer Q c (m₁ a) y' + φ y' a * ν y') ∧
      (∀ a b y', m₂ a b y' = transfer Q (fun y => c y ^ 2) (m₂ a b) y'
        + φ y' b * transfer Q c (m₁ a) y' + φ y' a * transfer Q c (m₁ b) y'
        + φ y' a * φ y' b * ν y') ∧
      ∃ Sig, lyapOp (A₁₁ - A₁₂ * (Ginv * A₂₁) - (βbar / 2) • 1) Sig =
          traceGamma Q (fun y y' => F₁ y y' + c y' • U₁ y' - U₁ y)
              (fun y y' => e₁ y y' + U₁ y' (φ y') + hh₁ y' - hh₁ y) ν m₁ m₂
            - lmul (A₁₂ * Ginv) (transCLM (traceCross Q
                (fun y y' => F₁ y y' + c y' • U₁ y' - U₁ y)
                (fun y y' => e₁ y y' + U₁ y' (φ y') + hh₁ y' - hh₁ y)
                (fun y y' => F₂ y y' + c y' • U₂ y' - U₂ y)
                (fun y y' => e₂ y y' + U₂ y' (φ y') + hh₂ y' - hh₂ y) ν m₁ m₂))
            - rmul (A₁₂ * Ginv) (traceCross Q
                (fun y y' => F₁ y y' + c y' • U₁ y' - U₁ y)
                (fun y y' => e₁ y y' + U₁ y' (φ y') + hh₁ y' - hh₁ y)
                (fun y y' => F₂ y y' + c y' • U₂ y' - U₂ y)
                (fun y y' => e₂ y y' + U₂ y' (φ y') + hh₂ y' - hh₂ y) ν m₁ m₂)
            + lmul (A₁₂ * Ginv) (rmul (A₁₂ * Ginv) (traceGamma Q
                (fun y y' => F₂ y y' + c y' • U₂ y' - U₂ y)
                (fun y y' => e₂ y y' + U₂ y' (φ y') + hh₂ y' - hh₂ y) ν m₁ m₂)) ∧
        Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 Sig) := by
  obtain ⟨hzk, hz2⟩ := trace_bounds hY hQ hρ hρ0 hρ1 hc1 hlaw hz hz0 hzrec
  obtain ⟨m₁, m₂, hm₁, hm₂, ht₁, ht₂⟩ :=
    tendsto_trace_moments hY hQ hρ hρ0 hρ1 hc1 hz hzk hzrec hlaw
  refine ⟨m₁, m₂, hm₁, hm₂, ?_⟩
  set G₁ : S → S → E p →L[ℝ] E d₁ := fun y y' => F₁ y y' + c y' • U₁ y' - U₁ y with hG₁
  set g₁ : S → S → E d₁ := fun y y' => e₁ y y' + U₁ y' (φ y') + hh₁ y' - hh₁ y with hg₁
  set G₂ : S → S → E p →L[ℝ] E d₂ := fun y y' => F₂ y y' + c y' • U₂ y' - U₂ y with hG₂
  set g₂ : S → S → E d₂ := fun y y' => e₂ y y' + U₂ y' (φ y') + hh₂ y' - hh₂ y with hg₂
  -- the martingale parts and their limits
  set M : ℕ → Ω → E d₁ := fun n ω => traceNoise F₁ e₁ Y z n.pred ω
    + tracePoisson U₁ hh₁ Y z n ω - tracePoisson U₁ hh₁ Y z n.pred ω with hM
  set M' : ℕ → Ω → E d₂ := fun n ω => traceNoise F₂ e₂ Y z n.pred ω
    + tracePoisson U₂ hh₂ Y z n ω - tracePoisson U₂ hh₂ Y z n.pred ω with hM'
  have eM : ∀ k, M (k + 1) = fun ω => G₁ (Y k ω) (Y (k + 1) ω) (z k ω) + g₁ (Y k ω) (Y (k + 1) ω) :=
    fun k => funext fun ω => traceMart_eq_affine hzrec F₁ e₁ U₁ hh₁ k ω
  have eM' : ∀ k, M' (k + 1) = fun ω => G₂ (Y k ω) (Y (k + 1) ω) (z k ω)
      + g₂ (Y k ω) (Y (k + 1) ω) :=
    fun k => funext fun ω => traceMart_eq_affine hzrec F₂ e₂ U₂ hh₂ k ω
  have l₁₁ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop
      (𝓝 (traceGamma Q G₁ g₁ ν m₁ m₂)) := by
    simp only [eM, secondMoment]
    exact tendsto_crossMoment_of_moments hY hz hzk hlaw ht₁ ht₂ G₁ g₁ G₁ g₁
  have l₁₂ : Tendsto (fun k => crossMoment μ (M (k + 1)) (M' (k + 1))) atTop
      (𝓝 (traceCross Q G₁ g₁ G₂ g₂ ν m₁ m₂)) := by
    simp only [eM, eM']
    exact tendsto_crossMoment_of_moments hY hz hzk hlaw ht₁ ht₂ G₁ g₁ G₂ g₂
  have l₂₂ : Tendsto (fun k => secondMoment μ (M' (k + 1))) atTop
      (𝓝 (traceGamma Q G₂ g₂ ν m₁ m₂)) := by
    simp only [eM', secondMoment]
    exact tendsto_crossMoment_of_moments hY hz hzk hlaw ht₁ ht₂ G₂ g₂ G₂ g₂
  -- the remaining hypotheses
  obtain ⟨smH₁, hHL₁, ⟨CH₁, hHB₁⟩, smM₁, hML₁, ⟨CM₁, hMB₁⟩, hmart₁⟩ :=
    traceNoise_facts hY hz hzk hz2 hzrec F₁ e₁ U₁ hh₁ hU₁ hhh₁
  obtain ⟨smH₂, hHL₂, ⟨CH₂, hHB₂⟩, smM₂, hML₂, ⟨CM₂, hMB₂⟩, hmart₂⟩ :=
    traceNoise_facts hY hz hzk hz2 hzrec F₂ e₂ U₂ hh₂ hU₂ hhh₂
  have hrec : MTTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M (tracePoisson U₁ hh₁ Y z) y M'
      (tracePoisson U₂ hh₂ Y z) W := by
    constructor
    · intro k ω
      rw [hx k ω]
      simp only [hM, Nat.pred_succ]
      module
    · intro k ω
      rw [hy k ω]
      simp only [hM', Nat.pred_succ]
      module
  exact tendsto_mtts_slow hβ hγ hβγ hγβ Ginv hG hη hΔ hA₂₂ hrec hx0 hx0L hy0 hy0L smH₁ hHL₁
    hHB₁ smH₂ hHL₂ hHB₂ smM₁ hML₁ hMB₁ smM₂ hML₂ hMB₂ hmart₁ hmart₂ l₁₁ l₁₂ l₂₂

end StochasticApproximation
