/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.ParamMarkovNoise
import RLTheory.StochasticApproximation.TwoTimeScaleMarkov

/-!
# Two time scales with a parameter-dependent chain

The iteration `x_{k+1} = x_k + β_k H₁(x_k, y_k, ξ_{k+1})`, `y_{k+1} = y_k + γ_k H₂(x_k, y_k, ξ_{k+1})`,
where the finite chain moves by `ξ_{k+1} ~ P_{(x_k, y_k)}(ξ_k, ·)`. With Poisson pairs
`(U_i, V_i)` for each component, the noise splits as in `param_noise_decomp`, with the parameter
`p_k = (x_k, y_k)` lagged in the Poisson shifts:
`H_i(p_k, ξ_{k+1}) = F_i(p_k) + M^i_{k+1} + r^i_k + h^i_k - h^i_{k+1}`.
The remainders are `O(‖p_k - p_{k-1}‖) = O(γ_k)` for both components, because the critic moves at
rate `γ`. Since `γ²/β → 0`, this is small enough for the slow component too.

* `condExp_poisson_eq_zero`: the martingale part has conditional mean zero, for any parameter
  space.
* `tts_param_decomp`: the decomposition along the process.
* `tendsto_tts_param_chain`: the two-time-scale linearization with θ-dependent sampling, given the
  limits of the noise covariances.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- **The martingale part of a Poisson pair.** If `V_t = P_t U_t` and the conditional law of
`ξ_{k+1}` given `ℱ_k` is `P_{p_k}(ξ_k, ·)`, then `U_{p_k}(ξ_{k+1}) - V_{p_k}(ξ_k)` has conditional
mean zero. -/
lemma condExp_poisson_eq_zero {T : Type*} [TopologicalSpace T] {n : ℕ}
    (ℱ : MeasureTheory.Filtration ℕ m0) (k : ℕ) {p : Ω → T} (hp : StronglyMeasurable[ℱ k] p)
    {ξk ξk1 : Ω → S} (hξk : Measurable[ℱ k] ξk) (hξk1 : Measurable[ℱ (k + 1)] ξk1)
    {P : T → S → S → ℝ}
    (hlaw : ∀ s, μ[{ω | ξk1 ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (p ω) (ξk ω) s)
    {U V : T → S → E n} (hV : ∀ t s, V t s = ∑ s', P t s s' • U t s')
    (hUc : ∀ s, Continuous fun t => U t s) (hVc : ∀ s, Continuous fun t => V t s) {CU CV : ℝ}
    (hUb : ∀ t s, ‖U t s‖ ≤ CU) (hVb : ∀ t s, ‖V t s‖ ≤ CV) (j : Fin n) :
    μ[fun ω => (U (p ω) (ξk1 ω) - V (p ω) (ξk ω)) j | ℱ k] =ᵐ[μ] 0 := by
  have habs : ∀ v : E n, |v j| ≤ ‖v‖ := fun v => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j
  have hcompsum : ∀ (c : S → ℝ) (u : S → E n), (∑ s, c s • u s) j = ∑ s, c s * u s j :=
    fun c u => by rw [Finset.sum_apply]; simp
  have hmix := condExp_finite_mix (μ := μ) ℱ k (hξk1.mono (ℱ.le (k + 1)) le_rfl) hlaw
    (G := fun s ω => U (p ω) s j)
    (fun s => ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.comp (hUc s)).comp_stronglyMeasurable
      hp)
    (fun s => ⟨CU, fun ω => (habs _).trans (hUb _ _)⟩)
  have hVk : StronglyMeasurable[ℱ k] (fun ω => V (p ω) (ξk ω) j) :=
    ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous).comp_stronglyMeasurable
      (stronglyMeasurable_comp_finite hp hξk hVc)
  have iU : Integrable (fun ω => U (p ω) (ξk1 ω) j) μ := by
    refine (memLp_top_of_bound ((((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous
      ).comp_stronglyMeasurable (stronglyMeasurable_comp_finite (hp.mono (ℱ.mono k.le_succ))
        hξk1 hUc)).mono (ℱ.le (k + 1))).aestronglyMeasurable CU
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    rw [Real.norm_eq_abs]; exact (habs _).trans (hUb _ _)
  have iV : Integrable (fun ω => V (p ω) (ξk ω) j) μ :=
    (memLp_top_of_bound (hVk.mono (ℱ.le k)).aestronglyMeasurable CV
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact (habs _).trans (hVb _ _))).integrable le_top
  have e : (fun ω => (U (p ω) (ξk1 ω) - V (p ω) (ξk ω)) j) =
      (fun ω => U (p ω) (ξk1 ω) j) - fun ω => V (p ω) (ξk ω) j := by
    funext ω; simp
  rw [e]
  filter_upwards [condExp_sub iU iV (ℱ k), hmix] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable (ℱ.le k) hVk iV]
  simp only [Pi.zero_apply]
  rw [hV, hcompsum]
  simp

section TTS

variable {d₁ d₂ : ℕ}

/-- The martingale part `M_{k+1} = U_{p_k}(ξ_{k+1}) - V_{p_k}(ξ_k)`, `p = (x, y)`. -/
noncomputable def ttsM {n : ℕ} (U V : E d₁ → E d₂ → S → E n) (x : ℕ → Ω → E d₁)
    (y : ℕ → Ω → E d₂) (ξ : ℕ → Ω → S) (m : ℕ) (ω : Ω) : E n :=
  U (x (m - 1) ω) (y (m - 1) ω) (ξ m ω) - V (x (m - 1) ω) (y (m - 1) ω) (ξ (m - 1) ω)

/-- The Poisson shift `h_k = V_{p_{k-1}}(ξ_k)`. -/
def ttsH {n : ℕ} (V : E d₁ → E d₂ → S → E n) (x : ℕ → Ω → E d₁) (y : ℕ → Ω → E d₂)
    (ξ : ℕ → Ω → S) (k : ℕ) (ω : Ω) : E n :=
  V (x (k - 1) ω) (y (k - 1) ω) (ξ k ω)

/-- The remainder `r_k = V_{p_k}(ξ_k) - V_{p_{k-1}}(ξ_k)`. -/
noncomputable def ttsR {n : ℕ} (V : E d₁ → E d₂ → S → E n) (x : ℕ → Ω → E d₁)
    (y : ℕ → Ω → E d₂) (ξ : ℕ → Ω → S) (k : ℕ) (ω : Ω) : E n :=
  V (x k ω) (y k ω) (ξ k ω) - V (x (k - 1) ω) (y (k - 1) ω) (ξ k ω)

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- The pathwise decomposition for one component. -/
lemma tts_noise_decomp {n : ℕ} {x : ℕ → Ω → E d₁} {y : ℕ → Ω → E d₂} {ξ : ℕ → Ω → S}
    {H U V : E d₁ → E d₂ → S → E n} {F : E d₁ → E d₂ → E n}
    (hpois : ∀ u w s, U u w s - V u w s = H u w s - F u w) (k : ℕ) (ω : Ω) :
    H (x k ω) (y k ω) (ξ (k + 1) ω) = F (x k ω) (y k ω) + ttsM U V x y ξ (k + 1) ω
      + ttsR V x y ξ k ω + ttsH V x y ξ k ω - ttsH V x y ξ (k + 1) ω := by
  have h1 : H (x k ω) (y k ω) (ξ (k + 1) ω) = F (x k ω) (y k ω)
      + (U (x k ω) (y k ω) (ξ (k + 1) ω) - V (x k ω) (y k ω) (ξ (k + 1) ω)) := by
    rw [hpois]; abel
  simp only [ttsM, ttsH, ttsR, Nat.add_sub_cancel]
  rw [h1]
  abel

omit [IsProbabilityMeasure μ] [DecidableEq S] in
/-- Measurability, bounds and the martingale property of the decomposition for one component. -/
lemma tts_decomp_facts {n : ℕ} (ℱ : MeasureTheory.Filtration ℕ m0) {x : ℕ → Ω → E d₁}
    {y : ℕ → Ω → E d₂} {ξ : ℕ → Ω → S} (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k))
    (hym : ∀ k, StronglyMeasurable[ℱ k] (y k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    {U V : E d₁ → E d₂ → S → E n}
    (hUc : ∀ s, Continuous fun p : E d₁ × E d₂ => U p.1 p.2 s)
    (hVc : ∀ s, Continuous fun p : E d₁ × E d₂ => V p.1 p.2 s) {CU CV : ℝ}
    (hUb : ∀ u w s, ‖U u w s‖ ≤ CU) (hVb : ∀ u w s, ‖V u w s‖ ≤ CV) :
    (∀ k, StronglyMeasurable[ℱ k] (ttsH V x y ξ k)) ∧ (∀ k ω, ‖ttsH V x y ξ k ω‖ ≤ CV) ∧
    (∀ k, StronglyMeasurable[ℱ k] (ttsR V x y ξ k)) ∧
    (∀ k, StronglyMeasurable[ℱ (k + 1)] (ttsM U V x y ξ (k + 1))) ∧
    (∀ k ω, ‖ttsM U V x y ξ (k + 1) ω‖ ≤ CU + CV) := by
  have hp : ∀ k, StronglyMeasurable[ℱ k] (fun ω => (x k ω, y k ω)) := fun k =>
    (hxm k).prodMk (hym k)
  have hpprev : ∀ k, StronglyMeasurable[ℱ k] (fun ω => (x (k - 1) ω, y (k - 1) ω)) := fun k =>
    (hp (k - 1)).mono (ℱ.mono (Nat.sub_le k 1))
  have hhm : ∀ k, StronglyMeasurable[ℱ k] (ttsH V x y ξ k) := fun k =>
    stronglyMeasurable_comp_finite (G := fun p : E d₁ × E d₂ => V p.1 p.2) (hpprev k) (hξm k) hVc
  refine ⟨hhm, fun k ω => hVb _ _ _, fun k => ?_, fun k => ?_, fun k ω => ?_⟩
  · exact (stronglyMeasurable_comp_finite (G := fun p : E d₁ × E d₂ => V p.1 p.2) (hp k) (hξm k)
      hVc).sub (hhm k)
  · show StronglyMeasurable[ℱ (k + 1)] fun ω =>
      U (x k ω) (y k ω) (ξ (k + 1) ω) - V (x k ω) (y k ω) (ξ k ω)
    exact (stronglyMeasurable_comp_finite (G := fun p : E d₁ × E d₂ => U p.1 p.2)
      ((hp k).mono (ℱ.mono k.le_succ)) (hξm (k + 1)) hUc).sub
      ((stronglyMeasurable_comp_finite (G := fun p : E d₁ × E d₂ => V p.1 p.2) (hp k) (hξm k)
        hVc).mono (ℱ.mono k.le_succ))
  · show ‖U (x k ω) (y k ω) (ξ (k + 1) ω) - V (x k ω) (y k ω) (ξ k ω)‖ ≤ _
    exact (norm_sub_le _ _).trans (add_le_add (hUb _ _ _) (hVb _ _ _))

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- **The remainders are `O(γ)`.** With `V` Lipschitz in the parameter and bounded noise,
`‖r_k‖ ≤ L_V (‖x_k - x_{k-1}‖ + ‖y_k - y_{k-1}‖) = O(γ_k)`. -/
lemma tts_remainder_le {β γ : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar)
    (hγ : StepSizeRate γ 0) (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0)) {n : ℕ}
    {x : ℕ → Ω → E d₁} {y : ℕ → Ω → E d₂} {ξ : ℕ → Ω → S} {H₁ : E d₁ → E d₂ → S → E d₁}
    {H₂ : E d₁ → E d₂ → S → E d₂} {CH : ℝ}
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • H₁ (x k ω) (y k ω) (ξ (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • H₂ (x k ω) (y k ω) (ξ (k + 1) ω))
    (hH₁b : ∀ u w s, ‖H₁ u w s‖ ≤ CH) (hH₂b : ∀ u w s, ‖H₂ u w s‖ ≤ CH)
    {V : E d₁ → E d₂ → S → E n} {LV : ℝ}
    (hVL : ∀ u w u' w' s, ‖V u w s - V u' w' s‖ ≤ LV * (‖u - u'‖ + ‖w - w'‖)) :
    ∃ Cr, ∀ k ω, ‖ttsR V x y ξ k ω‖ ≤ Cr * γ k := by
  obtain ⟨Rβ, Cβ, hRβ1, -, hRβ⟩ := hβ.prev_le
  obtain ⟨Rγ, Cγ, hRγ1, -, hRγ⟩ := hγ.prev_le
  obtain ⟨Bq₀, hBq₀⟩ := hβγ.bddAbove_range
  set Bq := max Bq₀ 0
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have h1 : β k / γ k ≤ Bq := (hBq₀ ⟨k, rfl⟩).trans (le_max_left _ _)
    rwa [div_le_iff₀ (hγ.pos k)] at h1
  set LV₀ := max LV 0
  set CH₀ := max CH 0
  have hLV : 0 ≤ LV₀ := le_max_right _ _
  have hCH : 0 ≤ CH₀ := le_max_right _ _
  refine ⟨LV₀ * CH₀ * (Rβ * Bq + Rγ), fun k ω => ?_⟩
  cases k with
  | zero => simp [ttsR]; have := hγ.pos 0; have : 0 ≤ Bq := le_max_right _ _; positivity
  | succ j =>
    simp only [ttsR, Nat.add_sub_cancel]
    have h1 := (hVL (x (j + 1) ω) (y (j + 1) ω) (x j ω) (y j ω) (ξ (j + 1) ω)).trans
      (mul_le_mul_of_nonneg_right (le_max_left LV 0) (by positivity))
    have hdx : ‖x (j + 1) ω - x j ω‖ ≤ β j * CH₀ := by
      rw [hx j ω, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hβ.pos j)]
      exact mul_le_mul_of_nonneg_left ((hH₁b _ _ _).trans (le_max_left _ _)) (hβ.pos j).le
    have hdy : ‖y (j + 1) ω - y j ω‖ ≤ γ j * CH₀ := by
      rw [hy j ω, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hγ.pos j)]
      exact mul_le_mul_of_nonneg_left ((hH₂b _ _ _).trans (le_max_left _ _)) (hγ.pos j).le
    have hb1 : β j ≤ Rβ * Bq * γ (j + 1) := by
      have := (hRβ (j + 1)).1
      simp only [Nat.add_sub_cancel] at this
      have h2 := mul_le_mul_of_nonneg_left (hbq (j + 1)) (by linarith : (0 : ℝ) ≤ Rβ)
      linarith
    have hg1 : γ j ≤ Rγ * γ (j + 1) := by simpa using (hRγ (j + 1)).1
    have h3 : ‖x (j + 1) ω - x j ω‖ + ‖y (j + 1) ω - y j ω‖ ≤
        CH₀ * (Rβ * Bq + Rγ) * γ (j + 1) := by
      have := mul_le_mul_of_nonneg_right hb1 hCH
      have := mul_le_mul_of_nonneg_right hg1 hCH
      nlinarith
    have := mul_le_mul_of_nonneg_left h3 hLV
    calc _ ≤ LV₀ * (‖x (j + 1) ω - x j ω‖ + ‖y (j + 1) ω - y j ω‖) := h1
      _ ≤ LV₀ * (CH₀ * (Rβ * Bq + Rγ) * γ (j + 1)) := this
      _ = _ := by ring

set_option maxHeartbeats 8000000 in
/-- **Two time scales with θ-dependent sampling.** Let
`x_{k+1} = x_k + β_k H₁(x_k, y_k, ξ_{k+1})` and `y_{k+1} = y_k + γ_k H₂(x_k, y_k, ξ_{k+1})`, with the
finite chain moving by `P_{(x_k, y_k)}(ξ_k, ·)`. Suppose:
* each `H_i` has a bounded Poisson pair `(U_i, V_i)`, with `U_i - V_i = H_i - F_i` and
  `V_i = P U_i`, continuous in the parameter, `V_i` Lipschitz;
* the mean drifts `F_i` satisfy the hypotheses of `tendsto_tts_dissipative_markov`;
* the covariances of the martingale parts `M^i_{k+1} = U_i(p_k, ξ_{k+1}) - V_i(p_k, ξ_k)` converge.

Then the conclusions of the two-time-scale linearization hold. -/
theorem tendsto_tts_param_chain {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0)) {η c₀ K L LF CU CV CH LV : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η) (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hLF : 0 ≤ LF)
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η' : ℝ} (hη' : 0 < η')
    (hΔ : ∀ x, η' * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η' * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x : ℕ → Ω → E d₁} {y : ℕ → Ω → E d₂} {ξ : ℕ → Ω → S}
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
    {H₁ U₁ V₁ : E d₁ → E d₂ → S → E d₁} {H₂ U₂ V₂ : E d₁ → E d₂ → S → E d₂}
    {P : E d₁ → E d₂ → S → S → ℝ}
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • H₁ (x k ω) (y k ω) (ξ (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • H₂ (x k ω) (y k ω) (ξ (k + 1) ω))
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hym : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    (hx0 : ∃ C, ∀ ω, ‖x 0 ω‖ ≤ C) (hy0 : ∃ C, ∀ ω, ‖y 0 ω‖ ≤ C)
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (x k ω) (y k ω) (ξ k ω) s)
    (hpois₁ : ∀ u w s, U₁ u w s - V₁ u w s = H₁ u w s - F₁ u w)
    (hpois₂ : ∀ u w s, U₂ u w s - V₂ u w s = H₂ u w s - F₂ u w)
    (hV₁ : ∀ u w s, V₁ u w s = ∑ s', P u w s s' • U₁ u w s')
    (hV₂ : ∀ u w s, V₂ u w s = ∑ s', P u w s s' • U₂ u w s')
    (hU₁c : ∀ s, Continuous fun p : E d₁ × E d₂ => U₁ p.1 p.2 s)
    (hV₁c : ∀ s, Continuous fun p : E d₁ × E d₂ => V₁ p.1 p.2 s)
    (hU₂c : ∀ s, Continuous fun p : E d₁ × E d₂ => U₂ p.1 p.2 s)
    (hV₂c : ∀ s, Continuous fun p : E d₁ × E d₂ => V₂ p.1 p.2 s)
    (hU₁b : ∀ u w s, ‖U₁ u w s‖ ≤ CU) (hV₁b : ∀ u w s, ‖V₁ u w s‖ ≤ CV)
    (hU₂b : ∀ u w s, ‖U₂ u w s‖ ≤ CU) (hV₂b : ∀ u w s, ‖V₂ u w s‖ ≤ CV)
    (hV₁L : ∀ u w u' w' s, ‖V₁ u w s - V₁ u' w' s‖ ≤ LV * (‖u - u'‖ + ‖w - w'‖))
    (hV₂L : ∀ u w u' w' s, ‖V₂ u w s - V₂ u' w' s‖ ≤ LV * (‖u - u'‖ + ‖w - w'‖))
    (hH₁b : ∀ u w s, ‖H₁ u w s‖ ≤ CH) (hH₂b : ∀ u w s, ‖H₂ u w s‖ ≤ CH)
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂}
    (hΓ₁₁ : Tendsto (fun k => secondMoment μ (ttsM U₁ V₁ x y ξ (k + 1))) atTop (𝓝 Γ₁₁))
    (hΓ₁₂ : Tendsto (fun k => crossMoment μ (ttsM U₁ V₁ x y ξ (k + 1))
      (ttsM U₂ V₂ x y ξ (k + 1))) atTop (𝓝 Γ₁₂))
    (hΓ₂₂ : Tendsto (fun k => secondMoment μ (ttsM U₂ V₂ x y ξ (k + 1))) atTop (𝓝 Γ₂₂)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  obtain ⟨hhm, hhb, hr₁m, hM₁m, hM₁b⟩ := tts_decomp_facts ℱ hxm hym hξm hU₁c hV₁c hU₁b
    hV₁b
  obtain ⟨hgm, hgb, hr₂m, hM₂m, hM₂b⟩ := tts_decomp_facts ℱ hxm hym hξm hU₂c hV₂c hU₂b
    hV₂b
  obtain ⟨Cr₁, hr₁b⟩ := tts_remainder_le hβ hγ hβγ hx hy hH₁b hH₂b hV₁L
  obtain ⟨Cr₂, hr₂b⟩ := tts_remainder_le hβ hγ hβγ hx hy hH₁b hH₂b hV₂L
  set Cr := max Cr₁ Cr₂
  have hr₁b' : ∀ k ω, ‖ttsR V₁ x y ξ k ω‖ ≤ Cr * γ k := fun k ω =>
    (hr₁b k ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hγ.pos k).le)
  have hr₂b' : ∀ k ω, ‖ttsR V₂ x y ξ k ω‖ ≤ Cr * γ k := fun k ω =>
    (hr₂b k ω).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hγ.pos k).le)
  have hp : ∀ k, StronglyMeasurable[ℱ k] (fun ω => (x k ω, y k ω)) := fun k =>
    (hxm k).prodMk (hym k)
  have hmart₁ : ∀ k j, μ[fun ω => ttsM U₁ V₁ x y ξ (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j =>
    condExp_poisson_eq_zero (μ := μ) ℱ k (hp k) (hξm k) (hξm (k + 1))
      (P := fun p : E d₁ × E d₂ => P p.1 p.2) (hlaw k) (U := fun p => U₁ p.1 p.2)
      (V := fun p => V₁ p.1 p.2) (fun t s => hV₁ t.1 t.2 s) hU₁c hV₁c
      (fun t s => hU₁b t.1 t.2 s) (fun t s => hV₁b t.1 t.2 s) j
  have hmart₂ : ∀ k j, μ[fun ω => ttsM U₂ V₂ x y ξ (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j =>
    condExp_poisson_eq_zero (μ := μ) ℱ k (hp k) (hξm k) (hξm (k + 1))
      (P := fun p : E d₁ × E d₂ => P p.1 p.2) (hlaw k) (U := fun p => U₂ p.1 p.2)
      (V := fun p => V₂ p.1 p.2) (fun t s => hV₂ t.1 t.2 s) hU₂c hV₂c
      (fun t s => hU₂b t.1 t.2 s) (fun t s => hV₂b t.1 t.2 s) j
  have hx' : ∀ k ω, x (k + 1) ω = x k ω + β k • (F₁ (x k ω) (y k ω) + ttsM U₁ V₁ x y ξ (k + 1) ω
      + ttsR V₁ x y ξ k ω + ttsH V₁ x y ξ k ω - ttsH V₁ x y ξ (k + 1) ω) := fun k ω => by
    rw [hx k ω, tts_noise_decomp hpois₁ k ω]
  have hy' : ∀ k ω, y (k + 1) ω = y k ω + γ k • (F₂ (x k ω) (y k ω) + ttsM U₂ V₂ x y ξ (k + 1) ω
      + ttsR V₂ x y ξ k ω + ttsH V₂ x y ξ k ω - ttsH V₂ x y ξ (k + 1) ω) := fun k ω => by
    rw [hy k ω, tts_noise_decomp hpois₂ k ω]
  -- the covariance deviations, with `C = 0`
  exact tendsto_tts_dissipative_markov hβ hγ hβγ hγβ hc₀ hc₀η hratio hK hL hLF A₁₁ A₁₂ A₂₁ A₂₂ D
    hD hη' hΔ hA₂₂ ℱ hF₁in hF₁g hF₂in hF₂g hF₁L hF₂L hF₁ hF₂ hF₁c hF₂c hx' hy' hxm hym hx0 hy0
    hhm (Ch := max CV CV) (fun k ω => (hhb k ω).trans (le_max_left _ _)) hgm
    (fun k ω => (hgb k ω).trans (le_max_left _ _)) hr₁m hr₁b' hr₂m hr₂b' hM₁m hM₁b hmart₁ hM₂m
    (fun k ω => hM₂b k ω) hmart₂ le_rfl
    (δ₁ := fun k => ‖secondMoment μ (ttsM U₁ V₁ x y ξ (k + 1)) - Γ₁₁‖)
    (δ₂ := fun k => ‖crossMoment μ (ttsM U₁ V₁ x y ξ (k + 1)) (ttsM U₂ V₂ x y ξ (k + 1)) - Γ₁₂‖)
    (δ₃ := fun k => ‖secondMoment μ (ttsM U₂ V₂ x y ξ (k + 1)) - Γ₂₂‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (tendsto_iff_norm_sub_tendsto_zero.mp hΓ₁₁)
    (tendsto_iff_norm_sub_tendsto_zero.mp hΓ₁₂) (tendsto_iff_norm_sub_tendsto_zero.mp hΓ₂₂) (fun k => by simp) (fun k => by simp) (fun k => by simp)

end TTS

end StochasticApproximation
