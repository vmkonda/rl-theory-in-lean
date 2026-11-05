/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TraceMoments

/-!
# Orthogonal martingale parts add their covariances

The martingale step of Theorems 4.5 and 4.6 of `docs/actor-critic-rates.md`. The REINFORCE (or
TD(`λ`)) noise splits as the TD(0) actor-critic noise plus `D_k = δ_k (B_k - b(s_k))`. With
respect to the filtration `𝒢_k` that contains the history and the current state but not the
current action:

* `D` is a martingale difference, because `E[δ_k | 𝒢_k] = 0`;
* `D` is asymptotically uncorrelated with every function of the current state and the next
  observation, because the law of the next observation depends on `𝒢_k` only through the state,
  and `B_k - b(s_k)` has conditional mean zero given the state.

So the limit covariances add: `Γ_AO = Γ_AC + lim E[D Dᵀ]`.

* `tendsto_secondMoment_of_orthogonal_split`: Theorem 2.1 when the martingale part is `M + D`
  with `E[M Dᵀ] → 0`: the covariance is `Γ_M + Γ_D`.
* `crossMoment_centered_eq`, `tendsto_crossMoment_centered`, `condExp_centered_eq_zero`: the
  orthogonality and the martingale property, from the hypothesis that the law of the next
  observation depends on the past only through the state.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory

namespace StochasticApproximation

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : MeasureTheory.Filtration ℕ m0}

/-! ### Covariances add -/

lemma tendsto_transpose_crossMoment {d₁ d₂ : ℕ} {a : ℕ → Ω → E d₁} {c : ℕ → Ω → E d₂}
    (haL : ∀ k, MemLp (a k) 2 μ) (hcL : ∀ k, MemLp (c k) 2 μ)
    (h : Tendsto (fun k => crossMoment μ (a k) (c k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossMoment μ (c k) (a k)) atTop (𝓝 0) := by
  refine tendsto_euclid_of_coord fun ij => ?_
  have h1 := ((EuclideanSpace.proj (𝕜 := ℝ) (ij.2, ij.1)).continuous.tendsto _).comp h
  simp only [Function.comp_def, map_zero] at h1
  refine h1.congr fun k => ?_
  show crossMoment μ (a k) (c k) (ij.2, ij.1) = crossMoment μ (c k) (a k) ij
  rw [crossMoment_apply (haL k) (hcL k), crossMoment_apply (hcL k) (haL k)]
  exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)

/-- **Orthogonal martingale parts add their covariances.** If the noise of a linear iteration is
`M_{k+1} + D_{k+1} + h_k - h_{k+1}` with `M`, `D` martingale differences and
`E[M_{k+1} D_{k+1}ᵀ] → 0`, then `β_k⁻¹ E[θ_k θ_kᵀ]` converges to the solution of the Lyapunov
equation with `Γ = Γ_M + Γ_D`. -/
theorem tendsto_secondMoment_of_orthogonal_split {β : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
    (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    {θ M D h : ℕ → Ω → E d} {ΓM ΓD : Mat d}
    (hθ : ∀ k ω, θ (k + 1) ω =
      θ k ω - β k • matCLM A (θ k ω) + β k • (M (k + 1) ω + D (k + 1) ω + h k ω - h (k + 1) ω))
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
    (hMB : ∃ CM, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
    (hmartM : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D (k + 1))) (hDL : ∀ k, MemLp (D (k + 1)) 2 μ)
    (hDB : ∃ CD, ∀ k, ∫ ω, ‖D (k + 1) ω‖ ^ 2 ∂μ ≤ CD)
    (hmartD : ∀ k j, μ[fun ω => D (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hΓM : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 ΓM))
    (hΓD : Tendsto (fun k => secondMoment μ (D (k + 1))) atTop (𝓝 ΓD))
    (hMD : Tendsto (fun k => crossMoment μ (M (k + 1)) (D (k + 1))) atTop (𝓝 0)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = ΓM + ΓD ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨CM, hCM⟩ := hMB
  obtain ⟨CD, hCD⟩ := hDB
  have hsum : ∀ k, secondMoment μ (fun ω => M (k + 1) ω + D (k + 1) ω) =
      secondMoment μ (M (k + 1)) + crossMoment μ (M (k + 1)) (D (k + 1))
        + crossMoment μ (D (k + 1)) (M (k + 1)) + secondMoment μ (D (k + 1)) := fun k => by
    have hS : MemLp (fun ω => M (k + 1) ω + D (k + 1) ω) 2 μ := (hML k).add (hDL k)
    rw [secondMoment, crossMoment_add_left (hML k) (hDL k) hS,
      crossMoment_add_right (hML k) (hML k) (hDL k), crossMoment_add_right (hDL k) (hML k) (hDL k)]
    simp only [secondMoment]
    abel
  have hDM := tendsto_transpose_crossMoment hML hDL hMD
  have hΓ : Tendsto (fun k => secondMoment μ (fun ω => M (k + 1) ω + D (k + 1) ω)) atTop
      (𝓝 (ΓM + ΓD)) := by
    simp only [hsum]
    simpa using ((hΓM.add hMD).add hDM).add hΓD
  have hpt : ∀ k ω, ‖M (k + 1) ω + D (k + 1) ω‖ ^ 2 ≤ 2 * ‖M (k + 1) ω‖ ^ 2
      + 2 * ‖D (k + 1) ω‖ ^ 2 := fun k ω => by
    have := norm_add_le (M (k + 1) ω) (D (k + 1) ω)
    have h0 := norm_nonneg (M (k + 1) ω + D (k + 1) ω)
    nlinarith [sq_nonneg (‖M (k + 1) ω‖ - ‖D (k + 1) ω‖)]
  have hB : ∀ k, ∫ ω, ‖M (k + 1) ω + D (k + 1) ω‖ ^ 2 ∂μ ≤ 2 * CM + 2 * CD := fun k => by
    have i1 := (memLp_sq_integrable (hML k)).const_mul 2
    have i2 := (memLp_sq_integrable (hDL k)).const_mul 2
    have i12 : Integrable (fun ω => 2 * ‖M (k + 1) ω‖ ^ 2 + 2 * ‖D (k + 1) ω‖ ^ 2) μ := i1.add i2
    have hS : MemLp (fun ω => M (k + 1) ω + D (k + 1) ω) 2 μ := (hML k).add (hDL k)
    have hint := integral_mono (memLp_sq_integrable hS) i12 (hpt k)
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hint
    linarith [hCM k, hCD k]
  refine tendsto_secondMoment_of_markov_noise hβ A hη hA ℱ (M := fun n ω => M n ω + D n ω)
    (fun k ω => by rw [hθ k ω]) hθ0 hθ0L hh hhL hhB (fun k => (hM k).add (hD k))
    (fun k => (hML k).add (hDL k)) ⟨_, hB⟩ (fun k j => ?_) hΓ
  have iM := (memLp_apply (hML k) j).integrable one_le_two
  have iD := (memLp_apply (hDL k) j).integrable one_le_two
  filter_upwards [condExp_add iM iD (ℱ k), hmartM k j, hmartD k j] with ω h1 h2 h3
  simp only [PiLp.add_apply] at h1 ⊢
  rw [show (fun ω => M (k + 1) ω j + D (k + 1) ω j) = (fun ω => M (k + 1) ω j)
    + fun ω => D (k + 1) ω j from rfl, h1, Pi.add_apply, h2, h3, Pi.zero_apply, add_zero]

/-! ### Orthogonality from the conditional law of the next observation -/

section Centered

variable {S X : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  {σ : ℕ → Ω → S} {ξ : ℕ → Ω → X} {P : S → X → ℝ}

omit [IsProbabilityMeasure μ] [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] in
lemma norm_le_sum_sum₂ {d₁ : ℕ} (Φ : S → X → E d₁) (s : S) (x : X) :
    ‖Φ s x‖ ≤ ∑ s, ∑ x, ‖Φ s x‖ :=
  (single_le_sum (f := fun x => ‖Φ s x‖) (fun _ _ => norm_nonneg _) (mem_univ x)).trans
    (single_le_sum (f := fun s => ∑ x, ‖Φ s x‖) (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)
      (mem_univ s))

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] in
lemma integral_sq_le_of_bound {d₁ : ℕ} {g : Ω → E d₁} {C : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ C ^ 2 := by
  calc ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ ∫ _ω, C ^ 2 ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
          (integrable_const _) (Eventually.of_forall fun ω =>
            pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2)
    _ = C ^ 2 := by simp

omit [IsProbabilityMeasure μ] [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] in
lemma indicator_eq_of {k : ℕ} {s : S} {ω : Ω} (g : Ω → ℝ) (h : σ k ω = s) :
    {ω | σ k ω = s}.indicator g ω = g ω := Set.indicator_of_mem (show ω ∈ {ω | σ k ω = s} from h) g

omit [IsProbabilityMeasure μ] [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] in
lemma indicator_eq_zero_of {k : ℕ} {s : S} {ω : Ω} (g : Ω → ℝ) (h : σ k ω ≠ s) :
    {ω | σ k ω = s}.indicator g ω = 0 :=
  Set.indicator_of_not_mem (show ω ∉ {ω | σ k ω = s} from h) g

omit [IsProbabilityMeasure μ] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] in
/-- `Σ_s 1{σ_k = s} g f(s) = g f(σ_k)`. -/
lemma sum_indicator_mul {k : ℕ} (ω : Ω) (g : S → Ω → ℝ) (f : S → ℝ) :
    ∑ s, {ω | σ k ω = s}.indicator (g s) ω * f s = g (σ k ω) ω * f (σ k ω) := by
  rw [sum_eq_single (σ k ω)]
  · rw [indicator_eq_of _ rfl]
  · intro s _ hs; rw [indicator_eq_zero_of _ (Ne.symm hs), zero_mul]
  · simp

/-- The next observation's law depends on the past only through the current state:
`E[F(ξ_{k+1}) | 𝒢_k] = Σ_x P(σ_k, x) F(x)`. -/
structure StateDriven (μ : Measure Ω) (ℱ : MeasureTheory.Filtration ℕ m0) (σ : ℕ → Ω → S)
    (ξ : ℕ → Ω → X) (P : S → X → ℝ) : Prop where
  state : ∀ k, Measurable[ℱ k] (σ k)
  obs : ∀ k, Measurable[ℱ (k + 1)] (ξ (k + 1))
  law : ∀ k (F : X → ℝ), μ[fun ω => F (ξ (k + 1) ω) | ℱ k] =ᵐ[μ]
    fun ω => ∑ x, P (σ k ω) x * F x

lemma StateDriven.stronglyMeasurable_obs (hσ : StateDriven μ ℱ σ ξ P) (F : X → ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] fun ω => F (ξ (k + 1) ω) :=
  (StronglyMeasurable.of_discrete (f := F)).comp_measurable (hσ.obs k)

lemma StateDriven.integrable_obs (hσ : StateDriven μ ℱ σ ξ P) (F : X → ℝ) (k : ℕ) :
    Integrable (fun ω => F (ξ (k + 1) ω)) μ := by
  refine (memLp_top_of_bound ((hσ.stronglyMeasurable_obs F k).mono
    (ℱ.le (k + 1))).aestronglyMeasurable (∑ x, |F x|) (Eventually.of_forall fun ω => ?_)).integrable
    le_top
  rw [Real.norm_eq_abs]
  exact single_le_sum (f := fun x => |F x|) (fun _ _ => abs_nonneg _) (mem_univ _)

/-- The conditional law, integrated against a bounded `𝒢_k`-measurable weight. -/
lemma StateDriven.integral_mul (hσ : StateDriven μ ℱ σ ξ P) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (F : X → ℝ) :
    ∫ ω, W ω * F (ξ (k + 1) ω) ∂μ = ∫ ω, W ω * ∑ x, P (σ k ω) x * F x ∂μ := by
  obtain ⟨C, hC⟩ := hWB
  have hGi := hσ.integrable_obs F k
  have hprod : Integrable (W * fun ω => F (ξ (k + 1) ω)) μ :=
    hGi.bdd_mul (hW.mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω⟩
  have hc := integral_condExp (μ := μ) (ℱ.le k) (f := W * fun ω => F (ξ (k + 1) ω))
  change ∫ ω, (W * fun ω => F (ξ (k + 1) ω)) ω ∂μ = _
  rw [← hc]
  refine integral_congr_ae ?_
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hW hprod hGi, hσ.law k F] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]

/-- The conditional law for functions of the state and the next observation. -/
lemma StateDriven.law₂ (hσ : StateDriven μ ℱ σ ξ P) [DecidableEq S] (k : ℕ) (F : S → X → ℝ) :
    μ[fun ω => F (σ k ω) (ξ (k + 1) ω) | ℱ k] =ᵐ[μ]
      fun ω => ∑ x, P (σ k ω) x * F (σ k ω) x := by
  have hset : ∀ s, MeasurableSet[ℱ k] {ω | σ k ω = s} := fun s =>
    hσ.state k (measurableSet_singleton s)
  set I : S → Ω → ℝ := fun s => {ω | σ k ω = s}.indicator fun _ => 1 with hI
  have hIm : ∀ s, StronglyMeasurable[ℱ k] (I s) := fun s =>
    stronglyMeasurable_const.indicator (hset s)
  have e : (fun ω => F (σ k ω) (ξ (k + 1) ω)) =
      ∑ s, (I s * fun ω => F s (ξ (k + 1) ω)) := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, hI]
    rw [sum_indicator_mul ω (fun _ _ => 1) (fun s => F s (ξ (k + 1) ω)), one_mul]
  have hint : ∀ s, Integrable (I s * fun ω => F s (ξ (k + 1) ω)) μ := fun s =>
    (hσ.integrable_obs (F s) k).bdd_mul ((hIm s).mono (ℱ.le k)).aestronglyMeasurable
      ⟨1, fun ω => by
        simp only [hI]
        by_cases h : σ k ω = s
        · rw [indicator_eq_of _ h, norm_one]
        · rw [indicator_eq_zero_of _ h, norm_zero]; exact zero_le_one⟩
  rw [e]
  have hsum := condExp_finset_sum (s := univ) (μ := μ) (fun s _ => hint s) (ℱ k)
  have hterm : ∀ s, μ[I s * fun ω => F s (ξ (k + 1) ω) | ℱ k] =ᵐ[μ]
      fun ω => I s ω * ∑ x, P (σ k ω) x * F s x := fun s => by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hIm s) (hint s)
      (hσ.integrable_obs (F s) k), hσ.law k (F s)] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with ω h1 h2
  rw [h1, Finset.sum_apply, sum_congr rfl fun s _ => h2 s]
  simp only [hI]
  rw [sum_indicator_mul ω (fun _ _ => 1) (fun s => ∑ x, P (σ k ω) x * F s x), one_mul]

lemma StateDriven.stronglyMeasurable_pair (hσ : StateDriven μ ℱ σ ξ P) {d₁ : ℕ}
    (Φ : S → X → E d₁) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] fun ω => Φ (σ k ω) (ξ (k + 1) ω) :=
  (StronglyMeasurable.of_discrete (f := Function.uncurry Φ)).comp_measurable
    (((hσ.state k).mono (ℱ.mono (Nat.le_succ k)) le_rfl).prodMk (hσ.obs k))

/-- The centered variable `δ(ξ_{k+1}) (B_k - b(σ_k))` is `𝒢_{k+1}`-measurable. -/
lemma StateDriven.stronglyMeasurable_centered (hσ : StateDriven μ ℱ σ ξ P) {d₂ : ℕ}
    {B : ℕ → Ω → E d₂} (hB : ∀ k, StronglyMeasurable[ℱ k] (B k)) (b : S → E d₂) (δ : X → ℝ)
    (k : ℕ) : StronglyMeasurable[ℱ (k + 1)] fun ω => δ (ξ (k + 1) ω) • (B k ω - b (σ k ω)) := by
  have h1 := hσ.stronglyMeasurable_obs δ k
  have h2 : StronglyMeasurable[ℱ (k + 1)] fun ω => B k ω - b (σ k ω) :=
    ((hB k).sub ((StronglyMeasurable.of_discrete (f := b)).comp_measurable (hσ.state k))).mono
      (ℱ.mono (Nat.le_succ k))
  exact h1.smul h2

/-- **The cross moment, exactly.** For `M_{k+1} = Φ(σ_k, ξ_{k+1})` and
`D_{k+1} = δ(ξ_{k+1}) (B_k - b(σ_k))` with `B_k` bounded and `𝒢_k`-measurable,
`E[M_i D_j] = Σ_s (Σ_x P s x Φ(s, x)_i δ(x)) E[(B_k - b(s))_j 1{σ_k = s}]`. -/
lemma StateDriven.integral_centered_eq (hσ : StateDriven μ ℱ σ ξ P) {d₁ d₂ : ℕ} {k : ℕ}
    {B : Ω → E d₂} (hB : StronglyMeasurable[ℱ k] B) (hBB : ∃ C, ∀ ω, ‖B ω‖ ≤ C) (b : S → E d₂)
    (Φ : S → X → E d₁) (δ : X → ℝ) (i : Fin d₁) (j : Fin d₂) :
    ∫ ω, Φ (σ k ω) (ξ (k + 1) ω) i * (δ (ξ (k + 1) ω) • (B ω - b (σ k ω))) j ∂μ =
      ∑ s, (∑ x, P s x * (Φ s x i * δ x)) *
        ∫ ω, {ω | σ k ω = s}.indicator (fun ω => B ω j - b s j) ω ∂μ := by
  obtain ⟨C, hC⟩ := hBB
  have hset : ∀ s, MeasurableSet[ℱ k] {ω | σ k ω = s} := fun s =>
    hσ.state k (measurableSet_singleton s)
  have hW : ∀ s, StronglyMeasurable[ℱ k] ({ω | σ k ω = s}.indicator fun ω => B ω j - b s j) :=
    fun s => (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_stronglyMeasurable hB).sub
      stronglyMeasurable_const).indicator (hset s)
  have hWB : ∀ s, ∃ C', ∀ ω, |({ω | σ k ω = s}.indicator fun ω => B ω j - b s j) ω| ≤ C' :=
    fun s => ⟨C + ‖b s‖, fun ω => by
      by_cases h : σ k ω = s
      · rw [indicator_eq_of _ h]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le _ j).trans (hC ω)
        · rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ j
      · rw [indicator_eq_zero_of _ h, abs_zero]
        exact add_nonneg ((norm_nonneg _).trans (hC ω)) (norm_nonneg _)⟩
  have e : ∀ ω, Φ (σ k ω) (ξ (k + 1) ω) i * (δ (ξ (k + 1) ω) • (B ω - b (σ k ω))) j =
      ∑ s, ({ω | σ k ω = s}.indicator (fun ω => B ω j - b s j)) ω
        * (fun x => Φ s x i * δ x) (ξ (k + 1) ω) := fun ω => by
    rw [sum_indicator_mul ω (fun s ω => B ω j - b s j) (fun s => Φ s (ξ (k + 1) ω) i * δ (ξ (k + 1) ω))]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  rw [integral_congr_ae (Eventually.of_forall e)]
  rw [integral_finset_sum _ fun s _ => by
    have hI : Integrable ({ω | σ k ω = s}.indicator fun ω => B ω j - b s j) μ := by
      obtain ⟨C', hC'⟩ := hWB s
      exact (memLp_top_of_bound ((hW s).mono (ℱ.le k)).aestronglyMeasurable C'
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC' ω)).integrable le_top
    exact (hσ.integrable_obs (fun x => Φ s x i * δ x) k).bdd_mul
      ((hW s).mono (ℱ.le k)).aestronglyMeasurable (by
        obtain ⟨C', hC'⟩ := hWB s
        exact ⟨C', fun ω => by rw [Real.norm_eq_abs]; exact hC' ω⟩)]
  refine sum_congr rfl fun s _ => ?_
  rw [hσ.integral_mul (hW s) (hWB s) (fun x => Φ s x i * δ x), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show {ω | σ k ω = s}.indicator (fun ω => B ω j - b s j) ω * ∑ x, P (σ k ω) x * (Φ s x i * δ x)
    = (∑ x, P s x * (Φ s x i * δ x)) * {ω | σ k ω = s}.indicator (fun ω => B ω j - b s j) ω
  by_cases h : σ k ω = s
  · rw [indicator_eq_of _ h, h]; ring
  · rw [indicator_eq_zero_of _ h]; ring

/-- **Orthogonality.** If `E[(B_k - b(s))_j 1{σ_k = s}] → 0` for every state (for instance
`b(s) = E[B_k | σ_k = s]` in stationarity), then `E[M_{k+1} D_{k+1}ᵀ] → 0` for every
`M_{k+1} = Φ(σ_k, ξ_{k+1})`. -/
theorem StateDriven.tendsto_crossMoment_centered (hσ : StateDriven μ ℱ σ ξ P) {d₁ d₂ : ℕ}
    {B : ℕ → Ω → E d₂} (hB : ∀ k, StronglyMeasurable[ℱ k] (B k))
    (hBB : ∀ k, ∃ C, ∀ ω, ‖B k ω‖ ≤ C) (b : S → E d₂) (Φ : S → X → E d₁) (δ : X → ℝ)
    (hcent : ∀ s j, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator
      (fun ω => B k ω j - b s j) ω ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => crossMoment μ (fun ω => Φ (σ k ω) (ξ (k + 1) ω))
      (fun ω => δ (ξ (k + 1) ω) • (B k ω - b (σ k ω)))) atTop (𝓝 0) := by
  have hΦL : ∀ k, MemLp (fun ω => Φ (σ k ω) (ξ (k + 1) ω)) 2 μ := fun k =>
    memLp_of_finite ((hσ.stronglyMeasurable_pair Φ k).mono (ℱ.le (k + 1))).aestronglyMeasurable
      (C := ∑ s, ∑ x, ‖Φ s x‖) fun ω => norm_le_sum_sum₂ Φ _ _
  have hDL : ∀ k, MemLp (fun ω => δ (ξ (k + 1) ω) • (B k ω - b (σ k ω))) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hBB k
    refine memLp_of_finite ((hσ.stronglyMeasurable_centered hB b δ k).mono
      (ℱ.le (k + 1))).aestronglyMeasurable (C := (∑ x, |δ x|) * (C + ∑ s, ‖b s‖)) fun ω => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (single_le_sum (f := fun x => |δ x|) (fun _ _ => abs_nonneg _) (mem_univ _))
      ((norm_sub_le _ _).trans (add_le_add (hC ω) (norm_le_sum_gen b _))) (norm_nonneg _)
      (sum_nonneg fun _ _ => abs_nonneg _)
  refine tendsto_euclid_of_coord fun ij => ?_
  have h : Tendsto (fun k => ∑ s, (∑ x, P s x * (Φ s x ij.1 * δ x)) *
      ∫ ω, {ω | σ k ω = s}.indicator (fun ω => B k ω ij.2 - b s ij.2) ω ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (univ : Finset S) fun s _ => (hcent s ij.2).const_mul
      (∑ x, P s x * (Φ s x ij.1 * δ x))
  refine h.congr fun k => ?_
  rw [crossMoment_apply (hΦL k) (hDL k), hσ.integral_centered_eq (hB k) (hBB k) b Φ δ ij.1 ij.2]

/-- **The martingale property.** If `δ` has mean zero under the conditional law of the next
observation, `Σ_x P s x δ x = 0`, then `D_{k+1} = δ(ξ_{k+1}) (B_k - b(σ_k))` is a martingale
difference. -/
theorem StateDriven.condExp_centered_eq_zero (hσ : StateDriven μ ℱ σ ξ P) {d₂ : ℕ}
    {B : ℕ → Ω → E d₂} (hB : ∀ k, StronglyMeasurable[ℱ k] (B k))
    (hBB : ∀ k, ∃ C, ∀ ω, ‖B k ω‖ ≤ C) (b : S → E d₂) (δ : X → ℝ)
    (hδ : ∀ s, ∑ x, P s x * δ x = 0) (k : ℕ) (j : Fin d₂) :
    μ[fun ω => (δ (ξ (k + 1) ω) • (B k ω - b (σ k ω))) j | ℱ k] =ᵐ[μ] 0 := by
  obtain ⟨C, hC⟩ := hBB k
  set W : Ω → ℝ := fun ω => B k ω j - b (σ k ω) j with hWdef
  have hW : StronglyMeasurable[ℱ k] W :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_stronglyMeasurable (hB k)).sub
      ((StronglyMeasurable.of_discrete (f := fun s => b s j)).comp_measurable (hσ.state k))
  have hGi := hσ.integrable_obs δ k
  have hprod : Integrable (W * fun ω => δ (ξ (k + 1) ω)) μ :=
    hGi.bdd_mul (hW.mono (ℱ.le k)).aestronglyMeasurable ⟨C + ∑ s, ‖b s‖, fun ω => by
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le _ j).trans (hC ω)
      · rw [← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le _ j).trans (norm_le_sum_gen b _)⟩
  have e : (fun ω => (δ (ξ (k + 1) ω) • (B k ω - b (σ k ω))) j) =
      W * fun ω => δ (ξ (k + 1) ω) := by
    funext ω
    simp only [hWdef, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Pi.mul_apply]
    ring
  rw [e]
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hW hprod hGi, hσ.law k δ] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, hδ, mul_zero, Pi.zero_apply]

/-- **Theorems 4.5 and 4.6, the martingale step.** Let the noise of a linear iteration split as
`M_{k+1} + D_{k+1} + h_k - h_{k+1}` with `M_{k+1} = Φ(σ_k, ξ_{k+1})` a martingale difference and
`D_{k+1} = δ(ξ_{k+1}) (B_k - b(σ_k))`. Suppose the law of the next observation depends on the past
only through the state, `δ` has conditional mean zero, `B` has bounded second moments and
`E[(B_k - b(s)) 1{σ_k = s}] → 0`. Then `β_k⁻¹ E[θ_k θ_kᵀ]` converges to the solution of the
Lyapunov equation with `Γ = Γ_M + Γ_D`: the covariances add. -/
theorem StateDriven.tendsto_secondMoment_of_centered_split (hσ : StateDriven μ ℱ σ ξ P)
    {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ}
    (hη : 0 < η) (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    {θ h B : ℕ → Ω → E d} (Φ : S → X → E d) (δ : X → ℝ) (b : S → E d) {ΓM ΓD : Mat d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω)
      + β k • (Φ (σ k ω) (ξ (k + 1) ω) + δ (ξ (k + 1) ω) • (B k ω - b (σ k ω)) + h k ω
        - h (k + 1) ω))
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
    (hΦ : ∀ s, ∑ x, P s x • Φ s x = 0) (hδ : ∀ s, ∑ x, P s x * δ x = 0)
    (hB : ∀ k, StronglyMeasurable[ℱ k] (B k)) (hBB : ∀ k, ∃ C, ∀ ω, ‖B k ω‖ ≤ C)
    (hB2 : ∃ C, ∀ k, ∫ ω, ‖B k ω‖ ^ 2 ∂μ ≤ C)
    (hcent : ∀ s j, Tendsto (fun k => ∫ ω, {ω | σ k ω = s}.indicator
      (fun ω => B k ω j - b s j) ω ∂μ) atTop (𝓝 0))
    (hΓM : Tendsto (fun k => secondMoment μ fun ω => Φ (σ k ω) (ξ (k + 1) ω)) atTop (𝓝 ΓM))
    (hΓD : Tendsto (fun k => secondMoment μ fun ω => δ (ξ (k + 1) ω) • (B k ω - b (σ k ω)))
      atTop (𝓝 ΓD)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = ΓM + ΓD ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨C₂, hC₂⟩ := hB2
  set Cδ := ∑ x, |δ x|
  set Cb := ∑ s, ‖b s‖
  have hCδ : 0 ≤ Cδ := sum_nonneg fun _ _ => abs_nonneg _
  have hCb : 0 ≤ Cb := sum_nonneg fun _ _ => norm_nonneg _
  have hΦL : ∀ k, MemLp (fun ω => Φ (σ k ω) (ξ (k + 1) ω)) 2 μ := fun k =>
    memLp_of_finite ((hσ.stronglyMeasurable_pair Φ k).mono (ℱ.le (k + 1))).aestronglyMeasurable
      (C := ∑ s, ∑ x, ‖Φ s x‖) fun ω => norm_le_sum_sum₂ Φ _ _
  have hBL : ∀ k, MemLp (B k) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hBB k
    exact memLp_of_finite ((hB k).mono (ℱ.le k)).aestronglyMeasurable hC
  have bD : ∀ k ω, ‖δ (ξ (k + 1) ω) • (B k ω - b (σ k ω))‖ ≤ Cδ * ‖B k ω‖ + Cδ * Cb :=
    fun k ω => by
      rw [norm_smul, Real.norm_eq_abs, ← mul_add]
      exact mul_le_mul (single_le_sum (f := fun x => |δ x|) (fun _ _ => abs_nonneg _)
        (mem_univ _)) ((norm_sub_le _ _).trans (add_le_add_left (norm_le_sum_gen b _) _))
        (norm_nonneg _) hCδ
  have hDL : ∀ k, MemLp (fun ω => δ (ξ (k + 1) ω) • (B k ω - b (σ k ω))) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hBB k
    exact memLp_of_finite ((hσ.stronglyMeasurable_centered hB b δ k).mono
      (ℱ.le (k + 1))).aestronglyMeasurable (C := Cδ * C + Cδ * Cb) fun ω =>
        (bD k ω).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hC ω) hCδ) _)
  have hMart : ∀ k j, μ[fun ω => Φ (σ k ω) (ξ (k + 1) ω) j | ℱ k] =ᵐ[μ] 0 := fun k j => by
    classical
    filter_upwards [hσ.law₂ k (fun s x => Φ s x j)] with ω h
    rw [h, Pi.zero_apply]
    have := congrArg (fun v : E d => v j) (hΦ (σ k ω))
    simpa [euclid_sum_apply'] using this
  refine tendsto_secondMoment_of_orthogonal_split (ℱ := ℱ) hβ A hη hA
    (M := fun n ω => Φ (σ n.pred ω) (ξ n ω))
    (D := fun n ω => δ (ξ n ω) • (B n.pred ω - b (σ n.pred ω))) (h := h) (fun k ω => hθ k ω)
    hθ0 hθ0L hh hhL hhB (fun k => hσ.stronglyMeasurable_pair Φ k) hΦL
    ⟨_, fun k => integral_sq_le_of_bound (μ := μ) fun ω => norm_le_sum_sum₂ Φ (σ k ω) (ξ (k + 1) ω)⟩
    hMart (fun k => hσ.stronglyMeasurable_centered hB b δ k) hDL
    ⟨_, fun k => (integral_sq_le_of_affine (hDL k) (hBL k) (bD k) hCδ
      (mul_nonneg hCδ hCb)).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hC₂ k)
        (by positivity)) _)⟩
    (fun k j => hσ.condExp_centered_eq_zero hB hBB b δ hδ k j) hΓM hΓD
    (hσ.tendsto_crossMoment_centered hB hBB b Φ δ hcent)

end Centered

end StochasticApproximation
