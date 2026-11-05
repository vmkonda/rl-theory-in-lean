/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.MultiplicativeNoiseCovariance

/-!
# Linearization

Section 2 of `docs/actor-critic-rates.md`.

* `hasFDerivAt_implicit`: Lemma 2.1. If the critic's fixed point `r*(θ)` solves
  `Ḡ(θ, r*(θ)) = 0` and is differentiable, the actor's mean direction `f(θ) = F̄(θ, r*(θ))` has
  derivative `-(A₁₁ - A₁₂ A₂₂⁻¹ A₂₁)` at the root, with `A_ij` the negated partial derivatives.
* `tendsto_secondMoment_of_nonlinear`: Assumption 2.2 for a single time scale with martingale
  noise. The nonlinear iteration `θ_{k+1} = θ_k + β_k (f(θ_k) + M_{k+1})`, with
  `f(θ) = -A(θ - θ̂) + O(‖θ - θ̂‖²)` and fourth moments `E‖θ_k - θ̂‖⁴ = O(β_k²)`, has the asymptotic
  covariance of its linearization `x_{k+1} = x_k - β_k A x_k + β_k M_{k+1}`.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory

namespace StochasticApproximation

/-! ### Lemma 2.1: the Jacobian of the actor's direction -/

section Implicit

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Lemma 2.1.** Let `F̄ : X × Y → X` and `Ḡ : X × Y → Y` be differentiable at `(θ̂, r̂)` with
partial derivatives `-A₁₁, -A₁₂` and `-A₂₁, -A₂₂`, and let `r*` be differentiable at `θ̂` with
`r*(θ̂) = r̂` and `Ḡ(θ, r*(θ)) = 0` for all `θ`. If `A₂₂` has a left inverse `A₂₂⁻¹`, then
`f(θ) = F̄(θ, r*(θ))` has derivative `-(A₁₁ - A₁₂ A₂₂⁻¹ A₂₁)` at `θ̂`, and `r*` has derivative
`-A₂₂⁻¹ A₂₁`. -/
theorem hasFDerivAt_implicit {Fb : X × Y → Z} {Gb : X × Y → Y} {rstar : X → Y} {θh : X}
    {DF : X × Y →L[ℝ] Z} {DG : X × Y →L[ℝ] Y} {Dr : X →L[ℝ] Y}
    (hF : HasFDerivAt Fb DF (θh, rstar θh)) (hG : HasFDerivAt Gb DG (θh, rstar θh))
    (hr : HasFDerivAt rstar Dr θh) (hroot : ∀ θ, Gb (θ, rstar θ) = 0)
    {A₂₂inv : Y →L[ℝ] Y} (hinv : A₂₂inv.comp (DG.comp (ContinuousLinearMap.inr ℝ X Y)) =
      ContinuousLinearMap.id ℝ Y) :
    Dr = -(A₂₂inv.comp (DG.comp (ContinuousLinearMap.inl ℝ X Y))) ∧
      HasFDerivAt (fun θ => Fb (θ, rstar θ))
        (DF.comp (ContinuousLinearMap.inl ℝ X Y) - (DF.comp (ContinuousLinearMap.inr ℝ X Y)).comp
          (A₂₂inv.comp (DG.comp (ContinuousLinearMap.inl ℝ X Y)))) θh := by
  have hpair : HasFDerivAt (fun θ => (θ, rstar θ)) ((ContinuousLinearMap.id ℝ X).prod Dr) θh :=
    (hasFDerivAt_id θh).prodMk hr
  -- the root equation has zero derivative
  have hG0 : HasFDerivAt (fun θ => Gb (θ, rstar θ)) (DG.comp ((ContinuousLinearMap.id ℝ X).prod Dr))
      θh := hG.comp θh hpair
  have hzero : DG.comp ((ContinuousLinearMap.id ℝ X).prod Dr) = 0 := by
    have hc : HasFDerivAt (fun θ => Gb (θ, rstar θ)) (0 : X →L[ℝ] Y) θh := by
      simp only [hroot]; exact hasFDerivAt_const 0 θh
    exact hG0.unique hc
  have hsplit : ∀ (x : X) (y : Y), ((x, y) : X × Y) = (x, 0) + (0, y) := fun x y => by simp
  have hinv' : ∀ y, A₂₂inv (DG (0, y)) = y := fun y => by
    have := congrArg (fun L : Y →L[ℝ] Y => L y) hinv
    simpa using this
  have hDr : Dr = -(A₂₂inv.comp (DG.comp (ContinuousLinearMap.inl ℝ X Y))) := by
    ext x
    have h1 := congrArg (fun L : X →L[ℝ] Y => A₂₂inv (L x)) hzero
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, map_zero] at h1
    rw [hsplit x (Dr x), map_add, map_add, hinv'] at h1
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h1
  refine ⟨hDr, ?_⟩
  have hf := hF.comp θh hpair
  have e : DF.comp ((ContinuousLinearMap.id ℝ X).prod Dr) =
      DF.comp (ContinuousLinearMap.inl ℝ X Y) - (DF.comp (ContinuousLinearMap.inr ℝ X Y)).comp
        (A₂₂inv.comp (DG.comp (ContinuousLinearMap.inl ℝ X Y))) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    rw [hsplit x (Dr x), map_add, hDr]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
    rw [show ((0 : X), -A₂₂inv (DG (x, 0))) = -((0 : X), A₂₂inv (DG (x, 0))) by simp, map_neg,
      sub_eq_add_neg]
  rw [← e]
  exact hf

end Implicit

/-! ### Assumption 2.2 for a single time scale -/

section Nonlinear

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {β : ℕ → ℝ} {βbar : ℝ}

set_option maxHeartbeats 800000 in
/-- **The linearization is exact to first order in the covariance.** Let
`θ_{k+1} = θ_k + β_k (f(θ_k) + M_{k+1})` with `M` a martingale difference whose covariance
converges to `Γ`, and let `f(θ) = -A(θ - θ̂) + ρ(θ)` with `‖ρ(θ)‖ ≤ L ‖θ - θ̂‖²` (a Taylor
expansion at the root). If the fourth moments are of the order of the step,
`E‖θ_k - θ̂‖⁴ ≤ C β_k²`, then `β_k⁻¹ E[(θ_k - θ̂)(θ_k - θ̂)ᵀ]` converges to the solution of the
Lyapunov equation of the linearized iteration `x_{k+1} = x_k - β_k A x_k + β_k M_{k+1}`. -/
theorem tendsto_secondMoment_of_nonlinear (hβ : StepSizeRate β βbar)
    (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
    (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ M : ℕ → Ω → E d} {θh : E d} {f : E d → E d}
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ x, ‖f x + matCLM A (x - θh)‖ ≤ L * ‖x - θh‖ ^ 2)
    (hfc : Continuous f) {Γ : Mat d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • (f (θ k ω) + M (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hθL : ∀ k, MemLp (θ k) 2 μ)
    (h4i : ∀ k, Integrable (fun ω => ‖θ k ω - θh‖ ^ 4) μ)
    (h4 : ∃ C₄, ∀ k, ∫ ω, ‖θ k ω - θh‖ ^ 4 ∂μ ≤ C₄ * β k ^ 2)
    (hML : ∀ k, MemLp (M (k + 1)) 2 μ) (hMB : ∃ CM, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hΓ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (fun ω => θ k ω - θh)) atTop (𝓝 Sig) := by
  obtain ⟨Sig, hSig⟩ := exists_solution_of_coercive _ (by positivity : (0 : ℝ) < 2 * η)
    (lyapOp_coercive _ hA) Γ
  refine ⟨Sig, hSig, ?_⟩
  obtain ⟨C₄, hC₄⟩ := h4
  obtain ⟨CM, hCM⟩ := hMB
  obtain ⟨B, hB⟩ := hβ.tendsto_zero.bddAbove_range
  have hβB : ∀ k, β k ≤ B := fun k => hB ⟨k, rfl⟩
  have hB0 : 0 ≤ B := (hβ.pos 0).le.trans (hβB 0)
  have hC₄0 : 0 ≤ C₄ := by
    have := hC₄ 0
    have h0 : 0 ≤ ∫ ω, ‖θ 0 ω - θh‖ ^ 4 ∂μ := integral_nonneg fun _ => by positivity
    have hb := hβ.pos 0
    by_contra hneg
    push_neg at hneg
    nlinarith [sq_nonneg (β 0), mul_pos hb hb]
  have hCM0 : 0 ≤ CM := (integral_norm_sq_nonneg (μ := μ) (M 1)).trans (hCM 0)
  set e : ℕ → Ω → E d := fun k ω => θ k ω - θh with he
  set ρ : ℕ → Ω → E d := fun k ω => f (θ k ω) + matCLM A (e k ω) with hρ
  have heL : ∀ k, MemLp (e k) 2 μ := fun k => (hθL k).sub (memLp_const θh)
  have hem : ∀ k, StronglyMeasurable[ℱ k] (e k) := fun k => (hθm k).sub stronglyMeasurable_const
  have hρb : ∀ k ω, ‖ρ k ω‖ ≤ L * ‖e k ω‖ ^ 2 := fun k ω => hf (θ k ω)
  have hρm : ∀ k, AEStronglyMeasurable (ρ k) μ := fun k =>
    ((hfc.comp_stronglyMeasurable ((hθm k).mono (ℱ.le k))).aestronglyMeasurable).add
      ((matCLM A).continuous.comp_aestronglyMeasurable ((hem k).mono (ℱ.le k)).aestronglyMeasurable)
  have hρsq : ∀ k ω, ‖ρ k ω‖ ^ 2 ≤ L ^ 2 * ‖θ k ω - θh‖ ^ 4 := fun k ω => by
    have h := hρb k ω
    have h0 := norm_nonneg (ρ k ω)
    calc ‖ρ k ω‖ ^ 2 ≤ (L * ‖e k ω‖ ^ 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = L ^ 2 * ‖θ k ω - θh‖ ^ 4 := by simp only [he]; ring
  have hρL : ∀ k, MemLp (ρ k) 2 μ := fun k => by
    rw [memLp_two_iff_integrable_sq_norm (hρm k)]
    refine ((h4i k).const_mul (L ^ 2)).mono' ((hρm k).norm.pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hρsq k ω
  have hρint : ∀ k, ∫ ω, ‖ρ k ω‖ ^ 2 ∂μ ≤ L ^ 2 * (C₄ * β k ^ 2) := fun k => by
    calc ∫ ω, ‖ρ k ω‖ ^ 2 ∂μ ≤ ∫ ω, L ^ 2 * ‖θ k ω - θh‖ ^ 4 ∂μ :=
          integral_mono (memLp_sq_integrable (hρL k)) ((h4i k).const_mul _) (hρsq k)
      _ ≤ L ^ 2 * (C₄ * β k ^ 2) := by
          rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hC₄ k) (sq_nonneg _)
  -- the recursion of the errors
  have hrec_e : ∀ k, e (k + 1) = fun ω => e k ω - β k • matCLM A (e k ω) + β k • M (k + 1) ω
      + β k • ρ k ω := fun k => by
    funext ω
    simp only [he, hρ, hθ k ω]
    module
  -- the second-moment recursion and its remainder
  set P : ℕ → Mat d := fun k => secondMoment μ (e k) with hP
  set R : ℕ → Mat d := fun k => P (k + 1) - (P k - β k • lyapOp A (P k)
    + β k ^ 2 • sandwich A (P k) + β k ^ 2 • secondMoment μ (M (k + 1))) with hR
  have hrec : ∀ k, P (k + 1) = P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
      + β k ^ 2 • secondMoment μ (M (k + 1)) + R k := fun k => by
    simp only [hR]; abel
  have hRb : ∀ k, ‖R k‖ ≤ (2 * (1 + B * ‖matCLM A‖) * √d * L * √C₄ + 2 * √CM * L * √C₄
      + L ^ 2 * C₄ * B) * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k) := fun k => by
    have hb := hβ.pos k
    have hcL : MemLp (fun ω => β k • ρ k ω) 2 μ := (hρL k).const_smul (β k)
    have hstep := secondMoment_step (μ := μ) (ℱ.le k) A hb.le (hem k) (heL k) (hML k) hcL
      (hmart k)
    have hsm : secondMoment μ (fun ω => e k ω - β k • matCLM A (e k ω) + β k • M (k + 1) ω
        + β k • ρ k ω) = P (k + 1) := by simp only [hP, hrec_e k]
    rw [hsm] at hstep
    -- the sizes
    have hEc : ∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ ≤ β k ^ 2 * (L ^ 2 * (C₄ * β k ^ 2)) := by
      have : (fun ω => ‖β k • ρ k ω‖ ^ 2) = fun ω => β k ^ 2 * ‖ρ k ω‖ ^ 2 := by
        funext ω; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [this, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hρint k) (sq_nonneg _)
    have hsc : √(∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ) ≤ β k ^ 2 * (L * √C₄) := by
      calc √(∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ) ≤ √(β k ^ 2 * (L ^ 2 * (C₄ * β k ^ 2))) :=
            Real.sqrt_le_sqrt hEc
        _ = β k ^ 2 * (L * √C₄) := by
            rw [show β k ^ 2 * (L ^ 2 * (C₄ * β k ^ 2)) = (β k ^ 2 * L) ^ 2 * C₄ by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
            ring
    have hsu : √(∫ ω, ‖e k ω‖ ^ 2 ∂μ) ≤ √d * √‖P k‖ := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
      exact Real.sqrt_le_sqrt (integral_norm_sq_le (heL k))
    have hsm' : √(∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ) ≤ √CM := Real.sqrt_le_sqrt (hCM k)
    have hc2 : ∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ ≤ L ^ 2 * C₄ * B * (β k ^ 2 * β k) := by
      refine hEc.trans ?_
      have hbb : β k ^ 4 ≤ B * β k ^ 3 := by
        have : β k ^ 4 = β k * β k ^ 3 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right (hβB k) (by positivity)
      nlinarith [sq_nonneg L, mul_nonneg (sq_nonneg L) hC₄0]
    have s0 := Real.sqrt_nonneg (∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ)
    have su0 := Real.sqrt_nonneg (∫ ω, ‖e k ω‖ ^ 2 ∂μ)
    have sm0 := Real.sqrt_nonneg (∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ)
    have hA0 : 0 ≤ 1 + β k * ‖matCLM A‖ := by positivity
    have t1 : 2 * ((1 + β k * ‖matCLM A‖) * √(∫ ω, ‖e k ω‖ ^ 2 ∂μ)
        * √(∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ)) ≤
        2 * (1 + B * ‖matCLM A‖) * √d * L * √C₄ * β k ^ 2 * √‖P k‖ := by
      have h1 : (1 + β k * ‖matCLM A‖) ≤ 1 + B * ‖matCLM A‖ := by
        gcongr; exact hβB k
      calc 2 * ((1 + β k * ‖matCLM A‖) * √(∫ ω, ‖e k ω‖ ^ 2 ∂μ)
            * √(∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ))
          ≤ 2 * ((1 + B * ‖matCLM A‖) * (√d * √‖P k‖) * (β k ^ 2 * (L * √C₄))) := by
            gcongr
        _ = _ := by ring
    have t2 : 2 * (β k * √(∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ) * √(∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ)) ≤
        2 * √CM * L * √C₄ * β k ^ 2 * β k := by
      calc 2 * (β k * √(∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ) * √(∫ ω, ‖β k • ρ k ω‖ ^ 2 ∂μ))
          ≤ 2 * (β k * √CM * (β k ^ 2 * (L * √C₄))) := by gcongr
        _ = _ := by ring
    have hRk : ‖R k‖ ≤ 2 * (1 + B * ‖matCLM A‖) * √d * L * √C₄ * β k ^ 2 * √‖P k‖
        + 2 * √CM * L * √C₄ * β k ^ 2 * β k + L ^ 2 * C₄ * B * (β k ^ 2 * β k) := by
      have : R k = P (k + 1) - (P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
          + β k ^ 2 • secondMoment μ (M (k + 1))) := rfl
      rw [this]
      exact hstep.trans (by linarith)
    have hP0 := norm_nonneg (P k)
    have hsP := Real.sqrt_nonneg ‖P k‖
    have hk0 : 0 ≤ 2 * (1 + B * ‖matCLM A‖) * √d * L * √C₄ := by positivity
    have hk1 : 0 ≤ 2 * √CM * L * √C₄ := by positivity
    have hk2 : 0 ≤ L ^ 2 * C₄ * B := by positivity
    have hb2 : 0 ≤ β k ^ 2 := sq_nonneg _
    refine hRk.trans ?_
    set a₁ := 2 * (1 + B * ‖matCLM A‖) * √d * L * √C₄
    set a₂ := 2 * √CM * L * √C₄
    set a₃ := L ^ 2 * C₄ * B
    have key : (a₁ + a₂ + a₃) * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k)
        - (a₁ * β k ^ 2 * √‖P k‖ + a₂ * β k ^ 2 * β k + a₃ * (β k ^ 2 * β k)) =
        a₁ * β k ^ 2 * (‖P k‖ + β k) + a₂ * β k ^ 2 * (√‖P k‖ + ‖P k‖)
          + a₃ * β k ^ 2 * (√‖P k‖ + ‖P k‖) := by ring
    have nn : 0 ≤ a₁ * β k ^ 2 * (‖P k‖ + β k) + a₂ * β k ^ 2 * (√‖P k‖ + ‖P k‖)
        + a₃ * β k ^ 2 * (√‖P k‖ + ‖P k‖) := by positivity
    linarith
  exact tendsto_normalized_second_moment hβ A hη hA hSig hΓ ⟨_, by positivity, hRb⟩ hrec

end Nonlinear

end StochasticApproximation
