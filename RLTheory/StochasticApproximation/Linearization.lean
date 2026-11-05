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
open scoped InnerProductSpace RealInnerProductSpace

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

/-! ### Moment bounds for a dissipative iteration -/

section MomentBounds

variable {β : ℕ → ℝ} {βbar : ℝ}

/-- The normalized contraction factor: if `2η > β̄`, eventually
`0 ≤ (β_k / β_{k+1}) (1 - 2η β_k + K² β_k²) ≤ 1 - a β_k` with `a = (2η - β̄)/2 > 0`. -/
lemma eventually_ratio_contract (hβ : StepSizeRate β βbar) {η K : ℝ} (h2 : βbar < 2 * η) :
    ∀ᶠ k in atTop, 0 ≤ β k / β (k + 1) * (1 - 2 * η * β k + K ^ 2 * β k ^ 2) ∧
      β k / β (k + 1) * (1 - 2 * η * β k + K ^ 2 * β k ^ 2) ≤
        1 - ((2 * η - βbar) / 2) * β k := by
  set ε : ℕ → ℝ := fun k => (β (k + 1))⁻¹ - (β k)⁻¹ with hε
  set t : ℕ → ℝ := fun k => β k / β (k + 1) * (1 - 2 * η * β k + K ^ 2 * β k ^ 2) with ht
  have hq : ∀ k, (t k - 1) / β k =
      ε k - 2 * η + K ^ 2 * β k - 2 * η * β k * ε k + K ^ 2 * β k ^ 2 * ε k := fun k => by
    have hb := (hβ.pos k).ne'
    simp only [ht, hβ.ratio_eq k, hε]
    field_simp
    ring
  have hlim : Tendsto (fun k => (t k - 1) / β k) atTop (𝓝 (βbar - 2 * η)) := by
    simp only [hq]
    have h0 := hβ.tendsto_zero
    have hε' : Tendsto ε atTop (𝓝 βbar) := hβ.inv_diff
    have := ((((hε'.sub_const (2 * η)).add (h0.const_mul (K ^ 2))).sub
      ((h0.const_mul (2 * η)).mul hε')).add (((h0.pow 2).const_mul (K ^ 2)).mul hε'))
    simpa using this
  have hlt : ∀ᶠ k in atTop, (t k - 1) / β k < (βbar - 2 * η) / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have ht1 : Tendsto t atTop (𝓝 1) := by
    have := (hlim.mul hβ.tendsto_zero).const_add 1
    simp only [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    have hb := (hβ.pos k).ne'
    field_simp
  have hpos : ∀ᶠ k in atTop, 0 ≤ t k := ht1.eventually (le_mem_nhds (by norm_num))
  filter_upwards [hlt, hpos] with k h1 h3
  refine ⟨h3, ?_⟩
  have hb := hβ.pos k
  have := (div_lt_iff₀ hb).mp h1
  show t k ≤ _
  nlinarith

/-- **Normalized moment bounds.** If `v ≥ 0` and
`v_{k+1} ≤ (1 - 2η β_k + K² β_k²)^p v_k + D β_k^{p+1}` with `p ≥ 1` and `2η > β̄`, then
`v_k ≤ W β_k^p` for some `W`. -/
lemma bdd_of_moment_recursion (hβ : StepSizeRate β βbar) {η K D : ℝ} (h2η : βbar < 2 * η)
    (hD : 0 ≤ D) {p : ℕ} (hp : 1 ≤ p) {v : ℕ → ℝ} (hv0 : ∀ k, 0 ≤ v k)
    (hrec : ∀ k, v (k + 1) ≤ (1 - 2 * η * β k + K ^ 2 * β k ^ 2) ^ p * v k + D * β k ^ (p + 1)) :
    ∃ W, ∀ k, v k ≤ W * β k ^ p := by
  set a := (2 * η - βbar) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set y : ℕ → ℝ := fun k => v k / β k ^ p with hy
  have hr2 : ∀ᶠ k in atTop, β k / β (k + 1) ≤ 2 := by
    have h := (hβ.tendsto_ratio.inv₀ one_ne_zero)
    simp only [inv_one] at h
    filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2))] with k hk
    rwa [inv_div] at hk
  have hsmall : ∀ᶠ k in atTop, a * β k ≤ 1 := by
    have h := hβ.tendsto_zero.const_mul a
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have hstep : ∀ᶠ k in atTop, y (k + 1) ≤ (1 - a * β k) * y k + (2 ^ p * D) * β k := by
    filter_upwards [eventually_ratio_contract hβ (η := η) (K := K) h2η, hr2, hsmall] with k hc hr hs
    obtain ⟨ht0, ht⟩ := hc
    have hb := hβ.pos k
    have hb1 := hβ.pos (k + 1)
    set q := 1 - 2 * η * β k + K ^ 2 * β k ^ 2
    set ρ := β k / β (k + 1)
    have hρ0 : 0 ≤ ρ := by positivity
    have hyk : 0 ≤ y k := div_nonneg (hv0 k) (by positivity)
    -- `y_{k+1} ≤ ρ^p (q^p y_k + D β_k)`
    have e1 : y (k + 1) ≤ ρ ^ p * (q ^ p * y k + D * β k) := by
      have hpk : v k = y k * β k ^ p := by
        simp only [hy]; field_simp
      have : y (k + 1) = v (k + 1) / β (k + 1) ^ p := rfl
      rw [this, div_le_iff₀ (by positivity)]
      calc v (k + 1) ≤ q ^ p * v k + D * β k ^ (p + 1) := hrec k
        _ = ρ ^ p * (q ^ p * y k + D * β k) * β (k + 1) ^ p := by
          rw [hpk]
          simp only [ρ, div_pow]
          field_simp
          ring
    have e2 : ρ ^ p * q ^ p = (ρ * q) ^ p := (mul_pow _ _ _).symm
    have e3 : (ρ * q) ^ p ≤ 1 - a * β k := by
      have h0 : 0 ≤ 1 - a * β k := by linarith
      have h1 : ρ * q ≤ 1 - a * β k := ht
      calc (ρ * q) ^ p ≤ (1 - a * β k) ^ p := pow_le_pow_left₀ ht0 h1 p
        _ ≤ 1 - a * β k := pow_le_of_le_one h0 (by linarith [mul_pos ha0 hb]) (by omega)
    have e4 : ρ ^ p ≤ 2 ^ p := pow_le_pow_left₀ hρ0 hr p
    calc y (k + 1) ≤ ρ ^ p * (q ^ p * y k + D * β k) := e1
      _ = (ρ * q) ^ p * y k + ρ ^ p * (D * β k) := by rw [← e2]; ring
      _ ≤ (1 - a * β k) * y k + 2 ^ p * (D * β k) := by
          gcongr
      _ = _ := by ring
  obtain ⟨W, hW⟩ := bdd_of_le_contraction ha0 (fun k => (hβ.pos k).le) hstep hsmall
  refine ⟨W, fun k => ?_⟩
  have hb := hβ.pos k
  have := hW k
  simp only [hy] at this
  rwa [div_le_iff₀ (by positivity)] at this

end MomentBounds

section Dissipative

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {β : ℕ → ℝ} {βbar : ℝ}

/-- `E⟨w, M⟩ = 0` for `ℱ`-measurable `w` and a martingale difference `M`. -/
lemma integral_inner_mart_eq_zero (ℱ : MeasureTheory.Filtration ℕ m0) (k : ℕ) {w c : Ω → E d}
    (hw : StronglyMeasurable[ℱ k] w) (hwL : MemLp w 2 μ) (hcL : MemLp c 2 μ)
    (hc : ∀ j, μ[fun ω => c ω j | ℱ k] =ᵐ[μ] 0) : ∫ ω, ⟪w ω, c ω⟫_ℝ ∂μ = 0 := by
  have h0 := crossMoment_eq_zero (μ := μ) (ℱ.le k) hw hwL hcL hc
  have e : ∀ ω, ⟪w ω, c ω⟫_ℝ = ∑ j, w ω j * c ω j := fun ω => by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    exact sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [e]
  rw [integral_finset_sum univ (f := fun j ω => w ω j * c ω j) fun j _ =>
    (memLp_apply hwL j).integrable_mul (memLp_apply hcL j)]
  refine sum_eq_zero fun j _ => ?_
  have := congrFun h0 (j, j)
  rw [crossMoment_apply hwL hcL] at this
  simpa using this

lemma integrable_of_norm_bdd (ℱ : MeasureTheory.Filtration ℕ m0) (k : ℕ) {g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ k] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) : Integrable g μ :=
  (memLp_top_of_bound (hg.mono (ℱ.le k)).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top

set_option maxHeartbeats 2000000 in
/-- **Moment bounds for a dissipative iteration.** Let `θ_{k+1} = θ_k + β_k (f(θ_k) + M_{k+1})`
with `⟨θ - θ̂, f(θ)⟩ ≤ -η ‖θ - θ̂‖²`, `‖f(θ)‖ ≤ K ‖θ - θ̂‖`, `2η > β̄`, a bounded martingale
difference `M` and a bounded start. Then each `θ_k` is bounded, and
`E‖θ_k - θ̂‖² ≤ W β_k` and `E‖θ_k - θ̂‖⁴ ≤ W₄ β_k²`. -/
theorem moment_bounds_of_dissipative (hβ : StepSizeRate β βbar)
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ M : ℕ → Ω → E d} {θh : E d} {f : E d → E d}
    {η K CM : ℝ} (h2η : βbar < 2 * η) (hK0 : 0 ≤ K)
    (hdis : ∀ x, ⟪x - θh, f x⟫_ℝ ≤ -η * ‖x - θh‖ ^ 2) (hlin : ∀ x, ‖f x‖ ≤ K * ‖x - θh‖)
    (hfc : Continuous f)
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • (f (θ k ω) + M (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hθ0 : ∃ C, ∀ ω, ‖θ 0 ω - θh‖ ≤ C)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hMb : ∀ k ω, ‖M (k + 1) ω‖ ≤ CM)
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0) :
    (∀ k, ∃ C, ∀ ω, ‖θ k ω - θh‖ ≤ C) ∧ (∃ W, ∀ k, ∫ ω, ‖θ k ω - θh‖ ^ 2 ∂μ ≤ W * β k) ∧
      ∃ W₄, ∀ k, ∫ ω, ‖θ k ω - θh‖ ^ 4 ∂μ ≤ W₄ * β k ^ 2 := by
  set e : ℕ → Ω → E d := fun k ω => θ k ω - θh with he
  set u : ℕ → Ω → E d := fun k ω => e k ω + β k • f (θ k ω) with hu
  set q : ℕ → ℝ := fun k => 1 - 2 * η * β k + K ^ 2 * β k ^ 2 with hq
  have hstep : ∀ k ω, e (k + 1) ω = u k ω + β k • M (k + 1) ω := fun k ω => by
    simp only [he, hu, hθ k ω, smul_add]; abel
  -- `‖u‖² ≤ q ‖e‖²`
  have hu2 : ∀ k ω, ‖u k ω‖ ^ 2 ≤ q k * ‖e k ω‖ ^ 2 := fun k ω => by
    have hb := hβ.pos k
    have h1 := hdis (θ k ω)
    have h2 := hlin (θ k ω)
    simp only [hu, hq, he]
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    have h3 : ‖f (θ k ω)‖ ^ 2 ≤ K ^ 2 * ‖θ k ω - θh‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2
      rw [mul_pow] at this; exact this
    nlinarith [mul_le_mul_of_nonneg_left h1 hb.le, mul_le_mul_of_nonneg_left h3 (sq_nonneg (β k))]
  -- each iterate is bounded
  have hbd : ∀ k, ∃ C, ∀ ω, ‖e k ω‖ ≤ C := by
    intro k
    induction k with
    | zero => exact hθ0
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C + β k * (K * C) + β k * CM, fun ω => ?_⟩
      have hb := hβ.pos k
      rw [hstep k ω]
      have h1 : ‖u k ω‖ ≤ C + β k * (K * C) := by
        simp only [hu]
        refine (norm_add_le _ _).trans (add_le_add (hC ω) ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
        exact mul_le_mul_of_nonneg_left ((hlin _).trans (mul_le_mul_of_nonneg_left (hC ω) hK0)) hb.le
      refine (norm_add_le _ _).trans (add_le_add h1 ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
      exact mul_le_mul_of_nonneg_left (hMb k ω) hb.le
  refine ⟨hbd, ?_⟩
  -- measurability and integrability
  have hem : ∀ k, StronglyMeasurable[ℱ k] (e k) := fun k => (hθm k).sub stronglyMeasurable_const
  have hum : ∀ k, StronglyMeasurable[ℱ k] (u k) := fun k =>
    (hem k).add ((hfc.comp_stronglyMeasurable (hθm k)).const_smul (β k))
  have hubd : ∀ k, ∃ C, ∀ ω, ‖u k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    refine ⟨C + β k * (K * C), fun ω => ?_⟩
    simp only [hu]
    refine (norm_add_le _ _).trans (add_le_add (hC ω) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hβ.pos k)]
    exact mul_le_mul_of_nonneg_left ((hlin _).trans (mul_le_mul_of_nonneg_left (hC ω) hK0))
      (hβ.pos k).le
  have hML : ∀ k, MemLp (M (k + 1)) 2 μ := fun k =>
    MemLp.of_bound ((hM k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM
      (Eventually.of_forall (hMb k))
  have huL : ∀ k, MemLp (u k) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hubd k
    exact MemLp.of_bound ((hum k).mono (ℱ.le k)).aestronglyMeasurable C (Eventually.of_forall hC)
  have hint : ∀ k (g : Ω → ℝ), StronglyMeasurable[ℱ (k + 1)] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      Integrable g μ := fun k g hg ⟨C, hC⟩ => integrable_of_norm_bdd ℱ (k + 1) hg hC
  have hmono : ∀ k, ℱ k ≤ ℱ (k + 1) := fun k => ℱ.mono (Nat.le_succ k)
  have smu : ∀ k, StronglyMeasurable[ℱ (k + 1)] (u k) := fun k => (hum k).mono (hmono k)
  have sme : ∀ k, StronglyMeasurable[ℱ k] fun ω => ‖e k ω‖ := fun k => (hem k).norm
  have sMn : ∀ k, StronglyMeasurable[ℱ (k + 1)] fun ω => ‖M (k + 1) ω‖ := fun k => (hM k).norm
  have sun : ∀ k, StronglyMeasurable[ℱ (k + 1)] fun ω => ‖u k ω‖ := fun k => (smu k).norm
  have sinner : ∀ k, StronglyMeasurable[ℱ (k + 1)] fun ω => ⟪u k ω, M (k + 1) ω⟫_ℝ := fun k =>
    (smu k).inner (hM k)
  -- the second moments
  set sq : ℕ → ℝ := fun k => ∫ ω, ‖e k ω‖ ^ 2 ∂μ with hsq
  have hsq0 : ∀ k, 0 ≤ sq k := fun k => integral_nonneg fun _ => by positivity
  have hexp2 : ∀ k ω, ‖e (k + 1) ω‖ ^ 2 = ‖u k ω‖ ^ 2 + 2 * β k * ⟪u k ω, M (k + 1) ω⟫_ℝ
      + β k ^ 2 * ‖M (k + 1) ω‖ ^ 2 := fun k ω => by
    rw [hstep k ω, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  have hzero : ∀ k, ∫ ω, ⟪u k ω, M (k + 1) ω⟫_ℝ ∂μ = 0 := fun k =>
    integral_inner_mart_eq_zero ℱ k (hum k) (huL k) (hML k) (hmart k)
  have hiu2 : ∀ k, Integrable (fun ω => ‖u k ω‖ ^ 2) μ := fun k => memLp_sq_integrable (huL k)
  have hiM2 : ∀ k, Integrable (fun ω => ‖M (k + 1) ω‖ ^ 2) μ := fun k => memLp_sq_integrable (hML k)
  have hiX : ∀ k, Integrable (fun ω => ⟪u k ω, M (k + 1) ω⟫_ℝ) μ := fun k => by
    obtain ⟨C, hC⟩ := hubd k
    exact hint k _ (sinner k) ⟨C * CM, fun ω => by
      rw [← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hC ω) (hMb k ω) (norm_nonneg _)
        ((norm_nonneg _).trans (hC ω)))⟩
  have hM2 : ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM ^ 2 := fun k => by
    calc ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ ∫ _ω, CM ^ 2 ∂μ :=
          integral_mono (hiM2 k) (integrable_const _) fun ω =>
            pow_le_pow_left₀ (norm_nonneg _) (hMb k ω) 2
      _ = CM ^ 2 := by simp
  have heL : ∀ k, MemLp (e k) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    exact MemLp.of_bound ((hem k).mono (ℱ.le k)).aestronglyMeasurable C (Eventually.of_forall hC)
  have hrec2 : ∀ k, sq (k + 1) ≤ (1 - 2 * η * β k + K ^ 2 * β k ^ 2) ^ 1 * sq k
      + CM ^ 2 * β k ^ (1 + 1) := fun k => by
    have hb := hβ.pos k
    simp only [hsq, hexp2]
    have iA : Integrable (fun ω => ‖u k ω‖ ^ 2 + 2 * β k * ⟪u k ω, M (k + 1) ω⟫_ℝ) μ :=
      (hiu2 k).add ((hiX k).const_mul _)
    rw [integral_add iA ((hiM2 k).const_mul _),
      integral_add (hiu2 k) ((hiX k).const_mul _), integral_const_mul, integral_const_mul, hzero,
      mul_zero, add_zero, pow_one]
    have h1 : ∫ ω, ‖u k ω‖ ^ 2 ∂μ ≤ q k * ∫ ω, ‖e k ω‖ ^ 2 ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono (hiu2 k) ((memLp_sq_integrable (heL k)).const_mul _) (hu2 k)
    have h2 := mul_le_mul_of_nonneg_left (hM2 k) (sq_nonneg (β k))
    simp only [hq] at h1
    linarith [h1, h2, show CM ^ 2 * β k ^ (1 + 1) = β k ^ 2 * CM ^ 2 by ring]
  obtain ⟨W, hW⟩ := bdd_of_moment_recursion hβ h2η (sq_nonneg CM) le_rfl hsq0 hrec2
  simp only [pow_one] at hW
  refine ⟨⟨W, hW⟩, ?_⟩
  -- the fourth moments
  have hW0 : 0 ≤ W := by
    have := (hsq0 0).trans (hW 0)
    exact nonneg_of_mul_nonneg_left this (hβ.pos 0) |> fun h => by nlinarith [hβ.pos 0]
  obtain ⟨B, hB⟩ := hβ.tendsto_zero.bddAbove_range
  have hβB : ∀ k, β k ≤ B := fun k => hB ⟨k, rfl⟩
  have hB0 : 0 ≤ B := (hβ.pos 0).le.trans (hβB 0)
  have hη0 : 0 < η := by linarith [hβ.βbar_nonneg]
  set v : ℕ → ℝ := fun k => ∫ ω, ‖e k ω‖ ^ 4 ∂μ with hv
  have hv0 : ∀ k, 0 ≤ v k := fun k => integral_nonneg fun _ => by positivity
  have hie4 : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    refine integrable_of_norm_bdd ℱ k ((sme k).pow 4) (C := C ^ 4) fun ω => ?_
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) 4
  have hiu4 : ∀ k, Integrable (fun ω => (‖u k ω‖ ^ 2) ^ 2) μ := fun k => by
    obtain ⟨C, hC⟩ := hubd k
    refine hint k _ (((sun k).pow 2).pow 2) ⟨(C ^ 2) ^ 2, fun ω => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2) 2
  have hiaX : ∀ k, Integrable (fun ω => ‖u k ω‖ ^ 2 * ⟪u k ω, M (k + 1) ω⟫_ℝ) μ := fun k => by
    obtain ⟨C', hC'⟩ := hubd k
    set C := max C' 0
    have hC0 : 0 ≤ C := le_max_right _ _
    have hC : ∀ ω, ‖u k ω‖ ≤ C := fun ω => (hC' ω).trans (le_max_left _ _)
    refine hint k _ (((sun k).pow 2).mul (sinner k)) ⟨C ^ 2 * (C * CM), fun ω => ?_⟩
    rw [abs_mul, abs_of_nonneg (by positivity), ← Real.norm_eq_abs]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2) ((norm_inner_le_norm _ _).trans
      (mul_le_mul (hC ω) (hMb k ω) (norm_nonneg _) hC0)) (norm_nonneg _) (by positivity)
  -- `E[‖u‖² ⟨u, M⟩] = 0`
  have hzero4 : ∀ k, ∫ ω, ‖u k ω‖ ^ 2 * ⟪u k ω, M (k + 1) ω⟫_ℝ ∂μ = 0 := fun k => by
    have hwm : StronglyMeasurable[ℱ k] fun ω => ‖u k ω‖ ^ 2 • u k ω :=
      ((hum k).norm.pow 2).smul (hum k)
    have hwL : MemLp (fun ω => ‖u k ω‖ ^ 2 • u k ω) 2 μ := by
      obtain ⟨C, hC⟩ := hubd k
      refine MemLp.of_bound (hwm.mono (ℱ.le k)).aestronglyMeasurable (C ^ 2 * C)
        (Eventually.of_forall fun ω => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2) (hC ω) (norm_nonneg _)
        (by have := (norm_nonneg _).trans (hC ω); positivity)
    have := integral_inner_mart_eq_zero ℱ k hwm hwL (hML k) (hmart k)
    simpa only [inner_smul_left, RCLike.conj_to_real] using this
  have hrec4 : ∀ k, v (k + 1) ≤ (1 - 2 * η * β k + K ^ 2 * β k ^ 2) ^ 2 * v k
      + (8 * CM ^ 2 * (1 + K ^ 2 * B ^ 2) * W + 3 * CM ^ 4 * B) * β k ^ (2 + 1) := fun k => by
    have hb := hβ.pos k
    -- the pointwise bound
    have hpt : ∀ ω, ‖e (k + 1) ω‖ ^ 4 ≤ (‖u k ω‖ ^ 2) ^ 2
        + 4 * β k * (‖u k ω‖ ^ 2 * ⟪u k ω, M (k + 1) ω⟫_ℝ)
        + 8 * β k ^ 2 * CM ^ 2 * ‖u k ω‖ ^ 2 + 3 * β k ^ 4 * CM ^ 4 := fun ω => by
      set a := ‖u k ω‖ ^ 2
      set X := ⟪u k ω, M (k + 1) ω⟫_ℝ
      set m := ‖M (k + 1) ω‖ ^ 2
      have h4 : ‖e (k + 1) ω‖ ^ 4 = (a + 2 * β k * X + β k ^ 2 * m) ^ 2 := by
        rw [show ‖e (k + 1) ω‖ ^ 4 = (‖e (k + 1) ω‖ ^ 2) ^ 2 by ring, hexp2]
      have ha : 0 ≤ a := by positivity
      have hm0 : 0 ≤ m := by positivity
      have hmC : m ≤ CM ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMb k ω) 2
      have hX2 : X ^ 2 ≤ a * m := by
        have := abs_real_inner_le_norm (u k ω) (M (k + 1) ω)
        have h0 : 0 ≤ ‖u k ω‖ * ‖M (k + 1) ω‖ := by positivity
        calc X ^ 2 = |X| ^ 2 := (sq_abs X).symm
          _ ≤ (‖u k ω‖ * ‖M (k + 1) ω‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = a * m := by simp only [a, m]; ring
      have hexp : (a + 2 * β k * X + β k ^ 2 * m) ^ 2 = a ^ 2 + 4 * β k * (a * X)
          + 4 * β k ^ 2 * X ^ 2 + 2 * β k ^ 2 * (a * m) + 4 * β k ^ 3 * (X * m)
          + β k ^ 4 * m ^ 2 := by ring
      have i1 : 4 * β k ^ 3 * (X * m) ≤ 2 * β k ^ 2 * X ^ 2 + 2 * β k ^ 4 * m ^ 2 := by
        nlinarith [sq_nonneg (X - β k * m), sq_nonneg (β k)]
      have i2 : β k ^ 2 * X ^ 2 ≤ β k ^ 2 * (a * m) := mul_le_mul_of_nonneg_left hX2 (sq_nonneg _)
      have i3 : β k ^ 2 * (a * m) ≤ β k ^ 2 * (a * CM ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmC ha) (sq_nonneg _)
      have i4 : β k ^ 4 * m ^ 2 ≤ β k ^ 4 * (CM ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmC 2) (by positivity)
      rw [h4, hexp]
      nlinarith [i1, i2, i3, i4]
    have iB : Integrable (fun ω => (‖u k ω‖ ^ 2) ^ 2
        + 4 * β k * (‖u k ω‖ ^ 2 * ⟪u k ω, M (k + 1) ω⟫_ℝ)) μ :=
      (hiu4 k).add ((hiaX k).const_mul _)
    have iC : Integrable (fun ω => (‖u k ω‖ ^ 2) ^ 2
        + 4 * β k * (‖u k ω‖ ^ 2 * ⟪u k ω, M (k + 1) ω⟫_ℝ)
        + 8 * β k ^ 2 * CM ^ 2 * ‖u k ω‖ ^ 2) μ := iB.add ((hiu2 k).const_mul _)
    have hint4 : Integrable (fun ω => (‖u k ω‖ ^ 2) ^ 2
        + 4 * β k * (‖u k ω‖ ^ 2 * ⟪u k ω, M (k + 1) ω⟫_ℝ)
        + 8 * β k ^ 2 * CM ^ 2 * ‖u k ω‖ ^ 2 + 3 * β k ^ 4 * CM ^ 4) μ :=
      iC.add (integrable_const _)
    have step1 := integral_mono (hie4 (k + 1)) hint4 hpt
    rw [integral_add iC (integrable_const _), integral_add iB ((hiu2 k).const_mul _),
      integral_add (hiu4 k) ((hiaX k).const_mul _),
      integral_const_mul, integral_const_mul, hzero4, mul_zero, add_zero] at step1
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at step1
    -- the pieces
    have h1 : ∫ ω, (‖u k ω‖ ^ 2) ^ 2 ∂μ ≤ q k ^ 2 * v k := by
      rw [hv, ← integral_const_mul]
      refine integral_mono (hiu4 k) ((hie4 k).const_mul _) fun ω => ?_
      have := pow_le_pow_left₀ (by positivity) (hu2 k ω) 2
      calc (‖u k ω‖ ^ 2) ^ 2 ≤ (q k * ‖e k ω‖ ^ 2) ^ 2 := this
        _ = q k ^ 2 * ‖e k ω‖ ^ 4 := by ring
    have h2 : ∫ ω, ‖u k ω‖ ^ 2 ∂μ ≤ (1 + K ^ 2 * B ^ 2) * (W * β k) := by
      have hq1 : q k ≤ 1 + K ^ 2 * B ^ 2 := by
        simp only [hq]
        nlinarith [hβB k, hb, sq_nonneg K, mul_le_mul (hβB k) (hβB k) hb.le hB0]
      calc ∫ ω, ‖u k ω‖ ^ 2 ∂μ ≤ ∫ ω, q k * ‖e k ω‖ ^ 2 ∂μ :=
            integral_mono (hiu2 k) ((memLp_sq_integrable (heL k)).const_mul _) (hu2 k)
        _ = q k * sq k := by rw [integral_const_mul]
        _ ≤ (1 + K ^ 2 * B ^ 2) * sq k := mul_le_mul_of_nonneg_right hq1 (hsq0 k)
        _ ≤ (1 + K ^ 2 * B ^ 2) * (W * β k) := mul_le_mul_of_nonneg_left (hW k) (by positivity)
    have hb4 : β k ^ 4 ≤ B * β k ^ 3 := by
      have : β k ^ 4 = β k * β k ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right (hβB k) (by positivity)
    have e3 : (8 * CM ^ 2 * (1 + K ^ 2 * B ^ 2) * W + 3 * CM ^ 4 * B) * β k ^ (2 + 1) =
        8 * β k ^ 2 * CM ^ 2 * ((1 + K ^ 2 * B ^ 2) * (W * β k)) + 3 * CM ^ 4 * (B * β k ^ 3) := by
      ring
    have hq2 : q k ^ 2 = (1 - 2 * η * β k + K ^ 2 * β k ^ 2) ^ 2 := rfl
    rw [e3, ← hq2]
    have t2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * β k ^ 2 * CM ^ 2)
    have t3 := mul_le_mul_of_nonneg_left hb4 (by positivity : (0 : ℝ) ≤ 3 * CM ^ 4)
    show ∫ ω, ‖e (k + 1) ω‖ ^ 4 ∂μ ≤ _
    nlinarith [step1, h1, t2, t3]
  obtain ⟨W₄, hW₄⟩ := bdd_of_moment_recursion hβ h2η (by positivity) (by norm_num) hv0 hrec4
  exact ⟨W₄, hW₄⟩

/-- **Assumption 2.2, single time scale.** A dissipative nonlinear iteration
`θ_{k+1} = θ_k + β_k (f(θ_k) + M_{k+1})` with bounded martingale noise, whose drift has the Taylor
expansion `f(θ) = -A(θ - θ̂) + O(‖θ - θ̂‖²)` at its root, has the asymptotic covariance of its
linearization: `β_k⁻¹ E[(θ_k - θ̂)(θ_k - θ̂)ᵀ] → Σ` with
`(A - β̄/2) Σ + Σ (A - β̄/2)ᵀ = lim E[M Mᵀ]`. The fourth-moment bound comes from
`moment_bounds_of_dissipative`. -/
theorem tendsto_secondMoment_of_dissipative (hβ : StepSizeRate β βbar)
    (A : Matrix (Fin d) (Fin d) ℝ) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hA : ∀ x, η₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ M : ℕ → Ω → E d} {θh : E d} {f : E d → E d}
    {η K L CM : ℝ} (h2η : βbar < 2 * η) (hK0 : 0 ≤ K) (hL : 0 ≤ L)
    (hdis : ∀ x, ⟪x - θh, f x⟫_ℝ ≤ -η * ‖x - θh‖ ^ 2) (hlin : ∀ x, ‖f x‖ ≤ K * ‖x - θh‖)
    (hf : ∀ x, ‖f x + matCLM A (x - θh)‖ ≤ L * ‖x - θh‖ ^ 2) (hfc : Continuous f) {Γ : Mat d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • (f (θ k ω) + M (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hθ0 : ∃ C, ∀ ω, ‖θ 0 ω - θh‖ ≤ C)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hMb : ∀ k ω, ‖M (k + 1) ω‖ ≤ CM)
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hΓ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (fun ω => θ k ω - θh)) atTop (𝓝 Sig) := by
  obtain ⟨hbd, -, h4⟩ := moment_bounds_of_dissipative hβ ℱ h2η hK0 hdis hlin hfc hθ hθm hθ0 hM hMb
    hmart
  have hθL : ∀ k, MemLp (θ k) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    refine MemLp.of_bound ((hθm k).mono (ℱ.le k)).aestronglyMeasurable (C + ‖θh‖)
      (Eventually.of_forall fun ω => ?_)
    calc ‖θ k ω‖ = ‖(θ k ω - θh) + θh‖ := by rw [sub_add_cancel]
      _ ≤ C + ‖θh‖ := (norm_add_le _ _).trans (add_le_add_right (hC ω) _)
  have h4i : ∀ k, Integrable (fun ω => ‖θ k ω - θh‖ ^ 4) μ := fun k => by
    obtain ⟨C, hC⟩ := hbd k
    refine integrable_of_norm_bdd ℱ k (((hθm k).sub stronglyMeasurable_const).norm.pow 4)
      (C := C ^ 4) fun ω => ?_
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) 4
  have hML : ∀ k, MemLp (M (k + 1)) 2 μ := fun k =>
    MemLp.of_bound ((hM k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM
      (Eventually.of_forall (hMb k))
  have hMB : ∃ C, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ C := ⟨CM ^ 2, fun k => by
    calc ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ ∫ _ω, CM ^ 2 ∂μ :=
          integral_mono (memLp_sq_integrable (hML k)) (integrable_const _) fun ω =>
            pow_le_pow_left₀ (norm_nonneg _) (hMb k ω) 2
      _ = CM ^ 2 := by simp⟩
  exact tendsto_secondMoment_of_nonlinear hβ A hη₀ hA ℱ hL hf hfc hθ hθm hθL h4i h4 hML hMB
    hmart hΓ

end Dissipative

end StochasticApproximation
