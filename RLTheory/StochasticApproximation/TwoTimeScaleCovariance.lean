/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.MultiplicativeNoiseCovariance
import RLTheory.StochasticApproximation.TwoTimeScaleRecursion

/-!
# Asymptotic covariance of linear two-time-scale stochastic approximation with Markov noise

The probabilistic part of `docs/two-time-scale-covariance.md`.

* `crossMoment_matCLM_left`, `crossMoment_matCLM_right`, `crossMoment_swap`: moments of
  linear images and transposes.
* `crossMoment_step`: one step of a cross-moment recursion,
  `E[(a + b + c)(a' + b' + c')ᵀ] = E[a a'ᵀ] + E[b b'ᵀ] + ρ`, for `ℱ`-measurable `a, a'` and
  martingale differences `b, b'`.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StochasticApproximation

variable {d₁ d₂ d₃ d₄ : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The root mean square `√E‖f‖²`. -/
noncomputable def rms (μ : Measure Ω) {d : ℕ} (f : Ω → E d) : ℝ := √(∫ ω, ‖f ω‖ ^ 2 ∂μ)

lemma rms_nonneg {d : ℕ} (f : Ω → E d) : 0 ≤ rms μ f := Real.sqrt_nonneg _

lemma norm_crossMoment_le_rms {a : Ω → E d₁} {c : Ω → E d₂} (ha : MemLp a 2 μ)
    (hc : MemLp c 2 μ) : ‖crossMoment μ a c‖ ≤ rms μ a * rms μ c :=
  norm_crossMoment_le ha hc

lemma rms_smul {d : ℕ} (r : ℝ) (f : Ω → E d) : rms μ (fun ω => r • f ω) = |r| * rms μ f := by
  unfold rms
  have h : ∀ ω, ‖r • f ω‖ ^ 2 = r ^ 2 * ‖f ω‖ ^ 2 := fun ω => by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [h]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma rms_le_of_le {d d' : ℕ} {f : Ω → E d} {g : Ω → E d'} {c : ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (hc : 0 ≤ c) (h : ∀ ω, ‖f ω‖ ≤ c * ‖g ω‖) : rms μ f ≤ c * rms μ g := by
  unfold rms
  have : ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ c ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (memLp_sq_integrable hf) ((memLp_sq_integrable hg).const_mul _)
      fun ω => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h ω) 2
  calc √(∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ √(c ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ) := Real.sqrt_le_sqrt this
    _ = c * √(∫ ω, ‖g ω‖ ^ 2 ∂μ) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

lemma rms_matCLM_le {f : Ω → E d₂} (F : Matrix (Fin d₁) (Fin d₂) ℝ) (hf : MemLp f 2 μ) :
    rms μ (fun ω => matCLM F (f ω)) ≤ ‖matCLM F‖ * rms μ f :=
  rms_le_of_le ((matCLM F).comp_memLp' hf) hf (norm_nonneg _) fun _ => (matCLM F).le_opNorm _

/-- `√E‖f + g‖² ≤ √2 (√E‖f‖² + √E‖g‖²)`. -/
lemma rms_add_le {d : ℕ} {f g : Ω → E d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    rms μ (fun ω => f ω + g ω) ≤ √2 * (rms μ f + rms μ g) := by
  unfold rms
  have hpt : ∀ ω, ‖f ω + g ω‖ ^ 2 ≤ 2 * ‖f ω‖ ^ 2 + 2 * ‖g ω‖ ^ 2 := fun ω =>
    norm_sq_le_of_le (norm_nonneg _) (norm_add_le _ _)
  have i1 := (memLp_sq_integrable hf).const_mul 2
  have i2 := (memLp_sq_integrable hg).const_mul 2
  have i12 : Integrable (fun ω => 2 * ‖f ω‖ ^ 2 + 2 * ‖g ω‖ ^ 2) μ := i1.add i2
  have hint := integral_mono (memLp_sq_integrable (hf.add hg)) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hint
  refine (Real.sqrt_le_sqrt hint).trans ?_
  have hA := integral_norm_sq_nonneg (μ := μ) f
  have hB := integral_norm_sq_nonneg (μ := μ) g
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfA : √(∫ ω, ‖f ω‖ ^ 2 ∂μ) ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := Real.sq_sqrt hA
  have hgB : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ^ 2 = ∫ ω, ‖g ω‖ ^ 2 ∂μ := Real.sq_sqrt hB
  have e : (√2 * (√(∫ ω, ‖f ω‖ ^ 2 ∂μ) + √(∫ ω, ‖g ω‖ ^ 2 ∂μ))) ^ 2 =
      2 * ∫ ω, ‖f ω‖ ^ 2 ∂μ + 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ
        + 2 * (2 * √(∫ ω, ‖f ω‖ ^ 2 ∂μ) * √(∫ ω, ‖g ω‖ ^ 2 ∂μ)) := by
    rw [mul_pow, h2, add_sq, hfA, hgB]; ring
  rw [e]
  have : 0 ≤ 2 * (2 * √(∫ ω, ‖f ω‖ ^ 2 ∂μ) * √(∫ ω, ‖g ω‖ ^ 2 ∂μ)) := by positivity
  linarith

lemma rms_sub_le {d : ℕ} {f g : Ω → E d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    rms μ (fun ω => f ω - g ω) ≤ √2 * (rms μ f + rms μ g) := by
  have h := rms_add_le (μ := μ) hf (hg.const_smul (-1 : ℝ))
  have e1 : (fun ω => f ω + ((-1 : ℝ) • g) ω) = fun ω => f ω - g ω := by
    funext ω; simp [sub_eq_add_neg]
  have e2 : rms μ ((-1 : ℝ) • g) = rms μ g := by
    have := rms_smul (μ := μ) (-1 : ℝ) g
    simpa using this
  rw [e1, e2] at h
  exact h

lemma rms_sq_le {d : ℕ} {f : Ω → E d} (hf : MemLp f 2 μ) :
    rms μ f ^ 2 ≤ d * ‖secondMoment μ f‖ := by
  unfold rms
  rw [Real.sq_sqrt (integral_norm_sq_nonneg f)]
  exact integral_norm_sq_le hf

/-! ### Moments of linear images -/

lemma crossMoment_matCLM_left (F : Matrix (Fin d₃) (Fin d₁) ℝ) {u : Ω → E d₁} {v : Ω → E d₂}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    crossMoment μ (fun ω => matCLM F (u ω)) v = lmul F (crossMoment μ u v) := by
  funext ij
  have hFu : MemLp (fun ω => matCLM F (u ω)) 2 μ := (matCLM F).comp_memLp' hu
  rw [crossMoment_apply hFu hv, lmul_apply]
  simp only [matCLM_apply, sum_mul]
  rw [integral_finset_sum _ fun k _ => ((memLp_apply hu k).integrable_mul
    (memLp_apply hv ij.2)).const_mul (F ij.1 k) |>.congr
      (Eventually.of_forall fun ω => by simp [mul_assoc])]
  refine sum_congr rfl fun k _ => ?_
  rw [crossMoment_apply hu hv]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp [mul_assoc])

lemma crossMoment_matCLM_right (H : Matrix (Fin d₃) (Fin d₂) ℝ) {u : Ω → E d₁} {v : Ω → E d₂}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    crossMoment μ u (fun ω => matCLM H (v ω)) = rmul H (crossMoment μ u v) := by
  funext ij
  have hHv : MemLp (fun ω => matCLM H (v ω)) 2 μ := (matCLM H).comp_memLp' hv
  rw [crossMoment_apply hu hHv, rmul_apply]
  simp only [matCLM_apply, mul_sum]
  rw [integral_finset_sum _ fun k _ => ((memLp_apply hu ij.1).integrable_mul
    (memLp_apply hv k)).mul_const (H ij.2 k) |>.congr
      (Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring)]
  refine sum_congr rfl fun k _ => ?_
  rw [crossMoment_apply hu hv]
  rw [← integral_mul_const]
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)

lemma crossMoment_swap {u : Ω → E d₁} {v : Ω → E d₂} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    crossMoment μ v u = transCLM (crossMoment μ u v) := by
  funext ij
  rw [transCLM_apply, crossMoment_apply hv hu, crossMoment_apply hu hv]
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)

/-- `E[(u - p)(v - q)ᵀ] = E[u vᵀ] - E[u qᵀ] - E[p vᵀ] + E[p qᵀ]`. -/
lemma crossMoment_sub_sub {u p : Ω → E d₁} {v q : Ω → E d₂} (hu : MemLp u 2 μ)
    (hp : MemLp p 2 μ) (hv : MemLp v 2 μ) (hq : MemLp q 2 μ) :
    crossMoment μ (fun ω => u ω - p ω) (fun ω => v ω - q ω) =
      crossMoment μ u v - crossMoment μ u q - crossMoment μ p v + crossMoment μ p q := by
  simp only [crossMoment]
  have e : ∀ ω, outer (u ω - p ω) (v ω - q ω) =
      outer (u ω) (v ω) - outer (u ω) (q ω) - outer (p ω) (v ω) + outer (p ω) (q ω) := by
    intro ω; funext ij; simp [outer]; ring
  simp_rw [e]
  have i1 := integrable_outer hu hv
  have i2 := integrable_outer hu hq
  have i3 := integrable_outer hp hv
  have i4 := integrable_outer hp hq
  have i12 : Integrable (fun ω => outer (u ω) (v ω) - outer (u ω) (q ω)) μ := i1.sub i2
  have i123 : Integrable (fun ω => outer (u ω) (v ω) - outer (u ω) (q ω) - outer (p ω) (v ω)) μ :=
    i12.sub i3
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]

/-- One step of a cross-moment recursion. -/
theorem crossMoment_step [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    {a b c : Ω → E d₁} {a' b' c' : Ω → E d₂}
    (ha : StronglyMeasurable[ℱ] a) (ha' : StronglyMeasurable[ℱ] a')
    (haL : MemLp a 2 μ) (hbL : MemLp b 2 μ) (hcL : MemLp c 2 μ)
    (haL' : MemLp a' 2 μ) (hbL' : MemLp b' 2 μ) (hcL' : MemLp c' 2 μ)
    (hb : ∀ j, μ[fun ω => b ω j | ℱ] =ᵐ[μ] 0) (hb' : ∀ j, μ[fun ω => b' ω j | ℱ] =ᵐ[μ] 0) :
    ‖crossMoment μ (fun ω => a ω + b ω + c ω) (fun ω => a' ω + b' ω + c' ω)
      - (crossMoment μ a a' + crossMoment μ b b')‖ ≤
      (rms μ a + rms μ b + rms μ c) * rms μ c' + rms μ c * (rms μ a' + rms μ b') := by
  have hab : MemLp (fun ω => a ω + b ω) 2 μ := haL.add hbL
  have hab' : MemLp (fun ω => a' ω + b' ω) 2 μ := haL'.add hbL'
  have habc' : MemLp (fun ω => a' ω + b' ω + c' ω) 2 μ := hab'.add hcL'
  have hexp : crossMoment μ (fun ω => a ω + b ω + c ω) (fun ω => a' ω + b' ω + c' ω) =
      crossMoment μ a a' + crossMoment μ a b' + crossMoment μ a c'
      + (crossMoment μ b a' + crossMoment μ b b' + crossMoment μ b c')
      + (crossMoment μ c a' + crossMoment μ c b' + crossMoment μ c c') := by
    rw [crossMoment_add_left hab hcL habc', crossMoment_add_left haL hbL habc',
      crossMoment_add_right haL hab' hcL', crossMoment_add_right haL haL' hbL',
      crossMoment_add_right hbL hab' hcL', crossMoment_add_right hbL haL' hbL',
      crossMoment_add_right hcL hab' hcL', crossMoment_add_right hcL haL' hbL']
  have h1 : crossMoment μ a b' = 0 := crossMoment_eq_zero hℱ ha haL hbL' hb'
  have h2 : crossMoment μ b a' = 0 := crossMoment_eq_zero' hℱ ha' haL' hbL hb
  rw [hexp, h1, h2]
  have e : crossMoment μ a a' + 0 + crossMoment μ a c' + (0 + crossMoment μ b b' + crossMoment μ b c')
      + (crossMoment μ c a' + crossMoment μ c b' + crossMoment μ c c')
      - (crossMoment μ a a' + crossMoment μ b b') =
      crossMoment μ a c' + crossMoment μ b c' + crossMoment μ c c'
        + (crossMoment μ c a' + crossMoment μ c b') := by abel
  rw [e]
  have n1 := norm_crossMoment_le_rms (μ := μ) haL hcL'
  have n2 := norm_crossMoment_le_rms (μ := μ) hbL hcL'
  have n3 := norm_crossMoment_le_rms (μ := μ) hcL hcL'
  have n4 := norm_crossMoment_le_rms (μ := μ) hcL haL'
  have n5 := norm_crossMoment_le_rms (μ := μ) hcL hbL'
  have t1 := norm_add_le (crossMoment μ a c' + crossMoment μ b c' + crossMoment μ c c')
    (crossMoment μ c a' + crossMoment μ c b')
  have t2 := norm_add_le (crossMoment μ a c' + crossMoment μ b c') (crossMoment μ c c')
  have t3 := norm_add_le (crossMoment μ a c') (crossMoment μ b c')
  have t4 := norm_add_le (crossMoment μ c a') (crossMoment μ c b')
  nlinarith

/-! ### The iteration and the change of variables -/

lemma matCLM_mul (A : Matrix (Fin d₁) (Fin d₂) ℝ) (B : Matrix (Fin d₂) (Fin d₃) ℝ) (x : E d₃) :
    matCLM (A * B) x = matCLM A (matCLM B x) := by
  ext i
  simp only [matCLM_apply, Matrix.mul_apply, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma matCLM_sub (A B : Matrix (Fin d₁) (Fin d₂) ℝ) (x : E d₂) :
    matCLM (A - B) x = matCLM A x - matCLM B x := by
  ext i
  simp only [matCLM_apply, Matrix.sub_apply, sub_mul, sum_sub_distrib, PiLp.sub_apply]

/-- The two-time-scale iteration with Markov noise in Poisson form. -/
def TTSRecursion (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (β γ : ℕ → ℝ)
    (x M h : ℕ → Ω → E d₁) (y M' g : ℕ → Ω → E d₂) : Prop :=
  (∀ k ω, x (k + 1) ω = x k ω - β k • (matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω))
    + β k • (M (k + 1) ω + h k ω - h (k + 1) ω)) ∧
  (∀ k ω, y (k + 1) ω = y k ω - γ k • (matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω))
    + γ k • (M' (k + 1) ω + g k ω - g (k + 1) ω))

/-- The shifted slow iterate `x + β h`. -/
noncomputable def ttsX (β : ℕ → ℝ) (x h : ℕ → Ω → E d₁) (k : ℕ) : Ω → E d₁ :=
  fun ω => x k ω + β k • h k ω

/-- The shifted fast iterate `ŷ + γ g + β D h`, with `ŷ = y + D x`. -/
noncomputable def ttsY (D : Matrix (Fin d₂) (Fin d₁) ℝ) (β γ : ℕ → ℝ) (x h : ℕ → Ω → E d₁)
    (y g : ℕ → Ω → E d₂) (k : ℕ) : Ω → E d₂ :=
  fun ω => y k ω + matCLM D (x k ω) + γ k • g k ω + β k • matCLM D (h k ω)

section Shift

variable {A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ} {A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ}
  {A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ} {A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ}
  {D : Matrix (Fin d₂) (Fin d₁) ℝ} {β γ : ℕ → ℝ} {x M h : ℕ → Ω → E d₁} {y M' g : ℕ → Ω → E d₂}

/-- Lemma 3.1 of the write-up, slow component. -/
lemma ttsX_succ (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g)
    (k : ℕ) (ω : Ω) :
    ttsX β x h (k + 1) ω =
      (ttsX β x h k ω - β k • (matCLM (A₁₁ - A₁₂ * D) (ttsX β x h k ω)
        + matCLM A₁₂ (ttsY D β γ x h y g k ω)))
      + β k • M (k + 1) ω
      + (β k • (β k • matCLM (A₁₁ - A₁₂ * D) (h k ω) + γ k • matCLM A₁₂ (g k ω)
          + β k • matCLM A₁₂ (matCLM D (h k ω))) + (β (k + 1) - β k) • h (k + 1) ω) := by
  simp only [ttsX, ttsY]
  rw [hrec.1 k ω]
  simp only [matCLM_sub, matCLM_mul, map_add, map_smul]
  module

/-- Lemma 3.1 of the write-up, fast component. -/
lemma ttsY_succ (hD : A₂₂ * D = A₂₁) (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g)
    (k : ℕ) (ω : Ω) :
    ttsY D β γ x h y g (k + 1) ω =
      (ttsY D β γ x h y g k ω - (γ k • matCLM A₂₂ (ttsY D β γ x h y g k ω)
        + β k • matCLM D (matCLM (A₁₁ - A₁₂ * D) (ttsX β x h k ω)
          + matCLM A₁₂ (ttsY D β γ x h y g k ω))))
      + (γ k • M' (k + 1) ω + β k • matCLM D (M (k + 1) ω))
      + (γ k • matCLM A₂₂ (γ k • g k ω + β k • matCLM D (h k ω))
        + β k • matCLM D (β k • matCLM (A₁₁ - A₁₂ * D) (h k ω) + γ k • matCLM A₁₂ (g k ω)
          + β k • matCLM A₁₂ (matCLM D (h k ω)))
        + (γ (k + 1) - γ k) • g (k + 1) ω + (β (k + 1) - β k) • matCLM D (h (k + 1) ω)) := by
  simp only [ttsX, ttsY]
  rw [hrec.1 k ω, hrec.2 k ω, ← hD]
  simp only [matCLM_sub, matCLM_mul, map_add, map_sub, map_smul]
  module

/-- The iterates are adapted and square integrable. -/
lemma tts_adapted (ℱ : MeasureTheory.Filtration ℕ m0)
    (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hg : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
    (hM' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M' (k + 1)))
    (hM'L : ∀ k, MemLp (M' (k + 1)) 2 μ) :
    ∀ k, (StronglyMeasurable[ℱ k] (x k) ∧ MemLp (x k) 2 μ) ∧
      (StronglyMeasurable[ℱ k] (y k) ∧ MemLp (y k) 2 μ) := by
  intro k
  induction k with
  | zero => exact ⟨⟨hx0, hx0L⟩, ⟨hy0, hy0L⟩⟩
  | succ k ih =>
    obtain ⟨⟨hxm, hxL⟩, ⟨hym, hyL⟩⟩ := ih
    have hmono := ℱ.mono (Nat.le_succ k)
    have hfx : x (k + 1) = fun ω => x k ω - β k • (matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω))
        + β k • (M (k + 1) ω + h k ω - h (k + 1) ω) := funext (hrec.1 k)
    have hfy : y (k + 1) = fun ω => y k ω - γ k • (matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω))
        + γ k • (M' (k + 1) ω + g k ω - g (k + 1) ω) := funext (hrec.2 k)
    have cx1 := ((matCLM A₁₁).continuous.comp_stronglyMeasurable hxm).mono hmono
    have cx2 := ((matCLM A₁₂).continuous.comp_stronglyMeasurable hym).mono hmono
    have cy1 := ((matCLM A₂₁).continuous.comp_stronglyMeasurable hxm).mono hmono
    have cy2 := ((matCLM A₂₂).continuous.comp_stronglyMeasurable hym).mono hmono
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hfx]
      exact ((hxm.mono hmono).sub ((cx1.add cx2).const_smul (β k))).add
        ((((hM k).add ((hh k).mono hmono)).sub (hh (k + 1))).const_smul (β k))
    · rw [hfx]
      exact (hxL.sub ((((matCLM A₁₁).comp_memLp' hxL).add ((matCLM A₁₂).comp_memLp' hyL)).const_smul
        (β k))).add ((((hML k).add (hhL k)).sub (hhL (k + 1))).const_smul (β k))
    · rw [hfy]
      exact ((hym.mono hmono).sub ((cy1.add cy2).const_smul (γ k))).add
        ((((hM' k).add ((hg k).mono hmono)).sub (hg (k + 1))).const_smul (γ k))
    · rw [hfy]
      exact (hyL.sub ((((matCLM A₂₁).comp_memLp' hxL).add ((matCLM A₂₂).comp_memLp' hyL)).const_smul
        (γ k))).add ((((hM'L k).add (hgL k)).sub (hgL (k + 1))).const_smul (γ k))

end Shift

/-! ### One step of the three moment recursions -/

/-- `crossMoment_step` with drifts: `a = u - p`, `a' = v - q`. -/
lemma crossMoment_drift_step [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    {u p b c : Ω → E d₁} {v q b' c' : Ω → E d₂}
    (hu : StronglyMeasurable[ℱ] u) (hp : StronglyMeasurable[ℱ] p)
    (hv : StronglyMeasurable[ℱ] v) (hq : StronglyMeasurable[ℱ] q)
    (huL : MemLp u 2 μ) (hpL : MemLp p 2 μ) (hbL : MemLp b 2 μ) (hcL : MemLp c 2 μ)
    (hvL : MemLp v 2 μ) (hqL : MemLp q 2 μ) (hbL' : MemLp b' 2 μ) (hcL' : MemLp c' 2 μ)
    (hb : ∀ j, μ[fun ω => b ω j | ℱ] =ᵐ[μ] 0) (hb' : ∀ j, μ[fun ω => b' ω j | ℱ] =ᵐ[μ] 0) :
    ‖crossMoment μ (fun ω => (u ω - p ω) + b ω + c ω) (fun ω => (v ω - q ω) + b' ω + c' ω)
      - (crossMoment μ u v - crossMoment μ u q - crossMoment μ p v + crossMoment μ p q
        + crossMoment μ b b')‖ ≤
      (rms μ (fun ω => u ω - p ω) + rms μ b + rms μ c) * rms μ c'
        + rms μ c * (rms μ (fun ω => v ω - q ω) + rms μ b') := by
  have h := crossMoment_step (μ := μ) hℱ (a := fun ω => u ω - p ω) (a' := fun ω => v ω - q ω)
    (hu.sub hp) (hv.sub hq) (huL.sub hpL) hbL hcL (hvL.sub hqL) hbL' hcL' hb hb'
  rwa [crossMoment_sub_sub huL hpL hvL hqL] at h

lemma cm_matCLM_add_right {u : Ω → E d₁} {v : Ω → E d₂}
    (F : Matrix (Fin d₃) (Fin d₁) ℝ) (H : Matrix (Fin d₃) (Fin d₂) ℝ) {z : Ω → E d₄}
    (hz : MemLp z 2 μ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    crossMoment μ z (fun ω => matCLM F (u ω) + matCLM H (v ω)) =
      rmul F (crossMoment μ z u) + rmul H (crossMoment μ z v) := by
  have hFu : MemLp (fun ω => matCLM F (u ω)) 2 μ := (matCLM F).comp_memLp' hu
  have hHv : MemLp (fun ω => matCLM H (v ω)) 2 μ := (matCLM H).comp_memLp' hv
  rw [crossMoment_add_right hz hFu hHv, crossMoment_matCLM_right F hz hu,
    crossMoment_matCLM_right H hz hv]

lemma cm_matCLM_add_left {u : Ω → E d₁} {v : Ω → E d₂}
    (F : Matrix (Fin d₃) (Fin d₁) ℝ) (H : Matrix (Fin d₃) (Fin d₂) ℝ) {z : Ω → E d₄}
    (hz : MemLp z 2 μ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    crossMoment μ (fun ω => matCLM F (u ω) + matCLM H (v ω)) z =
      lmul F (crossMoment μ u z) + lmul H (crossMoment μ v z) := by
  have hFu : MemLp (fun ω => matCLM F (u ω)) 2 μ := (matCLM F).comp_memLp' hu
  have hHv : MemLp (fun ω => matCLM H (v ω)) 2 μ := (matCLM H).comp_memLp' hv
  rw [crossMoment_add_left hFu hHv hz, crossMoment_matCLM_left F hu hz,
    crossMoment_matCLM_left H hv hz]

/-- A linear image of a martingale difference is a martingale difference. -/
lemma condExp_matCLM_eq_zero [IsFiniteMeasure μ] {ℱ : MeasurableSpace Ω} {M : Ω → E d₁}
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hML : MemLp M 2 μ)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0) (i : Fin d₂) :
    μ[fun ω => (matCLM D (M ω)) i | ℱ] =ᵐ[μ] 0 := by
  simp only [matCLM_apply]
  have hsum := condExp_finset_sum (s := univ) (μ := μ)
    (fun k _ => ((memLp_apply hML k).integrable one_le_two).const_mul (D i k)) ℱ
  have e : (fun ω => ∑ k, D i k * M ω k) = ∑ k, fun ω => D i k * M ω k := by
    funext ω; rw [Finset.sum_apply]
  rw [e]
  have hk : ∀ k, μ[fun ω => D i k * M ω k | ℱ] =ᵐ[μ] 0 := fun k => by
    have e2 : (fun ω => D i k * M ω k) = D i k • fun ω => M ω k := rfl
    rw [e2]
    filter_upwards [condExp_smul (μ := μ) (D i k) (fun ω => M ω k) ℱ, hmart k] with ω h1 h2
    rw [h1]; simp [h2]
  filter_upwards [hsum, ae_all_iff.mpr hk] with ω h1 h2
  rw [h1, Finset.sum_apply]
  simp [h2]

lemma condExp_smul_eq_zero {ℱ : MeasurableSpace Ω} {M : Ω → E d₁} (b : ℝ)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0) (j : Fin d₁) :
    μ[fun ω => (b • M ω) j | ℱ] =ᵐ[μ] 0 := by
  filter_upwards [condExp_smul (μ := μ) b (fun ω => M ω j) ℱ, hmart j] with ω h1 h2
  simp only [PiLp.smul_apply]
  rw [show (fun ω => b • M ω j) = b • fun ω => M ω j from rfl, h1]
  simp [h2]

lemma condExp_add_eq_zero [IsFiniteMeasure μ] {ℱ : MeasurableSpace Ω} {M M' : Ω → E d₁} (hML : MemLp M 2 μ)
    (hM'L : MemLp M' 2 μ) (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0)
    (hmart' : ∀ j, μ[fun ω => M' ω j | ℱ] =ᵐ[μ] 0) (j : Fin d₁) :
    μ[fun ω => (M ω + M' ω) j | ℱ] =ᵐ[μ] 0 := by
  have hadd := condExp_add ((memLp_apply hML j).integrable one_le_two)
    ((memLp_apply hM'L j).integrable one_le_two) ℱ (μ := μ)
  have e : (fun ω => (M ω + M' ω) j) = (fun ω => M ω j) + fun ω => M' ω j := by
    funext ω; simp
  rw [e]
  filter_upwards [hadd, hmart j, hmart' j] with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  simp

/-- One step of the slow second moment `X = E[x̃ x̃ᵀ]` (Lemma 3.2 of the write-up). -/
theorem tts_step_X [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    {xs M c : Ω → E d₁} {ys : Ω → E d₂} {b : ℝ}
    (hxs : StronglyMeasurable[ℱ] xs) (hys : StronglyMeasurable[ℱ] ys)
    (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ) (hML : MemLp M 2 μ) (hcL : MemLp c 2 μ)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0) (Γ : Mat d₁) :
    ‖secondMoment μ (fun ω => (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • M ω + c ω)
      - (secondMoment μ xs - b • (lyapOp Δ (secondMoment μ xs)
        + coupleCLM A₁₂ (crossMoment μ xs ys)) + b ^ 2 • Γ)‖ ≤
      b ^ 2 * rms μ (fun ω => matCLM Δ (xs ω) + matCLM A₁₂ (ys ω)) ^ 2
        + b ^ 2 * ‖secondMoment μ M - Γ‖
        + ((rms μ (fun ω => xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω)))
          + rms μ (fun ω => b • M ω) + rms μ c) * rms μ c
          + rms μ c * (rms μ (fun ω => xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω)))
            + rms μ (fun ω => b • M ω))) := by
  set w := fun ω => matCLM Δ (xs ω) + matCLM A₁₂ (ys ω) with hw
  have hwm : StronglyMeasurable[ℱ] w :=
    ((matCLM Δ).continuous.comp_stronglyMeasurable hxs).add
      ((matCLM A₁₂).continuous.comp_stronglyMeasurable hys)
  have hwL : MemLp w 2 μ := ((matCLM Δ).comp_memLp' hxsL).add ((matCLM A₁₂).comp_memLp' hysL)
  have hbwm : StronglyMeasurable[ℱ] (fun ω => b • w ω) := hwm.const_smul b
  have hbwL : MemLp (fun ω => b • w ω) 2 μ := hwL.const_smul b
  have hbML : MemLp (fun ω => b • M ω) 2 μ := hML.const_smul b
  have hbMm := condExp_smul_eq_zero (μ := μ) b hmart
  have hstep := crossMoment_drift_step (μ := μ) hℱ hxs hbwm hxs hbwm hxsL hbwL hbML hcL hxsL hbwL
    hbML hcL hbMm hbMm
  have i1 : crossMoment μ xs (fun ω => b • w ω) =
      b • (rmul Δ (secondMoment μ xs) + rmul A₁₂ (crossMoment μ xs ys)) := by
    rw [crossMoment_smul_right, hw, cm_matCLM_add_right Δ A₁₂ hxsL hxsL hysL]; rfl
  have i2 : crossMoment μ (fun ω => b • w ω) xs =
      b • (lmul Δ (secondMoment μ xs) + lmul A₁₂ (transCLM (crossMoment μ xs ys))) := by
    rw [crossMoment_smul_left, hw, cm_matCLM_add_left Δ A₁₂ hxsL hxsL hysL,
      crossMoment_swap hxsL hysL]; rfl
  have i3 : crossMoment μ (fun ω => b • w ω) (fun ω => b • w ω) = b ^ 2 • crossMoment μ w w := by
    rw [crossMoment_smul_left, crossMoment_smul_right, smul_smul, sq]
  have i4 : crossMoment μ (fun ω => b • M ω) (fun ω => b • M ω) = b ^ 2 • secondMoment μ M := by
    rw [crossMoment_smul_left, crossMoment_smul_right, smul_smul, sq]; rfl
  rw [i1, i2, i3, i4] at hstep
  have hsplit : secondMoment μ (fun ω => (xs ω - b • w ω) + b • M ω + c ω)
      - (secondMoment μ xs - b • (lyapOp Δ (secondMoment μ xs)
        + coupleCLM A₁₂ (crossMoment μ xs ys)) + b ^ 2 • Γ) =
      (crossMoment μ (fun ω => (xs ω - b • w ω) + b • M ω + c ω)
          (fun ω => (xs ω - b • w ω) + b • M ω + c ω)
        - (crossMoment μ xs xs
          - b • (rmul Δ (secondMoment μ xs) + rmul A₁₂ (crossMoment μ xs ys))
          - b • (lmul Δ (secondMoment μ xs) + lmul A₁₂ (transCLM (crossMoment μ xs ys)))
          + b ^ 2 • crossMoment μ w w + b ^ 2 • secondMoment μ M))
      + (b ^ 2 • crossMoment μ w w + b ^ 2 • (secondMoment μ M - Γ)) := by
    rw [lyapOp_eq, coupleCLM_apply, smul_sub]
    simp only [secondMoment, smul_add]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have n1 := norm_add_le (b ^ 2 • crossMoment μ w w) (b ^ 2 • (secondMoment μ M - Γ))
  have n2 : ‖b ^ 2 • crossMoment μ w w‖ ≤ b ^ 2 * rms μ w ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq (rms μ w)]
    exact mul_le_mul_of_nonneg_left (norm_crossMoment_le_rms hwL hwL) (sq_nonneg _)
  have n3 : ‖b ^ 2 • (secondMoment μ M - Γ)‖ = b ^ 2 * ‖secondMoment μ M - Γ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith



/-- One step of the cross moment `Z = E[x̃ ỹᵀ]` (Lemma 3.2 of the write-up). -/
theorem tts_step_Z [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {xs M c : Ω → E d₁} {ys M' c' : Ω → E d₂} {b g : ℝ} (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hxs : StronglyMeasurable[ℱ] xs) (hys : StronglyMeasurable[ℱ] ys)
    (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ) (hML : MemLp M 2 μ) (hM'L : MemLp M' 2 μ)
    (hcL : MemLp c 2 μ) (hcL' : MemLp c' 2 μ)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0) (hmart' : ∀ j, μ[fun ω => M' ω j | ℱ] =ᵐ[μ] 0)
    (Γ : Rect d₁ d₂) :
    let w := fun ω => matCLM Δ (xs ω) + matCLM A₁₂ (ys ω)
    let q := fun ω => g • matCLM A₂₂ (ys ω) + b • matCLM D (w ω)
    let bv := fun ω => g • M' ω + b • matCLM D (M ω)
    ‖crossMoment μ (fun ω => (xs ω - b • w ω) + b • M ω + c ω)
        (fun ω => (ys ω - q ω) + bv ω + c' ω)
      - (crossMoment μ xs ys - g • rmul A₂₂ (crossMoment μ xs ys)
        - b • lmul A₁₂ (secondMoment μ ys) + (b * g) • Γ)‖ ≤
      b * (rms μ xs * rms μ (fun ω => matCLM D (w ω))) + b * ‖lmul Δ (crossMoment μ xs ys)‖
        + b * (rms μ w * rms μ q) + b * g * ‖crossMoment μ M M' - Γ‖
        + b ^ 2 * (rms μ M * rms μ (fun ω => matCLM D (M ω)))
        + ((rms μ (fun ω => xs ω - b • w ω) + rms μ (fun ω => b • M ω) + rms μ c) * rms μ c'
          + rms μ c * (rms μ (fun ω => ys ω - q ω) + rms μ bv)) := by
  intro w q bv
  have hwm : StronglyMeasurable[ℱ] w :=
    ((matCLM Δ).continuous.comp_stronglyMeasurable hxs).add
      ((matCLM A₁₂).continuous.comp_stronglyMeasurable hys)
  have hwL : MemLp w 2 μ := ((matCLM Δ).comp_memLp' hxsL).add ((matCLM A₁₂).comp_memLp' hysL)
  have hDwL : MemLp (fun ω => matCLM D (w ω)) 2 μ := (matCLM D).comp_memLp' hwL
  have hAyL : MemLp (fun ω => matCLM A₂₂ (ys ω)) 2 μ := (matCLM A₂₂).comp_memLp' hysL
  have hqm : StronglyMeasurable[ℱ] q :=
    (((matCLM A₂₂).continuous.comp_stronglyMeasurable hys).const_smul g).add
      (((matCLM D).continuous.comp_stronglyMeasurable hwm).const_smul b)
  have hqL : MemLp q 2 μ := (hAyL.const_smul g).add (hDwL.const_smul b)
  have hbwm : StronglyMeasurable[ℱ] (fun ω => b • w ω) := hwm.const_smul b
  have hbwL : MemLp (fun ω => b • w ω) 2 μ := hwL.const_smul b
  have hbML : MemLp (fun ω => b • M ω) 2 μ := hML.const_smul b
  have hDML : MemLp (fun ω => matCLM D (M ω)) 2 μ := (matCLM D).comp_memLp' hML
  have hbvL : MemLp bv 2 μ := (hM'L.const_smul g).add (hDML.const_smul b)
  have hbMm := condExp_smul_eq_zero (μ := μ) b hmart
  have hbvm : ∀ j, μ[fun ω => bv ω j | ℱ] =ᵐ[μ] 0 :=
    condExp_add_eq_zero (hM'L.const_smul g) (hDML.const_smul b)
      (condExp_smul_eq_zero g hmart')
      (condExp_smul_eq_zero b (condExp_matCLM_eq_zero D hML hmart))
  have hstep := crossMoment_drift_step (μ := μ) hℱ hxs hbwm hys hqm hxsL hbwL hbML hcL hysL hqL
    hbvL hcL' hbMm hbvm
  have hgAy : MemLp (fun ω => g • matCLM A₂₂ (ys ω)) 2 μ := hAyL.const_smul g
  have hbDw : MemLp (fun ω => b • matCLM D (w ω)) 2 μ := hDwL.const_smul b
  have hw : w = fun ω => matCLM Δ (xs ω) + matCLM A₁₂ (ys ω) := rfl
  have i1 : crossMoment μ xs q = g • rmul A₂₂ (crossMoment μ xs ys)
      + b • crossMoment μ xs (fun ω => matCLM D (w ω)) := by
    rw [crossMoment_add_right hxsL hgAy hbDw,
      crossMoment_smul_right, crossMoment_smul_right, crossMoment_matCLM_right A₂₂ hxsL hysL]
  have i2 : crossMoment μ (fun ω => b • w ω) ys =
      b • (lmul Δ (crossMoment μ xs ys) + lmul A₁₂ (secondMoment μ ys)) := by
    rw [crossMoment_smul_left, hw, cm_matCLM_add_left Δ A₁₂ hysL hxsL hysL]; rfl
  have i3 : crossMoment μ (fun ω => b • M ω) bv =
      (b * g) • crossMoment μ M M' + b ^ 2 • crossMoment μ M (fun ω => matCLM D (M ω)) := by
    have hgM' : MemLp (fun ω => g • M' ω) 2 μ := hM'L.const_smul g
    have hbDM : MemLp (fun ω => b • matCLM D (M ω)) 2 μ := hDML.const_smul b
    rw [crossMoment_add_right hbML hgM' hbDM,
      crossMoment_smul_left, crossMoment_smul_left, crossMoment_smul_right, crossMoment_smul_right,
      smul_smul, smul_smul, sq]
  rw [i1, i2, i3] at hstep
  have hsplit : crossMoment μ (fun ω => (xs ω - b • w ω) + b • M ω + c ω)
        (fun ω => (ys ω - q ω) + bv ω + c' ω)
      - (crossMoment μ xs ys - g • rmul A₂₂ (crossMoment μ xs ys)
        - b • lmul A₁₂ (secondMoment μ ys) + (b * g) • Γ) =
      (crossMoment μ (fun ω => (xs ω - b • w ω) + b • M ω + c ω)
          (fun ω => (ys ω - q ω) + bv ω + c' ω)
        - (crossMoment μ xs ys - (g • rmul A₂₂ (crossMoment μ xs ys)
          + b • crossMoment μ xs (fun ω => matCLM D (w ω)))
          - b • (lmul Δ (crossMoment μ xs ys) + lmul A₁₂ (secondMoment μ ys))
          + crossMoment μ (fun ω => b • w ω) q
          + ((b * g) • crossMoment μ M M' + b ^ 2 • crossMoment μ M (fun ω => matCLM D (M ω)))))
      + (-(b • crossMoment μ xs (fun ω => matCLM D (w ω))) - b • lmul Δ (crossMoment μ xs ys)
        + crossMoment μ (fun ω => b • w ω) q + (b * g) • (crossMoment μ M M' - Γ)
        + b ^ 2 • crossMoment μ M (fun ω => matCLM D (M ω))) := by
    rw [smul_add, smul_sub]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have n1 : ‖b • crossMoment μ xs (fun ω => matCLM D (w ω))‖ ≤
      b * (rms μ xs * rms μ (fun ω => matCLM D (w ω))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (norm_crossMoment_le_rms hxsL hDwL) hb
  have n2 : ‖b • lmul Δ (crossMoment μ xs ys)‖ = b * ‖lmul Δ (crossMoment μ xs ys)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have n3 : ‖crossMoment μ (fun ω => b • w ω) q‖ ≤ b * (rms μ w * rms μ q) := by
    refine (norm_crossMoment_le_rms hbwL hqL).trans ?_
    rw [rms_smul, abs_of_nonneg hb, mul_assoc]
  have n4 : ‖(b * g) • (crossMoment μ M M' - Γ)‖ = b * g * ‖crossMoment μ M M' - Γ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb hg)]
  have n5 : ‖b ^ 2 • crossMoment μ M (fun ω => matCLM D (M ω))‖ ≤
      b ^ 2 * (rms μ M * rms μ (fun ω => matCLM D (M ω))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_crossMoment_le_rms hML hDML) (sq_nonneg _)
  have t1 := norm_add_le (-(b • crossMoment μ xs (fun ω => matCLM D (w ω)))
    - b • lmul Δ (crossMoment μ xs ys) + crossMoment μ (fun ω => b • w ω) q
    + (b * g) • (crossMoment μ M M' - Γ)) (b ^ 2 • crossMoment μ M (fun ω => matCLM D (M ω)))
  have t2 := norm_add_le (-(b • crossMoment μ xs (fun ω => matCLM D (w ω)))
    - b • lmul Δ (crossMoment μ xs ys) + crossMoment μ (fun ω => b • w ω) q)
    ((b * g) • (crossMoment μ M M' - Γ))
  have t3 := norm_add_le (-(b • crossMoment μ xs (fun ω => matCLM D (w ω)))
    - b • lmul Δ (crossMoment μ xs ys)) (crossMoment μ (fun ω => b • w ω) q)
  have t4 := norm_sub_le (-(b • crossMoment μ xs (fun ω => matCLM D (w ω))))
    (b • lmul Δ (crossMoment μ xs ys))
  rw [norm_neg] at t4
  linarith

/-- One step of the fast second moment `Y = E[ỹ ỹᵀ]` (Lemma 3.2 of the write-up). -/
theorem tts_step_Y [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {xs M : Ω → E d₁} {ys M' c' : Ω → E d₂} {b g : ℝ} (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hxs : StronglyMeasurable[ℱ] xs) (hys : StronglyMeasurable[ℱ] ys)
    (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ) (hML : MemLp M 2 μ) (hM'L : MemLp M' 2 μ)
    (hcL' : MemLp c' 2 μ)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0) (hmart' : ∀ j, μ[fun ω => M' ω j | ℱ] =ᵐ[μ] 0)
    (Γ : Mat d₂) :
    let w := fun ω => matCLM Δ (xs ω) + matCLM A₁₂ (ys ω)
    let q := fun ω => g • matCLM A₂₂ (ys ω) + b • matCLM D (w ω)
    let bv := fun ω => g • M' ω + b • matCLM D (M ω)
    ‖secondMoment μ (fun ω => (ys ω - q ω) + bv ω + c' ω)
      - (secondMoment μ ys - g • lyapOp A₂₂ (secondMoment μ ys) + g ^ 2 • Γ)‖ ≤
      b * (2 * (rms μ ys * rms μ (fun ω => matCLM D (w ω)))) + rms μ q ^ 2
        + g ^ 2 * ‖secondMoment μ M' - Γ‖
        + g * b * (2 * (rms μ M' * rms μ (fun ω => matCLM D (M ω))))
        + b ^ 2 * rms μ (fun ω => matCLM D (M ω)) ^ 2
        + ((rms μ (fun ω => ys ω - q ω) + rms μ bv + rms μ c') * rms μ c'
          + rms μ c' * (rms μ (fun ω => ys ω - q ω) + rms μ bv)) := by
  intro w q bv
  have hwm : StronglyMeasurable[ℱ] w :=
    ((matCLM Δ).continuous.comp_stronglyMeasurable hxs).add
      ((matCLM A₁₂).continuous.comp_stronglyMeasurable hys)
  have hwL : MemLp w 2 μ := ((matCLM Δ).comp_memLp' hxsL).add ((matCLM A₁₂).comp_memLp' hysL)
  have hDwL : MemLp (fun ω => matCLM D (w ω)) 2 μ := (matCLM D).comp_memLp' hwL
  have hAyL : MemLp (fun ω => matCLM A₂₂ (ys ω)) 2 μ := (matCLM A₂₂).comp_memLp' hysL
  have hqm : StronglyMeasurable[ℱ] q :=
    (((matCLM A₂₂).continuous.comp_stronglyMeasurable hys).const_smul g).add
      (((matCLM D).continuous.comp_stronglyMeasurable hwm).const_smul b)
  have hgAy : MemLp (fun ω => g • matCLM A₂₂ (ys ω)) 2 μ := hAyL.const_smul g
  have hbDw : MemLp (fun ω => b • matCLM D (w ω)) 2 μ := hDwL.const_smul b
  have hqL : MemLp q 2 μ := hgAy.add hbDw
  have hDML : MemLp (fun ω => matCLM D (M ω)) 2 μ := (matCLM D).comp_memLp' hML
  have hgM' : MemLp (fun ω => g • M' ω) 2 μ := hM'L.const_smul g
  have hbDM : MemLp (fun ω => b • matCLM D (M ω)) 2 μ := hDML.const_smul b
  have hbvL : MemLp bv 2 μ := hgM'.add hbDM
  have hbvm : ∀ j, μ[fun ω => bv ω j | ℱ] =ᵐ[μ] 0 :=
    condExp_add_eq_zero hgM' hbDM (condExp_smul_eq_zero g hmart')
      (condExp_smul_eq_zero b (condExp_matCLM_eq_zero D hML hmart))
  have hstep := crossMoment_drift_step (μ := μ) hℱ hys hqm hys hqm hysL hqL hbvL hcL' hysL hqL
    hbvL hcL' hbvm hbvm
  have i1 : crossMoment μ ys q = g • rmul A₂₂ (secondMoment μ ys)
      + b • crossMoment μ ys (fun ω => matCLM D (w ω)) := by
    rw [crossMoment_add_right hysL hgAy hbDw,
      crossMoment_smul_right, crossMoment_smul_right, crossMoment_matCLM_right A₂₂ hysL hysL]; rfl
  have i2 : crossMoment μ q ys = g • lmul A₂₂ (secondMoment μ ys)
      + b • crossMoment μ (fun ω => matCLM D (w ω)) ys := by
    rw [crossMoment_add_left hgAy hbDw hysL,
      crossMoment_smul_left, crossMoment_smul_left, crossMoment_matCLM_left A₂₂ hysL hysL]; rfl
  have i3 : crossMoment μ bv bv = g ^ 2 • secondMoment μ M'
      + (g * b) • (crossMoment μ M' (fun ω => matCLM D (M ω))
        + crossMoment μ (fun ω => matCLM D (M ω)) M')
      + b ^ 2 • secondMoment μ (fun ω => matCLM D (M ω)) := by
    rw [crossMoment_add_left hgM' hbDM hbvL, crossMoment_add_right hgM' hgM' hbDM,
      crossMoment_add_right hbDM hgM' hbDM]
    simp only [crossMoment_smul_left, crossMoment_smul_right, smul_smul, secondMoment]
    rw [smul_add]
    have e1 : g * g = g ^ 2 := by ring
    have e2 : b * b = b ^ 2 := by ring
    have e3 : b * g = g * b := by ring
    rw [e1, e2, e3]
    abel
  rw [i1, i2, i3] at hstep
  have hsplit : secondMoment μ (fun ω => (ys ω - q ω) + bv ω + c' ω)
      - (secondMoment μ ys - g • lyapOp A₂₂ (secondMoment μ ys) + g ^ 2 • Γ) =
      (crossMoment μ (fun ω => (ys ω - q ω) + bv ω + c' ω) (fun ω => (ys ω - q ω) + bv ω + c' ω)
        - (crossMoment μ ys ys - (g • rmul A₂₂ (secondMoment μ ys)
          + b • crossMoment μ ys (fun ω => matCLM D (w ω)))
          - (g • lmul A₂₂ (secondMoment μ ys) + b • crossMoment μ (fun ω => matCLM D (w ω)) ys)
          + crossMoment μ q q
          + (g ^ 2 • secondMoment μ M'
            + (g * b) • (crossMoment μ M' (fun ω => matCLM D (M ω))
              + crossMoment μ (fun ω => matCLM D (M ω)) M')
            + b ^ 2 • secondMoment μ (fun ω => matCLM D (M ω)))))
      + (-(b • (crossMoment μ ys (fun ω => matCLM D (w ω))
          + crossMoment μ (fun ω => matCLM D (w ω)) ys))
        + crossMoment μ q q + g ^ 2 • (secondMoment μ M' - Γ)
        + (g * b) • (crossMoment μ M' (fun ω => matCLM D (M ω))
          + crossMoment μ (fun ω => matCLM D (M ω)) M')
        + b ^ 2 • secondMoment μ (fun ω => matCLM D (M ω))) := by
    rw [lyapOp_eq]
    simp only [secondMoment, smul_add, smul_sub]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have n1 : ‖b • (crossMoment μ ys (fun ω => matCLM D (w ω))
      + crossMoment μ (fun ω => matCLM D (w ω)) ys)‖ ≤
      b * (2 * (rms μ ys * rms μ (fun ω => matCLM D (w ω)))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hb
    have := norm_crossMoment_le_rms hysL hDwL (μ := μ)
    have := norm_crossMoment_le_rms hDwL hysL (μ := μ)
    linarith
  have n2 : ‖crossMoment μ q q‖ ≤ rms μ q ^ 2 := by
    rw [sq]; exact norm_crossMoment_le_rms hqL hqL
  have n3 : ‖g ^ 2 • (secondMoment μ M' - Γ)‖ = g ^ 2 * ‖secondMoment μ M' - Γ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have n4 : ‖(g * b) • (crossMoment μ M' (fun ω => matCLM D (M ω))
      + crossMoment μ (fun ω => matCLM D (M ω)) M')‖ ≤
      g * b * (2 * (rms μ M' * rms μ (fun ω => matCLM D (M ω)))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg hb)]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (mul_nonneg hg hb)
    have := norm_crossMoment_le_rms hM'L hDML (μ := μ)
    have := norm_crossMoment_le_rms hDML hM'L (μ := μ)
    linarith
  have n5 : ‖b ^ 2 • secondMoment μ (fun ω => matCLM D (M ω))‖ ≤
      b ^ 2 * rms μ (fun ω => matCLM D (M ω)) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq (rms μ _)]
    exact mul_le_mul_of_nonneg_left (norm_crossMoment_le_rms hDML hDML) (sq_nonneg _)
  have t1 := norm_add_le (-(b • (crossMoment μ ys (fun ω => matCLM D (w ω))
      + crossMoment μ (fun ω => matCLM D (w ω)) ys))
    + crossMoment μ q q + g ^ 2 • (secondMoment μ M' - Γ)
    + (g * b) • (crossMoment μ M' (fun ω => matCLM D (M ω))
      + crossMoment μ (fun ω => matCLM D (M ω)) M'))
    (b ^ 2 • secondMoment μ (fun ω => matCLM D (M ω)))
  have t2 := norm_add_le (-(b • (crossMoment μ ys (fun ω => matCLM D (w ω))
      + crossMoment μ (fun ω => matCLM D (w ω)) ys))
    + crossMoment μ q q + g ^ 2 • (secondMoment μ M' - Γ))
    ((g * b) • (crossMoment μ M' (fun ω => matCLM D (M ω))
      + crossMoment μ (fun ω => matCLM D (M ω)) M'))
  have t3 := norm_add_le (-(b • (crossMoment μ ys (fun ω => matCLM D (w ω))
      + crossMoment μ (fun ω => matCLM D (w ω)) ys))
    + crossMoment μ q q) (g ^ 2 • (secondMoment μ M' - Γ))
  have t4 := norm_add_le (-(b • (crossMoment μ ys (fun ω => matCLM D (w ω))
      + crossMoment μ (fun ω => matCLM D (w ω)) ys))) (crossMoment μ q q)
  rw [norm_neg] at t4
  linarith

/-! ### Bookkeeping for the remainders -/

/-- `t ≤ t²` for `t ≥ 1`. -/
lemma le_sq_of_one_le {t : ℝ} (ht : 1 ≤ t) : t ≤ t ^ 2 := by nlinarith

/-- The remainder of the slow recursion is `ε₁ β² n`. -/
lemma tts_R1_le {b gm t sb sg d₁' cw Kx mM G Sw Sa SbM Sc : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (hsb : 0 < sb) (hsb2 : sb ^ 2 = b) (hsg : 0 ≤ sg)
    (hsg2 : sg ^ 2 = gm) (ht : 1 ≤ t) (hd : 0 ≤ d₁') (hcw : 0 ≤ cw) (hK : 0 ≤ Kx) (hm : 0 ≤ mM)
    (hG : 0 ≤ G) (hSw0 : 0 ≤ Sw) (_hSa0 : 0 ≤ Sa) (_hSbM0 : 0 ≤ SbM) (hSc0 : 0 ≤ Sc)
    (hSw : Sw ≤ cw * sg * t) (hSa : Sa ≤ √2 * (d₁' * sb * t + b * (cw * sg * t)))
    (hSbM : SbM ≤ b * mM) (hSc : Sc ≤ Kx * b * gm) :
    b ^ 2 * Sw ^ 2 + b ^ 2 * G + ((Sa + SbM + Sc) * Sc + Sc * (Sa + SbM)) ≤
      (cw ^ 2 * gm + G + 2 * (√2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) + mM * Kx * gm
        + Kx ^ 2 * gm ^ 2)) * b ^ 2 * t ^ 2 := by
  have ht2 := le_sq_of_one_le ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hn1 : 1 ≤ t ^ 2 := ht.trans ht2
  have s2 := Real.sqrt_nonneg (2 : ℝ)
  have e1 : b ^ 2 * Sw ^ 2 ≤ cw ^ 2 * gm * b ^ 2 * t ^ 2 := by
    have h := pow_le_pow_left₀ hSw0 hSw 2
    have e : (cw * sg * t) ^ 2 = cw ^ 2 * gm * t ^ 2 := by rw [← hsg2]; ring
    rw [e] at h
    have h' := mul_le_mul_of_nonneg_left h (sq_nonneg b)
    linarith only [h', show b ^ 2 * (cw ^ 2 * gm * t ^ 2) = cw ^ 2 * gm * b ^ 2 * t ^ 2 by ring]
  have e2 : b ^ 2 * G ≤ G * b ^ 2 * t ^ 2 := by
    have h := le_mul_of_one_le_right (mul_nonneg (sq_nonneg b) hG) hn1
    linarith only [h, show b ^ 2 * G * t ^ 2 = G * b ^ 2 * t ^ 2 by ring]
  have hSaSc : Sa * Sc ≤ √2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) * b ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSa hSc hSc0 (by positivity)
    have e : √2 * (d₁' * sb * t + b * (cw * sg * t)) * (Kx * b * gm) =
        √2 * Kx * (d₁' * (gm / sb) * t + cw * gm * sg * t) * b ^ 2 := by
      rw [← hsb2]; field_simp; ring
    rw [e] at h1
    have hq : 0 ≤ d₁' * (gm / sb) := by positivity
    have hq' : 0 ≤ cw * gm * sg := by positivity
    have h2 : √2 * Kx * (d₁' * (gm / sb) * t + cw * gm * sg * t) * b ^ 2 ≤
        √2 * Kx * (d₁' * (gm / sb) * t ^ 2 + cw * gm * sg * t ^ 2) * b ^ 2 := by
      gcongr
    linarith only [h1, h2, show √2 * Kx * (d₁' * (gm / sb) * t ^ 2 + cw * gm * sg * t ^ 2) * b ^ 2
      = √2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) * b ^ 2 * t ^ 2 by ring]
  have hSbSc : SbM * Sc ≤ mM * Kx * gm * b ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSbM hSc hSc0 (by positivity)
    have h2 : mM * Kx * gm * b ^ 2 ≤ mM * Kx * gm * b ^ 2 * t ^ 2 :=
      le_mul_of_one_le_right (by positivity) hn1
    linarith only [h1, h2, show b * mM * (Kx * b * gm) = mM * Kx * gm * b ^ 2 by ring]
  have hScSc : Sc * Sc ≤ Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSc hSc hSc0 (by positivity)
    have h2 : Kx ^ 2 * gm ^ 2 * b ^ 2 ≤ Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2 :=
      le_mul_of_one_le_right (by positivity) hn1
    linarith only [h1, h2, show Kx * b * gm * (Kx * b * gm) = Kx ^ 2 * gm ^ 2 * b ^ 2 by ring]
  have hpos : 0 ≤ Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2 := by positivity
  have e : (cw ^ 2 * gm + G + 2 * (√2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) + mM * Kx * gm
        + Kx ^ 2 * gm ^ 2)) * b ^ 2 * t ^ 2 =
      cw ^ 2 * gm * b ^ 2 * t ^ 2 + G * b ^ 2 * t ^ 2
        + 2 * (√2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) * b ^ 2 * t ^ 2)
        + 2 * (mM * Kx * gm * b ^ 2 * t ^ 2) + 2 * (Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2) := by ring
  rw [e]
  linarith only [e1, e2, hSaSc, hSbSc, hScSc, hpos,
    show (Sa + SbM + Sc) * Sc + Sc * (Sa + SbM) = 2 * (Sa * Sc) + 2 * (SbM * Sc) + Sc * Sc by ring]

/-- The remainder of the cross recursion is `ε₂ β γ n`. -/
lemma tts_R2_le {b gm t sb sg d₁' d₂' cw cq Kx Ky mM mM' nD LΔ G Z Sx SDw Sw Sq SM SDM Sa SbM Sc
      Scy Say Sbv : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (hsb : 0 < sb) (hsb2 : sb ^ 2 = b) (hsg : 0 < sg)
    (hsg2 : sg ^ 2 = gm) (ht : 1 ≤ t) (hd₁ : 0 ≤ d₁') (hd₂ : 0 ≤ d₂') (hcw : 0 ≤ cw)
    (hcq : 0 ≤ cq) (hKx : 0 ≤ Kx) (hKy : 0 ≤ Ky) (hm : 0 ≤ mM) (hm' : 0 ≤ mM') (hnD : 0 ≤ nD)
    (hLΔ : 0 ≤ LΔ) (hG : 0 ≤ G)
    (_hSx0 : 0 ≤ Sx) (hSDw0 : 0 ≤ SDw) (_hSw0 : 0 ≤ Sw) (hSq0 : 0 ≤ Sq) (_hSM0 : 0 ≤ SM)
    (hSDM0 : 0 ≤ SDM) (_hSa0 : 0 ≤ Sa) (_hSbM0 : 0 ≤ SbM) (_hSc0 : 0 ≤ Sc) (hScy0 : 0 ≤ Scy)
    (hSay0 : 0 ≤ Say) (hSbv0 : 0 ≤ Sbv)
    (hSx : Sx ≤ d₁' * sb * t) (hSDw : SDw ≤ nD * (cw * sg * t)) (hSw : Sw ≤ cw * sg * t)
    (hZ : Z ≤ b * t ^ 2) (hSq : Sq ≤ cq * gm * sg * t) (hSM : SM ≤ mM) (hSDM : SDM ≤ nD * mM)
    (hSa : Sa ≤ √2 * (d₁' * sb * t + b * (cw * sg * t))) (hSbM : SbM ≤ b * mM)
    (hSc : Sc ≤ Kx * b * gm) (hScy : Scy ≤ Ky * gm ^ 2)
    (hSay : Say ≤ √2 * (d₂' * sg * t + cq * gm * sg * t)) (hSbv : Sbv ≤ √2 * (gm * mM' + b * (nD * mM))) :
    b * (Sx * SDw) + b * (LΔ * Z) + b * (Sw * Sq) + b * gm * G + b ^ 2 * (SM * SDM)
      + ((Sa + SbM + Sc) * Scy + Sc * (Say + Sbv)) ≤
      (d₁' * nD * cw * (sb / sg) + LΔ * (b / gm) + cw * cq * gm + G + (b / gm) * (nD * mM ^ 2)
        + √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) + mM * Ky * gm + Kx * Ky * gm ^ 2
        + Kx * √2 * (d₂' * sg + cq * gm * sg) + Kx * √2 * (gm * mM' + b * (nD * mM)))
        * (b * gm) * t ^ 2 := by
  have ht2 := le_sq_of_one_le ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hn1 : 1 ≤ t ^ 2 := ht.trans ht2
  have s2 := Real.sqrt_nonneg (2 : ℝ)
  have hbg : 0 < b * gm := mul_pos hb hgm
  -- `le_mul_of_one_le_right` with `t²`
  have up : ∀ x, 0 ≤ x → x ≤ x * t ^ 2 := fun x hx => le_mul_of_one_le_right hx hn1
  have up' : ∀ x, 0 ≤ x → x * t ≤ x * t ^ 2 := fun x hx => mul_le_mul_of_nonneg_left ht2 hx
  have u1 : b * (Sx * SDw) ≤ d₁' * nD * cw * (sb / sg) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul hSx hSDw hSDw0 (by positivity)) hb.le
    have e : b * (d₁' * sb * t * (nD * (cw * sg * t))) = d₁' * nD * cw * (sb / sg) * (b * gm) * t ^ 2 := by
      rw [← hsg2]; field_simp; ring
    linarith only [h1, e]
  have u2 : b * (LΔ * Z) ≤ LΔ * (b / gm) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hLΔ) hb.le
    have e : b * (LΔ * (b * t ^ 2)) = LΔ * (b / gm) * (b * gm) * t ^ 2 := by field_simp; ring
    linarith only [h1, e]
  have u3 : b * (Sw * Sq) ≤ cw * cq * gm * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul hSw hSq hSq0 (by positivity)) hb.le
    have e : b * (cw * sg * t * (cq * gm * sg * t)) = cw * cq * gm * (b * gm) * t ^ 2 := by
      rw [← hsg2]; ring
    linarith only [h1, e]
  have u4 : b * gm * G ≤ G * (b * gm) * t ^ 2 := by
    have := up (G * (b * gm)) (by positivity)
    linarith only [this, show b * gm * G = G * (b * gm) by ring]
  have u5 : b ^ 2 * (SM * SDM) ≤ (b / gm) * (nD * mM ^ 2) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul hSM hSDM hSDM0 hm) (sq_nonneg b)
    have h2 := up ((b / gm) * (nD * mM ^ 2) * (b * gm)) (by positivity)
    have e : b ^ 2 * (mM * (nD * mM)) = (b / gm) * (nD * mM ^ 2) * (b * gm) := by field_simp; ring
    linarith only [h1, h2, e]
  have u6 : Sa * Scy ≤ √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSa hScy hScy0 (by positivity)
    have e : √2 * (d₁' * sb * t + b * (cw * sg * t)) * (Ky * gm ^ 2) =
        √2 * Ky * (d₁' * (gm / sb) * t + cw * sg * gm * t) * (b * gm) := by
      rw [← hsb2]; field_simp; ring
    have hq : 0 ≤ d₁' * (gm / sb) := by positivity
    have h2 : √2 * Ky * (d₁' * (gm / sb) * t + cw * sg * gm * t) * (b * gm) ≤
        √2 * Ky * (d₁' * (gm / sb) * t ^ 2 + cw * sg * gm * t ^ 2) * (b * gm) := by gcongr
    linarith only [h1, h2, e, show √2 * Ky * (d₁' * (gm / sb) * t ^ 2 + cw * sg * gm * t ^ 2) * (b * gm)
      = √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) * (b * gm) * t ^ 2 by ring]
  have u7 : SbM * Scy ≤ mM * Ky * gm * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSbM hScy hScy0 (by positivity)
    have h2 := up (mM * Ky * gm * (b * gm)) (by positivity)
    linarith only [h1, h2, show b * mM * (Ky * gm ^ 2) = mM * Ky * gm * (b * gm) by ring]
  have u8 : Sc * Scy ≤ Kx * Ky * gm ^ 2 * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSc hScy hScy0 (by positivity)
    have h2 := up (Kx * Ky * gm ^ 2 * (b * gm)) (by positivity)
    linarith only [h1, h2, show Kx * b * gm * (Ky * gm ^ 2) = Kx * Ky * gm ^ 2 * (b * gm) by ring]
  have u9 : Sc * Say ≤ Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSc hSay hSay0 (by positivity)
    have h2 := up' (Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm)) (by positivity)
    linarith only [h1, h2, show Kx * b * gm * (√2 * (d₂' * sg * t + cq * gm * sg * t))
      = Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm) * t by ring]
  have u10 : Sc * Sbv ≤ Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSc hSbv hSbv0 (by positivity)
    have h2 := up (Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm)) (by positivity)
    linarith only [h1, h2, show Kx * b * gm * (√2 * (gm * mM' + b * (nD * mM)))
      = Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm) by ring]
  have e : (d₁' * nD * cw * (sb / sg) + LΔ * (b / gm) + cw * cq * gm + G + (b / gm) * (nD * mM ^ 2)
        + √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) + mM * Ky * gm + Kx * Ky * gm ^ 2
        + Kx * √2 * (d₂' * sg + cq * gm * sg) + Kx * √2 * (gm * mM' + b * (nD * mM)))
        * (b * gm) * t ^ 2 =
      d₁' * nD * cw * (sb / sg) * (b * gm) * t ^ 2 + LΔ * (b / gm) * (b * gm) * t ^ 2
        + cw * cq * gm * (b * gm) * t ^ 2 + G * (b * gm) * t ^ 2
        + (b / gm) * (nD * mM ^ 2) * (b * gm) * t ^ 2
        + √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) * (b * gm) * t ^ 2
        + mM * Ky * gm * (b * gm) * t ^ 2 + Kx * Ky * gm ^ 2 * (b * gm) * t ^ 2
        + Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm) * t ^ 2
        + Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm) * t ^ 2 := by ring
  rw [e]
  linarith only [u1, u2, u3, u4, u5, u6, u7, u8, u9, u10,
    show (Sa + SbM + Sc) * Scy + Sc * (Say + Sbv) = Sa * Scy + SbM * Scy + Sc * Scy + Sc * Say
      + Sc * Sbv by ring]

/-- The remainder of the fast recursion is `ε₃ γ² n`. -/
lemma tts_R3_le {b gm t sg d₂' cw cq Ky mM mM' nD G Sy SDw Sq SM' SDM Scy Say Sbv : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (hsg : 0 < sg)
    (hsg2 : sg ^ 2 = gm) (ht : 1 ≤ t) (hd₂ : 0 ≤ d₂') (_hcw : 0 ≤ cw)
    (hcq : 0 ≤ cq) (hKy : 0 ≤ Ky) (hm : 0 ≤ mM) (hm' : 0 ≤ mM') (hnD : 0 ≤ nD) (hG : 0 ≤ G)
    (_hSy0 : 0 ≤ Sy) (hSDw0 : 0 ≤ SDw) (hSq0 : 0 ≤ Sq) (_hSM'0 : 0 ≤ SM') (hSDM0 : 0 ≤ SDM)
    (hScy0 : 0 ≤ Scy) (_hSay0 : 0 ≤ Say) (_hSbv0 : 0 ≤ Sbv)
    (hSy : Sy ≤ d₂' * sg * t) (hSDw : SDw ≤ nD * (cw * sg * t)) (hSq : Sq ≤ cq * gm * sg * t)
    (hSM' : SM' ≤ mM') (hSDM : SDM ≤ nD * mM) (hScy : Scy ≤ Ky * gm ^ 2)
    (hSay : Say ≤ √2 * (d₂' * sg * t + cq * gm * sg * t)) (hSbv : Sbv ≤ √2 * (gm * mM' + b * (nD * mM))) :
    b * (2 * (Sy * SDw)) + Sq ^ 2 + gm ^ 2 * G + gm * b * (2 * (SM' * SDM)) + b ^ 2 * SDM ^ 2
      + ((Say + Sbv + Scy) * Scy + Scy * (Say + Sbv)) ≤
      (2 * d₂' * nD * cw * (b / gm) + cq ^ 2 * gm + G + 2 * (b / gm) * (mM' * (nD * mM))
        + (b / gm) ^ 2 * (nD * mM) ^ 2 + 2 * (√2 * Ky * (d₂' * sg + cq * gm * sg))
        + 2 * (√2 * Ky * (gm * mM' + b * (nD * mM))) + Ky ^ 2 * gm ^ 2) * gm ^ 2 * t ^ 2 := by
  have ht2 := le_sq_of_one_le ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hn1 : 1 ≤ t ^ 2 := ht.trans ht2
  have s2 := Real.sqrt_nonneg (2 : ℝ)
  have up : ∀ x, 0 ≤ x → x ≤ x * t ^ 2 := fun x hx => le_mul_of_one_le_right hx hn1
  have up' : ∀ x, 0 ≤ x → x * t ≤ x * t ^ 2 := fun x hx => mul_le_mul_of_nonneg_left ht2 hx
  have u1 : b * (2 * (Sy * SDw)) ≤ 2 * d₂' * nD * cw * (b / gm) * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul hSy hSDw hSDw0 (by positivity)) zero_le_two) hb.le
    have e : b * (2 * (d₂' * sg * t * (nD * (cw * sg * t)))) =
        2 * d₂' * nD * cw * (b / gm) * gm ^ 2 * t ^ 2 := by
      rw [← hsg2]; field_simp; ring
    linarith only [h1, e]
  have u2 : Sq ^ 2 ≤ cq ^ 2 * gm * gm ^ 2 * t ^ 2 := by
    have h1 := pow_le_pow_left₀ hSq0 hSq 2
    have e : (cq * gm * sg * t) ^ 2 = cq ^ 2 * gm * gm ^ 2 * t ^ 2 := by rw [← hsg2]; ring
    linarith only [h1, e]
  have u3 : gm ^ 2 * G ≤ G * gm ^ 2 * t ^ 2 := by
    have := up (G * gm ^ 2) (by positivity)
    linarith only [this, show gm ^ 2 * G = G * gm ^ 2 by ring]
  have u4 : gm * b * (2 * (SM' * SDM)) ≤ 2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul hSM' hSDM hSDM0 hm') zero_le_two) (mul_nonneg hgm.le hb.le)
    have h2 := up (2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2) (by positivity)
    have e : gm * b * (2 * (mM' * (nD * mM))) = 2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2 := by
      field_simp; ring
    linarith only [h1, h2, e]
  have u5 : b ^ 2 * SDM ^ 2 ≤ (b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSDM0 hSDM 2) (sq_nonneg b)
    have h2 := up ((b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2) (by positivity)
    have e : b ^ 2 * (nD * mM) ^ 2 = (b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2 := by field_simp
    linarith only [h1, h2, e]
  have u6 : Say * Scy ≤ √2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSay hScy hScy0 (by positivity)
    have h2 := up' (√2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2) (by positivity)
    linarith only [h1, h2, show √2 * (d₂' * sg * t + cq * gm * sg * t) * (Ky * gm ^ 2)
      = √2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2 * t by ring]
  have u7 : Sbv * Scy ≤ √2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSbv hScy hScy0 (by positivity)
    have h2 := up (√2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2) (by positivity)
    linarith only [h1, h2, show √2 * (gm * mM' + b * (nD * mM)) * (Ky * gm ^ 2)
      = √2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2 by ring]
  have u8 : Scy * Scy ≤ Ky ^ 2 * gm ^ 2 * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hScy hScy hScy0 (by positivity)
    have h2 := up (Ky ^ 2 * gm ^ 2 * gm ^ 2) (by positivity)
    linarith only [h1, h2, show Ky * gm ^ 2 * (Ky * gm ^ 2) = Ky ^ 2 * gm ^ 2 * gm ^ 2 by ring]
  have e : (2 * d₂' * nD * cw * (b / gm) + cq ^ 2 * gm + G + 2 * (b / gm) * (mM' * (nD * mM))
        + (b / gm) ^ 2 * (nD * mM) ^ 2 + 2 * (√2 * Ky * (d₂' * sg + cq * gm * sg))
        + 2 * (√2 * Ky * (gm * mM' + b * (nD * mM))) + Ky ^ 2 * gm ^ 2) * gm ^ 2 * t ^ 2 =
      2 * d₂' * nD * cw * (b / gm) * gm ^ 2 * t ^ 2 + cq ^ 2 * gm * gm ^ 2 * t ^ 2
        + G * gm ^ 2 * t ^ 2 + 2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2 * t ^ 2
        + (b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2 * t ^ 2
        + 2 * (√2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2 * t ^ 2)
        + 2 * (√2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2 * t ^ 2)
        + Ky ^ 2 * gm ^ 2 * gm ^ 2 * t ^ 2 := by ring
  rw [e]
  linarith only [u1, u2, u3, u4, u5, u6, u7, u8,
    show (Say + Sbv + Scy) * Scy + Scy * (Say + Sbv) = 2 * (Say * Scy) + 2 * (Sbv * Scy)
      + Scy * Scy by ring]

/-- A pointwise bound on the slow remainder `c` of Lemma 3.1. -/
lemma norm_tts_cx_le (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) {b b' gm Bq Cs : ℝ} (hb : 0 ≤ b) (hgm : 0 ≤ gm)
    (hbq : b ≤ Bq * gm) (hCs : |b' - b| ≤ Cs * b ^ 2) (_hBq : 0 ≤ Bq) (hCs0 : 0 ≤ Cs)
    (hh hh' : E d₁) (gg : E d₂) :
    ‖b • (b • matCLM Δ hh + gm • matCLM A₁₂ gg + b • matCLM A₁₂ (matCLM D hh)) + (b' - b) • hh'‖ ≤
      b * gm * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * ‖hh‖
        + ‖matCLM A₁₂‖ * ‖gg‖ + Cs * Bq * ‖hh'‖) := by
  have n1 : ‖matCLM Δ hh‖ ≤ ‖matCLM Δ‖ * ‖hh‖ := (matCLM Δ).le_opNorm _
  have n2 : ‖matCLM A₁₂ gg‖ ≤ ‖matCLM A₁₂‖ * ‖gg‖ := (matCLM A₁₂).le_opNorm _
  have n3 : ‖matCLM A₁₂ (matCLM D hh)‖ ≤ ‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖) :=
    ((matCLM A₁₂).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((matCLM D).le_opNorm _)
      (norm_nonneg _))
  have hin : ‖b • matCLM Δ hh + gm • matCLM A₁₂ gg + b • matCLM A₁₂ (matCLM D hh)‖ ≤
      b * (‖matCLM Δ‖ * ‖hh‖) + gm * (‖matCLM A₁₂‖ * ‖gg‖)
        + b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖)) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]; exact mul_le_mul_of_nonneg_left n1 hb
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgm]; exact mul_le_mul_of_nonneg_left n2 hgm
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]; exact mul_le_mul_of_nonneg_left n3 hb
  have t1 : ‖b • (b • matCLM Δ hh + gm • matCLM A₁₂ gg + b • matCLM A₁₂ (matCLM D hh))‖ ≤
      b * (b * (‖matCLM Δ‖ * ‖hh‖) + gm * (‖matCLM A₁₂‖ * ‖gg‖)
        + b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]; exact mul_le_mul_of_nonneg_left hin hb
  have t2 : ‖(b' - b) • hh'‖ ≤ Cs * b ^ 2 * ‖hh'‖ := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hCs (norm_nonneg _)
  refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
  have p0 := norm_nonneg hh
  have p1 := norm_nonneg hh'
  have p2 := norm_nonneg gg
  have q0 := norm_nonneg (matCLM Δ)
  have q1 := norm_nonneg (matCLM A₁₂)
  have q2 := norm_nonneg (matCLM D)
  have r1 : b * (b * (‖matCLM Δ‖ * ‖hh‖)) ≤ b * gm * (Bq * ‖matCLM Δ‖ * ‖hh‖) := by
    have := mul_le_mul_of_nonneg_right hbq (by positivity : 0 ≤ b * (‖matCLM Δ‖ * ‖hh‖))
    linarith only [this, show b * (b * (‖matCLM Δ‖ * ‖hh‖)) = b * (b * (‖matCLM Δ‖ * ‖hh‖)) by ring,
      show Bq * gm * (b * (‖matCLM Δ‖ * ‖hh‖)) = b * gm * (Bq * ‖matCLM Δ‖ * ‖hh‖) by ring,
      show b * (b * (‖matCLM Δ‖ * ‖hh‖)) = b * (b * (‖matCLM Δ‖ * ‖hh‖)) by ring]
  have r2 : b * (b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖))) ≤
      b * gm * (Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖ * ‖hh‖) := by
    have := mul_le_mul_of_nonneg_right hbq
      (by positivity : 0 ≤ b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖)))
    linarith only [this, show Bq * gm * (b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖)))
      = b * gm * (Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖ * ‖hh‖) by ring]
  have r3 : Cs * b ^ 2 * ‖hh'‖ ≤ b * gm * (Cs * Bq * ‖hh'‖) := by
    have := mul_le_mul_of_nonneg_right hbq (by positivity : 0 ≤ Cs * b * ‖hh'‖)
    linarith only [this, show Bq * gm * (Cs * b * ‖hh'‖) = b * gm * (Cs * Bq * ‖hh'‖) by ring,
      show b * (Cs * b * ‖hh'‖) = Cs * b ^ 2 * ‖hh'‖ by ring]
  have e : b * (b * (‖matCLM Δ‖ * ‖hh‖) + gm * (‖matCLM A₁₂‖ * ‖gg‖)
        + b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖))) =
      b * (b * (‖matCLM Δ‖ * ‖hh‖)) + b * gm * (‖matCLM A₁₂‖ * ‖gg‖)
        + b * (b * (‖matCLM A₁₂‖ * (‖matCLM D‖ * ‖hh‖))) := by ring
  rw [e]
  linarith only [r1, r2, r3, show b * gm * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * ‖hh‖
        + ‖matCLM A₁₂‖ * ‖gg‖ + Cs * Bq * ‖hh'‖) = b * gm * (Bq * ‖matCLM Δ‖ * ‖hh‖)
        + b * gm * (Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖ * ‖hh‖) + b * gm * (‖matCLM A₁₂‖ * ‖gg‖)
        + b * gm * (Cs * Bq * ‖hh'‖) by ring]

/-- A pointwise bound on the fast remainder `c'` of Lemma 3.1. -/
lemma norm_tts_cy_le (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {b b' gm gm' Bq Cs Ct : ℝ} (hb : 0 ≤ b) (hgm : 0 ≤ gm)
    (hbq : b ≤ Bq * gm) (hCs : |b' - b| ≤ Cs * b ^ 2) (hCt : |gm' - gm| ≤ Ct * gm ^ 2)
    (_hBq : 0 ≤ Bq) (hCs0 : 0 ≤ Cs) (_hCt0 : 0 ≤ Ct) (hh hh' : E d₁) (gg gg' : E d₂) :
    ‖gm • matCLM A₂₂ (gm • gg + b • matCLM D hh)
        + b • matCLM D (b • matCLM Δ hh + gm • matCLM A₁₂ gg + b • matCLM A₁₂ (matCLM D hh))
        + (gm' - gm) • gg' + (b' - b) • matCLM D hh'‖ ≤
      gm ^ 2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖) * ‖hh‖
        + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * ‖gg‖ + Ct * ‖gg'‖
        + Cs * Bq ^ 2 * ‖matCLM D‖ * ‖hh'‖) := by
  set nΔ := ‖matCLM Δ‖
  set n12 := ‖matCLM A₁₂‖
  set n22 := ‖matCLM A₂₂‖
  set nD := ‖matCLM D‖
  have q0 : 0 ≤ nΔ := norm_nonneg _
  have q1 : 0 ≤ n12 := norm_nonneg _
  have q2 : 0 ≤ n22 := norm_nonneg _
  have q3 : 0 ≤ nD := norm_nonneg _
  have p0 := norm_nonneg hh
  have p1 := norm_nonneg hh'
  have p2 := norm_nonneg gg
  have p3 := norm_nonneg gg'
  have hb2 : b ^ 2 ≤ Bq ^ 2 * gm ^ 2 := by
    have := pow_le_pow_left₀ hb hbq 2; rwa [mul_pow] at this
  have hbg : b * gm ≤ Bq * gm ^ 2 := by
    have := mul_le_mul_of_nonneg_right hbq hgm; rwa [mul_assoc, ← sq] at this
  -- term by term
  have t1 : ‖gm • matCLM A₂₂ (gm • gg + b • matCLM D hh)‖ ≤ gm * (n22 * (gm * ‖gg‖ + b * (nD * ‖hh‖))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgm]
    refine mul_le_mul_of_nonneg_left (((matCLM A₂₂).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) q2)) hgm
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgm]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left ((matCLM D).le_opNorm _) hb
  have hin : ‖b • matCLM Δ hh + gm • matCLM A₁₂ gg + b • matCLM A₁₂ (matCLM D hh)‖ ≤
      b * (nΔ * ‖hh‖) + gm * (n12 * ‖gg‖) + b * (n12 * (nD * ‖hh‖)) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left ((matCLM Δ).le_opNorm _) hb
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgm]
      exact mul_le_mul_of_nonneg_left ((matCLM A₁₂).le_opNorm _) hgm
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left (((matCLM A₁₂).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((matCLM D).le_opNorm _) q1)) hb
  have t2 : ‖b • matCLM D (b • matCLM Δ hh + gm • matCLM A₁₂ gg + b • matCLM A₁₂ (matCLM D hh))‖ ≤
      b * (nD * (b * (nΔ * ‖hh‖) + gm * (n12 * ‖gg‖) + b * (n12 * (nD * ‖hh‖)))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (((matCLM D).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hin q3)) hb
  have t3 : ‖(gm' - gm) • gg'‖ ≤ Ct * gm ^ 2 * ‖gg'‖ := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hCt p3
  have t4 : ‖(b' - b) • matCLM D hh'‖ ≤ Cs * b ^ 2 * (nD * ‖hh'‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hCs ((matCLM D).le_opNorm _) (norm_nonneg _) (by positivity)
  have tri := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)
  refine tri.trans ?_
  -- compare coefficients
  have r1 : gm * (n22 * (b * (nD * ‖hh‖))) ≤ gm ^ 2 * (Bq * n22 * nD * ‖hh‖) := by
    have := mul_le_mul_of_nonneg_right hbg (by positivity : 0 ≤ n22 * nD * ‖hh‖)
    linarith only [this, show gm * (n22 * (b * (nD * ‖hh‖))) = b * gm * (n22 * nD * ‖hh‖) by ring,
      show Bq * gm ^ 2 * (n22 * nD * ‖hh‖) = gm ^ 2 * (Bq * n22 * nD * ‖hh‖) by ring]
  have r2 : b * (nD * (b * (nΔ * ‖hh‖))) ≤ gm ^ 2 * (Bq ^ 2 * nD * nΔ * ‖hh‖) := by
    have := mul_le_mul_of_nonneg_right hb2 (by positivity : 0 ≤ nD * nΔ * ‖hh‖)
    linarith only [this, show b * (nD * (b * (nΔ * ‖hh‖))) = b ^ 2 * (nD * nΔ * ‖hh‖) by ring,
      show Bq ^ 2 * gm ^ 2 * (nD * nΔ * ‖hh‖) = gm ^ 2 * (Bq ^ 2 * nD * nΔ * ‖hh‖) by ring]
  have r3 : b * (nD * (gm * (n12 * ‖gg‖))) ≤ gm ^ 2 * (Bq * nD * n12 * ‖gg‖) := by
    have := mul_le_mul_of_nonneg_right hbg (by positivity : 0 ≤ nD * n12 * ‖gg‖)
    linarith only [this, show b * (nD * (gm * (n12 * ‖gg‖))) = b * gm * (nD * n12 * ‖gg‖) by ring,
      show Bq * gm ^ 2 * (nD * n12 * ‖gg‖) = gm ^ 2 * (Bq * nD * n12 * ‖gg‖) by ring]
  have r4 : b * (nD * (b * (n12 * (nD * ‖hh‖)))) ≤ gm ^ 2 * (Bq ^ 2 * nD * n12 * nD * ‖hh‖) := by
    have := mul_le_mul_of_nonneg_right hb2 (by positivity : 0 ≤ nD * n12 * nD * ‖hh‖)
    linarith only [this, show b * (nD * (b * (n12 * (nD * ‖hh‖)))) = b ^ 2 * (nD * n12 * nD * ‖hh‖)
      by ring, show Bq ^ 2 * gm ^ 2 * (nD * n12 * nD * ‖hh‖) = gm ^ 2 * (Bq ^ 2 * nD * n12 * nD * ‖hh‖)
      by ring]
  have r5 : Cs * b ^ 2 * (nD * ‖hh'‖) ≤ gm ^ 2 * (Cs * Bq ^ 2 * nD * ‖hh'‖) := by
    have := mul_le_mul_of_nonneg_right hb2 (by positivity : 0 ≤ Cs * nD * ‖hh'‖)
    linarith only [this, show Cs * b ^ 2 * (nD * ‖hh'‖) = b ^ 2 * (Cs * nD * ‖hh'‖) by ring,
      show Bq ^ 2 * gm ^ 2 * (Cs * nD * ‖hh'‖) = gm ^ 2 * (Cs * Bq ^ 2 * nD * ‖hh'‖) by ring]
  linarith only [r1, r2, r3, r4, r5,
    show gm * (n22 * (gm * ‖gg‖ + b * (nD * ‖hh‖))) = gm ^ 2 * (n22 * ‖gg‖)
      + gm * (n22 * (b * (nD * ‖hh‖))) by ring,
    show b * (nD * (b * (nΔ * ‖hh‖) + gm * (n12 * ‖gg‖) + b * (n12 * (nD * ‖hh‖)))) =
      b * (nD * (b * (nΔ * ‖hh‖))) + b * (nD * (gm * (n12 * ‖gg‖)))
        + b * (nD * (b * (n12 * (nD * ‖hh‖)))) by ring,
    show gm ^ 2 * ((Bq * n22 * nD + Bq ^ 2 * nD * nΔ + Bq ^ 2 * nD * n12 * nD) * ‖hh‖
        + (n22 + Bq * nD * n12) * ‖gg‖ + Ct * ‖gg'‖ + Cs * Bq ^ 2 * nD * ‖hh'‖) =
      gm ^ 2 * (Bq * n22 * nD * ‖hh‖) + gm ^ 2 * (Bq ^ 2 * nD * nΔ * ‖hh‖)
        + gm ^ 2 * (Bq ^ 2 * nD * n12 * nD * ‖hh‖) + gm ^ 2 * (n22 * ‖gg‖)
        + gm ^ 2 * (Bq * nD * n12 * ‖gg‖) + Ct * gm ^ 2 * ‖gg'‖
        + gm ^ 2 * (Cs * Bq ^ 2 * nD * ‖hh'‖) by ring]

lemma sq_add4_le' (x y z w : ℝ) : (x + y + z + w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z),
    sq_nonneg (y - w), sq_nonneg (z - w)]

/-- A pointwise bound by four norms gives a bound on the root mean square. -/
lemma rms_le_of_norm_le4 {d e₁ e₂ e₃ e₄ : ℕ} {f : Ω → E d} {u₁ : Ω → E e₁} {u₂ : Ω → E e₂}
    {u₃ : Ω → E e₃} {u₄ : Ω → E e₄} (hf : MemLp f 2 μ) (h₁ : MemLp u₁ 2 μ) (h₂ : MemLp u₂ 2 μ)
    (h₃ : MemLp u₃ 2 μ) (h₄ : MemLp u₄ 2 μ) {s a₁ a₂ a₃ a₄ : ℝ} (hs : 0 ≤ s) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄)
    (h : ∀ ω, ‖f ω‖ ≤ s * (a₁ * ‖u₁ ω‖ + a₂ * ‖u₂ ω‖ + a₃ * ‖u₃ ω‖ + a₄ * ‖u₄ ω‖)) :
    rms μ f ≤ 2 * s * (a₁ * rms μ u₁ + a₂ * rms μ u₂ + a₃ * rms μ u₃ + a₄ * rms μ u₄) := by
  have hpt : ∀ ω, ‖f ω‖ ^ 2 ≤ 4 * s ^ 2 * (a₁ ^ 2 * ‖u₁ ω‖ ^ 2 + a₂ ^ 2 * ‖u₂ ω‖ ^ 2
      + a₃ ^ 2 * ‖u₃ ω‖ ^ 2 + a₄ ^ 2 * ‖u₄ ω‖ ^ 2) := by
    intro ω
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (h ω) 2
    have h2 := sq_add4_le' (a₁ * ‖u₁ ω‖) (a₂ * ‖u₂ ω‖) (a₃ * ‖u₃ ω‖) (a₄ * ‖u₄ ω‖)
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
    calc ‖f ω‖ ^ 2 ≤ (s * (a₁ * ‖u₁ ω‖ + a₂ * ‖u₂ ω‖ + a₃ * ‖u₃ ω‖ + a₄ * ‖u₄ ω‖)) ^ 2 := h1
      _ = s ^ 2 * (a₁ * ‖u₁ ω‖ + a₂ * ‖u₂ ω‖ + a₃ * ‖u₃ ω‖ + a₄ * ‖u₄ ω‖) ^ 2 := by ring
      _ ≤ s ^ 2 * (4 * ((a₁ * ‖u₁ ω‖) ^ 2 + (a₂ * ‖u₂ ω‖) ^ 2 + (a₃ * ‖u₃ ω‖) ^ 2
          + (a₄ * ‖u₄ ω‖) ^ 2)) := h3
      _ = _ := by ring
  have i1 := (memLp_sq_integrable h₁).const_mul (a₁ ^ 2)
  have i2 := (memLp_sq_integrable h₂).const_mul (a₂ ^ 2)
  have i3 := (memLp_sq_integrable h₃).const_mul (a₃ ^ 2)
  have i4 := (memLp_sq_integrable h₄).const_mul (a₄ ^ 2)
  have i12 : Integrable (fun ω => a₁ ^ 2 * ‖u₁ ω‖ ^ 2 + a₂ ^ 2 * ‖u₂ ω‖ ^ 2) μ := i1.add i2
  have i123 : Integrable (fun ω => a₁ ^ 2 * ‖u₁ ω‖ ^ 2 + a₂ ^ 2 * ‖u₂ ω‖ ^ 2
      + a₃ ^ 2 * ‖u₃ ω‖ ^ 2) μ := i12.add i3
  have i1234 : Integrable (fun ω => a₁ ^ 2 * ‖u₁ ω‖ ^ 2 + a₂ ^ 2 * ‖u₂ ω‖ ^ 2
      + a₃ ^ 2 * ‖u₃ ω‖ ^ 2 + a₄ ^ 2 * ‖u₄ ω‖ ^ 2) μ := i123.add i4
  have hint := integral_mono (memLp_sq_integrable hf) (i1234.const_mul (4 * s ^ 2)) hpt
  rw [integral_const_mul, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at hint
  have r1 := Real.sq_sqrt (integral_norm_sq_nonneg (μ := μ) u₁)
  have r2 := Real.sq_sqrt (integral_norm_sq_nonneg (μ := μ) u₂)
  have r3 := Real.sq_sqrt (integral_norm_sq_nonneg (μ := μ) u₃)
  have r4 := Real.sq_sqrt (integral_norm_sq_nonneg (μ := μ) u₄)
  unfold rms
  refine Real.sqrt_le_iff.mpr ⟨by positivity, hint.trans ?_⟩
  have q1 := Real.sqrt_nonneg (∫ ω, ‖u₁ ω‖ ^ 2 ∂μ)
  have q2 := Real.sqrt_nonneg (∫ ω, ‖u₂ ω‖ ^ 2 ∂μ)
  have q3 := Real.sqrt_nonneg (∫ ω, ‖u₃ ω‖ ^ 2 ∂μ)
  have q4 := Real.sqrt_nonneg (∫ ω, ‖u₄ ω‖ ^ 2 ∂μ)
  set r₁ := √(∫ ω, ‖u₁ ω‖ ^ 2 ∂μ)
  set r₂ := √(∫ ω, ‖u₂ ω‖ ^ 2 ∂μ)
  set r₃ := √(∫ ω, ‖u₃ ω‖ ^ 2 ∂μ)
  set r₄ := √(∫ ω, ‖u₄ ω‖ ^ 2 ∂μ)
  rw [← r1, ← r2, ← r3, ← r4]
  have hc : 0 ≤ 4 * s ^ 2 * (2 * (a₁ * r₁) * (a₂ * r₂) + 2 * (a₁ * r₁) * (a₃ * r₃)
      + 2 * (a₁ * r₁) * (a₄ * r₄) + 2 * (a₂ * r₂) * (a₃ * r₃) + 2 * (a₂ * r₂) * (a₄ * r₄)
      + 2 * (a₃ * r₃) * (a₄ * r₄)) := by positivity
  have e : (2 * s * (a₁ * r₁ + a₂ * r₂ + a₃ * r₃ + a₄ * r₄)) ^ 2 =
      4 * s ^ 2 * (a₁ ^ 2 * r₁ ^ 2 + a₂ ^ 2 * r₂ ^ 2 + a₃ ^ 2 * r₃ ^ 2 + a₄ ^ 2 * r₄ ^ 2)
      + 4 * s ^ 2 * (2 * (a₁ * r₁) * (a₂ * r₂) + 2 * (a₁ * r₁) * (a₃ * r₃)
      + 2 * (a₁ * r₁) * (a₄ * r₄) + 2 * (a₂ * r₂) * (a₃ * r₃) + 2 * (a₂ * r₂) * (a₄ * r₄)
      + 2 * (a₃ * r₃) * (a₄ * r₄)) := by ring
  rw [e]
  linarith only [hc]

/-! ### Sizes of the pieces -/

lemma rms_le_sqrt_secondMoment {d : ℕ} {f : Ω → E d} (hf : MemLp f 2 μ) :
    rms μ f ≤ √(d * ‖secondMoment μ f‖) :=
  Real.sqrt_le_sqrt (integral_norm_sq_le hf)

/-- The root-mean-square sizes of the pieces of one step, in terms of
`t = √(1 + ‖X‖/β + ‖Z‖/β + ‖Y‖/γ)`. -/
lemma tts_sizes (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {xs : Ω → E d₁} {ys : Ω → E d₂} {b gm Bq cw cq : ℝ} (hb : 0 < b) (hgm : 0 < gm)
    (hBq : 0 ≤ Bq) (hbq : b ≤ Bq * gm) (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ)
    (hcw : cw = √2 * (‖matCLM Δ‖ * √d₁ * √Bq + ‖matCLM A₁₂‖ * √d₂))
    (hcq : cq = √2 * (‖matCLM A₂₂‖ * √d₂ + Bq * ‖matCLM D‖ * cw)) :
    let t := √(1 + ‖secondMoment μ xs‖ / b + ‖crossMoment μ xs ys‖ / b + ‖secondMoment μ ys‖ / gm)
    let w := fun ω => matCLM Δ (xs ω) + matCLM A₁₂ (ys ω)
    let q := fun ω => gm • matCLM A₂₂ (ys ω) + b • matCLM D (w ω)
    1 ≤ t ∧ rms μ xs ≤ √d₁ * √b * t ∧ rms μ ys ≤ √d₂ * √gm * t ∧ rms μ w ≤ cw * √gm * t ∧
    rms μ (fun ω => matCLM D (w ω)) ≤ ‖matCLM D‖ * (cw * √gm * t) ∧
    rms μ q ≤ cq * gm * √gm * t ∧
    rms μ (fun ω => xs ω - b • w ω) ≤ √2 * (√d₁ * √b * t + b * (cw * √gm * t)) ∧
    rms μ (fun ω => ys ω - q ω) ≤ √2 * (√d₂ * √gm * t + cq * gm * √gm * t) ∧
    ‖crossMoment μ xs ys‖ ≤ b * t ^ 2 := by
  intro t w q
  set X := ‖secondMoment μ xs‖
  set Z := ‖crossMoment μ xs ys‖
  set Y := ‖secondMoment μ ys‖
  have hX0 : 0 ≤ X := norm_nonneg _
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hn0 : 0 ≤ 1 + X / b + Z / b + Y / gm := by positivity
  have ht2 : t ^ 2 = 1 + X / b + Z / b + Y / gm := Real.sq_sqrt hn0
  have ht1 : 1 ≤ t := by
    refine Real.le_sqrt_of_sq_le ?_
    have : 0 ≤ X / b + Z / b + Y / gm := by positivity
    linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hXn : X ≤ b * t ^ 2 := by
    rw [ht2]
    have : X / b ≤ 1 + X / b + Z / b + Y / gm := by
      have : 0 ≤ Z / b + Y / gm := by positivity
      linarith
    calc X = b * (X / b) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hb.le
  have hZn : Z ≤ b * t ^ 2 := by
    rw [ht2]
    have : Z / b ≤ 1 + X / b + Z / b + Y / gm := by
      have : 0 ≤ X / b + Y / gm := by positivity
      linarith
    calc Z = b * (Z / b) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hb.le
  have hYn : Y ≤ gm * t ^ 2 := by
    rw [ht2]
    have : Y / gm ≤ 1 + X / b + Z / b + Y / gm := by
      have : 0 ≤ X / b + Z / b := by positivity
      linarith
    calc Y = gm * (Y / gm) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hgm.le
  have sq3 : ∀ {c u : ℝ}, 0 ≤ c → 0 ≤ u → √(c * (u * t ^ 2)) = √c * √u * t := by
    intro c u hc hu
    rw [Real.sqrt_mul hc, Real.sqrt_mul hu, Real.sqrt_sq ht0, mul_assoc]
  have hSx : rms μ xs ≤ √d₁ * √b * t := by
    refine (rms_le_sqrt_secondMoment hxsL).trans ?_
    rw [← sq3 (Nat.cast_nonneg d₁) hb.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hXn (Nat.cast_nonneg d₁))
  have hSy : rms μ ys ≤ √d₂ * √gm * t := by
    refine (rms_le_sqrt_secondMoment hysL).trans ?_
    rw [← sq3 (Nat.cast_nonneg d₂) hgm.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hYn (Nat.cast_nonneg d₂))
  have hsb : √b ≤ √Bq * √gm := by
    rw [← Real.sqrt_mul hBq]; exact Real.sqrt_le_sqrt hbq
  have nΔ := norm_nonneg (matCLM Δ)
  have n12 := norm_nonneg (matCLM A₁₂)
  have n22 := norm_nonneg (matCLM A₂₂)
  have nD := norm_nonneg (matCLM D)
  have hΔL : MemLp (fun ω => matCLM Δ (xs ω)) 2 μ := (matCLM Δ).comp_memLp' hxsL
  have hAL : MemLp (fun ω => matCLM A₁₂ (ys ω)) 2 μ := (matCLM A₁₂).comp_memLp' hysL
  have hwL : MemLp w 2 μ := hΔL.add hAL
  have hSw : rms μ w ≤ cw * √gm * t := by
    refine (rms_add_le hΔL hAL).trans ?_
    have h1 := rms_matCLM_le Δ hxsL (μ := μ)
    have h2 := rms_matCLM_le A₁₂ hysL (μ := μ)
    have h3 : √b * t ≤ √Bq * √gm * t := mul_le_mul_of_nonneg_right hsb ht0
    have e : cw * √gm * t = √2 * (‖matCLM Δ‖ * √d₁ * (√Bq * √gm * t)
        + ‖matCLM A₁₂‖ * (√d₂ * √gm * t)) := by rw [hcw]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h4 : ‖matCLM Δ‖ * rms μ xs ≤ ‖matCLM Δ‖ * √d₁ * (√Bq * √gm * t) := by
      calc ‖matCLM Δ‖ * rms μ xs ≤ ‖matCLM Δ‖ * (√d₁ * √b * t) := mul_le_mul_of_nonneg_left hSx nΔ
        _ = ‖matCLM Δ‖ * √d₁ * (√b * t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 := mul_le_mul_of_nonneg_left hSy n12
    linarith
  have hSDw : rms μ (fun ω => matCLM D (w ω)) ≤ ‖matCLM D‖ * (cw * √gm * t) :=
    (rms_matCLM_le D hwL).trans (mul_le_mul_of_nonneg_left hSw nD)
  have hcw0 : 0 ≤ cw := by rw [hcw]; positivity
  have hSq : rms μ q ≤ cq * gm * √gm * t := by
    have hgA : MemLp (fun ω => gm • matCLM A₂₂ (ys ω)) 2 μ := ((matCLM A₂₂).comp_memLp' hysL).const_smul gm
    have hbD : MemLp (fun ω => b • matCLM D (w ω)) 2 μ := ((matCLM D).comp_memLp' hwL).const_smul b
    refine (rms_add_le hgA hbD).trans ?_
    rw [rms_smul, rms_smul, abs_of_pos hgm, abs_of_pos hb]
    have h1 := rms_matCLM_le A₂₂ hysL (μ := μ)
    have e : cq * gm * √gm * t = √2 * (gm * (‖matCLM A₂₂‖ * (√d₂ * √gm * t))
        + Bq * gm * (‖matCLM D‖ * (cw * √gm * t))) := by rw [hcq]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h2 : gm * rms μ (fun ω => matCLM A₂₂ (ys ω)) ≤ gm * (‖matCLM A₂₂‖ * (√d₂ * √gm * t)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hSy n22)) hgm.le
    have h3 : b * rms μ (fun ω => matCLM D (w ω)) ≤ Bq * gm * (‖matCLM D‖ * (cw * √gm * t)) :=
      mul_le_mul hbq hSDw (rms_nonneg _) (by positivity)
    linarith
  have hSa : rms μ (fun ω => xs ω - b • w ω) ≤ √2 * (√d₁ * √b * t + b * (cw * √gm * t)) := by
    have hbw : MemLp (fun ω => b • w ω) 2 μ := hwL.const_smul b
    refine (rms_sub_le hxsL hbw).trans ?_
    rw [rms_smul, abs_of_pos hb]
    refine mul_le_mul_of_nonneg_left (add_le_add hSx (mul_le_mul_of_nonneg_left hSw hb.le))
      (Real.sqrt_nonneg _)
  have hqL : MemLp q 2 μ := (((matCLM A₂₂).comp_memLp' hysL).const_smul gm).add
    (((matCLM D).comp_memLp' hwL).const_smul b)
  have hSay : rms μ (fun ω => ys ω - q ω) ≤ √2 * (√d₂ * √gm * t + cq * gm * √gm * t) :=
    (rms_sub_le hysL hqL).trans (mul_le_mul_of_nonneg_left (add_le_add hSy hSq) (Real.sqrt_nonneg _))
  exact ⟨ht1, hSx, hSy, hSw, hSDw, hSq, hSa, hSay, hZn⟩

/-! ### The remainders of one step -/

/-- The three parts of the vanishing factor of the remainders. -/
noncomputable def ttsEps₁ (b gm G d₁' cw Kx mM : ℝ) : ℝ :=
  cw ^ 2 * gm + G + 2 * (√2 * Kx * (d₁' * (gm / √b) + cw * gm * √gm) + mM * Kx * gm
    + Kx ^ 2 * gm ^ 2)

noncomputable def ttsEps₂ (b gm G d₁' d₂' cw cq Kx Ky mM mM' nD LΔ : ℝ) : ℝ :=
  d₁' * nD * cw * (√b / √gm) + LΔ * (b / gm) + cw * cq * gm + G + (b / gm) * (nD * mM ^ 2)
    + √2 * Ky * (d₁' * (gm / √b) + cw * √gm * gm) + mM * Ky * gm + Kx * Ky * gm ^ 2
    + Kx * √2 * (d₂' * √gm + cq * gm * √gm) + Kx * √2 * (gm * mM' + b * (nD * mM))

noncomputable def ttsEps₃ (b gm G d₂' cw cq Ky mM mM' nD : ℝ) : ℝ :=
  2 * d₂' * nD * cw * (b / gm) + cq ^ 2 * gm + G + 2 * (b / gm) * (mM' * (nD * mM))
    + (b / gm) ^ 2 * (nD * mM) ^ 2 + 2 * (√2 * Ky * (d₂' * √gm + cq * gm * √gm))
    + 2 * (√2 * Ky * (gm * mM' + b * (nD * mM))) + Ky ^ 2 * gm ^ 2

/-! ### Bookkeeping when all sizes grow like `t` -/

/-- Square roots of the step sizes. -/
lemma sqrt_facts {b : ℝ} (hb : 0 < b) : 0 < √b ∧ √b ^ 2 = b :=
  ⟨Real.sqrt_pos.mpr hb, Real.sq_sqrt hb.le⟩

/-- `tts_R1_le` with sizes of the martingale part and the remainder growing like `t`. -/
lemma tts_R1_le' {b gm t d₁' cw Kx mM G Gd Sw Sa SbM Sc : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (ht : 1 ≤ t) (hd : 0 ≤ d₁') (hcw : 0 ≤ cw) (hK : 0 ≤ Kx)
    (hm : 0 ≤ mM) (_hG : 0 ≤ G) (hSw0 : 0 ≤ Sw) (hSc0 : 0 ≤ Sc)
    (hSw : Sw ≤ cw * √gm * t) (hSa : Sa ≤ √2 * (d₁' * √b * t + b * (cw * √gm * t)))
    (hSbM : SbM ≤ b * mM * t) (hSc : Sc ≤ Kx * b * gm * t) (hGd : Gd ≤ G * t ^ 2) :
    b ^ 2 * Sw ^ 2 + b ^ 2 * Gd + ((Sa + SbM + Sc) * Sc + Sc * (Sa + SbM)) ≤
      ttsEps₁ b gm G d₁' cw Kx mM * b ^ 2 * t ^ 2 := by
  obtain ⟨sb0, sb2⟩ := sqrt_facts hb
  obtain ⟨sg0, sg2⟩ := sqrt_facts hgm
  set sb := √b
  set sg := √gm
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have s2 := Real.sqrt_nonneg (2 : ℝ)
  have e1 : b ^ 2 * Sw ^ 2 ≤ cw ^ 2 * gm * b ^ 2 * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSw0 hSw 2) (sq_nonneg b)
    have e : b ^ 2 * (cw * sg * t) ^ 2 = cw ^ 2 * gm * b ^ 2 * t ^ 2 := by rw [← sg2]; ring
    linarith only [h, e]
  have e2 : b ^ 2 * Gd ≤ G * b ^ 2 * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hGd (sq_nonneg b)
    linarith only [this, show b ^ 2 * (G * t ^ 2) = G * b ^ 2 * t ^ 2 by ring]
  have e3 : Sa * Sc ≤ √2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) * b ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSa hSc hSc0 (by positivity)
    have e : √2 * (d₁' * sb * t + b * (cw * sg * t)) * (Kx * b * gm * t) =
        √2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) * b ^ 2 * t ^ 2 := by
      rw [← sb2]; field_simp; ring
    linarith only [h1, e]
  have e4 : SbM * Sc ≤ mM * Kx * gm * b ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSbM hSc hSc0 (by positivity)
    linarith only [h1, show b * mM * t * (Kx * b * gm * t) = mM * Kx * gm * b ^ 2 * t ^ 2 by ring]
  have e5 : Sc * Sc ≤ Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSc hSc hSc0 (by positivity)
    linarith only [h1, show Kx * b * gm * t * (Kx * b * gm * t) = Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2
      by ring]
  have hpos : 0 ≤ Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2 := by positivity
  have e : ttsEps₁ b gm G d₁' cw Kx mM * b ^ 2 * t ^ 2 =
      cw ^ 2 * gm * b ^ 2 * t ^ 2 + G * b ^ 2 * t ^ 2
        + 2 * (√2 * Kx * (d₁' * (gm / sb) + cw * gm * sg) * b ^ 2 * t ^ 2)
        + 2 * (mM * Kx * gm * b ^ 2 * t ^ 2) + 2 * (Kx ^ 2 * gm ^ 2 * b ^ 2 * t ^ 2) := by
    simp only [ttsEps₁]; ring
  rw [e]
  linarith only [e1, e2, e3, e4, e5, hpos,
    show (Sa + SbM + Sc) * Sc + Sc * (Sa + SbM) = 2 * (Sa * Sc) + 2 * (SbM * Sc) + Sc * Sc by ring]

/-- `tts_R2_le` with sizes growing like `t`. -/
lemma tts_R2_le' {b gm t d₁' d₂' cw cq Kx Ky mM mM' nD LΔ G Gd Z Sx SDw Sw Sq SM SDM Sa SbM Sc
      Scy Say Sbv : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (ht : 1 ≤ t) (hd₁ : 0 ≤ d₁') (_hd₂ : 0 ≤ d₂') (hcw : 0 ≤ cw)
    (_hcq : 0 ≤ cq) (hKx : 0 ≤ Kx) (_hKy : 0 ≤ Ky) (hm : 0 ≤ mM) (_hm' : 0 ≤ mM') (_hnD : 0 ≤ nD)
    (hLΔ : 0 ≤ LΔ) (_hG : 0 ≤ G)
    (hSDw0 : 0 ≤ SDw) (hSq0 : 0 ≤ Sq) (hSDM0 : 0 ≤ SDM) (_hSc0 : 0 ≤ Sc) (hScy0 : 0 ≤ Scy)
    (hSay0 : 0 ≤ Say) (hSbv0 : 0 ≤ Sbv)
    (hSx : Sx ≤ d₁' * √b * t) (hSDw : SDw ≤ nD * (cw * √gm * t)) (hSw : Sw ≤ cw * √gm * t)
    (hZ : Z ≤ b * t ^ 2) (hSq : Sq ≤ cq * gm * √gm * t) (hSM : SM ≤ mM * t)
    (hSDM : SDM ≤ nD * mM * t)
    (hSa : Sa ≤ √2 * (d₁' * √b * t + b * (cw * √gm * t))) (hSbM : SbM ≤ b * mM * t)
    (hSc : Sc ≤ Kx * b * gm * t) (hScy : Scy ≤ Ky * gm ^ 2 * t)
    (hSay : Say ≤ √2 * (d₂' * √gm * t + cq * gm * √gm * t))
    (hSbv : Sbv ≤ √2 * (gm * mM' + b * (nD * mM)) * t) (hGd : Gd ≤ G * t ^ 2) :
    b * (Sx * SDw) + b * (LΔ * Z) + b * (Sw * Sq) + b * gm * Gd + b ^ 2 * (SM * SDM)
      + ((Sa + SbM + Sc) * Scy + Sc * (Say + Sbv)) ≤
      ttsEps₂ b gm G d₁' d₂' cw cq Kx Ky mM mM' nD LΔ * (b * gm) * t ^ 2 := by
  obtain ⟨sb0, sb2⟩ := sqrt_facts hb
  obtain ⟨sg0, sg2⟩ := sqrt_facts hgm
  set sb := √b
  set sg := √gm
  have hbne : sb ≠ 0 := sb0.ne'
  have hgne : sg ≠ 0 := sg0.ne'
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have s2 := Real.sqrt_nonneg (2 : ℝ)
  have u1 : b * (Sx * SDw) ≤ d₁' * nD * cw * (sb / sg) * (b * gm) * t ^ 2 := by
    have hSx0' : 0 ≤ d₁' * sb * t := by positivity
    have h1 : Sx * SDw ≤ d₁' * sb * t * (nD * (cw * sg * t)) :=
      (mul_le_mul_of_nonneg_right hSx hSDw0).trans (mul_le_mul_of_nonneg_left hSDw hSx0')
    have h2 := mul_le_mul_of_nonneg_left h1 hb.le
    have e : b * (d₁' * sb * t * (nD * (cw * sg * t))) =
        d₁' * nD * cw * (sb / sg) * (b * gm) * t ^ 2 := by
      rw [← sg2]; field_simp; ring
    linarith only [h2, e]
  have u2 : b * (LΔ * Z) ≤ LΔ * (b / gm) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hLΔ) hb.le
    have e : b * (LΔ * (b * t ^ 2)) = LΔ * (b / gm) * (b * gm) * t ^ 2 := by field_simp; ring
    linarith only [h1, e]
  have u3 : b * (Sw * Sq) ≤ cw * cq * gm * (b * gm) * t ^ 2 := by
    have h1 : Sw * Sq ≤ cw * sg * t * (cq * gm * sg * t) :=
      (mul_le_mul_of_nonneg_right hSw hSq0).trans (mul_le_mul_of_nonneg_left hSq (by positivity))
    have h2 := mul_le_mul_of_nonneg_left h1 hb.le
    have e : b * (cw * sg * t * (cq * gm * sg * t)) = cw * cq * gm * (b * gm) * t ^ 2 := by
      rw [← sg2]; ring
    linarith only [h2, e]
  have u4 : b * gm * Gd ≤ G * (b * gm) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hGd (mul_nonneg hb.le hgm.le)
    linarith only [this, show b * gm * (G * t ^ 2) = G * (b * gm) * t ^ 2 by ring]
  have u5 : b ^ 2 * (SM * SDM) ≤ (b / gm) * (nD * mM ^ 2) * (b * gm) * t ^ 2 := by
    have h1 : SM * SDM ≤ mM * t * (nD * mM * t) :=
      (mul_le_mul_of_nonneg_right hSM hSDM0).trans (mul_le_mul_of_nonneg_left hSDM (by positivity))
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg b)
    have e : b ^ 2 * (mM * t * (nD * mM * t)) = (b / gm) * (nD * mM ^ 2) * (b * gm) * t ^ 2 := by
      field_simp; ring
    linarith only [h2, e]
  have u6 : Sa * Scy ≤ √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) * (b * gm) * t ^ 2 := by
    have h1 : Sa * Scy ≤ √2 * (d₁' * sb * t + b * (cw * sg * t)) * (Ky * gm ^ 2 * t) :=
      (mul_le_mul_of_nonneg_right hSa hScy0).trans (mul_le_mul_of_nonneg_left hScy (by positivity))
    have e : √2 * (d₁' * sb * t + b * (cw * sg * t)) * (Ky * gm ^ 2 * t) =
        √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) * (b * gm) * t ^ 2 := by
      rw [← sb2]; field_simp; ring
    linarith only [h1, e]
  have u7 : SbM * Scy ≤ mM * Ky * gm * (b * gm) * t ^ 2 := by
    have h1 : SbM * Scy ≤ b * mM * t * (Ky * gm ^ 2 * t) :=
      (mul_le_mul_of_nonneg_right hSbM hScy0).trans (mul_le_mul_of_nonneg_left hScy (by positivity))
    linarith only [h1, show b * mM * t * (Ky * gm ^ 2 * t) = mM * Ky * gm * (b * gm) * t ^ 2 by ring]
  have u8 : Sc * Scy ≤ Kx * Ky * gm ^ 2 * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSc hScy hScy0 (by positivity)
    linarith only [h1, show Kx * b * gm * t * (Ky * gm ^ 2 * t) = Kx * Ky * gm ^ 2 * (b * gm) * t ^ 2
      by ring]
  have u9 : Sc * Say ≤ Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSc hSay hSay0 (by positivity)
    linarith only [h1, show Kx * b * gm * t * (√2 * (d₂' * sg * t + cq * gm * sg * t))
      = Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm) * t ^ 2 by ring]
  have u10 : Sc * Sbv ≤ Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm) * t ^ 2 := by
    have h1 := mul_le_mul hSc hSbv hSbv0 (by positivity)
    linarith only [h1, show Kx * b * gm * t * (√2 * (gm * mM' + b * (nD * mM)) * t)
      = Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm) * t ^ 2 by ring]
  have e : ttsEps₂ b gm G d₁' d₂' cw cq Kx Ky mM mM' nD LΔ * (b * gm) * t ^ 2 =
      d₁' * nD * cw * (sb / sg) * (b * gm) * t ^ 2 + LΔ * (b / gm) * (b * gm) * t ^ 2
        + cw * cq * gm * (b * gm) * t ^ 2 + G * (b * gm) * t ^ 2
        + (b / gm) * (nD * mM ^ 2) * (b * gm) * t ^ 2
        + √2 * Ky * (d₁' * (gm / sb) + cw * sg * gm) * (b * gm) * t ^ 2
        + mM * Ky * gm * (b * gm) * t ^ 2 + Kx * Ky * gm ^ 2 * (b * gm) * t ^ 2
        + Kx * √2 * (d₂' * sg + cq * gm * sg) * (b * gm) * t ^ 2
        + Kx * √2 * (gm * mM' + b * (nD * mM)) * (b * gm) * t ^ 2 := by
    simp only [ttsEps₂]; ring
  rw [e]
  linarith only [u1, u2, u3, u4, u5, u6, u7, u8, u9, u10,
    show (Sa + SbM + Sc) * Scy + Sc * (Say + Sbv) = Sa * Scy + SbM * Scy + Sc * Scy + Sc * Say
      + Sc * Sbv by ring]

/-- `tts_R3_le` with sizes growing like `t`. -/
lemma tts_R3_le' {b gm t d₂' cw cq Ky mM mM' nD G Gd Sy SDw Sq SM' SDM Scy Say Sbv : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (ht : 1 ≤ t) (hd₂ : 0 ≤ d₂') (_hcw : 0 ≤ cw)
    (hcq : 0 ≤ cq) (hKy : 0 ≤ Ky) (hm : 0 ≤ mM) (hm' : 0 ≤ mM') (hnD : 0 ≤ nD) (_hG : 0 ≤ G)
    (hSDw0 : 0 ≤ SDw) (hSq0 : 0 ≤ Sq) (hSDM0 : 0 ≤ SDM) (hScy0 : 0 ≤ Scy) (_hSay0 : 0 ≤ Say)
    (_hSbv0 : 0 ≤ Sbv)
    (hSy : Sy ≤ d₂' * √gm * t) (hSDw : SDw ≤ nD * (cw * √gm * t)) (hSq : Sq ≤ cq * gm * √gm * t)
    (hSM' : SM' ≤ mM' * t) (hSDM : SDM ≤ nD * mM * t) (hScy : Scy ≤ Ky * gm ^ 2 * t)
    (hSay : Say ≤ √2 * (d₂' * √gm * t + cq * gm * √gm * t))
    (hSbv : Sbv ≤ √2 * (gm * mM' + b * (nD * mM)) * t) (hGd : Gd ≤ G * t ^ 2) :
    b * (2 * (Sy * SDw)) + Sq ^ 2 + gm ^ 2 * Gd + gm * b * (2 * (SM' * SDM)) + b ^ 2 * SDM ^ 2
      + ((Say + Sbv + Scy) * Scy + Scy * (Say + Sbv)) ≤
      ttsEps₃ b gm G d₂' cw cq Ky mM mM' nD * gm ^ 2 * t ^ 2 := by
  obtain ⟨sg0, sg2⟩ := sqrt_facts hgm
  set sg := √gm
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have s2 := Real.sqrt_nonneg (2 : ℝ)
  have u1 : b * (2 * (Sy * SDw)) ≤ 2 * d₂' * nD * cw * (b / gm) * gm ^ 2 * t ^ 2 := by
    have h1 : Sy * SDw ≤ d₂' * sg * t * (nD * (cw * sg * t)) :=
      (mul_le_mul_of_nonneg_right hSy hSDw0).trans (mul_le_mul_of_nonneg_left hSDw (by positivity))
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 zero_le_two) hb.le
    have e : b * (2 * (d₂' * sg * t * (nD * (cw * sg * t)))) =
        2 * d₂' * nD * cw * (b / gm) * gm ^ 2 * t ^ 2 := by
      rw [← sg2]; field_simp; ring
    linarith only [h2, e]
  have u2 : Sq ^ 2 ≤ cq ^ 2 * gm * gm ^ 2 * t ^ 2 := by
    have h1 := pow_le_pow_left₀ hSq0 hSq 2
    have e : (cq * gm * sg * t) ^ 2 = cq ^ 2 * gm * gm ^ 2 * t ^ 2 := by rw [← sg2]; ring
    linarith only [h1, e]
  have u3 : gm ^ 2 * Gd ≤ G * gm ^ 2 * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hGd (sq_nonneg gm)
    linarith only [this, show gm ^ 2 * (G * t ^ 2) = G * gm ^ 2 * t ^ 2 by ring]
  have u4 : gm * b * (2 * (SM' * SDM)) ≤ 2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2 * t ^ 2 := by
    have h1 : SM' * SDM ≤ mM' * t * (nD * mM * t) :=
      (mul_le_mul_of_nonneg_right hSM' hSDM0).trans (mul_le_mul_of_nonneg_left hSDM (by positivity))
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 zero_le_two)
      (mul_nonneg hgm.le hb.le)
    have e : gm * b * (2 * (mM' * t * (nD * mM * t))) =
        2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2 * t ^ 2 := by field_simp; ring
    linarith only [h2, e]
  have u5 : b ^ 2 * SDM ^ 2 ≤ (b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSDM0 hSDM 2) (sq_nonneg b)
    have e : b ^ 2 * (nD * mM * t) ^ 2 = (b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2 * t ^ 2 := by
      field_simp; ring
    linarith only [h1, e]
  have u6 : Say * Scy ≤ √2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSay hScy hScy0 (by positivity)
    linarith only [h1, show √2 * (d₂' * sg * t + cq * gm * sg * t) * (Ky * gm ^ 2 * t)
      = √2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2 * t ^ 2 by ring]
  have u7 : Sbv * Scy ≤ √2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hSbv hScy hScy0 (by positivity)
    linarith only [h1, show √2 * (gm * mM' + b * (nD * mM)) * t * (Ky * gm ^ 2 * t)
      = √2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2 * t ^ 2 by ring]
  have u8 : Scy * Scy ≤ Ky ^ 2 * gm ^ 2 * gm ^ 2 * t ^ 2 := by
    have h1 := mul_le_mul hScy hScy hScy0 (by positivity)
    linarith only [h1, show Ky * gm ^ 2 * t * (Ky * gm ^ 2 * t) = Ky ^ 2 * gm ^ 2 * gm ^ 2 * t ^ 2
      by ring]
  have e : ttsEps₃ b gm G d₂' cw cq Ky mM mM' nD * gm ^ 2 * t ^ 2 =
      2 * d₂' * nD * cw * (b / gm) * gm ^ 2 * t ^ 2 + cq ^ 2 * gm * gm ^ 2 * t ^ 2
        + G * gm ^ 2 * t ^ 2 + 2 * (b / gm) * (mM' * (nD * mM)) * gm ^ 2 * t ^ 2
        + (b / gm) ^ 2 * (nD * mM) ^ 2 * gm ^ 2 * t ^ 2
        + 2 * (√2 * Ky * (d₂' * sg + cq * gm * sg) * gm ^ 2 * t ^ 2)
        + 2 * (√2 * Ky * (gm * mM' + b * (nD * mM)) * gm ^ 2 * t ^ 2)
        + Ky ^ 2 * gm ^ 2 * gm ^ 2 * t ^ 2 := by
    simp only [ttsEps₃]; ring
  rw [e]
  linarith only [u1, u2, u3, u4, u5, u6, u7, u8,
    show (Say + Sbv + Scy) * Scy + Scy * (Say + Sbv) = 2 * (Say * Scy) + 2 * (Sbv * Scy)
      + Scy * Scy by ring]

set_option maxHeartbeats 2000000 in
/-- The general form of one step: arbitrary martingale parts `m, m'` and remainders `c, c'`
whose sizes and covariance errors grow at most like `t` and `t²`. -/
theorem tts_remainder_step_gen [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {xs xs' m cx : Ω → E d₁} {ys ys' m' cy : Ω → E d₂}
    {b gm Bq cw cq Kx Ky mM mM' G₁ G₂ G₃ : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (hBq : 0 ≤ Bq) (hbq : b ≤ Bq * gm)
    (hxs : StronglyMeasurable[ℱ] xs) (hys : StronglyMeasurable[ℱ] ys)
    (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ) (hmL : MemLp m 2 μ) (hm'L : MemLp m' 2 μ)
    (hcxL : MemLp cx 2 μ) (hcyL : MemLp cy 2 μ)
    (hmart : ∀ j, μ[fun ω => m ω j | ℱ] =ᵐ[μ] 0) (hmart' : ∀ j, μ[fun ω => m' ω j | ℱ] =ᵐ[μ] 0)
    (hmM : 0 ≤ mM) (hmM' : 0 ≤ mM') (hKx : 0 ≤ Kx) (hKy : 0 ≤ Ky)
    (hG₁ : 0 ≤ G₁) (hG₂ : 0 ≤ G₂) (hG₃ : 0 ≤ G₃)
    (hcw : cw = √2 * (‖matCLM Δ‖ * √d₁ * √Bq + ‖matCLM A₁₂‖ * √d₂))
    (hcq : cq = √2 * (‖matCLM A₂₂‖ * √d₂ + Bq * ‖matCLM D‖ * cw))
    (hxs' : ∀ ω, xs' ω = (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • m ω + cx ω)
    (hys' : ∀ ω, ys' ω = (ys ω - (gm • matCLM A₂₂ (ys ω)
        + b • matCLM D (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))))
      + (gm • m' ω + b • matCLM D (m ω)) + cy ω)
    (Γ₁ : Mat d₁) (Γ₂ : Rect d₁ d₂) (Γ₃ : Mat d₂) :
    let n := 1 + ‖secondMoment μ xs‖ / b + ‖crossMoment μ xs ys‖ / b + ‖secondMoment μ ys‖ / gm
    rms μ m ≤ mM * √n → rms μ m' ≤ mM' * √n → rms μ cx ≤ Kx * b * gm * √n →
    rms μ cy ≤ Ky * gm ^ 2 * √n → ‖secondMoment μ m - Γ₁‖ ≤ G₁ * n →
    ‖crossMoment μ m m' - Γ₂‖ ≤ G₂ * n → ‖secondMoment μ m' - Γ₃‖ ≤ G₃ * n →
    ‖secondMoment μ xs' - (secondMoment μ xs - b • (lyapOp Δ (secondMoment μ xs)
        + coupleCLM A₁₂ (crossMoment μ xs ys)) + b ^ 2 • Γ₁)‖ ≤
      ttsEps₁ b gm G₁ √d₁ cw Kx mM * b ^ 2 * n ∧
    ‖crossMoment μ xs' ys' - (crossMoment μ xs ys - gm • rmul A₂₂ (crossMoment μ xs ys)
        - b • lmul A₁₂ (secondMoment μ ys) + (b * gm) • Γ₂)‖ ≤
      ttsEps₂ b gm G₂ √d₁ √d₂ cw cq Kx Ky mM mM' ‖matCLM D‖
        ‖(lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * (b * gm) * n ∧
    ‖secondMoment μ ys' - (secondMoment μ ys - gm • lyapOp A₂₂ (secondMoment μ ys)
        + gm ^ 2 • Γ₃)‖ ≤
      ttsEps₃ b gm G₃ √d₂ cw cq Ky mM mM' ‖matCLM D‖ * gm ^ 2 * n := by
  intro n rm rm' rcx rcy dG₁ dG₂ dG₃
  obtain ⟨ht1, hSx, hSy, hSw, hSDw, hSq, hSa, hSay, hZn⟩ :=
    tts_sizes (μ := μ) Δ A₁₂ A₂₂ D hb hgm hBq hbq hxsL hysL hcw hcq
  set t := √n with ht_def
  have hn0 : 0 ≤ n := by simp only [n]; positivity
  have ht2 : t ^ 2 = n := Real.sq_sqrt hn0
  rw [← ht2] at dG₁ dG₂ dG₃ ⊢
  have nD := norm_nonneg (matCLM D)
  have hcw0 : 0 ≤ cw := by rw [hcw]; positivity
  have hcq0 : 0 ≤ cq := by rw [hcq]; positivity
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hDmL : MemLp (fun ω => matCLM D (m ω)) 2 μ := (matCLM D).comp_memLp' hmL
  have hSDM : rms μ (fun ω => matCLM D (m ω)) ≤ ‖matCLM D‖ * mM * t := by
    refine (rms_matCLM_le D hmL).trans ?_
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left rm nD
  have hSbM : rms μ (fun ω => b • m ω) ≤ b * mM * t := by
    rw [rms_smul, abs_of_pos hb, mul_assoc]; exact mul_le_mul_of_nonneg_left rm hb.le
  have hSbv : rms μ (fun ω => gm • m' ω + b • matCLM D (m ω)) ≤
      √2 * (gm * mM' + b * (‖matCLM D‖ * mM)) * t := by
    have hgm' : MemLp (fun ω => gm • m' ω) 2 μ := hm'L.const_smul gm
    have hbDm : MemLp (fun ω => b • matCLM D (m ω)) 2 μ := hDmL.const_smul b
    refine (rms_add_le hgm' hbDm).trans ?_
    rw [rms_smul, rms_smul, abs_of_pos hgm, abs_of_pos hb]
    have h1 := mul_le_mul_of_nonneg_left rm' hgm.le
    have h2 := mul_le_mul_of_nonneg_left hSDM hb.le
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg 2)
    linarith only [this, show √2 * (gm * (mM' * t) + b * (‖matCLM D‖ * mM * t)) =
      √2 * (gm * mM' + b * (‖matCLM D‖ * mM)) * t by ring]
  have exs : xs' = fun ω => (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • m ω + cx ω :=
    funext hxs'
  have eys : ys' = fun ω => (ys ω - (gm • matCLM A₂₂ (ys ω)
      + b • matCLM D (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))))
      + (gm • m' ω + b • matCLM D (m ω)) + cy ω := funext hys'
  have sX := tts_step_X (μ := μ) (b := b) hℱ Δ A₁₂ hxs hys hxsL hysL hmL hcxL hmart Γ₁
  have sZ := tts_step_Z (μ := μ) hℱ Δ A₁₂ A₂₂ D hb.le hgm.le hxs hys hxsL hysL hmL hm'L hcxL hcyL
    hmart hmart' Γ₂
  have sY := tts_step_Y (μ := μ) hℱ Δ A₁₂ A₂₂ D hb.le hgm.le hxs hys hxsL hysL hmL hm'L hcyL
    hmart hmart' Γ₃
  dsimp only at sZ sY
  rw [exs, eys]
  have d1 := Real.sqrt_nonneg (d₁ : ℝ)
  have d2 := Real.sqrt_nonneg (d₂ : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · exact sX.trans (tts_R1_le' hb hgm ht1 d1 hcw0 hKx hmM hG₁ (rms_nonneg _) (rms_nonneg _)
      hSw hSa hSbM rcx dG₁)
  · have hL : ‖lmul Δ (crossMoment μ xs ys)‖ ≤
        ‖(lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * ‖crossMoment μ xs ys‖ := (lmul Δ).le_opNorm _
    have := tts_R2_le' hb hgm ht1 d1 d2 hcw0 hcq0 hKx hKy hmM hmM' nD
      (norm_nonneg (lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)) hG₂
      (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _)
      (rms_nonneg _) (rms_nonneg _) hSx hSDw hSw hZn hSq rm hSDM hSa hSbM rcx rcy hSay hSbv dG₂
    refine sZ.trans (le_trans ?_ this)
    have := mul_le_mul_of_nonneg_left hL hb.le
    linarith
  · exact sY.trans (tts_R3_le' hb hgm ht1 d2 hcw0 hcq0 hKy hmM hmM' nD hG₃
      (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _)
      hSy hSDw hSq rm' hSDM rcy hSay hSbv dG₃)

set_option maxHeartbeats 2000000 in
/-- Lemma 3.2 of the write-up, for one step: the three remainders are bounded by the
vanishing factors `ttsEps₁`, `ttsEps₂`, `ttsEps₃` times `β² n`, `β γ n`, `γ² n`. -/
theorem tts_remainder_step [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {xs xs' M h h' : Ω → E d₁} {ys ys' M' g g' : Ω → E d₂}
    {b b' gm gm' Bq Cs Ct mh mg mM mM' cw cq Kx Ky : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (hBq : 0 ≤ Bq) (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hbq : b ≤ Bq * gm) (hCs : |b' - b| ≤ Cs * b ^ 2) (hCt : |gm' - gm| ≤ Ct * gm ^ 2)
    (hxs : StronglyMeasurable[ℱ] xs) (hys : StronglyMeasurable[ℱ] ys)
    (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ) (hML : MemLp M 2 μ) (hM'L : MemLp M' 2 μ)
    (hhL : MemLp h 2 μ) (hh'L : MemLp h' 2 μ) (hgL : MemLp g 2 μ) (hg'L : MemLp g' 2 μ)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ] =ᵐ[μ] 0) (hmart' : ∀ j, μ[fun ω => M' ω j | ℱ] =ᵐ[μ] 0)
    (hmh : 0 ≤ mh) (hmg : 0 ≤ mg) (hmM : 0 ≤ mM) (hmM' : 0 ≤ mM')
    (rh : rms μ h ≤ mh) (rh' : rms μ h' ≤ mh) (rg : rms μ g ≤ mg) (rg' : rms μ g' ≤ mg)
    (rM : rms μ M ≤ mM) (rM' : rms μ M' ≤ mM')
    (hcw : cw = √2 * (‖matCLM Δ‖ * √d₁ * √Bq + ‖matCLM A₁₂‖ * √d₂))
    (hcq : cq = √2 * (‖matCLM A₂₂‖ * √d₂ + Bq * ‖matCLM D‖ * cw))
    (hKx : Kx = 2 * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * mh
      + ‖matCLM A₁₂‖ * mg + Cs * Bq * mh))
    (hKy : Ky = 2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖) * mh
        + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * mg + Ct * mg
        + Cs * Bq ^ 2 * ‖matCLM D‖ * mh))
    (hxs' : ∀ ω, xs' ω = (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • M ω
      + (b • (b • matCLM Δ (h ω) + gm • matCLM A₁₂ (g ω) + b • matCLM A₁₂ (matCLM D (h ω)))
        + (b' - b) • h' ω))
    (hys' : ∀ ω, ys' ω = (ys ω - (gm • matCLM A₂₂ (ys ω)
        + b • matCLM D (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))))
      + (gm • M' ω + b • matCLM D (M ω))
      + (gm • matCLM A₂₂ (gm • g ω + b • matCLM D (h ω))
        + b • matCLM D (b • matCLM Δ (h ω) + gm • matCLM A₁₂ (g ω) + b • matCLM A₁₂ (matCLM D (h ω)))
        + (gm' - gm) • g' ω + (b' - b) • matCLM D (h' ω)))
    (Γ₁ : Mat d₁) (Γ₂ : Rect d₁ d₂) (Γ₃ : Mat d₂) :
    let n := 1 + ‖secondMoment μ xs‖ / b + ‖crossMoment μ xs ys‖ / b + ‖secondMoment μ ys‖ / gm
    ‖secondMoment μ xs' - (secondMoment μ xs - b • (lyapOp Δ (secondMoment μ xs)
        + coupleCLM A₁₂ (crossMoment μ xs ys)) + b ^ 2 • Γ₁)‖ ≤
      ttsEps₁ b gm ‖secondMoment μ M - Γ₁‖ √d₁ cw Kx mM * b ^ 2 * n ∧
    ‖crossMoment μ xs' ys' - (crossMoment μ xs ys - gm • rmul A₂₂ (crossMoment μ xs ys)
        - b • lmul A₁₂ (secondMoment μ ys) + (b * gm) • Γ₂)‖ ≤
      ttsEps₂ b gm ‖crossMoment μ M M' - Γ₂‖ √d₁ √d₂ cw cq Kx Ky mM mM' ‖matCLM D‖
        ‖(lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * (b * gm) * n ∧
    ‖secondMoment μ ys' - (secondMoment μ ys - gm • lyapOp A₂₂ (secondMoment μ ys)
        + gm ^ 2 • Γ₃)‖ ≤
      ttsEps₃ b gm ‖secondMoment μ M' - Γ₃‖ √d₂ cw cq Ky mM mM' ‖matCLM D‖ * gm ^ 2 * n := by
  intro n
  obtain ⟨ht1, hSx, hSy, hSw, hSDw, hSq, hSa, hSay, hZn⟩ :=
    tts_sizes (μ := μ) Δ A₁₂ A₂₂ D hb hgm hBq hbq hxsL hysL hcw hcq
  set t := √n with ht_def
  have ht2 : t ^ 2 = n := Real.sq_sqrt (by
    have : 1 ≤ t := ht1
    have h0 : 0 ≤ n := by
      simp only [n]; positivity
    exact h0)
  have nΔ := norm_nonneg (matCLM Δ)
  have n12 := norm_nonneg (matCLM A₁₂)
  have n22 := norm_nonneg (matCLM A₂₂)
  have nD := norm_nonneg (matCLM D)
  have hcw0 : 0 ≤ cw := by rw [hcw]; positivity
  have hcq0 : 0 ≤ cq := by rw [hcq]; positivity
  have hKx0 : 0 ≤ Kx := by rw [hKx]; positivity
  have hKy0 : 0 ≤ Ky := by rw [hKy]; positivity
  -- the remainders and their sizes
  set cx := fun ω => b • (b • matCLM Δ (h ω) + gm • matCLM A₁₂ (g ω)
    + b • matCLM A₁₂ (matCLM D (h ω))) + (b' - b) • h' ω with hcx
  set cy := fun ω => gm • matCLM A₂₂ (gm • g ω + b • matCLM D (h ω))
    + b • matCLM D (b • matCLM Δ (h ω) + gm • matCLM A₁₂ (g ω) + b • matCLM A₁₂ (matCLM D (h ω)))
    + (gm' - gm) • g' ω + (b' - b) • matCLM D (h' ω) with hcy
  have hDhL : MemLp (fun ω => matCLM D (h ω)) 2 μ := (matCLM D).comp_memLp' hhL
  have hinL : MemLp (fun ω => b • matCLM Δ (h ω) + gm • matCLM A₁₂ (g ω)
      + b • matCLM A₁₂ (matCLM D (h ω))) 2 μ :=
    ((((matCLM Δ).comp_memLp' hhL).const_smul b).add
      (((matCLM A₁₂).comp_memLp' hgL).const_smul gm)).add
      (((matCLM A₁₂).comp_memLp' hDhL).const_smul b)
  have hcxL : MemLp cx 2 μ := (hinL.const_smul b).add (hh'L.const_smul (b' - b))
  have hcyL : MemLp cy 2 μ :=
    (((((matCLM A₂₂).comp_memLp' ((hgL.const_smul gm).add (hDhL.const_smul b))).const_smul gm).add
      (((matCLM D).comp_memLp' hinL).const_smul b)).add (hg'L.const_smul (gm' - gm))).add
      (((matCLM D).comp_memLp' hh'L).const_smul (b' - b))
  have hSc : rms μ cx ≤ Kx * b * gm := by
    have := rms_le_of_norm_le4 (μ := μ) hcxL hhL hgL hh'L hhL (mul_nonneg hb.le hgm.le)
      (by positivity : 0 ≤ Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) n12
      (mul_nonneg hCs0 hBq) le_rfl (fun ω => by
        have := norm_tts_cx_le Δ A₁₂ D hb.le hgm.le hbq hCs hBq hCs0 (h ω) (h' ω) (g ω)
        rw [zero_mul, add_zero]
        exact this)
    refine this.trans ?_
    rw [hKx]
    have e1 := mul_le_mul_of_nonneg_left rh
      (by positivity : 0 ≤ Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖)
    have e2 := mul_le_mul_of_nonneg_left rg n12
    have e3 := mul_le_mul_of_nonneg_left rh' (mul_nonneg hCs0 hBq)
    have hbg := mul_nonneg hb.le hgm.le
    nlinarith
  have hScy : rms μ cy ≤ Ky * gm ^ 2 := by
    have := rms_le_of_norm_le4 (μ := μ) hcyL hhL hgL hg'L hh'L (sq_nonneg gm)
      (by positivity : 0 ≤ Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖)
      (by positivity : 0 ≤ ‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) hCt0
      (by positivity : 0 ≤ Cs * Bq ^ 2 * ‖matCLM D‖)
      (fun ω => norm_tts_cy_le Δ A₁₂ A₂₂ D hb.le hgm.le hbq hCs hCt hBq hCs0 hCt0
        (h ω) (h' ω) (g ω) (g' ω))
    refine this.trans ?_
    rw [hKy]
    have e1 := mul_le_mul_of_nonneg_left rh
      (by positivity : 0 ≤ Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖)
    have e2 := mul_le_mul_of_nonneg_left rg
      (by positivity : 0 ≤ ‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖)
    have e3 := mul_le_mul_of_nonneg_left rg' hCt0
    have e4 := mul_le_mul_of_nonneg_left rh' (by positivity : 0 ≤ Cs * Bq ^ 2 * ‖matCLM D‖)
    have hg2 := sq_nonneg gm
    nlinarith
  have hDML : MemLp (fun ω => matCLM D (M ω)) 2 μ := (matCLM D).comp_memLp' hML
  have hSDM : rms μ (fun ω => matCLM D (M ω)) ≤ ‖matCLM D‖ * mM :=
    (rms_matCLM_le D hML).trans (mul_le_mul_of_nonneg_left rM nD)
  have hSbM : rms μ (fun ω => b • M ω) ≤ b * mM := by
    rw [rms_smul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left rM hb.le
  have hSbv : rms μ (fun ω => gm • M' ω + b • matCLM D (M ω)) ≤
      √2 * (gm * mM' + b * (‖matCLM D‖ * mM)) := by
    have hgM' : MemLp (fun ω => gm • M' ω) 2 μ := hM'L.const_smul gm
    have hbDM : MemLp (fun ω => b • matCLM D (M ω)) 2 μ := hDML.const_smul b
    refine (rms_add_le hgM' hbDM).trans ?_
    rw [rms_smul, rms_smul, abs_of_pos hgm, abs_of_pos hb]
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left rM' hgm.le)
      (mul_le_mul_of_nonneg_left hSDM hb.le)) (Real.sqrt_nonneg _)
  -- the step lemmas
  have exs : xs' = fun ω => (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • M ω + cx ω :=
    funext hxs'
  have eys : ys' = fun ω => (ys ω - (gm • matCLM A₂₂ (ys ω)
      + b • matCLM D (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))))
      + (gm • M' ω + b • matCLM D (M ω)) + cy ω := funext hys'
  have sX := tts_step_X (μ := μ) (b := b) hℱ Δ A₁₂ hxs hys hxsL hysL hML hcxL hmart Γ₁
  have sZ := tts_step_Z (μ := μ) hℱ Δ A₁₂ A₂₂ D hb.le hgm.le hxs hys hxsL hysL hML hM'L hcxL hcyL
    hmart hmart' Γ₂
  have sY := tts_step_Y (μ := μ) hℱ Δ A₁₂ A₂₂ D hb.le hgm.le hxs hys hxsL hysL hML hM'L hcyL
    hmart hmart' Γ₃
  dsimp only at sZ sY
  rw [exs, eys]
  have sb0 : 0 < √b := Real.sqrt_pos.mpr hb
  have sg0 : 0 < √gm := Real.sqrt_pos.mpr hgm
  have sb2 : √b ^ 2 = b := Real.sq_sqrt hb.le
  have sg2 : √gm ^ 2 = gm := Real.sq_sqrt hgm.le
  have d1 := Real.sqrt_nonneg (d₁ : ℝ)
  have d2 := Real.sqrt_nonneg (d₂ : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · refine sX.trans ?_
    have := tts_R1_le hb hgm sb0 sb2 sg0.le sg2 ht1 d1 hcw0 hKx0 hmM (norm_nonneg (secondMoment μ M - Γ₁))
      (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) hSw hSa hSbM hSc
    rw [ht2] at this
    exact this
  · have hL : ‖lmul Δ (crossMoment μ xs ys)‖ ≤
        ‖(lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * ‖crossMoment μ xs ys‖ := (lmul Δ).le_opNorm _
    have := tts_R2_le hb hgm sb0 sb2 sg0 sg2 ht1 d1 d2 hcw0 hcq0 hKx0 hKy0 hmM hmM' nD
      (norm_nonneg (lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)) (norm_nonneg (crossMoment μ M M' - Γ₂))
      (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _)
      (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _)
      (rms_nonneg _) (rms_nonneg _) hSx hSDw hSw hZn hSq rM hSDM hSa hSbM hSc hScy hSay hSbv
    rw [ht2] at this
    refine sZ.trans (le_trans ?_ this)
    have := mul_le_mul_of_nonneg_left hL hb.le
    linarith
  · have := tts_R3_le hb hgm sg0 sg2 ht1 d2 hcw0 hcq0 hKy0 hmM hmM' nD (norm_nonneg (secondMoment μ M' - Γ₃))
      (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _) (rms_nonneg _)
      (rms_nonneg _) (rms_nonneg _) hSy hSDw hSq rM' hSDM hScy hSay hSbv
    rw [ht2] at this
    exact sY.trans this

/-! ### The shifted iterates -/

lemma sqrt_le_sqrt_of_integral_le {d : ℕ} {f : Ω → E d} {C : ℝ}
    (h : ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ C) : rms μ f ≤ √C := Real.sqrt_le_sqrt h

lemma tendsto_sqrt_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun k => √(f k)) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp hf
  rwa [Real.sqrt_zero] at this

set_option maxHeartbeats 4000000 in
/-- One step of the perturbed recursion: the shift `η, ζ`, the martingale parts `m, m'` and the
extra remainders `ρ, ρ'` have sizes `O(1 + R)` (and `O(γ (1 + R))` for `ρ, ρ'`), where
`R = rms x + rms y ≤ C (rms x̃ + rms ỹ + γ)`. -/
theorem tts_perturbed_step [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (D : Matrix (Fin d₂) (Fin d₁) ℝ)
    {xs xs' m ρ ηk ηk1 : Ω → E d₁} {ys ys' m' ρ' ζk ζk1 : Ω → E d₂}
    {b b' gm gm' Bq Cs Ct C C1 R δ₁ δ₂ δ₃ rB cw cq : ℝ}
    (hb : 0 < b) (hgm : 0 < gm) (hBq : 0 ≤ Bq) (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct) (hC : 0 ≤ C)
    (hC1 : 0 ≤ C1) (hR0 : 0 ≤ R) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₃ : 0 ≤ δ₃) (hrB : 0 ≤ rB)
    (hbq : b ≤ Bq * gm) (hCs : |b' - b| ≤ Cs * b ^ 2) (hCt : |gm' - gm| ≤ Ct * gm ^ 2)
    (hxs : StronglyMeasurable[ℱ] xs) (hys : StronglyMeasurable[ℱ] ys)
    (hxsL : MemLp xs 2 μ) (hysL : MemLp ys 2 μ) (hmL : MemLp m 2 μ) (hm'L : MemLp m' 2 μ)
    (hρL : MemLp ρ 2 μ) (hρ'L : MemLp ρ' 2 μ) (hηkL : MemLp ηk 2 μ) (hηk1L : MemLp ηk1 2 μ)
    (hζkL : MemLp ζk 2 μ) (hζk1L : MemLp ζk1 2 μ)
    (hmart : ∀ j, μ[fun ω => m ω j | ℱ] =ᵐ[μ] 0) (hmart' : ∀ j, μ[fun ω => m' ω j | ℱ] =ᵐ[μ] 0)
    (rηk : rms μ ηk ≤ C * (1 + R)) (rζk : rms μ ζk ≤ C * (1 + R))
    (rηk1 : rms μ ηk1 ≤ C1 * (1 + R)) (rζk1 : rms μ ζk1 ≤ C1 * (1 + R))
    (rm : rms μ m ≤ C * (1 + R)) (rm' : rms μ m' ≤ C * (1 + R))
    (rρ : rms μ ρ ≤ C * gm * (1 + R)) (rρ' : rms μ ρ' ≤ C * gm * (1 + R))
    (hinv : R ≤ C * (rms μ xs + rms μ ys + gm))
    (hrB : C * (√d₁ * √b + √d₂ * √gm + gm) ≤ rB)
    (hcw : cw = √2 * (‖matCLM Δ‖ * √d₁ * √Bq + ‖matCLM A₁₂‖ * √d₂))
    (hcq : cq = √2 * (‖matCLM A₂₂‖ * √d₂ + Bq * ‖matCLM D‖ * cw))
    (hxs' : ∀ ω, xs' ω = (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • (m ω - ρ ω)
      + (b • (b • matCLM Δ (ηk ω) + gm • matCLM A₁₂ (ζk ω) + b • matCLM A₁₂ (matCLM D (ηk ω)))
        + (b' - b) • ηk1 ω))
    (hys' : ∀ ω, ys' ω = (ys ω - (gm • matCLM A₂₂ (ys ω)
        + b • matCLM D (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))))
      + (gm • (m' ω - ρ' ω) + b • matCLM D (m ω - ρ ω))
      + (gm • matCLM A₂₂ (gm • ζk ω + b • matCLM D (ηk ω))
        + b • matCLM D (b • matCLM Δ (ηk ω) + gm • matCLM A₁₂ (ζk ω)
          + b • matCLM A₁₂ (matCLM D (ηk ω)))
        + (gm' - gm) • ζk1 ω + (b' - b) • matCLM D (ηk1 ω)))
    (Γ₁ : Mat d₁) (Γ₂ : Rect d₁ d₂) (Γ₃ : Mat d₂)
    (dev₁ : ‖secondMoment μ m - Γ₁‖ ≤ δ₁ + C * (R + R ^ 2))
    (dev₂ : ‖crossMoment μ m m' - Γ₂‖ ≤ δ₂ + C * (R + R ^ 2))
    (dev₃ : ‖secondMoment μ m' - Γ₃‖ ≤ δ₃ + C * (R + R ^ 2)) :
    let n := 1 + ‖secondMoment μ xs‖ / b + ‖crossMoment μ xs ys‖ / b + ‖secondMoment μ ys‖ / gm
    let r := C * (√d₁ * √b + √d₂ * √gm + gm)
    let A := C * (1 + rB)
    let A1 := C1 * (1 + rB)
    let Kx := √2 * (2 * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * A
      + ‖matCLM A₁₂‖ * A + Cs * Bq * A1) + A)
    let Ky := √2 * (2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖) * A
        + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * A + Ct * A1
        + Cs * Bq ^ 2 * ‖matCLM D‖ * A1) + √2 * (A + Bq * ‖matCLM D‖ * A))
    ‖secondMoment μ xs' - (secondMoment μ xs - b • (lyapOp Δ (secondMoment μ xs)
        + coupleCLM A₁₂ (crossMoment μ xs ys)) + b ^ 2 • Γ₁)‖ ≤
      ttsEps₁ b gm (δ₁ + C * (r + r ^ 2)) √d₁ cw Kx A * b ^ 2 * n ∧
    ‖crossMoment μ xs' ys' - (crossMoment μ xs ys - gm • rmul A₂₂ (crossMoment μ xs ys)
        - b • lmul A₁₂ (secondMoment μ ys) + (b * gm) • Γ₂)‖ ≤
      ttsEps₂ b gm (δ₂ + C * (r + r ^ 2)) √d₁ √d₂ cw cq Kx Ky A A ‖matCLM D‖
        ‖(lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * (b * gm) * n ∧
    ‖secondMoment μ ys' - (secondMoment μ ys - gm • lyapOp A₂₂ (secondMoment μ ys)
        + gm ^ 2 • Γ₃)‖ ≤
      ttsEps₃ b gm (δ₃ + C * (r + r ^ 2)) √d₂ cw cq Ky A A ‖matCLM D‖ * gm ^ 2 * n := by
  intro n r A A1 Kx Ky
  obtain ⟨ht1, hSx, hSy, -, -, -, -, -, -⟩ :=
    tts_sizes (μ := μ) Δ A₁₂ A₂₂ D hb hgm hBq hbq hxsL hysL hcw hcq
  set t := √n with ht_def
  have hn0 : 0 ≤ n := by simp only [n]; positivity
  have ht2 : t ^ 2 = n := Real.sq_sqrt hn0
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have htt : t ≤ t ^ 2 := le_sq_of_one_le ht1
  have hr0 : 0 ≤ r := by simp only [r]; positivity
  have hrB' : r ≤ rB := hrB
  have nΔ := norm_nonneg (matCLM Δ)
  have n12 := norm_nonneg (matCLM A₁₂)
  have n22 := norm_nonneg (matCLM A₂₂)
  have nD := norm_nonneg (matCLM D)
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hA10 : 0 ≤ A1 := by simp only [A1]; positivity
  have hKx0 : 0 ≤ Kx := by simp only [Kx]; positivity
  have hKy0 : 0 ≤ Ky := by simp only [Ky]; positivity
  -- `R ≤ r t` and `1 + R ≤ (1 + rB) t`
  have hRt : R ≤ r * t := by
    refine hinv.trans ?_
    have h1 : gm ≤ gm * t := le_mul_of_one_le_right hgm.le ht1
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hSx hSy) h1) hC
    simp only [r]
    linarith only [this, show C * (√d₁ * √b * t + √d₂ * √gm * t + gm * t) =
      C * (√d₁ * √b + √d₂ * √gm + gm) * t by ring]
  have h1R : 1 + R ≤ (1 + rB) * t := by
    have := mul_le_mul_of_nonneg_right hrB' ht0
    nlinarith
  have bA : ∀ {K : ℝ}, 0 ≤ K → K * (1 + R) ≤ K * (1 + rB) * t := fun {K} hK => by
    have := mul_le_mul_of_nonneg_left h1R hK
    linarith only [this, show K * ((1 + rB) * t) = K * (1 + rB) * t by ring]
  -- the martingale parts
  have rmt : rms μ m ≤ A * t := rm.trans (bA hC)
  have rm't : rms μ m' ≤ A * t := rm'.trans (bA hC)
  -- the remainders
  set cxo := fun ω => b • (b • matCLM Δ (ηk ω) + gm • matCLM A₁₂ (ζk ω)
    + b • matCLM A₁₂ (matCLM D (ηk ω))) + (b' - b) • ηk1 ω with hcxo
  set cyo := fun ω => gm • matCLM A₂₂ (gm • ζk ω + b • matCLM D (ηk ω))
    + b • matCLM D (b • matCLM Δ (ηk ω) + gm • matCLM A₁₂ (ζk ω)
      + b • matCLM A₁₂ (matCLM D (ηk ω)))
    + (gm' - gm) • ζk1 ω + (b' - b) • matCLM D (ηk1 ω) with hcyo
  have hDηL : MemLp (fun ω => matCLM D (ηk ω)) 2 μ := (matCLM D).comp_memLp' hηkL
  have hinL : MemLp (fun ω => b • matCLM Δ (ηk ω) + gm • matCLM A₁₂ (ζk ω)
      + b • matCLM A₁₂ (matCLM D (ηk ω))) 2 μ :=
    ((((matCLM Δ).comp_memLp' hηkL).const_smul b).add
      (((matCLM A₁₂).comp_memLp' hζkL).const_smul gm)).add
      (((matCLM A₁₂).comp_memLp' hDηL).const_smul b)
  have hcxoL : MemLp cxo 2 μ := (hinL.const_smul b).add (hηk1L.const_smul (b' - b))
  have hcyoL : MemLp cyo 2 μ :=
    (((((matCLM A₂₂).comp_memLp' ((hζkL.const_smul gm).add (hDηL.const_smul b))).const_smul gm).add
      (((matCLM D).comp_memLp' hinL).const_smul b)).add (hζk1L.const_smul (gm' - gm))).add
      (((matCLM D).comp_memLp' hηk1L).const_smul (b' - b))
  have hbρL : MemLp (fun ω => b • ρ ω) 2 μ := hρL.const_smul b
  have hρρL : MemLp (fun ω => gm • ρ' ω + b • matCLM D (ρ ω)) 2 μ :=
    (hρ'L.const_smul gm).add (((matCLM D).comp_memLp' hρL).const_smul b)
  set cx := fun ω => cxo ω - b • ρ ω with hcx
  set cy := fun ω => cyo ω - (gm • ρ' ω + b • matCLM D (ρ ω)) with hcy
  have hcxL : MemLp cx 2 μ := hcxoL.sub hbρL
  have hcyL : MemLp cy 2 μ := hcyoL.sub hρρL
  have rcxo : rms μ cxo ≤ 2 * (b * gm) * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖)
      * (A * t) + ‖matCLM A₁₂‖ * (A * t) + Cs * Bq * (A1 * t)) := by
    have h := rms_le_of_norm_le4 (μ := μ) hcxoL hηkL hζkL hηk1L hηkL (mul_nonneg hb.le hgm.le)
      (by positivity : 0 ≤ Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) n12
      (mul_nonneg hCs0 hBq) le_rfl (fun ω => by
        have := norm_tts_cx_le Δ A₁₂ D hb.le hgm.le hbq hCs hBq hCs0 (ηk ω) (ηk1 ω) (ζk ω)
        rw [zero_mul, add_zero]
        exact this)
    refine h.trans ?_
    rw [zero_mul, add_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e1 := mul_le_mul_of_nonneg_left (rηk.trans (bA hC))
      (by positivity : 0 ≤ Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖)
    have e2 := mul_le_mul_of_nonneg_left (rζk.trans (bA hC)) n12
    have e3 := mul_le_mul_of_nonneg_left (rηk1.trans (bA hC1)) (mul_nonneg hCs0 hBq)
    simp only [A, A1] at e1 e2 e3 ⊢
    linarith
  have rcx : rms μ cx ≤ Kx * b * gm * t := by
    refine (rms_sub_le hcxoL hbρL).trans ?_
    rw [rms_smul, abs_of_pos hb]
    have h2 : b * rms μ ρ ≤ b * gm * (A * t) := by
      have := mul_le_mul_of_nonneg_left (rρ.trans (show C * gm * (1 + R) ≤ C * gm * (1 + rB) * t
        from bA (mul_nonneg hC hgm.le))) hb.le
      simp only [A]
      linarith only [this, show b * (C * gm * (1 + rB) * t) = b * gm * (C * (1 + rB) * t) by ring]
    have := mul_le_mul_of_nonneg_left (add_le_add rcxo h2) (Real.sqrt_nonneg 2)
    simp only [Kx]
    linarith only [this, show √2 * (2 * (b * gm) * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖)
      * (A * t) + ‖matCLM A₁₂‖ * (A * t) + Cs * Bq * (A1 * t)) + b * gm * (A * t)) =
      √2 * (2 * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * A + ‖matCLM A₁₂‖ * A
        + Cs * Bq * A1) + A) * b * gm * t by ring]
  have rcyo : rms μ cyo ≤ 2 * gm ^ 2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖
        + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖)
      * (A * t) + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * (A * t) + Ct * (A1 * t)
      + Cs * Bq ^ 2 * ‖matCLM D‖ * (A1 * t)) := by
    have h := rms_le_of_norm_le4 (μ := μ) hcyoL hηkL hζkL hζk1L hηk1L (sq_nonneg gm)
      (by positivity : 0 ≤ Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖)
      (by positivity : 0 ≤ ‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) hCt0
      (by positivity : 0 ≤ Cs * Bq ^ 2 * ‖matCLM D‖)
      (fun ω => norm_tts_cy_le Δ A₁₂ A₂₂ D hb.le hgm.le hbq hCs hCt hBq hCs0 hCt0
        (ηk ω) (ηk1 ω) (ζk ω) (ζk1 ω))
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have e1 := mul_le_mul_of_nonneg_left (rηk.trans (bA hC))
      (by positivity : 0 ≤ Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖)
    have e2 := mul_le_mul_of_nonneg_left (rζk.trans (bA hC))
      (by positivity : 0 ≤ ‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖)
    have e3 := mul_le_mul_of_nonneg_left (rζk1.trans (bA hC1)) hCt0
    have e4 := mul_le_mul_of_nonneg_left (rηk1.trans (bA hC1))
      (by positivity : 0 ≤ Cs * Bq ^ 2 * ‖matCLM D‖)
    simp only [A, A1] at e1 e2 e3 e4 ⊢
    linarith
  have rcy : rms μ cy ≤ Ky * gm ^ 2 * t := by
    have hgρ : MemLp (fun ω => gm • ρ' ω) 2 μ := hρ'L.const_smul gm
    have hbDρ : MemLp (fun ω => b • matCLM D (ρ ω)) 2 μ := ((matCLM D).comp_memLp' hρL).const_smul b
    refine (rms_sub_le hcyoL hρρL).trans ?_
    have h2 : rms μ (fun ω => gm • ρ' ω + b • matCLM D (ρ ω)) ≤
        √2 * (A + Bq * ‖matCLM D‖ * A) * gm ^ 2 * t := by
      refine (rms_add_le hgρ hbDρ).trans ?_
      rw [rms_smul, rms_smul, abs_of_pos hgm, abs_of_pos hb]
      have hρt : rms μ ρ ≤ gm * (A * t) := by
        have := rρ.trans (show C * gm * (1 + R) ≤ C * gm * (1 + rB) * t
          from bA (mul_nonneg hC hgm.le))
        simp only [A]; linarith only [this, show C * gm * (1 + rB) * t = gm * (C * (1 + rB) * t)
          by ring]
      have hρ't : rms μ ρ' ≤ gm * (A * t) := by
        have := rρ'.trans (show C * gm * (1 + R) ≤ C * gm * (1 + rB) * t
          from bA (mul_nonneg hC hgm.le))
        simp only [A]; linarith only [this, show C * gm * (1 + rB) * t = gm * (C * (1 + rB) * t)
          by ring]
      have f1 := mul_le_mul_of_nonneg_left hρ't hgm.le
      have f2 : b * rms μ (fun ω => matCLM D (ρ ω)) ≤ Bq * gm * (‖matCLM D‖ * (gm * (A * t))) :=
        mul_le_mul hbq ((rms_matCLM_le D hρL).trans (mul_le_mul_of_nonneg_left hρt nD))
          (rms_nonneg _) (by positivity)
      have := mul_le_mul_of_nonneg_left (add_le_add f1 f2) (Real.sqrt_nonneg 2)
      linarith only [this, show √2 * (gm * (gm * (A * t)) + Bq * gm * (‖matCLM D‖ * (gm * (A * t))))
        = √2 * (A + Bq * ‖matCLM D‖ * A) * gm ^ 2 * t by ring]
    have := mul_le_mul_of_nonneg_left (add_le_add rcyo h2) (Real.sqrt_nonneg 2)
    simp only [Ky]
    linarith only [this, show √2 * (2 * gm ^ 2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖
        + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖)
      * (A * t) + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * (A * t) + Ct * (A1 * t)
      + Cs * Bq ^ 2 * ‖matCLM D‖ * (A1 * t)) + √2 * (A + Bq * ‖matCLM D‖ * A) * gm ^ 2 * t) =
      √2 * (2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖) * A
        + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * A + Ct * A1
        + Cs * Bq ^ 2 * ‖matCLM D‖ * A1) + √2 * (A + Bq * ‖matCLM D‖ * A)) * gm ^ 2 * t by ring]
  -- deviations
  have hdev : ∀ {G δ : ℝ}, 0 ≤ δ → G ≤ δ + C * (R + R ^ 2) → G ≤ (δ + C * (r + r ^ 2)) * n := by
    intro G δ hδ hG
    have h1 : R ≤ r * t ^ 2 := hRt.trans (mul_le_mul_of_nonneg_left htt hr0)
    have h2 : R ^ 2 ≤ r ^ 2 * t ^ 2 := by
      have := pow_le_pow_left₀ hR0 hRt 2; rwa [mul_pow] at this
    have h3 : δ ≤ δ * t ^ 2 := le_mul_of_one_le_right hδ (ht1.trans htt)
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    rw [← ht2]
    linarith only [hG, h3, this, show (δ + C * (r + r ^ 2)) * t ^ 2 =
      δ * t ^ 2 + C * (r * t ^ 2 + r ^ 2 * t ^ 2) by ring]
  -- apply the general step
  have hxs'' : ∀ ω, xs' ω = (xs ω - b • (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))) + b • m ω
      + cx ω := fun ω => by rw [hxs' ω]; simp only [cx, cxo, smul_sub]; abel
  have hys'' : ∀ ω, ys' ω = (ys ω - (gm • matCLM A₂₂ (ys ω)
      + b • matCLM D (matCLM Δ (xs ω) + matCLM A₁₂ (ys ω))))
      + (gm • m' ω + b • matCLM D (m ω)) + cy ω := fun ω => by
    rw [hys' ω]; simp only [cy, cyo, smul_sub, map_sub]; abel
  have hgen := tts_remainder_step_gen (μ := μ) (G₁ := δ₁ + C * (r + r ^ 2))
    (G₂ := δ₂ + C * (r + r ^ 2)) (G₃ := δ₃ + C * (r + r ^ 2)) hℱ Δ A₁₂ A₂₂ D hb hgm hBq hbq hxs hys hxsL hysL
    hmL hm'L hcxL hcyL hmart hmart' hA0 hA0 hKx0 hKy0
    (add_nonneg hδ₁ (mul_nonneg hC (by positivity))) (add_nonneg hδ₂ (mul_nonneg hC (by positivity)))
    (add_nonneg hδ₃ (mul_nonneg hC (by positivity))) hcw hcq hxs'' hys'' Γ₁ Γ₂ Γ₃
  exact hgen rmt rm't rcx rcy (hdev hδ₁ dev₁) (hdev hδ₂ dev₂) (hdev hδ₃ dev₃)

set_option maxHeartbeats 4000000 in
/-- The conclusion of the deterministic part, from one-step bounds by the vanishing factors
`ttsEps₁`, `ttsEps₂`, `ttsEps₃` with covariance errors `G₁, G₂, G₃ → 0`. -/
theorem tts_limits_of_steps {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((Δ - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    {cw cq Kx Ky mM mM' nD LΔ : ℝ} (hcw0 : 0 ≤ cw) (hcq0 : 0 ≤ cq) (hKx0 : 0 ≤ Kx)
    (hKy0 : 0 ≤ Ky) (hmM : 0 ≤ mM) (hmM' : 0 ≤ mM') (hnD : 0 ≤ nD) (hLΔ : 0 ≤ LΔ)
    {G₁ G₂ G₃ : ℕ → ℝ} (hG₁0 : ∀ k, 0 ≤ G₁ k) (hG₂0 : ∀ k, 0 ≤ G₂ k) (hG₃0 : ∀ k, 0 ≤ G₃ k)
    (hG₁ : Tendsto G₁ atTop (𝓝 0)) (hG₂ : Tendsto G₂ atTop (𝓝 0)) (hG₃ : Tendsto G₃ atTop (𝓝 0))
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂}
    {X : ℕ → Mat d₁} {Z : ℕ → Rect d₁ d₂} {Y : ℕ → Mat d₂}
    (hstep : ∀ k,
      ‖X (k + 1) - (X k - β k • (lyapOp Δ (X k) + coupleCLM A₁₂ (Z k)) + β k ^ 2 • Γ₁₁)‖ ≤
        ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM * β k ^ 2
          * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) ∧
      ‖Z (k + 1) - (Z k - γ k • rmul A₂₂ (Z k) - β k • lmul A₁₂ (Y k) + (β k * γ k) • Γ₁₂)‖ ≤
        ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ * (β k * γ k)
          * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) ∧
      ‖Y (k + 1) - (Y k - γ k • lyapOp A₂₂ (Y k) + γ k ^ 2 • Γ₂₂)‖ ≤
        ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD * γ k ^ 2
          * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k))
    {a : Mat d₁} {c : Rect d₁ d₂} {b : Mat d₂} (hb : lyapOp A₂₂ b = Γ₂₂)
    (hc : rmul A₂₂ c + lmul A₁₂ b = Γ₁₂)
    (ha : lyapOp (Δ - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁) :
    Tendsto (fun k => (β k)⁻¹ • X k) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • Z k) atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • Y k) atTop (𝓝 b) := by
  set ε := fun k => ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM
    + ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ
    + ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD with hε_def
  have e₁0 : ∀ k, 0 ≤ ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM := fun k => by
    have := hβ.pos k; have := hγ.pos k; have := hG₁0 k; simp only [ttsEps₁]; positivity
  have e₂0 : ∀ k, 0 ≤ ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ := fun k => by
    have := hβ.pos k; have := hγ.pos k; have := hG₂0 k; simp only [ttsEps₂]; positivity
  have e₃0 : ∀ k, 0 ≤ ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD := fun k => by
    have := hβ.pos k; have := hγ.pos k; have := hG₃0 k; simp only [ttsEps₃]; positivity
  have hε0 : ∀ k, 0 ≤ ε k := fun k => add_nonneg (add_nonneg (e₁0 k) (e₂0 k)) (e₃0 k)
  -- the vanishing factor tends to zero
  have hb0 := hβ.tendsto_zero
  have hg0 := hγ.tendsto_zero
  have hsg : Tendsto (fun k => √(γ k)) atTop (𝓝 0) := tendsto_sqrt_zero hg0
  have hρ : Tendsto (fun k => γ k / √(β k)) atTop (𝓝 0) := by
    refine (tendsto_sqrt_zero hγβ).congr fun k => ?_
    rw [Real.sqrt_div' _ (hβ.pos k).le, Real.sqrt_sq (hγ.pos k).le]
  have hθ : Tendsto (fun k => √(β k) / √(γ k)) atTop (𝓝 0) := by
    refine (tendsto_sqrt_zero hβγ).congr fun k => ?_
    rw [Real.sqrt_div' _ (hγ.pos k).le]
  have hε : Tendsto ε atTop (𝓝 0) := by
    have l1 : Tendsto (fun k => ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM) atTop (𝓝 0) := by
      simp only [ttsEps₁]
      have := ((hg0.const_mul (cw ^ 2)).add hG₁).add ((((((hρ.const_mul √d₁).add
        ((hg0.mul hsg).const_mul cw)).const_mul (√2 * Kx)).add (hg0.const_mul (mM * Kx))).add
        ((hg0.pow 2).const_mul (Kx ^ 2))).const_mul 2)
      convert this using 1
      · funext k; ring
      · simp
    have l2 : Tendsto (fun k => ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ)
        atTop (𝓝 0) := by
      simp only [ttsEps₂]
      have t1 := hθ.const_mul (√d₁ * nD * cw)
      have t2 := hβγ.const_mul LΔ
      have t3 := hg0.const_mul (cw * cq)
      have t4 := hβγ.mul_const (nD * mM ^ 2)
      have t5 := ((hρ.const_mul √d₁).add ((hsg.mul hg0).const_mul cw)).const_mul (√2 * Ky)
      have t6 := hg0.const_mul (mM * Ky)
      have t7 := (hg0.pow 2).const_mul (Kx * Ky)
      have t8 := ((hsg.const_mul √d₂).add ((hg0.mul hsg).const_mul cq)).const_mul (Kx * √2)
      have t9 := ((hg0.const_mul mM').add (hb0.const_mul (nD * mM))).const_mul (Kx * √2)
      have := ((((((((t1.add t2).add t3).add hG₂).add t4).add t5).add t6).add t7).add t8).add t9
      convert this using 1
      · funext k; ring
      · simp
    have l3 : Tendsto (fun k => ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD) atTop (𝓝 0) := by
      simp only [ttsEps₃]
      have := (((((((hβγ.const_mul (2 * √d₂ * nD * cw)).add (hg0.const_mul (cq ^ 2))).add hG₃).add
        (hβγ.const_mul (2 * (mM' * (nD * mM))))).add ((hβγ.pow 2).mul_const ((nD * mM) ^ 2))).add
        (((hsg.const_mul √d₂).add ((hg0.mul hsg).const_mul cq)).const_mul (2 * (√2 * Ky)))).add
        (((hg0.const_mul mM').add (hb0.const_mul (nD * mM))).const_mul (2 * (√2 * Ky)))).add
        ((hg0.pow 2).const_mul (Ky ^ 2))
      convert this using 1
      · funext k; ring
      · simp
    simpa using (l1.add l2).add l3
  set R₁ := fun k => X (k + 1) - (X k - β k • (lyapOp Δ (X k) + coupleCLM A₁₂ (Z k))
    + β k ^ 2 • Γ₁₁)
  set R₂ := fun k => Z (k + 1) - (Z k - γ k • rmul A₂₂ (Z k) - β k • lmul A₁₂ (Y k)
    + (β k * γ k) • Γ₁₂)
  set R₃ := fun k => Y (k + 1) - (Y k - γ k • lyapOp A₂₂ (Y k) + γ k ^ 2 • Γ₂₂)
  have hn0 : ∀ k, 0 ≤ 1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k := fun k => by
    have := hβ.pos k; have := hγ.pos k; positivity
  have hR₁ : ∀ k, ‖R₁ k‖ ≤ ε k * β k ^ 2 * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) := by
    intro k
    have hs := hstep k
    have hle : ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM ≤ ε k := by
      have := e₂0 k; have := e₃0 k; simp only [ε]; linarith
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (β k)) (hn0 k))
    have h1 := hs.1
    linarith
  have hR₂ : ∀ k, ‖R₂ k‖ ≤ ε k * (β k * γ k) * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) := by
    intro k
    have hs := hstep k
    have hle : ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ ≤ ε k := by
      have := e₁0 k; have := e₃0 k; simp only [ε]; linarith
    have := mul_le_mul_of_nonneg_right hle
      (mul_nonneg (mul_nonneg (hβ.pos k).le (hγ.pos k).le) (hn0 k))
    have h1 := hs.2.1
    linarith
  have hR₃ : ∀ k, ‖R₃ k‖ ≤ ε k * γ k ^ 2 * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) := by
    intro k
    have hs := hstep k
    have hle : ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD ≤ ε k := by
      have := e₁0 k; have := e₂0 k; simp only [ε]; linarith
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (γ k)) (hn0 k))
    have h1 := hs.2.2
    linarith
  exact tendsto_two_time_scale_moments hβ hγ hβγ Δ A₁₂ A₂₂ hη hΔ hA₂₂ hε hε0 hR₁ hR₂ hR₃
    (fun k => by simp only [R₁]; abel) (fun k => by simp only [R₂]; abel)
    (fun k => by simp only [R₃]; abel) hb hc ha



set_option maxHeartbeats 4000000 in
/-- Theorem 2.1 of the write-up for the shifted iterates `x̃ = x + β h`,
`ỹ = y + D x + γ g + β D h`. -/
theorem tts_shifted_limits [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x M h : ℕ → Ω → E d₁} {y M' g : ℕ → Ω → E d₂}
    (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    {Ch Cg CM CM' : ℝ} (hhB : ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
    (hg : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
    (hgB : ∀ k, ∫ ω, ‖g k ω‖ ^ 2 ∂μ ≤ Cg)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
    (hMB : ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
    (hM' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M' (k + 1)))
    (hM'L : ∀ k, MemLp (M' (k + 1)) 2 μ) (hM'B : ∀ k, ∫ ω, ‖M' (k + 1) ω‖ ^ 2 ∂μ ≤ CM')
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hmart' : ∀ k j, μ[fun ω => M' (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂}
    (hΓ₁₁ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ₁₁))
    (hΓ₁₂ : Tendsto (fun k => crossMoment μ (M (k + 1)) (M' (k + 1))) atTop (𝓝 Γ₁₂))
    (hΓ₂₂ : Tendsto (fun k => secondMoment μ (M' (k + 1))) atTop (𝓝 Γ₂₂))
    {a : Mat d₁} {c : Rect d₁ d₂} {b : Mat d₂} (hb : lyapOp A₂₂ b = Γ₂₂)
    (hc : rmul A₂₂ c + lmul A₁₂ b = Γ₁₂)
    (ha : lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁) :
    Tendsto (fun k => (β k)⁻¹ • secondMoment μ (ttsX β x h k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (ttsX β x h k) (ttsY D β γ x h y g k)) atTop
        (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (ttsY D β γ x h y g k)) atTop (𝓝 b) := by
  set Δ := A₁₁ - A₁₂ * D with hΔdef
  have hadapt := tts_adapted (μ := μ) ℱ hrec hx0 hx0L hy0 hy0L hh hhL hg hgL hM hML hM' hM'L
  -- constants
  obtain ⟨Cs, hCs0, hCs⟩ := hβ.abs_sub_le
  obtain ⟨Ct, hCt0, hCt⟩ := hγ.abs_sub_le
  obtain ⟨B0, hB0⟩ := hβγ.bddAbove_range
  obtain ⟨Bq, hBq_def⟩ : ∃ B, B = max B0 0 := ⟨_, rfl⟩
  have hBq : 0 ≤ Bq := hBq_def ▸ le_max_right _ _
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have h1 : β k / γ k ≤ Bq := (hB0 ⟨k, rfl⟩).trans (hBq_def ▸ le_max_left _ _)
    rwa [div_le_iff₀ (hγ.pos k)] at h1
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hhB 0)
  have hCg0 : 0 ≤ Cg := (integral_norm_sq_nonneg (μ := μ) (g 0)).trans (hgB 0)
  have hCM0 : 0 ≤ CM := (integral_norm_sq_nonneg (μ := μ) (M 1)).trans (hMB 0)
  have hCM'0 : 0 ≤ CM' := (integral_norm_sq_nonneg (μ := μ) (M' 1)).trans (hM'B 0)
  set mh := √Ch
  set mg := √Cg
  set mM := √CM
  set mM' := √CM'
  obtain ⟨cw, hcw⟩ : ∃ c, c = √2 * (‖matCLM Δ‖ * √d₁ * √Bq + ‖matCLM A₁₂‖ * √d₂) := ⟨_, rfl⟩
  obtain ⟨cq, hcq⟩ : ∃ c, c = √2 * (‖matCLM A₂₂‖ * √d₂ + Bq * ‖matCLM D‖ * cw) := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ K, K = 2 * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * mh
      + ‖matCLM A₁₂‖ * mg + Cs * Bq * mh) := ⟨_, rfl⟩
  obtain ⟨Ky, hKy⟩ : ∃ K, K = 2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖
        + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
        + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖) * mh
      + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * mg + Ct * mg
      + Cs * Bq ^ 2 * ‖matCLM D‖ * mh) := ⟨_, rfl⟩
  have hcw0 : 0 ≤ cw := by rw [hcw]; positivity
  have hcq0 : 0 ≤ cq := by rw [hcq]; positivity
  have hKx0 : 0 ≤ Kx := by rw [hKx]; positivity
  have hKy0 : 0 ≤ Ky := by rw [hKy]; positivity
  set nD := ‖matCLM D‖
  set LΔ := ‖(lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖
  -- the vanishing factor
  set G₁ := fun k => ‖secondMoment μ (M (k + 1)) - Γ₁₁‖
  set G₂ := fun k => ‖crossMoment μ (M (k + 1)) (M' (k + 1)) - Γ₁₂‖
  set G₃ := fun k => ‖secondMoment μ (M' (k + 1)) - Γ₂₂‖
  set ε := fun k => ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM
    + ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ
    + ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD with hε_def
  have hnD : 0 ≤ nD := norm_nonneg _
  have hLΔ : 0 ≤ LΔ := norm_nonneg _
  have e₁0 : ∀ k, 0 ≤ ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM := fun k => by
    have := hβ.pos k; have := hγ.pos k; simp only [ttsEps₁, G₁]; positivity
  have e₂0 : ∀ k, 0 ≤ ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ := fun k => by
    have := hβ.pos k; have := hγ.pos k; simp only [ttsEps₂, G₂]; positivity
  have e₃0 : ∀ k, 0 ≤ ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD := fun k => by
    have := hβ.pos k; have := hγ.pos k; simp only [ttsEps₃, G₃]; positivity
  have hε0 : ∀ k, 0 ≤ ε k := fun k => add_nonneg (add_nonneg (e₁0 k) (e₂0 k)) (e₃0 k)
  -- the vanishing factor tends to zero
  have hb0 := hβ.tendsto_zero
  have hg0 := hγ.tendsto_zero
  have hsg : Tendsto (fun k => √(γ k)) atTop (𝓝 0) := tendsto_sqrt_zero hg0
  have hρ : Tendsto (fun k => γ k / √(β k)) atTop (𝓝 0) := by
    refine (tendsto_sqrt_zero hγβ).congr fun k => ?_
    rw [Real.sqrt_div' _ (hβ.pos k).le, Real.sqrt_sq (hγ.pos k).le]
  have hθ : Tendsto (fun k => √(β k) / √(γ k)) atTop (𝓝 0) := by
    refine (tendsto_sqrt_zero hβγ).congr fun k => ?_
    rw [Real.sqrt_div' _ (hγ.pos k).le]
  have hG₁ : Tendsto G₁ atTop (𝓝 0) := by
    simpa [G₁] using (hΓ₁₁.sub_const Γ₁₁).norm
  have hG₂ : Tendsto G₂ atTop (𝓝 0) := by
    simpa [G₂] using (hΓ₁₂.sub_const Γ₁₂).norm
  have hG₃ : Tendsto G₃ atTop (𝓝 0) := by
    simpa [G₃] using (hΓ₂₂.sub_const Γ₂₂).norm
  have hε : Tendsto ε atTop (𝓝 0) := by
    have l1 : Tendsto (fun k => ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM) atTop (𝓝 0) := by
      simp only [ttsEps₁]
      have := ((hg0.const_mul (cw ^ 2)).add hG₁).add ((((((hρ.const_mul √d₁).add
        ((hg0.mul hsg).const_mul cw)).const_mul (√2 * Kx)).add (hg0.const_mul (mM * Kx))).add
        ((hg0.pow 2).const_mul (Kx ^ 2))).const_mul 2)
      convert this using 1
      · funext k; ring
      · simp
    have l2 : Tendsto (fun k => ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ)
        atTop (𝓝 0) := by
      simp only [ttsEps₂]
      have t1 := hθ.const_mul (√d₁ * nD * cw)
      have t2 := hβγ.const_mul LΔ
      have t3 := hg0.const_mul (cw * cq)
      have t4 := hβγ.mul_const (nD * mM ^ 2)
      have t5 := ((hρ.const_mul √d₁).add ((hsg.mul hg0).const_mul cw)).const_mul (√2 * Ky)
      have t6 := hg0.const_mul (mM * Ky)
      have t7 := (hg0.pow 2).const_mul (Kx * Ky)
      have t8 := ((hsg.const_mul √d₂).add ((hg0.mul hsg).const_mul cq)).const_mul (Kx * √2)
      have t9 := ((hg0.const_mul mM').add (hb0.const_mul (nD * mM))).const_mul (Kx * √2)
      have := ((((((((t1.add t2).add t3).add hG₂).add t4).add t5).add t6).add t7).add t8).add t9
      convert this using 1
      · funext k; ring
      · simp
    have l3 : Tendsto (fun k => ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD) atTop (𝓝 0) := by
      simp only [ttsEps₃]
      have := (((((((hβγ.const_mul (2 * √d₂ * nD * cw)).add (hg0.const_mul (cq ^ 2))).add hG₃).add
        (hβγ.const_mul (2 * (mM' * (nD * mM))))).add ((hβγ.pow 2).mul_const ((nD * mM) ^ 2))).add
        (((hsg.const_mul √d₂).add ((hg0.mul hsg).const_mul cq)).const_mul (2 * (√2 * Ky)))).add
        (((hg0.const_mul mM').add (hb0.const_mul (nD * mM))).const_mul (2 * (√2 * Ky)))).add
        ((hg0.pow 2).const_mul (Ky ^ 2))
      convert this using 1
      · funext k; ring
      · simp
    simpa using (l1.add l2).add l3
  -- one step of the three moments
  have hstep : ∀ k, _ := fun k =>
    tts_remainder_step (μ := μ) (ℱ.le k) Δ A₁₂ A₂₂ D
      (xs := ttsX β x h k) (xs' := ttsX β x h (k + 1)) (M := M (k + 1)) (h := h k) (h' := h (k + 1))
      (ys := ttsY D β γ x h y g k) (ys' := ttsY D β γ x h y g (k + 1)) (M' := M' (k + 1))
      (g := g k) (g' := g (k + 1)) (hβ.pos k) (hγ.pos k) hBq hCs0 hCt0 (hbq k) (hCs k) (hCt k)
      ((hadapt k).1.1.add ((hh k).const_smul (β k)))
      ((((hadapt k).2.1.add ((matCLM D).continuous.comp_stronglyMeasurable (hadapt k).1.1)).add
        ((hg k).const_smul (γ k))).add
        (((matCLM D).continuous.comp_stronglyMeasurable (hh k)).const_smul (β k)))
      ((hadapt k).1.2.add ((hhL k).const_smul (β k)))
      ((((hadapt k).2.2.add ((matCLM D).comp_memLp' (hadapt k).1.2)).add
        ((hgL k).const_smul (γ k))).add (((matCLM D).comp_memLp' (hhL k)).const_smul (β k)))
      (hML k) (hM'L k) (hhL k) (hhL (k + 1)) (hgL k) (hgL (k + 1)) (hmart k) (hmart' k)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_le_sqrt (hhB k)) (Real.sqrt_le_sqrt (hhB (k + 1))) (Real.sqrt_le_sqrt (hgB k))
      (Real.sqrt_le_sqrt (hgB (k + 1))) (Real.sqrt_le_sqrt (hMB k)) (Real.sqrt_le_sqrt (hM'B k))
      hcw hcq hKx hKy (ttsX_succ hrec k) (ttsY_succ hD hrec k) Γ₁₁ Γ₁₂ Γ₂₂
  set X := fun k => secondMoment μ (ttsX β x h k)
  set Z := fun k => crossMoment μ (ttsX β x h k) (ttsY D β γ x h y g k)
  set Y := fun k => secondMoment μ (ttsY D β γ x h y g k)
  set R₁ := fun k => X (k + 1) - (X k - β k • (lyapOp Δ (X k) + coupleCLM A₁₂ (Z k))
    + β k ^ 2 • Γ₁₁)
  set R₂ := fun k => Z (k + 1) - (Z k - γ k • rmul A₂₂ (Z k) - β k • lmul A₁₂ (Y k)
    + (β k * γ k) • Γ₁₂)
  set R₃ := fun k => Y (k + 1) - (Y k - γ k • lyapOp A₂₂ (Y k) + γ k ^ 2 • Γ₂₂)
  have hn0 : ∀ k, 0 ≤ 1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k := fun k => by
    have := hβ.pos k; have := hγ.pos k; positivity
  have hR₁ : ∀ k, ‖R₁ k‖ ≤ ε k * β k ^ 2 * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) := by
    intro k
    have hs := hstep k
    dsimp only at hs
    have hle : ttsEps₁ (β k) (γ k) (G₁ k) √d₁ cw Kx mM ≤ ε k := by
      have := e₂0 k; have := e₃0 k; simp only [ε]; linarith
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (β k)) (hn0 k))
    have h1 := hs.1
    linarith
  have hR₂ : ∀ k, ‖R₂ k‖ ≤ ε k * (β k * γ k) * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) := by
    intro k
    have hs := hstep k
    dsimp only at hs
    have hle : ttsEps₂ (β k) (γ k) (G₂ k) √d₁ √d₂ cw cq Kx Ky mM mM' nD LΔ ≤ ε k := by
      have := e₁0 k; have := e₃0 k; simp only [ε]; linarith
    have := mul_le_mul_of_nonneg_right hle
      (mul_nonneg (mul_nonneg (hβ.pos k).le (hγ.pos k).le) (hn0 k))
    have h1 := hs.2.1
    linarith
  have hR₃ : ∀ k, ‖R₃ k‖ ≤ ε k * γ k ^ 2 * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k) := by
    intro k
    have hs := hstep k
    dsimp only at hs
    have hle : ttsEps₃ (β k) (γ k) (G₃ k) √d₂ cw cq Ky mM mM' nD ≤ ε k := by
      have := e₁0 k; have := e₂0 k; simp only [ε]; linarith
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (γ k)) (hn0 k))
    have h1 := hs.2.2
    linarith
  exact tendsto_two_time_scale_moments hβ hγ hβγ Δ A₁₂ A₂₂ hη hΔ hA₂₂ hε hε0 hR₁ hR₂ hR₃
    (fun k => by simp only [R₁]; abel) (fun k => by simp only [R₂]; abel)
    (fun k => by simp only [R₃]; abel) hb hc ha


/-! ### The main theorem -/

lemma norm_crossMoment_sub_sub_le {u p : Ω → E d₁} {v q : Ω → E d₂} (hu : MemLp u 2 μ)
    (hp : MemLp p 2 μ) (hv : MemLp v 2 μ) (hq : MemLp q 2 μ) :
    ‖crossMoment μ (fun ω => u ω - p ω) (fun ω => v ω - q ω) - crossMoment μ u v‖ ≤
      rms μ u * rms μ q + rms μ p * rms μ v + rms μ p * rms μ q := by
  rw [crossMoment_sub_sub hu hp hv hq]
  have e : crossMoment μ u v - crossMoment μ u q - crossMoment μ p v + crossMoment μ p q
      - crossMoment μ u v = -crossMoment μ u q - crossMoment μ p v + crossMoment μ p q := by abel
  rw [e]
  have n1 := norm_crossMoment_le_rms (μ := μ) hu hq
  have n2 := norm_crossMoment_le_rms (μ := μ) hp hv
  have n3 := norm_crossMoment_le_rms (μ := μ) hp hq
  have t1 := norm_add_le (-crossMoment μ u q - crossMoment μ p v) (crossMoment μ p q)
  have t2 := norm_sub_le (-crossMoment μ u q) (crossMoment μ p v)
  rw [norm_neg] at t2
  linarith

lemma tendsto_norm_of_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ → ℝ}
    {P : ℕ → V} {L : V} (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0))
    (hP : Tendsto (fun k => (s k)⁻¹ • P k) atTop (𝓝 L)) : Tendsto (fun k => ‖P k‖) atTop (𝓝 0) := by
  have h1 := (hs0.smul hP).norm
  rw [zero_smul, norm_zero] at h1
  refine h1.congr fun k => ?_
  rw [smul_smul, mul_inv_cancel₀ (hs k).ne', one_smul]

set_option maxHeartbeats 4000000 in
/-- Removing the shift: if the shifted iterates `x̃ = x + β h`, `ỹ = y + D x + γ g + β D h`
have normalized moments converging to `a, c, b`, so do `x` and `ŷ = y + D x`. -/
theorem tts_unshift [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) {x h : ℕ → Ω → E d₁} {y g : ℕ → Ω → E d₂}
    (hxL : ∀ k, MemLp (x k) 2 μ) (hyL : ∀ k, MemLp (y k) 2 μ)
    (hhL : ∀ k, MemLp (h k) 2 μ) (hgL : ∀ k, MemLp (g k) 2 μ) {Ch Cg : ℝ}
    (hCh : ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch) (hCg : ∀ k, ∫ ω, ‖g k ω‖ ^ 2 ∂μ ≤ Cg)
    {a : Mat d₁} {c : Rect d₁ d₂} {b : Mat d₂}
    (lX : Tendsto (fun k => (β k)⁻¹ • secondMoment μ (ttsX β x h k)) atTop (𝓝 a))
    (lZ : Tendsto (fun k => (β k)⁻¹ • crossMoment μ (ttsX β x h k) (ttsY D β γ x h y g k)) atTop
      (𝓝 c))
    (lY : Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (ttsY D β γ x h y g k)) atTop (𝓝 b)) :
    Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  set X := fun k => secondMoment μ (ttsX β x h k)
  set Y := fun k => secondMoment μ (ttsY D β γ x h y g k)
  have hX0 := tendsto_norm_of_smul hβ.pos hβ.tendsto_zero lX
  have hY0 := tendsto_norm_of_smul hγ.pos hγ.tendsto_zero lY
  have hxsL : ∀ k, MemLp (ttsX β x h k) 2 μ := fun k => (hxL k).add ((hhL k).const_smul (β k))
  have hysL : ∀ k, MemLp (ttsY D β γ x h y g k) 2 μ := fun k =>
    (((hyL k).add ((matCLM D).comp_memLp' (hxL k))).add
      ((hgL k).const_smul (γ k))).add (((matCLM D).comp_memLp' (hhL k)).const_smul (β k))
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hCh 0)
  have hCg0 : 0 ≤ Cg := (integral_norm_sq_nonneg (μ := μ) (g 0)).trans (hCg 0)
  set mh := √Ch
  set mg := √Cg
  set nD := ‖matCLM D‖
  have hmh : ∀ k, rms μ (h k) ≤ mh := fun k => Real.sqrt_le_sqrt (hCh k)
  have hmg : ∀ k, rms μ (g k) ≤ mg := fun k => Real.sqrt_le_sqrt (hCg k)
  -- the shifts
  have hu : ∀ k, MemLp (fun ω => β k • h k ω) 2 μ := fun k => (hhL k).const_smul (β k)
  have hv : ∀ k, MemLp (fun ω => γ k • g k ω + β k • matCLM D (h k ω)) 2 μ := fun k =>
    ((hgL k).const_smul (γ k)).add (((matCLM D).comp_memLp' (hhL k)).const_smul (β k))
  have rmu : ∀ k, rms μ (fun ω => β k • h k ω) ≤ β k * mh := fun k => by
    rw [rms_smul, abs_of_pos (hβ.pos k)]; exact mul_le_mul_of_nonneg_left (hmh k) (hβ.pos k).le
  have rmv : ∀ k, rms μ (fun ω => γ k • g k ω + β k • matCLM D (h k ω)) ≤
      √2 * (γ k * mg + β k * (nD * mh)) := fun k => by
    have h1 : MemLp (fun ω => γ k • g k ω) 2 μ := (hgL k).const_smul (γ k)
    have h2 : MemLp (fun ω => β k • matCLM D (h k ω)) 2 μ :=
      ((matCLM D).comp_memLp' (hhL k)).const_smul (β k)
    refine (rms_add_le h1 h2).trans ?_
    rw [rms_smul, rms_smul, abs_of_pos (hγ.pos k), abs_of_pos (hβ.pos k)]
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hmg k) (hγ.pos k).le)
      (mul_le_mul_of_nonneg_left ((rms_matCLM_le D (hhL k)).trans
        (mul_le_mul_of_nonneg_left (hmh k) (norm_nonneg _))) (hβ.pos k).le)) (Real.sqrt_nonneg _)
  have ex : ∀ k, x k = fun ω => ttsX β x h k ω - β k • h k ω := fun k => by
    funext ω; simp [ttsX]
  have ey : ∀ k, (fun ω => y k ω + matCLM D (x k ω)) =
      fun ω => ttsY D β γ x h y g k ω - (γ k • g k ω + β k • matCLM D (h k ω)) := fun k => by
    funext ω; simp only [ttsY]; abel
  have rx : ∀ k, rms μ (ttsX β x h k) ≤ √(d₁ * ‖X k‖) := fun k => rms_le_sqrt_secondMoment (hxsL k)
  have ry : ∀ k, rms μ (ttsY D β γ x h y g k) ≤ √(d₂ * ‖Y k‖) := fun k =>
    rms_le_sqrt_secondMoment (hysL k)
  have hsX : Tendsto (fun k => √(d₁ * ‖X k‖)) atTop (𝓝 0) := by
    have := hX0.const_mul (d₁ : ℝ); rw [mul_zero] at this; exact tendsto_sqrt_zero this
  have hsY : Tendsto (fun k => √(d₂ * ‖Y k‖)) atTop (𝓝 0) := by
    have := hY0.const_mul (d₂ : ℝ); rw [mul_zero] at this; exact tendsto_sqrt_zero this
  have hmh0 : 0 ≤ mh := Real.sqrt_nonneg _
  have hmg0 : 0 ≤ mg := Real.sqrt_nonneg _
  have hnD0 : 0 ≤ nD := norm_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · -- the slow iterate
    have hd : ∀ k, ‖(β k)⁻¹ • secondMoment μ (x k) - (β k)⁻¹ • X k‖ ≤
        2 * (mh * √(d₁ * ‖X k‖)) + β k * mh ^ 2 := by
      intro k
      have hb := hβ.pos k
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb, ex k]
      have h1 := norm_crossMoment_sub_sub_le (hxsL k) (hu k) (hxsL k) (hu k) (μ := μ)
      have h2 := mul_le_mul (rx k) (rmu k) (rms_nonneg _) (Real.sqrt_nonneg _)
      have h3 := mul_le_mul (rmu k) (rx k) (rms_nonneg _) (by positivity)
      have h4 := mul_le_mul (rmu k) (rmu k) (rms_nonneg _) (by positivity)
      have h5 : ‖secondMoment μ (fun ω => ttsX β x h k ω - β k • h k ω) - X k‖ ≤
          β k * (2 * (mh * √(d₁ * ‖X k‖)) + β k * mh ^ 2) := by
        have e : secondMoment μ (fun ω => ttsX β x h k ω - β k • h k ω) - X k =
            crossMoment μ (fun ω => ttsX β x h k ω - β k • h k ω)
              (fun ω => ttsX β x h k ω - β k • h k ω)
            - crossMoment μ (ttsX β x h k) (ttsX β x h k) := rfl
        rw [e]
        have e2 : β k * (2 * (mh * √(d₁ * ‖X k‖)) + β k * mh ^ 2) =
            √(d₁ * ‖X k‖) * (β k * mh) + β k * mh * √(d₁ * ‖X k‖) + β k * mh * (β k * mh) := by ring
        rw [e2]
        linarith
      calc (β k)⁻¹ * ‖secondMoment μ (fun ω => ttsX β x h k ω - β k • h k ω) - X k‖
          ≤ (β k)⁻¹ * (β k * (2 * (mh * √(d₁ * ‖X k‖)) + β k * mh ^ 2)) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = _ := by field_simp
    have hlim : Tendsto (fun k => 2 * (mh * √(d₁ * ‖X k‖)) + β k * mh ^ 2) atTop (𝓝 0) := by
      simpa using ((hsX.const_mul mh).const_mul 2).add (hβ.tendsto_zero.mul_const (mh ^ 2))
    have := lX.add (squeeze_zero_norm hd hlim)
    rw [add_zero] at this
    exact this.congr fun k => by abel
  · -- the cross term
    set Z := fun k => crossMoment μ (ttsX β x h k) (ttsY D β γ x h y g k)
    set sx := fun k => √(d₁ * ‖(β k)⁻¹ • X k‖)
    have hsx : ∀ k, √(d₁ * ‖X k‖) = sx k * √(β k) := fun k => by
      have hb := hβ.pos k
      have : (d₁ : ℝ) * ‖X k‖ = d₁ * ‖(β k)⁻¹ • X k‖ * β k := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]; field_simp
      rw [this, Real.sqrt_mul (by positivity)]
    have hd : ∀ k, ‖(β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω))
        - (β k)⁻¹ • Z k‖ ≤
        √2 * sx k * (mg * (γ k / √(β k)) + nD * mh * √(β k)) + mh * √(d₂ * ‖Y k‖)
          + mh * (√2 * (γ k * mg + β k * (nD * mh))) := by
      intro k
      have hb := hβ.pos k
      have sb := Real.sqrt_pos.mpr hb
      have sb2 : √(β k) ^ 2 = β k := Real.sq_sqrt hb.le
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb, ey k]
      conv_lhs => rw [show (x k) = fun ω => ttsX β x h k ω - β k • h k ω from ex k]
      have h1 := norm_crossMoment_sub_sub_le (hxsL k) (hu k) (hysL k) (hv k) (μ := μ)
      have hsx0 : 0 ≤ sx k := Real.sqrt_nonneg _
      have rx' : rms μ (ttsX β x h k) ≤ sx k * √(β k) := (rx k).trans (hsx k).le
      have h2 := mul_le_mul rx' (rmv k) (rms_nonneg _) (by positivity)
      have h3 := mul_le_mul (rmu k) (ry k) (rms_nonneg _) (by positivity)
      have h4 := mul_le_mul (rmu k) (rmv k) (rms_nonneg _) (by positivity)
      have e1 : sx k * √(β k) * (√2 * (γ k * mg + β k * (nD * mh))) =
          β k * (√2 * sx k * (mg * (γ k / √(β k)) + nD * mh * √(β k))) := by
        have hne : √(β k) ≠ 0 := sb.ne'
        set r := √(β k)
        rw [← sb2]
        field_simp
        ring
      have h5 : ‖crossMoment μ (fun ω => ttsX β x h k ω - β k • h k ω)
          (fun ω => ttsY D β γ x h y g k ω - (γ k • g k ω + β k • matCLM D (h k ω))) - Z k‖ ≤
          β k * (√2 * sx k * (mg * (γ k / √(β k)) + nD * mh * √(β k)) + mh * √(d₂ * ‖Y k‖)
            + mh * (√2 * (γ k * mg + β k * (nD * mh)))) := by
        have e2 : β k * (√2 * sx k * (mg * (γ k / √(β k)) + nD * mh * √(β k)) + mh * √(d₂ * ‖Y k‖)
            + mh * (√2 * (γ k * mg + β k * (nD * mh)))) =
            sx k * √(β k) * (√2 * (γ k * mg + β k * (nD * mh))) + β k * mh * √(d₂ * ‖Y k‖)
              + β k * mh * (√2 * (γ k * mg + β k * (nD * mh))) := by rw [e1]; ring
        rw [e2]
        linarith
      calc (β k)⁻¹ * ‖crossMoment μ (fun ω => ttsX β x h k ω - β k • h k ω)
            (fun ω => ttsY D β γ x h y g k ω - (γ k • g k ω + β k • matCLM D (h k ω))) - Z k‖
          ≤ (β k)⁻¹ * (β k * (√2 * sx k * (mg * (γ k / √(β k)) + nD * mh * √(β k))
            + mh * √(d₂ * ‖Y k‖) + mh * (√2 * (γ k * mg + β k * (nD * mh))))) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = _ := by field_simp
    have hρ : Tendsto (fun k => γ k / √(β k)) atTop (𝓝 0) := by
      refine (tendsto_sqrt_zero hγβ).congr fun k => ?_
      rw [Real.sqrt_div' _ (hβ.pos k).le, Real.sqrt_sq (hγ.pos k).le]
    have hsb := tendsto_sqrt_zero hβ.tendsto_zero
    have hsxl : Tendsto sx atTop (𝓝 (√(d₁ * ‖a‖))) :=
      (Real.continuous_sqrt.tendsto _).comp (lX.norm.const_mul (d₁ : ℝ))
    have hlim : Tendsto (fun k => √2 * sx k * (mg * (γ k / √(β k)) + nD * mh * √(β k))
        + mh * √(d₂ * ‖Y k‖) + mh * (√2 * (γ k * mg + β k * (nD * mh)))) atTop (𝓝 0) := by
      have := (((hsxl.const_mul √2).mul ((hρ.const_mul mg).add (hsb.const_mul (nD * mh)))).add
        (hsY.const_mul mh)).add (((((hγ.tendsto_zero.mul_const mg).add
          (hβ.tendsto_zero.mul_const (nD * mh))).const_mul √2)).const_mul mh)
      convert this using 1
      simp
    have := lZ.add (squeeze_zero_norm hd hlim)
    rw [add_zero] at this
    exact this.congr fun k => by abel
  · -- the fast iterate
    have hd : ∀ k, ‖(γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω)) - (γ k)⁻¹ • Y k‖ ≤
        2 * √2 * √(d₂ * ‖Y k‖) * (mg + β k / γ k * (nD * mh))
          + 2 * γ k * (mg + β k / γ k * (nD * mh)) ^ 2 := by
      intro k
      have hg := hγ.pos k
      have hb := hβ.pos k
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hg, ey k]
      have h1 := norm_crossMoment_sub_sub_le (hysL k) (hv k) (hysL k) (hv k) (μ := μ)
      have h2 := mul_le_mul (ry k) (rmv k) (rms_nonneg _) (Real.sqrt_nonneg _)
      have h3 := mul_le_mul (rmv k) (ry k) (rms_nonneg _) (by positivity)
      have h4 := mul_le_mul (rmv k) (rmv k) (rms_nonneg _) (by positivity)
      have s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have e1 : γ k * (2 * √2 * √(d₂ * ‖Y k‖) * (mg + β k / γ k * (nD * mh))
          + 2 * γ k * (mg + β k / γ k * (nD * mh)) ^ 2) =
          √(d₂ * ‖Y k‖) * (√2 * (γ k * mg + β k * (nD * mh)))
            + √2 * (γ k * mg + β k * (nD * mh)) * √(d₂ * ‖Y k‖)
            + √2 * (γ k * mg + β k * (nD * mh)) * (√2 * (γ k * mg + β k * (nD * mh))) := by
        field_simp
        rw [show √2 * (γ k * mg + β k * (nD * mh)) * (√2 * (γ k * mg + β k * (nD * mh)))
          = √2 ^ 2 * (γ k * mg + β k * (nD * mh)) ^ 2 by ring, s2]
        ring
      have h5 : ‖secondMoment μ (fun ω => ttsY D β γ x h y g k ω - (γ k • g k ω
          + β k • matCLM D (h k ω))) - Y k‖ ≤ γ k * (2 * √2 * √(d₂ * ‖Y k‖)
          * (mg + β k / γ k * (nD * mh)) + 2 * γ k * (mg + β k / γ k * (nD * mh)) ^ 2) := by
        rw [e1]
        have e : secondMoment μ (fun ω => ttsY D β γ x h y g k ω - (γ k • g k ω
            + β k • matCLM D (h k ω))) - Y k = crossMoment μ (fun ω => ttsY D β γ x h y g k ω
              - (γ k • g k ω + β k • matCLM D (h k ω))) (fun ω => ttsY D β γ x h y g k ω
              - (γ k • g k ω + β k • matCLM D (h k ω)))
            - crossMoment μ (ttsY D β γ x h y g k) (ttsY D β γ x h y g k) := rfl
        rw [e]
        linarith
      calc (γ k)⁻¹ * ‖secondMoment μ (fun ω => ttsY D β γ x h y g k ω - (γ k • g k ω
            + β k • matCLM D (h k ω))) - Y k‖
          ≤ (γ k)⁻¹ * (γ k * (2 * √2 * √(d₂ * ‖Y k‖) * (mg + β k / γ k * (nD * mh))
            + 2 * γ k * (mg + β k / γ k * (nD * mh)) ^ 2)) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = _ := by field_simp
    have hlim : Tendsto (fun k => 2 * √2 * √(d₂ * ‖Y k‖) * (mg + β k / γ k * (nD * mh))
        + 2 * γ k * (mg + β k / γ k * (nD * mh)) ^ 2) atTop (𝓝 0) := by
      have hq := (tendsto_const_nhds (x := mg)).add (hβγ.mul_const (nD * mh))
      have := ((hsY.const_mul (2 * √2)).mul hq).add ((hγ.tendsto_zero.const_mul 2).mul (hq.pow 2))
      simpa using this
    have := lY.add (squeeze_zero_norm hd hlim)
    rw [add_zero] at this
    exact this.congr fun k => by abel

set_option maxHeartbeats 4000000 in
/-- **Theorem 2.1 of `docs/two-time-scale-covariance.md`.** For the linear two-time-scale
iteration with Markov noise in Poisson form, with `D = A₂₂⁻¹ A₂₁` and `ŷ = y + D x`,
`β⁻¹ E[x xᵀ] → a`, `β⁻¹ E[x ŷᵀ] → c`, `γ⁻¹ E[ŷ ŷᵀ] → b`, where
`A₂₂ b + b A₂₂ᵀ = Γ₂₂`, `c A₂₂ᵀ + A₁₂ b = Γ₁₂` and
`(Δ - β̄/2) a + a (Δ - β̄/2)ᵀ + A₁₂ cᵀ + c A₁₂ᵀ = Γ₁₁` with `Δ = A₁₁ - A₁₂ D`. -/
theorem tendsto_two_time_scale_covariance [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x M h : ℕ → Ω → E d₁} {y M' g : ℕ → Ω → E d₂}
    (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ C, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ C)
    (hg : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
    (hgB : ∃ C, ∀ k, ∫ ω, ‖g k ω‖ ^ 2 ∂μ ≤ C)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
    (hMB : ∃ C, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ C)
    (hM' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M' (k + 1)))
    (hM'L : ∀ k, MemLp (M' (k + 1)) 2 μ) (hM'B : ∃ C, ∀ k, ∫ ω, ‖M' (k + 1) ω‖ ^ 2 ∂μ ≤ C)
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hmart' : ∀ k j, μ[fun ω => M' (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂}
    (hΓ₁₁ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ₁₁))
    (hΓ₁₂ : Tendsto (fun k => crossMoment μ (M (k + 1)) (M' (k + 1))) atTop (𝓝 Γ₁₂))
    (hΓ₂₂ : Tendsto (fun k => secondMoment μ (M' (k + 1))) atTop (𝓝 Γ₂₂)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  obtain ⟨Ch, hCh⟩ := hhB
  obtain ⟨Cg, hCg⟩ := hgB
  obtain ⟨CM, hCM⟩ := hMB
  obtain ⟨CM', hCM'⟩ := hM'B
  -- the limits
  obtain ⟨b, hb⟩ := exists_solution_of_coercive (lyapOp A₂₂) (by positivity : (0 : ℝ) < 2 * η)
    (lyapOp_coercive A₂₂ hA₂₂) Γ₂₂
  obtain ⟨c, hc⟩ := exists_solution_of_coercive (rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂) hη
    (rmul_coercive A₂₂ hA₂₂) (Γ₁₂ - lmul A₁₂ b)
  obtain ⟨a, ha⟩ := exists_solution_of_coercive (lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1))
    (by positivity : (0 : ℝ) < 2 * η) (lyapOp_coercive _ hΔ) (Γ₁₁ - coupleCLM A₁₂ c)
  have hc' : rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ := by rw [hc]; abel
  have ha' : lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ := by
    rw [ha]; abel
  refine ⟨a, c, b, hb, hc', ha', ?_⟩
  have hadapt := tts_adapted (μ := μ) ℱ hrec hx0 hx0L hy0 hy0L hh hhL hg hgL hM hML hM' hM'L
  obtain ⟨lX, lZ, lY⟩ := tts_shifted_limits hβ hγ hβγ hγβ A₁₁ A₁₂ A₂₁ A₂₂ D hD hη hΔ hA₂₂ ℱ
    hrec hx0 hx0L hy0 hy0L hh hhL hCh hg hgL hCg hM hML hCM hM' hM'L hCM' hmart hmart'
    hΓ₁₁ hΓ₁₂ hΓ₂₂ hb hc' ha'
  exact tts_unshift hβ hγ hβγ hγβ D (fun k => (hadapt k).1.2) (fun k => (hadapt k).2.2) hhL hgL
    hCh hCg lX lZ lY

/-- **Corollary 2.2 of `docs/two-time-scale-covariance.md`** (Konda 2002, Thm 7.8, for Markov
noise). The slow iterate of the two-time-scale iteration has the asymptotic covariance of the
single-time-scale iteration `x' = x - β Δ x + β (V - F W)` with `F = A₁₂ A₂₂⁻¹`:
`β⁻¹ E[x xᵀ] → Σ` with `(Δ - β̄/2) Σ + Σ (Δ - β̄/2)ᵀ = Γ₁₁ - F Γ₂₁ - Γ₁₂ Fᵀ + F Γ₂₂ Fᵀ`. -/
theorem tendsto_two_time_scale_slow [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ G : Matrix (Fin d₂) (Fin d₂) ℝ)
    (hG : G * A₂₂ = 1) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * (G * A₂₁) - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x M h : ℕ → Ω → E d₁} {y M' g : ℕ → Ω → E d₂}
    (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ C, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ C)
    (hg : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
    (hgB : ∃ C, ∀ k, ∫ ω, ‖g k ω‖ ^ 2 ∂μ ≤ C)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
    (hMB : ∃ C, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ C)
    (hM' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M' (k + 1)))
    (hM'L : ∀ k, MemLp (M' (k + 1)) 2 μ) (hM'B : ∃ C, ∀ k, ∫ ω, ‖M' (k + 1) ω‖ ^ 2 ∂μ ≤ C)
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hmart' : ∀ k j, μ[fun ω => M' (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂}
    (hΓ₁₁ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ₁₁))
    (hΓ₁₂ : Tendsto (fun k => crossMoment μ (M (k + 1)) (M' (k + 1))) atTop (𝓝 Γ₁₂))
    (hΓ₂₂ : Tendsto (fun k => secondMoment μ (M' (k + 1))) atTop (𝓝 Γ₂₂)) :
    ∃ Sig, lyapOp (A₁₁ - A₁₂ * (G * A₂₁) - (βbar / 2) • 1) Sig =
        Γ₁₁ - lmul (A₁₂ * G) (transCLM Γ₁₂) - rmul (A₁₂ * G) Γ₁₂
          + lmul (A₁₂ * G) (rmul (A₁₂ * G) Γ₂₂) ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 Sig) := by
  have hD : A₂₂ * (G * A₂₁) = A₂₁ := by
    have hG' : A₂₂ * G = 1 := Matrix.mul_eq_one_comm.mp hG
    rw [← Matrix.mul_assoc, hG', Matrix.one_mul]
  obtain ⟨a, c, b, hb, hc, ha, hlim, -, -⟩ := tendsto_two_time_scale_covariance hβ hγ hβγ hγβ
    A₁₁ A₁₂ A₂₁ A₂₂ (G * A₂₁) hD hη hΔ hA₂₂ ℱ hrec hx0 hx0L hy0 hy0L hh hhL hhB hg hgL hgB hM hML
    hMB hM' hM'L hM'B hmart hmart' hΓ₁₁ hΓ₁₂ hΓ₂₂
  have hΓsym : transCLM Γ₂₂ = Γ₂₂ := by
    have h1 : Tendsto (fun k => transCLM (secondMoment μ (M' (k + 1)))) atTop
        (𝓝 (transCLM Γ₂₂)) := (transCLM.continuous.tendsto _).comp hΓ₂₂
    have h2 : (fun k => transCLM (secondMoment μ (M' (k + 1)))) =
        fun k => secondMoment μ (M' (k + 1)) := by
      funext k; exact (crossMoment_swap (hM'L k) (hM'L k)).symm
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hΓ₂₂
  have hbsym := transCLM_eq_of_lyapOp A₂₂ hη hA₂₂ hΓsym hb
  exact ⟨a, effective_lyapunov A₁₂ A₂₂ G hG _ hbsym hb hc ha, hlim⟩

/-! ### Perturbed two-time-scale iterations -/

lemma bdd_of_tendsto_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) : ∃ B, 0 ≤ B ∧ ∀ k, f k ≤ B := by
  obtain ⟨B, hB⟩ := hf.bddAbove_range
  exact ⟨max B 0, le_max_right _ _, fun k => (hB ⟨k, rfl⟩).trans (le_max_left _ _)⟩

set_option maxHeartbeats 8000000 in
/-- **The two-time-scale theorem with perturbations.** The iteration of `TTSRecursion` with
noise `Mx (k+1) = m (k+1) - ρ k`, `My (k+1) = m' (k+1) - ρ' k` and telescoping parts `η, ζ`
that may depend on the iterates, where `m, m'` are martingale differences whose covariances
are close to `Γ` when the iterates are small, and `ρ, ρ' = O(γ)`. All sizes are relative to
`R = rms x + rms y`. This covers multiplicative noise (Section 3 of the write-up). -/
theorem tendsto_tts_perturbed [IsProbabilityMeasure μ] {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x Mx ηp m ρ : ℕ → Ω → E d₁}
    {y My ζ m' ρ' : ℕ → Ω → E d₂}
    (hrec : TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x Mx ηp y My ζ)
    (hMx : ∀ k ω, Mx (k + 1) ω = m (k + 1) ω - ρ k ω)
    (hMy : ∀ k ω, My (k + 1) ω = m' (k + 1) ω - ρ' k ω)
    (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
    (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
    (hηm : ∀ k, StronglyMeasurable[ℱ k] (ηp k)) (hηL : ∀ k, MemLp (ηp k) 2 μ)
    (hζm : ∀ k, StronglyMeasurable[ℱ k] (ζ k)) (hζL : ∀ k, MemLp (ζ k) 2 μ)
    (hmm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (m (k + 1))) (hmL : ∀ k, MemLp (m (k + 1)) 2 μ)
    (hm'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (m' (k + 1)))
    (hm'L : ∀ k, MemLp (m' (k + 1)) 2 μ)
    (hρm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ρ k)) (hρL : ∀ k, MemLp (ρ k) 2 μ)
    (hρ'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (ρ' k)) (hρ'L : ∀ k, MemLp (ρ' k) 2 μ)
    (hmart : ∀ k j, μ[fun ω => m (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hmart' : ∀ k j, μ[fun ω => m' (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 ≤ C)
    (rη : ∀ k, rms μ (ηp k) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rζ : ∀ k, rms μ (ζ k) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rm : ∀ k, rms μ (m (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rm' : ∀ k, rms μ (m' (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (rρ : ∀ k, rms μ (ρ k) ≤ C * γ k * (1 + (rms μ (x k) + rms μ (y k))))
    (rρ' : ∀ k, rms μ (ρ' k) ≤ C * γ k * (1 + (rms μ (x k) + rms μ (y k))))
    (hR1 : ∀ k, rms μ (x (k + 1)) + rms μ (y (k + 1)) ≤ C * (1 + (rms μ (x k) + rms μ (y k))))
    (hinv : ∀ k, rms μ (x k) + rms μ (y k) ≤
      C * (rms μ (ttsX β x ηp k) + rms μ (ttsY D β γ x ηp y ζ k) + γ k))
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
  set Δ := A₁₁ - A₁₂ * D with hΔdef
  -- the limits
  obtain ⟨b, hb⟩ := exists_solution_of_coercive (lyapOp A₂₂) (by positivity : (0 : ℝ) < 2 * η)
    (lyapOp_coercive A₂₂ hA₂₂) Γ₂₂
  obtain ⟨c, hc⟩ := exists_solution_of_coercive (rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂) hη
    (rmul_coercive A₂₂ hA₂₂) (Γ₁₂ - lmul A₁₂ b)
  obtain ⟨a, ha⟩ := exists_solution_of_coercive (lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1))
    (by positivity : (0 : ℝ) < 2 * η) (lyapOp_coercive _ hΔ) (Γ₁₁ - coupleCLM A₁₂ c)
  have hc' : rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ := by rw [hc]; abel
  have ha' : lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ := by
    rw [ha]; abel
  refine ⟨a, c, b, hb, hc', ha', ?_⟩
  -- adaptedness
  have hMxm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Mx (k + 1)) := fun k => by
    rw [show Mx (k + 1) = fun ω => m (k + 1) ω - ρ k ω from funext (hMx k)]
    exact (hmm k).sub (hρm k)
  have hMxL : ∀ k, MemLp (Mx (k + 1)) 2 μ := fun k => by
    rw [show Mx (k + 1) = fun ω => m (k + 1) ω - ρ k ω from funext (hMx k)]
    exact (hmL k).sub (hρL k)
  have hMym : ∀ k, StronglyMeasurable[ℱ (k + 1)] (My (k + 1)) := fun k => by
    rw [show My (k + 1) = fun ω => m' (k + 1) ω - ρ' k ω from funext (hMy k)]
    exact (hm'm k).sub (hρ'm k)
  have hMyL : ∀ k, MemLp (My (k + 1)) 2 μ := fun k => by
    rw [show My (k + 1) = fun ω => m' (k + 1) ω - ρ' k ω from funext (hMy k)]
    exact (hm'L k).sub (hρ'L k)
  have hadapt := tts_adapted (μ := μ) ℱ hrec hx0 hx0L hy0 hy0L hηm hηL hζm hζL hMxm hMxL hMym hMyL
  -- constants
  obtain ⟨Cs, hCs0, hCs⟩ := hβ.abs_sub_le
  obtain ⟨Ct, hCt0, hCt⟩ := hγ.abs_sub_le
  obtain ⟨B0, hB0⟩ := hβγ.bddAbove_range
  obtain ⟨Bq, hBq_def⟩ : ∃ B, B = max B0 0 := ⟨_, rfl⟩
  have hBq : 0 ≤ Bq := hBq_def ▸ le_max_right _ _
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have h1 : β k / γ k ≤ Bq := (hB0 ⟨k, rfl⟩).trans (hBq_def ▸ le_max_left _ _)
    rwa [div_le_iff₀ (hγ.pos k)] at h1
  obtain ⟨Bb, hBb0, hBb⟩ := bdd_of_tendsto_zero hβ.tendsto_zero
  obtain ⟨Bg, hBg0, hBg⟩ := bdd_of_tendsto_zero hγ.tendsto_zero
  set rB := C * (√d₁ * √Bb + √d₂ * √Bg + Bg)
  have hrB0 : 0 ≤ rB := by positivity
  have hrB : ∀ k, C * (√d₁ * √(β k) + √d₂ * √(γ k) + γ k) ≤ rB := fun k => by
    have h1 := Real.sqrt_le_sqrt (hBb k)
    have h2 := Real.sqrt_le_sqrt (hBg k)
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (d₁ : ℝ))
    have := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (d₂ : ℝ))
    linarith [hBg k]
  set C1 := C * (1 + C)
  have hC1 : 0 ≤ C1 := by positivity
  set R := fun k => rms μ (x k) + rms μ (y k)
  have hR0 : ∀ k, 0 ≤ R k := fun k => add_nonneg (rms_nonneg _) (rms_nonneg _)
  have rη1 : ∀ k, rms μ (ηp (k + 1)) ≤ C1 * (1 + R k) := fun k => by
    have h1 : rms μ (ηp (k + 1)) ≤ C * (1 + R (k + 1)) := rη (k + 1)
    have h2 : C * R (k + 1) ≤ C * (C * (1 + R k)) := mul_le_mul_of_nonneg_left (hR1 k) hC
    have h4 : 0 ≤ C * R k := mul_nonneg hC (hR0 k)
    have e : C1 * (1 + R k) = C + C * (C * (1 + R k)) + C * R k := by simp only [C1]; ring
    rw [e]
    linarith only [h1, h2, h4, show C * (1 + R (k + 1)) = C + C * R (k + 1) by ring]
  have rζ1 : ∀ k, rms μ (ζ (k + 1)) ≤ C1 * (1 + R k) := fun k => by
    have h1 : rms μ (ζ (k + 1)) ≤ C * (1 + R (k + 1)) := rζ (k + 1)
    have h2 : C * R (k + 1) ≤ C * (C * (1 + R k)) := mul_le_mul_of_nonneg_left (hR1 k) hC
    have h4 : 0 ≤ C * R k := mul_nonneg hC (hR0 k)
    have e : C1 * (1 + R k) = C + C * (C * (1 + R k)) + C * R k := by simp only [C1]; ring
    rw [e]
    linarith only [h1, h2, h4, show C * (1 + R (k + 1)) = C + C * R (k + 1) by ring]
  set A := C * (1 + rB)
  set A1 := C1 * (1 + rB)
  obtain ⟨cw, hcw⟩ : ∃ c, c = √2 * (‖matCLM Δ‖ * √d₁ * √Bq + ‖matCLM A₁₂‖ * √d₂) := ⟨_, rfl⟩
  obtain ⟨cq, hcq⟩ : ∃ c, c = √2 * (‖matCLM A₂₂‖ * √d₂ + Bq * ‖matCLM D‖ * cw) := ⟨_, rfl⟩
  set Kx := √2 * (2 * ((Bq * ‖matCLM Δ‖ + Bq * ‖matCLM A₁₂‖ * ‖matCLM D‖) * A
      + ‖matCLM A₁₂‖ * A + Cs * Bq * A1) + A)
  set Ky := √2 * (2 * ((Bq * ‖matCLM A₂₂‖ * ‖matCLM D‖ + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM Δ‖
          + Bq ^ 2 * ‖matCLM D‖ * ‖matCLM A₁₂‖ * ‖matCLM D‖) * A
        + (‖matCLM A₂₂‖ + Bq * ‖matCLM D‖ * ‖matCLM A₁₂‖) * A + Ct * A1
        + Cs * Bq ^ 2 * ‖matCLM D‖ * A1) + √2 * (A + Bq * ‖matCLM D‖ * A))
  set rk := fun k => C * (√d₁ * √(β k) + √d₂ * √(γ k) + γ k)
  set G₁ := fun k => δ₁ k + C * (rk k + rk k ^ 2)
  set G₂ := fun k => δ₂ k + C * (rk k + rk k ^ 2)
  set G₃ := fun k => δ₃ k + C * (rk k + rk k ^ 2)
  -- one step
  have hstep : ∀ k, _ := fun k =>
    tts_perturbed_step (μ := μ) (ℱ.le k) Δ A₁₂ A₂₂ D
      (xs := ttsX β x ηp k) (xs' := ttsX β x ηp (k + 1)) (m := m (k + 1)) (ρ := ρ k)
      (ηk := ηp k) (ηk1 := ηp (k + 1)) (ys := ttsY D β γ x ηp y ζ k)
      (ys' := ttsY D β γ x ηp y ζ (k + 1)) (m' := m' (k + 1)) (ρ' := ρ' k) (ζk := ζ k)
      (ζk1 := ζ (k + 1)) (R := R k) (hβ.pos k) (hγ.pos k) hBq hCs0 hCt0 hC hC1 (hR0 k)
      (hδ₁0 k) (hδ₂0 k) (hδ₃0 k) hrB0 (hbq k) (hCs k) (hCt k)
      ((hadapt k).1.1.add ((hηm k).const_smul (β k)))
      ((((hadapt k).2.1.add ((matCLM D).continuous.comp_stronglyMeasurable (hadapt k).1.1)).add
        ((hζm k).const_smul (γ k))).add
        (((matCLM D).continuous.comp_stronglyMeasurable (hηm k)).const_smul (β k)))
      ((hadapt k).1.2.add ((hηL k).const_smul (β k)))
      ((((hadapt k).2.2.add ((matCLM D).comp_memLp' (hadapt k).1.2)).add
        ((hζL k).const_smul (γ k))).add (((matCLM D).comp_memLp' (hηL k)).const_smul (β k)))
      (hmL k) (hm'L k) (hρL k) (hρ'L k) (hηL k) (hηL (k + 1)) (hζL k) (hζL (k + 1))
      (hmart k) (hmart' k) (rη k) (rζ k) (rη1 k) (rζ1 k) (rm k) (rm' k) (rρ k) (rρ' k)
      (hinv k) (hrB k) hcw hcq
      (fun ω => by rw [ttsX_succ hrec k ω, hMx k ω])
      (fun ω => by rw [ttsY_succ hD hrec k ω, hMy k ω, hMx k ω])
      Γ₁₁ Γ₁₂ Γ₂₂ (dev₁ k) (dev₂ k) (dev₃ k)
  -- the vanishing factors
  have hrk : Tendsto rk atTop (𝓝 0) := by
    have := (((tendsto_sqrt_zero hβ.tendsto_zero).const_mul √d₁).add
      ((tendsto_sqrt_zero hγ.tendsto_zero).const_mul √d₂)).add hγ.tendsto_zero
    simpa [rk] using this.const_mul C
  have hq : Tendsto (fun k => C * (rk k + rk k ^ 2)) atTop (𝓝 0) := by
    simpa using (hrk.add (hrk.pow 2)).const_mul C
  have hrk0 : ∀ k, 0 ≤ rk k := fun k => by have := hγ.pos k; simp only [rk]; positivity
  have hcw0 : 0 ≤ cw := by rw [hcw]; positivity
  have hcq0 : 0 ≤ cq := by rw [hcq]; positivity
  have hA0 : 0 ≤ A := by positivity
  have hKx0 : 0 ≤ Kx := by positivity
  have hKy0 : 0 ≤ Ky := by positivity
  obtain ⟨lX, lZ, lY⟩ := tts_limits_of_steps (X := fun k => secondMoment μ (ttsX β x ηp k))
    (Z := fun k => crossMoment μ (ttsX β x ηp k) (ttsY D β γ x ηp y ζ k))
    (Y := fun k => secondMoment μ (ttsY D β γ x ηp y ζ k)) (G₁ := G₁) (G₂ := G₂) (G₃ := G₃)
    (Γ₁₁ := Γ₁₁) (Γ₁₂ := Γ₁₂) (Γ₂₂ := Γ₂₂)
    hβ hγ hβγ hγβ Δ A₁₂ A₂₂ hη hΔ hA₂₂ hcw0 hcq0 hKx0 hKy0 hA0 hA0 (norm_nonneg _)
    (norm_nonneg (lmul Δ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂))
    (fun k => add_nonneg (hδ₁0 k) (mul_nonneg hC (by have := hrk0 k; positivity)))
    (fun k => add_nonneg (hδ₂0 k) (mul_nonneg hC (by have := hrk0 k; positivity)))
    (fun k => add_nonneg (hδ₃0 k) (mul_nonneg hC (by have := hrk0 k; positivity)))
    (by simpa using hδ₁.add hq) (by simpa using hδ₂.add hq) (by simpa using hδ₃.add hq)
    (fun k => hstep k) hb hc' ha'
  -- bounded telescoping parts, then remove the shift
  have hX0 := tendsto_norm_of_smul hβ.pos hβ.tendsto_zero lX
  have hY0 := tendsto_norm_of_smul hγ.pos hγ.tendsto_zero lY
  obtain ⟨BX, hBX0, hBX⟩ := bdd_of_tendsto_zero hX0
  obtain ⟨BY, hBY0, hBY⟩ := bdd_of_tendsto_zero hY0
  have hxsL : ∀ k, MemLp (ttsX β x ηp k) 2 μ := fun k =>
    (hadapt k).1.2.add ((hηL k).const_smul (β k))
  have hysL : ∀ k, MemLp (ttsY D β γ x ηp y ζ k) 2 μ := fun k =>
    ((((hadapt k).2.2.add ((matCLM D).comp_memLp' (hadapt k).1.2)).add
        ((hζL k).const_smul (γ k))).add (((matCLM D).comp_memLp' (hηL k)).const_smul (β k)))
  set Rb := C * (√(d₁ * BX) + √(d₂ * BY) + Bg)
  have hRb : ∀ k, R k ≤ Rb := fun k => by
    refine (hinv k).trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) (hBg k)) hC)
    · exact (rms_le_sqrt_secondMoment (hxsL k)).trans (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (hBX k) (Nat.cast_nonneg _)))
    · exact (rms_le_sqrt_secondMoment (hysL k)).trans (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (hBY k) (Nat.cast_nonneg _)))
  have hsq : ∀ {d : ℕ} {f : Ω → E d} {B : ℝ}, 0 ≤ B → rms μ f ≤ B →
      ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ B ^ 2 := fun {d f B} hB h => by
    have := pow_le_pow_left₀ (rms_nonneg f) h 2
    rwa [rms, Real.sq_sqrt (integral_norm_sq_nonneg f)] at this
  have hRb0 : 0 ≤ Rb := by positivity
  exact tts_unshift hβ hγ hβγ hγβ D (fun k => (hadapt k).1.2) (fun k => (hadapt k).2.2) hηL hζL
    (fun k => hsq (by positivity) ((rη k).trans (mul_le_mul_of_nonneg_left
      (show 1 + (rms μ (x k) + rms μ (y k)) ≤ 1 + Rb by
        have := hRb k; simp only [R] at this; linarith) hC)))
    (fun k => hsq (by positivity) ((rζ k).trans (mul_le_mul_of_nonneg_left
      (show 1 + (rms μ (x k) + rms μ (y k)) ≤ 1 + Rb by
        have := hRb k; simp only [R] at this; linarith) hC))) lX lZ lY

end StochasticApproximation
