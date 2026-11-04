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
    (hG : 0 ≤ G) (hSw0 : 0 ≤ Sw) (hSa0 : 0 ≤ Sa) (hSbM0 : 0 ≤ SbM) (hSc0 : 0 ≤ Sc)
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
    (hSx0 : 0 ≤ Sx) (hSDw0 : 0 ≤ SDw) (hSw0 : 0 ≤ Sw) (hSq0 : 0 ≤ Sq) (hSM0 : 0 ≤ SM)
    (hSDM0 : 0 ≤ SDM) (hSa0 : 0 ≤ Sa) (hSbM0 : 0 ≤ SbM) (hSc0 : 0 ≤ Sc) (hScy0 : 0 ≤ Scy)
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
    (hsg2 : sg ^ 2 = gm) (ht : 1 ≤ t) (hd₂ : 0 ≤ d₂') (hcw : 0 ≤ cw)
    (hcq : 0 ≤ cq) (hKy : 0 ≤ Ky) (hm : 0 ≤ mM) (hm' : 0 ≤ mM') (hnD : 0 ≤ nD) (hG : 0 ≤ G)
    (hSy0 : 0 ≤ Sy) (hSDw0 : 0 ≤ SDw) (hSq0 : 0 ≤ Sq) (hSM'0 : 0 ≤ SM') (hSDM0 : 0 ≤ SDM)
    (hScy0 : 0 ≤ Scy) (hSay0 : 0 ≤ Say) (hSbv0 : 0 ≤ Sbv)
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
    (hbq : b ≤ Bq * gm) (hCs : |b' - b| ≤ Cs * b ^ 2) (hBq : 0 ≤ Bq) (hCs0 : 0 ≤ Cs)
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
    (hBq : 0 ≤ Bq) (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct) (hh hh' : E d₁) (gg gg' : E d₂) :
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

end StochasticApproximation
