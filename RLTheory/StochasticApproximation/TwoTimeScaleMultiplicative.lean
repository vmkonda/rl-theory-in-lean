/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TwoTimeScaleCovariance

/-!
# Two time scales with multiplicative Markov noise

Section 4 of `docs/two-time-scale-covariance.md`: the linear two-time-scale iteration in which
every block of the matrix is random, `A_ij + N_ij (k+1) + G_ij k - G_ij (k+1)`, with
`N_ij (k+1)` martingale differences and `G_ij` bounded. The multiplicative noise does not change
the asymptotic covariances: the conclusions of Theorem 2.1 and Corollary 2.2 hold with the
covariances of the additive martingale parts.

The proof verifies the hypotheses of `tendsto_tts_perturbed` with the shifts
`η = h - G₁₁ x - G₁₂ y`, `ζ = g - G₂₁ x - G₂₂ y`.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StochasticApproximation

variable {d₁ d₂ : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Root mean squares -/

lemma rms_eq_toReal {d : ℕ} {f : Ω → E d} (hf : MemLp f 2 μ) :
    rms μ f = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal
    (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, rms]
  rw [Real.sqrt_eq_rpow, one_div]

/-- Minkowski's inequality for root mean squares. -/
lemma rms_add_le' {d : ℕ} {f g : Ω → E d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    rms μ (fun ω => f ω + g ω) ≤ rms μ f + rms μ g := by
  have hfg : MemLp (fun ω => f ω + g ω) 2 μ := hf.add hg
  rw [rms_eq_toReal hfg, rms_eq_toReal hf, rms_eq_toReal hg,
    ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 one_le_two)

lemma rms_sub_le' {d : ℕ} {f g : Ω → E d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    rms μ (fun ω => f ω - g ω) ≤ rms μ f + rms μ g := by
  have h := rms_add_le' (μ := μ) hf (hg.const_smul (-1 : ℝ))
  have e1 : (fun ω => f ω + ((-1 : ℝ) • g) ω) = fun ω => f ω - g ω := by
    funext ω; simp [sub_eq_add_neg]
  have e2 : rms μ ((-1 : ℝ) • g) = rms μ g := by simpa using rms_smul (μ := μ) (-1 : ℝ) g
  rw [e1, e2] at h
  exact h

/-- A bounded random linear map changes the root mean square by at most its bound. -/
lemma rms_clm_le {n d : ℕ} {L : Ω → E n →L[ℝ] E d} {f : Ω → E n} {C : ℝ}
    (hL : AEStronglyMeasurable L μ) (hLB : ∀ ω, ‖L ω‖ ≤ C) (hC : 0 ≤ C) (hf : MemLp f 2 μ) :
    rms μ (fun ω => L ω (f ω)) ≤ C * rms μ f :=
  rms_le_of_le (memLp_clm_apply hL hLB hf) hf hC fun ω => norm_clm_apply_le (hLB ω) _

/-! ### The noise and the iteration -/

/-- The multiplicative noise of the four blocks: `Ã_ij k = N_ij (k+1) + G_ij k - G_ij (k+1)`,
with bounded `N_ij`, `G_ij`, `ℱ`-adapted, and `N_ij (k+1)` a martingale difference entrywise. -/
structure TTSMatrixNoise (μ : Measure Ω) (ℱ : MeasureTheory.Filtration ℕ m0) (d₁ d₂ : ℕ) where
  N₁₁ : ℕ → Ω → E d₁ →L[ℝ] E d₁
  N₁₂ : ℕ → Ω → E d₂ →L[ℝ] E d₁
  N₂₁ : ℕ → Ω → E d₁ →L[ℝ] E d₂
  N₂₂ : ℕ → Ω → E d₂ →L[ℝ] E d₂
  G₁₁ : ℕ → Ω → E d₁ →L[ℝ] E d₁
  G₁₂ : ℕ → Ω → E d₂ →L[ℝ] E d₁
  G₂₁ : ℕ → Ω → E d₁ →L[ℝ] E d₂
  G₂₂ : ℕ → Ω → E d₂ →L[ℝ] E d₂
  CN : ℝ
  CN_nonneg : 0 ≤ CN
  bN₁₁ : ∀ k ω, ‖N₁₁ (k + 1) ω‖ ≤ CN
  bN₁₂ : ∀ k ω, ‖N₁₂ (k + 1) ω‖ ≤ CN
  bN₂₁ : ∀ k ω, ‖N₂₁ (k + 1) ω‖ ≤ CN
  bN₂₂ : ∀ k ω, ‖N₂₂ (k + 1) ω‖ ≤ CN
  bG₁₁ : ∀ k ω, ‖G₁₁ k ω‖ ≤ CN
  bG₁₂ : ∀ k ω, ‖G₁₂ k ω‖ ≤ CN
  bG₂₁ : ∀ k ω, ‖G₂₁ k ω‖ ≤ CN
  bG₂₂ : ∀ k ω, ‖G₂₂ k ω‖ ≤ CN
  mN₁₁ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N₁₁ (k + 1))
  mN₁₂ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N₁₂ (k + 1))
  mN₂₁ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N₂₁ (k + 1))
  mN₂₂ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N₂₂ (k + 1))
  mG₁₁ : ∀ k, StronglyMeasurable[ℱ k] (G₁₁ k)
  mG₁₂ : ∀ k, StronglyMeasurable[ℱ k] (G₁₂ k)
  mG₂₁ : ∀ k, StronglyMeasurable[ℱ k] (G₂₁ k)
  mG₂₂ : ∀ k, StronglyMeasurable[ℱ k] (G₂₂ k)
  mart₁₁ : ∀ k i j, μ[fun ω => N₁₁ (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0
  mart₁₂ : ∀ k i j, μ[fun ω => N₁₂ (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0
  mart₂₁ : ∀ k i j, μ[fun ω => N₂₁ (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0
  mart₂₂ : ∀ k i j, μ[fun ω => N₂₂ (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0

variable {ℱ : MeasureTheory.Filtration ℕ m0}

/-- The two-time-scale iteration with multiplicative noise. -/
def MTTSRecursion (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (β γ : ℕ → ℝ)
    (x M h : ℕ → Ω → E d₁) (y M' g : ℕ → Ω → E d₂) (W : TTSMatrixNoise μ ℱ d₁ d₂) : Prop :=
  (∀ k ω, x (k + 1) ω = x k ω - β k • (matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω))
    - β k • ((W.N₁₁ (k + 1) ω + W.G₁₁ k ω - W.G₁₁ (k + 1) ω) (x k ω)
      + (W.N₁₂ (k + 1) ω + W.G₁₂ k ω - W.G₁₂ (k + 1) ω) (y k ω))
    + β k • (M (k + 1) ω + h k ω - h (k + 1) ω)) ∧
  (∀ k ω, y (k + 1) ω = y k ω - γ k • (matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω))
    - γ k • ((W.N₂₁ (k + 1) ω + W.G₂₁ k ω - W.G₂₁ (k + 1) ω) (x k ω)
      + (W.N₂₂ (k + 1) ω + W.G₂₂ k ω - W.G₂₂ (k + 1) ω) (y k ω))
    + γ k • (M' (k + 1) ω + g k ω - g (k + 1) ω))

namespace TTSMatrixNoise

noncomputable section

variable (W : TTSMatrixNoise μ ℱ d₁ d₂) (x : ℕ → Ω → E d₁) (y : ℕ → Ω → E d₂)

/-- The slow shift `η = h - G₁₁ x - G₁₂ y`. -/
def η (h : ℕ → Ω → E d₁) (k : ℕ) (ω : Ω) : E d₁ := h k ω - (W.G₁₁ k ω (x k ω) + W.G₁₂ k ω (y k ω))

/-- The fast shift `ζ = g - G₂₁ x - G₂₂ y`. -/
def ζ (g : ℕ → Ω → E d₂) (k : ℕ) (ω : Ω) : E d₂ := g k ω - (W.G₂₁ k ω (x k ω) + W.G₂₂ k ω (y k ω))

/-- The slow martingale part `M - N₁₁ x - N₁₂ y`. -/
def m (M : ℕ → Ω → E d₁) (n : ℕ) (ω : Ω) : E d₁ :=
  M n ω - (W.N₁₁ n ω (x n.pred ω) + W.N₁₂ n ω (y n.pred ω))

/-- The fast martingale part `M' - N₂₁ x - N₂₂ y`. -/
def m' (M' : ℕ → Ω → E d₂) (n : ℕ) (ω : Ω) : E d₂ :=
  M' n ω - (W.N₂₁ n ω (x n.pred ω) + W.N₂₂ n ω (y n.pred ω))

/-- The slow remainder `G₁₁' (x' - x) + G₁₂' (y' - y)`. -/
def ρ (k : ℕ) (ω : Ω) : E d₁ :=
  W.G₁₁ (k + 1) ω (x (k + 1) ω - x k ω) + W.G₁₂ (k + 1) ω (y (k + 1) ω - y k ω)

/-- The fast remainder `G₂₁' (x' - x) + G₂₂' (y' - y)`. -/
def ρ' (k : ℕ) (ω : Ω) : E d₂ :=
  W.G₂₁ (k + 1) ω (x (k + 1) ω - x k ω) + W.G₂₂ (k + 1) ω (y (k + 1) ω - y k ω)

/-- The full slow noise of the perturbed form. -/
def Mx (M : ℕ → Ω → E d₁) (n : ℕ) (ω : Ω) : E d₁ := W.m x y M n ω - W.ρ x y n.pred ω

/-- The full fast noise of the perturbed form. -/
def My (M' : ℕ → Ω → E d₂) (n : ℕ) (ω : Ω) : E d₂ := W.m' x y M' n ω - W.ρ' x y n.pred ω

end

end TTSMatrixNoise

variable {A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ} {A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ}
  {A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ} {A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ} {β γ : ℕ → ℝ}
  {x M h : ℕ → Ω → E d₁} {y M' g : ℕ → Ω → E d₂} {W : TTSMatrixNoise μ ℱ d₁ d₂}

/-- The multiplicative iteration is a perturbed additive one. -/
lemma tts_of_mtts (hrec : MTTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g W) :
    TTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x (W.Mx x y M) (W.η x y h) y (W.My x y M') (W.ζ x y g) := by
  constructor
  · intro k ω
    rw [hrec.1 k ω]
    simp only [TTSMatrixNoise.Mx, TTSMatrixNoise.m, TTSMatrixNoise.ρ, TTSMatrixNoise.η,
      Nat.pred_succ, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_sub]
    rw [hrec.1 k ω]
    simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    module
  · intro k ω
    rw [hrec.2 k ω]
    simp only [TTSMatrixNoise.My, TTSMatrixNoise.m', TTSMatrixNoise.ρ', TTSMatrixNoise.ζ,
      Nat.pred_succ, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_sub]
    rw [hrec.1 k ω, hrec.2 k ω]
    simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    module

/-! ### Measurability and integrability -/

section Measurability

variable (hrec : MTTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g W)
  (hx0 : StronglyMeasurable[ℱ 0] (x 0)) (hx0L : MemLp (x 0) 2 μ)
  (hy0 : StronglyMeasurable[ℱ 0] (y 0)) (hy0L : MemLp (y 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hg : ∀ k, StronglyMeasurable[ℱ k] (g k)) (hgL : ∀ k, MemLp (g k) 2 μ)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hM' : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M' (k + 1)))
  (hM'L : ∀ k, MemLp (M' (k + 1)) 2 μ)

lemma clm_sm {n d : ℕ} {m : MeasurableSpace Ω} {L : Ω → E n →L[ℝ] E d} {f : Ω → E n}
    (hL : StronglyMeasurable[m] L) (hf : StronglyMeasurable[m] f) :
    StronglyMeasurable[m] fun ω => L ω (f ω) := stronglyMeasurable_clm_apply hL hf

lemma clm_L {n d : ℕ} {L : Ω → E n →L[ℝ] E d} {f : Ω → E n} {C : ℝ}
    (hL : StronglyMeasurable[m0] L) (hLB : ∀ ω, ‖L ω‖ ≤ C) (hf : MemLp f 2 μ) :
    MemLp (fun ω => L ω (f ω)) 2 μ := memLp_clm_apply hL.aestronglyMeasurable hLB hf

/-- The bound `‖N + G - G'‖ ≤ 3 C`. -/
lemma norm_tilde_le {n d : ℕ} {N G G' : E n →L[ℝ] E d} {C : ℝ} (hN : ‖N‖ ≤ C) (hG : ‖G‖ ≤ C)
    (hG' : ‖G'‖ ≤ C) : ‖N + G - G'‖ ≤ 3 * C := by
  have := (norm_sub_le (N + G) G').trans (add_le_add_right (norm_add_le N G) _)
  linarith

include hrec hx0 hx0L hy0 hy0L hh hhL hg hgL hM hML hM' hM'L in
/-- The iterates are adapted and square integrable. -/
lemma mtts_adapted : ∀ k, (StronglyMeasurable[ℱ k] (x k) ∧ MemLp (x k) 2 μ) ∧
    (StronglyMeasurable[ℱ k] (y k) ∧ MemLp (y k) 2 μ) := by
  intro k
  induction k with
  | zero => exact ⟨⟨hx0, hx0L⟩, ⟨hy0, hy0L⟩⟩
  | succ k ih =>
    obtain ⟨⟨hxm, hxL⟩, ⟨hym, hyL⟩⟩ := ih
    have hmono := ℱ.mono (Nat.le_succ k)
    have hle := ℱ.le (k + 1)
    have hxm' := hxm.mono hmono
    have hym' := hym.mono hmono
    have t11 : StronglyMeasurable[ℱ (k + 1)] fun ω => W.N₁₁ (k + 1) ω + W.G₁₁ k ω - W.G₁₁ (k + 1) ω :=
      ((W.mN₁₁ k).add ((W.mG₁₁ k).mono hmono)).sub (W.mG₁₁ (k + 1))
    have t12 : StronglyMeasurable[ℱ (k + 1)] fun ω => W.N₁₂ (k + 1) ω + W.G₁₂ k ω - W.G₁₂ (k + 1) ω :=
      ((W.mN₁₂ k).add ((W.mG₁₂ k).mono hmono)).sub (W.mG₁₂ (k + 1))
    have t21 : StronglyMeasurable[ℱ (k + 1)] fun ω => W.N₂₁ (k + 1) ω + W.G₂₁ k ω - W.G₂₁ (k + 1) ω :=
      ((W.mN₂₁ k).add ((W.mG₂₁ k).mono hmono)).sub (W.mG₂₁ (k + 1))
    have t22 : StronglyMeasurable[ℱ (k + 1)] fun ω => W.N₂₂ (k + 1) ω + W.G₂₂ k ω - W.G₂₂ (k + 1) ω :=
      ((W.mN₂₂ k).add ((W.mG₂₂ k).mono hmono)).sub (W.mG₂₂ (k + 1))
    have b11 := fun ω => norm_tilde_le (W.bN₁₁ k ω) (W.bG₁₁ k ω) (W.bG₁₁ (k + 1) ω)
    have b12 := fun ω => norm_tilde_le (W.bN₁₂ k ω) (W.bG₁₂ k ω) (W.bG₁₂ (k + 1) ω)
    have b21 := fun ω => norm_tilde_le (W.bN₂₁ k ω) (W.bG₂₁ k ω) (W.bG₂₁ (k + 1) ω)
    have b22 := fun ω => norm_tilde_le (W.bN₂₂ k ω) (W.bG₂₂ k ω) (W.bG₂₂ (k + 1) ω)
    have hfx : x (k + 1) = fun ω => x k ω - β k • (matCLM A₁₁ (x k ω) + matCLM A₁₂ (y k ω))
        - β k • ((W.N₁₁ (k + 1) ω + W.G₁₁ k ω - W.G₁₁ (k + 1) ω) (x k ω)
          + (W.N₁₂ (k + 1) ω + W.G₁₂ k ω - W.G₁₂ (k + 1) ω) (y k ω))
        + β k • (M (k + 1) ω + h k ω - h (k + 1) ω) := funext (hrec.1 k)
    have hfy : y (k + 1) = fun ω => y k ω - γ k • (matCLM A₂₁ (x k ω) + matCLM A₂₂ (y k ω))
        - γ k • ((W.N₂₁ (k + 1) ω + W.G₂₁ k ω - W.G₂₁ (k + 1) ω) (x k ω)
          + (W.N₂₂ (k + 1) ω + W.G₂₂ k ω - W.G₂₂ (k + 1) ω) (y k ω))
        + γ k • (M' (k + 1) ω + g k ω - g (k + 1) ω) := funext (hrec.2 k)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hfx]
      exact ((hxm'.sub ((((matCLM A₁₁).continuous.comp_stronglyMeasurable hxm').add
        ((matCLM A₁₂).continuous.comp_stronglyMeasurable hym')).const_smul (β k))).sub
        (((clm_sm t11 hxm').add (clm_sm t12 hym')).const_smul (β k))).add
        ((((hM k).add ((hh k).mono hmono)).sub (hh (k + 1))).const_smul (β k))
    · rw [hfx]
      exact ((hxL.sub ((((matCLM A₁₁).comp_memLp' hxL).add ((matCLM A₁₂).comp_memLp' hyL)).const_smul
        (β k))).sub (((clm_L (t11.mono hle) b11 hxL).add (clm_L (t12.mono hle) b12 hyL)).const_smul
        (β k))).add ((((hML k).add (hhL k)).sub (hhL (k + 1))).const_smul (β k))
    · rw [hfy]
      exact ((hym'.sub ((((matCLM A₂₁).continuous.comp_stronglyMeasurable hxm').add
        ((matCLM A₂₂).continuous.comp_stronglyMeasurable hym')).const_smul (γ k))).sub
        (((clm_sm t21 hxm').add (clm_sm t22 hym')).const_smul (γ k))).add
        ((((hM' k).add ((hg k).mono hmono)).sub (hg (k + 1))).const_smul (γ k))
    · rw [hfy]
      exact ((hyL.sub ((((matCLM A₂₁).comp_memLp' hxL).add ((matCLM A₂₂).comp_memLp' hyL)).const_smul
        (γ k))).sub (((clm_L (t21.mono hle) b21 hxL).add (clm_L (t22.mono hle) b22 hyL)).const_smul
        (γ k))).add ((((hM'L k).add (hgL k)).sub (hgL (k + 1))).const_smul (γ k))

end Measurability

/-! ### Sizes -/

section Sizes

variable {xk xk1 Mk hk hk1 : Ω → E d₁} {yk yk1 : Ω → E d₂}

/-- `rms (h - (G₁ x + G₂ y)) ≤ rms h + C (rms x + rms y)`. -/
lemma rms_shift_le {n : ℕ} {u : Ω → E n} {L₁ : Ω → E d₁ →L[ℝ] E n} {L₂ : Ω → E d₂ →L[ℝ] E n}
    {C : ℝ} (hC : 0 ≤ C) (hL₁ : StronglyMeasurable[m0] L₁) (hL₂ : StronglyMeasurable[m0] L₂)
    (hB₁ : ∀ ω, ‖L₁ ω‖ ≤ C) (hB₂ : ∀ ω, ‖L₂ ω‖ ≤ C) (huL : MemLp u 2 μ) (hxL : MemLp xk 2 μ)
    (hyL : MemLp yk 2 μ) :
    rms μ (fun ω => u ω - (L₁ ω (xk ω) + L₂ ω (yk ω))) ≤ rms μ u + C * (rms μ xk + rms μ yk) := by
  have h1 := clm_L hL₁ hB₁ hxL (μ := μ)
  have h2 := clm_L hL₂ hB₂ hyL (μ := μ)
  have h12 : MemLp (fun ω => L₁ ω (xk ω) + L₂ ω (yk ω)) 2 μ := h1.add h2
  refine (rms_sub_le' huL h12).trans ?_
  have := (rms_add_le' h1 h2).trans (add_le_add (rms_clm_le hL₁.aestronglyMeasurable hB₁ hC hxL)
    (rms_clm_le hL₂.aestronglyMeasurable hB₂ hC hyL))
  linarith

/-- The increment of a multiplicative recursion:
`x' - x = s ((M + h - h') - (A₁ x + A₂ y + T₁ x + T₂ y))`. -/
lemma rms_incr_le {n : ℕ} {xn xn1 Mn hn hn1 : Ω → E n} {A₁ : Matrix (Fin n) (Fin d₁) ℝ}
    {A₂ : Matrix (Fin n) (Fin d₂) ℝ} {T₁ : Ω → E d₁ →L[ℝ] E n} {T₂ : Ω → E d₂ →L[ℝ] E n}
    {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hT₁ : StronglyMeasurable[m0] T₁)
    (hT₂ : StronglyMeasurable[m0] T₂) (hB₁ : ∀ ω, ‖T₁ ω‖ ≤ C) (hB₂ : ∀ ω, ‖T₂ ω‖ ≤ C)
    (hxL : MemLp xk 2 μ) (hyL : MemLp yk 2 μ) (hML : MemLp Mn 2 μ) (hhL : MemLp hn 2 μ)
    (hh1L : MemLp hn1 2 μ)
    (hrec : ∀ ω, xn1 ω = xn ω - s • (matCLM A₁ (xk ω) + matCLM A₂ (yk ω))
      - s • (T₁ ω (xk ω) + T₂ ω (yk ω)) + s • (Mn ω + hn ω - hn1 ω)) :
    rms μ (fun ω => xn1 ω - xn ω) ≤ s * (rms μ Mn + rms μ hn + rms μ hn1
      + (‖matCLM A₁‖ + C) * rms μ xk + (‖matCLM A₂‖ + C) * rms μ yk) := by
  have e : (fun ω => xn1 ω - xn ω) = fun ω => s • ((Mn ω + hn ω - hn1 ω)
      - ((matCLM A₁ (xk ω) + matCLM A₂ (yk ω)) + (T₁ ω (xk ω) + T₂ ω (yk ω)))) := by
    funext ω; rw [hrec ω]; module
  rw [e, rms_smul, abs_of_nonneg hs]
  refine mul_le_mul_of_nonneg_left ?_ hs
  have hV : MemLp (fun ω => Mn ω + hn ω - hn1 ω) 2 μ := (hML.add hhL).sub hh1L
  have hMh : MemLp (fun ω => Mn ω + hn ω) 2 μ := hML.add hhL
  have hA1 : MemLp (fun ω => matCLM A₁ (xk ω)) 2 μ := (matCLM A₁).comp_memLp' hxL
  have hA2 : MemLp (fun ω => matCLM A₂ (yk ω)) 2 μ := (matCLM A₂).comp_memLp' hyL
  have hA : MemLp (fun ω => matCLM A₁ (xk ω) + matCLM A₂ (yk ω)) 2 μ := hA1.add hA2
  have hT1 := clm_L hT₁ hB₁ hxL (μ := μ)
  have hT2 := clm_L hT₂ hB₂ hyL (μ := μ)
  have hT : MemLp (fun ω => T₁ ω (xk ω) + T₂ ω (yk ω)) 2 μ := hT1.add hT2
  have hw : MemLp (fun ω => (matCLM A₁ (xk ω) + matCLM A₂ (yk ω)) + (T₁ ω (xk ω) + T₂ ω (yk ω)))
    2 μ := hA.add hT
  have t1 := rms_sub_le' hV hw (μ := μ)
  have t2 := (rms_sub_le' hMh hh1L (μ := μ)).trans (add_le_add_right (rms_add_le' hML hhL) _)
  have t3 := rms_add_le' hA hT (μ := μ)
  have t4 := (rms_add_le' hA1 hA2 (μ := μ)).trans (add_le_add (rms_matCLM_le A₁ hxL)
    (rms_matCLM_le A₂ hyL))
  have t5 := (rms_add_le' hT1 hT2 (μ := μ)).trans
    (add_le_add (rms_clm_le hT₁.aestronglyMeasurable hB₁ hC hxL)
      (rms_clm_le hT₂.aestronglyMeasurable hB₂ hC hyL))
  linarith

end Sizes

/-- Covariances of martingale parts perturbed by `u, u'`. -/
lemma norm_crossMoment_sub_sub_sub_le {Mf u : Ω → E d₁} {Mg u' : Ω → E d₂} {Γ}
    (hM : MemLp Mf 2 μ) (hu : MemLp u 2 μ) (hM' : MemLp Mg 2 μ) (hu' : MemLp u' 2 μ) :
    ‖crossMoment μ (fun ω => Mf ω - u ω) (fun ω => Mg ω - u' ω) - Γ‖ ≤
      ‖crossMoment μ Mf Mg - Γ‖ + (rms μ Mf * rms μ u' + rms μ u * rms μ Mg + rms μ u * rms μ u') := by
  have h := norm_crossMoment_sub_sub_le hM hu hM' hu' (μ := μ)
  have e : crossMoment μ (fun ω => Mf ω - u ω) (fun ω => Mg ω - u' ω) - Γ =
      (crossMoment μ (fun ω => Mf ω - u ω) (fun ω => Mg ω - u' ω) - crossMoment μ Mf Mg)
        + (crossMoment μ Mf Mg - Γ) := by abel
  rw [e]
  have := norm_add_le (crossMoment μ (fun ω => Mf ω - u ω) (fun ω => Mg ω - u' ω)
    - crossMoment μ Mf Mg) (crossMoment μ Mf Mg - Γ)
  linarith

/-- Inverting the shift: when the steps are small, `‖x‖ + ‖y‖` is bounded by the shifted
iterates. -/
lemma inv_shift_le {X Y Xs Ys H G nD CN b gm : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hnD : 0 ≤ nD)
    (_hCN : 0 ≤ CN) (_hb : 0 ≤ b) (_hgm : 0 ≤ gm)
    (hsmall : CN * ((1 + 2 * nD) * b + gm) ≤ 1 / 2)
    (h1 : X ≤ Xs + b * H + b * CN * (X + Y))
    (h2 : Y ≤ Ys + nD * X + gm * (G + CN * (X + Y)) + b * nD * (H + CN * (X + Y))) :
    X + Y ≤ 2 * ((1 + nD) * Xs + Ys + (1 + 2 * nD) * b * H + gm * G) := by
  have hS : 0 ≤ X + Y := add_nonneg hX hY
  have k1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + nD)
  have k2 := mul_le_mul_of_nonneg_right hsmall hS
  nlinarith [mul_nonneg hnD hX]

lemma condExp_sub_add_eq_zero [IsFiniteMeasure μ] {ℱ' : MeasurableSpace Ω} {a b c : Ω → E d₁}
    (haL : MemLp a 2 μ) (hbL : MemLp b 2 μ) (hcL : MemLp c 2 μ)
    (ha : ∀ j, μ[fun ω => a ω j | ℱ'] =ᵐ[μ] 0) (hb : ∀ j, μ[fun ω => b ω j | ℱ'] =ᵐ[μ] 0)
    (hc : ∀ j, μ[fun ω => c ω j | ℱ'] =ᵐ[μ] 0) (j : Fin d₁) :
    μ[fun ω => (a ω - (b ω + c ω)) j | ℱ'] =ᵐ[μ] 0 := by
  have ia := (memLp_apply haL j).integrable one_le_two
  have ib := (memLp_apply hbL j).integrable one_le_two
  have ic := (memLp_apply hcL j).integrable one_le_two
  have hsub := condExp_sub ia (ib.add ic) ℱ' (μ := μ)
  have hadd := condExp_add ib ic ℱ' (μ := μ)
  have e : (fun ω => (a ω - (b ω + c ω)) j) =
      (fun ω => a ω j) - ((fun ω => b ω j) + fun ω => c ω j) := by funext ω; simp
  rw [e]
  filter_upwards [hsub, hadd, ha j, hb j, hc j] with ω h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, h4, h5]
  simp

set_option maxHeartbeats 8000000 in
/-- Theorem 4.1 of the write-up when the steps are small for every `k`. -/
theorem tendsto_mtts_of_small [IsProbabilityMeasure μ] {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (hrec : MTTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g W)
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
    (hsmall : ∀ k, W.CN * ((1 + 2 * ‖matCLM D‖) * β k + γ k) ≤ 1 / 2) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  have hadapt := mtts_adapted hrec hx0 hx0L hy0 hy0L hh hhL hg hgL hM hML hM' hM'L
  have hxm := fun k => (hadapt k).1.1
  have hxL := fun k => (hadapt k).1.2
  have hym := fun k => (hadapt k).2.1
  have hyL := fun k => (hadapt k).2.2
  set CN := W.CN
  have hCN := W.CN_nonneg
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hhB 0)
  have hCg0 : 0 ≤ Cg := (integral_norm_sq_nonneg (μ := μ) (g 0)).trans (hgB 0)
  have hCM0 : 0 ≤ CM := (integral_norm_sq_nonneg (μ := μ) (M 1)).trans (hMB 0)
  have hCM'0 : 0 ≤ CM' := (integral_norm_sq_nonneg (μ := μ) (M' 1)).trans (hM'B 0)
  set mh := √Ch
  set mg := √Cg
  set mM := √CM
  set mM' := √CM'
  have rh : ∀ k, rms μ (h k) ≤ mh := fun k => Real.sqrt_le_sqrt (hhB k)
  have rg : ∀ k, rms μ (g k) ≤ mg := fun k => Real.sqrt_le_sqrt (hgB k)
  have rM : ∀ k, rms μ (M (k + 1)) ≤ mM := fun k => Real.sqrt_le_sqrt (hMB k)
  have rM' : ∀ k, rms μ (M' (k + 1)) ≤ mM' := fun k => Real.sqrt_le_sqrt (hM'B k)
  have hmh := Real.sqrt_nonneg Ch
  have hmg := Real.sqrt_nonneg Cg
  have hmM := Real.sqrt_nonneg CM
  have hmM' := Real.sqrt_nonneg CM'
  obtain ⟨B0, hB0⟩ := hβγ.bddAbove_range
  obtain ⟨Bq, hBq_def⟩ : ∃ B, B = max B0 0 := ⟨_, rfl⟩
  have hBq : 0 ≤ Bq := hBq_def ▸ le_max_right _ _
  have hbq : ∀ k, β k ≤ Bq * γ k := fun k => by
    have h1 : β k / γ k ≤ Bq := (hB0 ⟨k, rfl⟩).trans (hBq_def ▸ le_max_left _ _)
    rwa [div_le_iff₀ (hγ.pos k)] at h1
  obtain ⟨Bb, hBb0, hBb⟩ := bdd_of_tendsto_zero hβ.tendsto_zero
  obtain ⟨Bg, hBg0, hBg⟩ := bdd_of_tendsto_zero hγ.tendsto_zero
  set nD := ‖matCLM D‖
  have hnD : 0 ≤ nD := norm_nonneg _
  set K1 := mM + 2 * mh + (‖matCLM A₁₁‖ + 3 * CN) + (‖matCLM A₁₂‖ + 3 * CN)
  set K2 := mM' + 2 * mg + (‖matCLM A₂₁‖ + 3 * CN) + (‖matCLM A₂₂‖ + 3 * CN)
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  set C := (mh + CN) + (mg + CN) + (mM + CN) + (mM' + CN) + CN * (Bq * K1 + K2)
    + (1 + Bb * K1 + Bg * K2) + (8 * (1 + nD) + 8 * ((1 + 2 * nD) * Bq * mh + mg))
    + (CN * (2 * mM + 2 * mM') + CN ^ 2)
  have p1 : 0 ≤ mh + CN := by positivity
  have p2 : 0 ≤ mg + CN := by positivity
  have p3 : 0 ≤ mM + CN := by positivity
  have p4 : 0 ≤ mM' + CN := by positivity
  have p5 : 0 ≤ CN * (Bq * K1 + K2) := by positivity
  have p6 : 0 ≤ 1 + Bb * K1 + Bg * K2 := by positivity
  have p7 : 0 ≤ 8 * (1 + nD) + 8 * ((1 + 2 * nD) * Bq * mh + mg) := by positivity
  have p8 : 0 ≤ CN * (2 * mM + 2 * mM') + CN ^ 2 := by positivity
  have hC : 0 ≤ C := by positivity
  have le_C : ∀ {q : ℝ}, (q = mh + CN ∨ q = mg + CN ∨ q = mM + CN ∨ q = mM' + CN ∨
      q = CN * (Bq * K1 + K2) ∨ q = 1 + Bb * K1 + Bg * K2 ∨
      q = 8 * (1 + nD) + 8 * ((1 + 2 * nD) * Bq * mh + mg) ∨ q = CN * (2 * mM + 2 * mM') + CN ^ 2) →
      q ≤ C := by
    intro q hq
    rcases hq with h | h | h | h | h | h | h | h <;> rw [h] <;> simp only [C] <;> linarith
  set R := fun k => rms μ (x k) + rms μ (y k)
  have hR0 : ∀ k, 0 ≤ R k := fun k => add_nonneg (rms_nonneg _) (rms_nonneg _)
  have up : ∀ {q : ℝ} (k : ℕ), (q = mh + CN ∨ q = mg + CN ∨ q = mM + CN ∨ q = mM' + CN ∨
      q = CN * (Bq * K1 + K2) ∨ q = 1 + Bb * K1 + Bg * K2 ∨
      q = 8 * (1 + nD) + 8 * ((1 + 2 * nD) * Bq * mh + mg) ∨ q = CN * (2 * mM + 2 * mM') + CN ^ 2) →
      q * (1 + R k) ≤ C * (1 + R k) := fun k hq =>
    mul_le_mul_of_nonneg_right (le_C hq) (by linarith [hR0 k])
  -- the processes
  have mT₁₁ : ∀ k, StronglyMeasurable[m0] fun ω => W.N₁₁ (k + 1) ω + W.G₁₁ k ω - W.G₁₁ (k + 1) ω :=
    fun k => (((W.mN₁₁ k).add ((W.mG₁₁ k).mono (ℱ.mono (Nat.le_succ k)))).sub (W.mG₁₁ (k + 1))).mono
      (ℱ.le _)
  have mT₁₂ : ∀ k, StronglyMeasurable[m0] fun ω => W.N₁₂ (k + 1) ω + W.G₁₂ k ω - W.G₁₂ (k + 1) ω :=
    fun k => (((W.mN₁₂ k).add ((W.mG₁₂ k).mono (ℱ.mono (Nat.le_succ k)))).sub (W.mG₁₂ (k + 1))).mono
      (ℱ.le _)
  have mT₂₁ : ∀ k, StronglyMeasurable[m0] fun ω => W.N₂₁ (k + 1) ω + W.G₂₁ k ω - W.G₂₁ (k + 1) ω :=
    fun k => (((W.mN₂₁ k).add ((W.mG₂₁ k).mono (ℱ.mono (Nat.le_succ k)))).sub (W.mG₂₁ (k + 1))).mono
      (ℱ.le _)
  have mT₂₂ : ∀ k, StronglyMeasurable[m0] fun ω => W.N₂₂ (k + 1) ω + W.G₂₂ k ω - W.G₂₂ (k + 1) ω :=
    fun k => (((W.mN₂₂ k).add ((W.mG₂₂ k).mono (ℱ.mono (Nat.le_succ k)))).sub (W.mG₂₂ (k + 1))).mono
      (ℱ.le _)
  have hdx : ∀ k, rms μ (fun ω => x (k + 1) ω - x k ω) ≤ β k * K1 * (1 + R k) := by
    intro k
    have := rms_incr_le (μ := μ) (s := β k) (C := 3 * CN) (hβ.pos k).le (by positivity)
      (mT₁₁ k) (mT₁₂ k) (fun ω => norm_tilde_le (W.bN₁₁ k ω) (W.bG₁₁ k ω) (W.bG₁₁ (k + 1) ω))
      (fun ω => norm_tilde_le (W.bN₁₂ k ω) (W.bG₁₂ k ω) (W.bG₁₂ (k + 1) ω)) (hxL k) (hyL k)
      (hML k) (hhL k) (hhL (k + 1)) (hrec.1 k)
    refine this.trans ?_
    have hb := (hβ.pos k).le
    have e1 := mul_le_mul_of_nonneg_left (rh k) hb
    have q1 : 0 ≤ ‖matCLM A₁₁‖ + 3 * CN := by positivity
    have q2 : 0 ≤ ‖matCLM A₁₂‖ + 3 * CN := by positivity
    have hx := rms_nonneg (x k) (μ := μ)
    have hy := rms_nonneg (y k) (μ := μ)
    have hxR : rms μ (x k) ≤ R k := by simp only [R]; linarith
    have hyR : rms μ (y k) ≤ R k := by simp only [R]; linarith
    have f1 := mul_le_mul_of_nonneg_left hxR q1
    have f2 := mul_le_mul_of_nonneg_left hyR q2
    have f3 := mul_le_mul_of_nonneg_left (by linarith [hR0 k] : (1 : ℝ) ≤ 1 + R k) (by positivity :
      (0 : ℝ) ≤ mM + 2 * mh)
    have g1 : rms μ (M (k + 1)) + rms μ (h k) + rms μ (h (k + 1)) + (‖matCLM A₁₁‖ + 3 * CN)
        * rms μ (x k) + (‖matCLM A₁₂‖ + 3 * CN) * rms μ (y k) ≤ K1 * (1 + R k) := by
      have := rM k; have := rh k; have := rh (k + 1)
      have e : K1 * (1 + R k) = (mM + 2 * mh) * (1 + R k) + (‖matCLM A₁₁‖ + 3 * CN) * (1 + R k)
          + (‖matCLM A₁₂‖ + 3 * CN) * (1 + R k) := by simp only [K1]; ring
      have f4 := mul_le_mul_of_nonneg_left (by linarith [hR0 k] : R k ≤ 1 + R k) q1
      have f5 := mul_le_mul_of_nonneg_left (by linarith [hR0 k] : R k ≤ 1 + R k) q2
      rw [e]; nlinarith
    have := mul_le_mul_of_nonneg_left g1 hb
    linarith only [this, show β k * (K1 * (1 + R k)) = β k * K1 * (1 + R k) by ring]
  have hdy : ∀ k, rms μ (fun ω => y (k + 1) ω - y k ω) ≤ γ k * K2 * (1 + R k) := by
    intro k
    have := rms_incr_le (μ := μ) (s := γ k) (C := 3 * CN) (hγ.pos k).le (by positivity)
      (mT₂₁ k) (mT₂₂ k) (fun ω => norm_tilde_le (W.bN₂₁ k ω) (W.bG₂₁ k ω) (W.bG₂₁ (k + 1) ω))
      (fun ω => norm_tilde_le (W.bN₂₂ k ω) (W.bG₂₂ k ω) (W.bG₂₂ (k + 1) ω)) (hxL k) (hyL k)
      (hM'L k) (hgL k) (hgL (k + 1)) (hrec.2 k)
    refine this.trans ?_
    have hb := (hγ.pos k).le
    have q1 : 0 ≤ ‖matCLM A₂₁‖ + 3 * CN := by positivity
    have q2 : 0 ≤ ‖matCLM A₂₂‖ + 3 * CN := by positivity
    have hx := rms_nonneg (x k) (μ := μ)
    have hy := rms_nonneg (y k) (μ := μ)
    have hxR : rms μ (x k) ≤ R k := by simp only [R]; linarith
    have hyR : rms μ (y k) ≤ R k := by simp only [R]; linarith
    have g1 : rms μ (M' (k + 1)) + rms μ (g k) + rms μ (g (k + 1)) + (‖matCLM A₂₁‖ + 3 * CN)
        * rms μ (x k) + (‖matCLM A₂₂‖ + 3 * CN) * rms μ (y k) ≤ K2 * (1 + R k) := by
      have := rM' k; have := rg k; have := rg (k + 1)
      have e : K2 * (1 + R k) = (mM' + 2 * mg) * (1 + R k) + (‖matCLM A₂₁‖ + 3 * CN) * (1 + R k)
          + (‖matCLM A₂₂‖ + 3 * CN) * (1 + R k) := by simp only [K2]; ring
      have f1 := mul_le_mul_of_nonneg_left hxR q1
      have f2 := mul_le_mul_of_nonneg_left hyR q2
      have f3 := mul_le_mul_of_nonneg_left (by linarith [hR0 k] : (1 : ℝ) ≤ 1 + R k) (by positivity :
        (0 : ℝ) ≤ mM' + 2 * mg)
      have f4 := mul_le_mul_of_nonneg_left (by linarith [hR0 k] : R k ≤ 1 + R k) q1
      have f5 := mul_le_mul_of_nonneg_left (by linarith [hR0 k] : R k ≤ 1 + R k) q2
      rw [e]; nlinarith
    have := mul_le_mul_of_nonneg_left g1 hb
    linarith only [this, show γ k * (K2 * (1 + R k)) = γ k * K2 * (1 + R k) by ring]
  have hdxL : ∀ k, MemLp (fun ω => x (k + 1) ω - x k ω) 2 μ := fun k => (hxL (k + 1)).sub (hxL k)
  have hdyL : ∀ k, MemLp (fun ω => y (k + 1) ω - y k ω) 2 μ := fun k => (hyL (k + 1)).sub (hyL k)
  have hincr : ∀ k, CN * (rms μ (fun ω => x (k + 1) ω - x k ω)
      + rms μ (fun ω => y (k + 1) ω - y k ω)) ≤ C * γ k * (1 + R k) := by
    intro k
    have h1 := hdx k
    have h2 := hdy k
    have hbq' := mul_le_mul_of_nonneg_right (hbq k) (mul_nonneg hK1 (by linarith [hR0 k] :
      (0 : ℝ) ≤ 1 + R k))
    have h3 : CN * (Bq * K1 + K2) * γ k * (1 + R k) ≤ C * γ k * (1 + R k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_C (by tauto)) (hγ.pos k).le)
        (by linarith [hR0 k])
    have e : CN * (Bq * K1 + K2) * γ k * (1 + R k) =
        CN * (Bq * γ k * (K1 * (1 + R k)) + γ k * K2 * (1 + R k)) := by ring
    have h4 := mul_le_mul_of_nonneg_left (add_le_add (h1.trans
      (show β k * K1 * (1 + R k) ≤ Bq * γ k * (K1 * (1 + R k)) by
        linarith only [hbq', show β k * K1 * (1 + R k) = β k * (K1 * (1 + R k)) by ring])) h2) hCN
    linarith
  have rρ : ∀ k, rms μ (W.ρ x y k) ≤ C * γ k * (1 + R k) := by
    intro k
    have h1 := clm_L ((W.mG₁₁ (k + 1)).mono (ℱ.le _)) (W.bG₁₁ (k + 1)) (hdxL k) (μ := μ)
    have h2 := clm_L ((W.mG₁₂ (k + 1)).mono (ℱ.le _)) (W.bG₁₂ (k + 1)) (hdyL k) (μ := μ)
    have := (rms_add_le' h1 h2).trans (add_le_add
      (rms_clm_le ((W.mG₁₁ (k + 1)).mono (ℱ.le _)).aestronglyMeasurable (W.bG₁₁ (k + 1)) hCN
        (hdxL k))
      (rms_clm_le ((W.mG₁₂ (k + 1)).mono (ℱ.le _)).aestronglyMeasurable (W.bG₁₂ (k + 1)) hCN
        (hdyL k)))
    exact this.trans (by linarith [hincr k])
  have rρ' : ∀ k, rms μ (W.ρ' x y k) ≤ C * γ k * (1 + R k) := by
    intro k
    have h1 := clm_L ((W.mG₂₁ (k + 1)).mono (ℱ.le _)) (W.bG₂₁ (k + 1)) (hdxL k) (μ := μ)
    have h2 := clm_L ((W.mG₂₂ (k + 1)).mono (ℱ.le _)) (W.bG₂₂ (k + 1)) (hdyL k) (μ := μ)
    have := (rms_add_le' h1 h2).trans (add_le_add
      (rms_clm_le ((W.mG₂₁ (k + 1)).mono (ℱ.le _)).aestronglyMeasurable (W.bG₂₁ (k + 1)) hCN
        (hdxL k))
      (rms_clm_le ((W.mG₂₂ (k + 1)).mono (ℱ.le _)).aestronglyMeasurable (W.bG₂₂ (k + 1)) hCN
        (hdyL k)))
    exact this.trans (by linarith [hincr k])
  have hR1 : ∀ k, R (k + 1) ≤ C * (1 + R k) := by
    intro k
    have ex : x (k + 1) = fun ω => x k ω + (x (k + 1) ω - x k ω) := by funext ω; abel
    have ey : y (k + 1) = fun ω => y k ω + (y (k + 1) ω - y k ω) := by funext ω; abel
    have h1 : rms μ (x (k + 1)) ≤ rms μ (x k) + rms μ (fun ω => x (k + 1) ω - x k ω) := by
      conv_lhs => rw [ex]
      exact rms_add_le' (hxL k) (hdxL k)
    have h2 : rms μ (y (k + 1)) ≤ rms μ (y k) + rms μ (fun ω => y (k + 1) ω - y k ω) := by
      conv_lhs => rw [ey]
      exact rms_add_le' (hyL k) (hdyL k)
    have h3 := hdx k
    have h4 := hdy k
    have hb1 := mul_le_mul_of_nonneg_right (hBb k) (mul_nonneg hK1 (by linarith [hR0 k] :
      (0 : ℝ) ≤ 1 + R k))
    have hb2 := mul_le_mul_of_nonneg_right (hBg k) (mul_nonneg hK2 (by linarith [hR0 k] :
      (0 : ℝ) ≤ 1 + R k))
    have h5 := up k (q := 1 + Bb * K1 + Bg * K2) (by tauto)
    simp only [R] at h5 hb1 hb2 h3 h4 ⊢
    nlinarith [hR0 k]
  -- sizes of the shifts and of the martingale parts
  have shiftC : ∀ k {u : ℝ}, u ≤ mh + CN * R k ∨ u ≤ mg + CN * R k ∨ u ≤ mM + CN * R k ∨
      u ≤ mM' + CN * R k → u ≤ C * (1 + R k) := by
    intro k u hu
    have hRk := hR0 k
    rcases hu with h | h | h | h
    · exact h.trans (by have := up k (q := mh + CN) (by tauto); nlinarith)
    · exact h.trans (by have := up k (q := mg + CN) (by tauto); nlinarith)
    · exact h.trans (by have := up k (q := mM + CN) (by tauto); nlinarith)
    · exact h.trans (by have := up k (q := mM' + CN) (by tauto); nlinarith)
  have rη : ∀ k, rms μ (W.η x y h k) ≤ C * (1 + R k) := fun k => by
    have := rms_shift_le (μ := μ) hCN ((W.mG₁₁ k).mono (ℱ.le k)) ((W.mG₁₂ k).mono (ℱ.le k))
      (W.bG₁₁ k) (W.bG₁₂ k) (hhL k) (hxL k) (hyL k)
    exact shiftC k (Or.inl (this.trans (by simp only [R]; linarith [rh k])))
  have rζ : ∀ k, rms μ (W.ζ x y g k) ≤ C * (1 + R k) := fun k => by
    have := rms_shift_le (μ := μ) hCN ((W.mG₂₁ k).mono (ℱ.le k)) ((W.mG₂₂ k).mono (ℱ.le k))
      (W.bG₂₁ k) (W.bG₂₂ k) (hgL k) (hxL k) (hyL k)
    exact shiftC k (Or.inr (Or.inl (this.trans (by simp only [R]; linarith [rg k]))))
  have rm : ∀ k, rms μ (W.m x y M (k + 1)) ≤ C * (1 + R k) := fun k => by
    have := rms_shift_le (μ := μ) hCN ((W.mN₁₁ k).mono (ℱ.le _)) ((W.mN₁₂ k).mono (ℱ.le _))
      (W.bN₁₁ k) (W.bN₁₂ k) (hML k) (hxL k) (hyL k)
    exact shiftC k (Or.inr (Or.inr (Or.inl (this.trans (by simp only [R]; linarith [rM k])))))
  have rm' : ∀ k, rms μ (W.m' x y M' (k + 1)) ≤ C * (1 + R k) := fun k => by
    have := rms_shift_le (μ := μ) hCN ((W.mN₂₁ k).mono (ℱ.le _)) ((W.mN₂₂ k).mono (ℱ.le _))
      (W.bN₂₁ k) (W.bN₂₂ k) (hM'L k) (hxL k) (hyL k)
    exact shiftC k (Or.inr (Or.inr (Or.inr (this.trans (by simp only [R]; linarith [rM' k])))))
  -- measurability and integrability
  have hηm : ∀ k, StronglyMeasurable[ℱ k] (W.η x y h k) := fun k =>
    (hh k).sub ((clm_sm (W.mG₁₁ k) (hxm k)).add (clm_sm (W.mG₁₂ k) (hym k)))
  have hζm : ∀ k, StronglyMeasurable[ℱ k] (W.ζ x y g k) := fun k =>
    (hg k).sub ((clm_sm (W.mG₂₁ k) (hxm k)).add (clm_sm (W.mG₂₂ k) (hym k)))
  have hηL : ∀ k, MemLp (W.η x y h k) 2 μ := fun k =>
    (hhL k).sub ((clm_L ((W.mG₁₁ k).mono (ℱ.le k)) (W.bG₁₁ k) (hxL k)).add
      (clm_L ((W.mG₁₂ k).mono (ℱ.le k)) (W.bG₁₂ k) (hyL k)))
  have hζL : ∀ k, MemLp (W.ζ x y g k) 2 μ := fun k =>
    (hgL k).sub ((clm_L ((W.mG₂₁ k).mono (ℱ.le k)) (W.bG₂₁ k) (hxL k)).add
      (clm_L ((W.mG₂₂ k).mono (ℱ.le k)) (W.bG₂₂ k) (hyL k)))
  have hNx : ∀ k, MemLp (fun ω => W.N₁₁ (k + 1) ω (x k ω)) 2 μ := fun k =>
    clm_L ((W.mN₁₁ k).mono (ℱ.le _)) (W.bN₁₁ k) (hxL k)
  have hNy : ∀ k, MemLp (fun ω => W.N₁₂ (k + 1) ω (y k ω)) 2 μ := fun k =>
    clm_L ((W.mN₁₂ k).mono (ℱ.le _)) (W.bN₁₂ k) (hyL k)
  have hNx' : ∀ k, MemLp (fun ω => W.N₂₁ (k + 1) ω (x k ω)) 2 μ := fun k =>
    clm_L ((W.mN₂₁ k).mono (ℱ.le _)) (W.bN₂₁ k) (hxL k)
  have hNy' : ∀ k, MemLp (fun ω => W.N₂₂ (k + 1) ω (y k ω)) 2 μ := fun k =>
    clm_L ((W.mN₂₂ k).mono (ℱ.le _)) (W.bN₂₂ k) (hyL k)
  have hmm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W.m x y M (k + 1)) := fun k =>
    (hM k).sub ((clm_sm (W.mN₁₁ k) ((hxm k).mono (ℱ.mono (Nat.le_succ k)))).add
      (clm_sm (W.mN₁₂ k) ((hym k).mono (ℱ.mono (Nat.le_succ k)))))
  have hm'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W.m' x y M' (k + 1)) := fun k =>
    (hM' k).sub ((clm_sm (W.mN₂₁ k) ((hxm k).mono (ℱ.mono (Nat.le_succ k)))).add
      (clm_sm (W.mN₂₂ k) ((hym k).mono (ℱ.mono (Nat.le_succ k)))))
  have hmL : ∀ k, MemLp (W.m x y M (k + 1)) 2 μ := fun k => (hML k).sub ((hNx k).add (hNy k))
  have hm'L : ∀ k, MemLp (W.m' x y M' (k + 1)) 2 μ := fun k => (hM'L k).sub ((hNx' k).add (hNy' k))
  have hρm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W.ρ x y k) := fun k =>
    (clm_sm (W.mG₁₁ (k + 1)) ((hxm (k + 1)).sub ((hxm k).mono (ℱ.mono (Nat.le_succ k))))).add
      (clm_sm (W.mG₁₂ (k + 1)) ((hym (k + 1)).sub ((hym k).mono (ℱ.mono (Nat.le_succ k)))))
  have hρ'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (W.ρ' x y k) := fun k =>
    (clm_sm (W.mG₂₁ (k + 1)) ((hxm (k + 1)).sub ((hxm k).mono (ℱ.mono (Nat.le_succ k))))).add
      (clm_sm (W.mG₂₂ (k + 1)) ((hym (k + 1)).sub ((hym k).mono (ℱ.mono (Nat.le_succ k)))))
  have hρL : ∀ k, MemLp (W.ρ x y k) 2 μ := fun k =>
    (clm_L ((W.mG₁₁ (k + 1)).mono (ℱ.le _)) (W.bG₁₁ (k + 1)) (hdxL k)).add
      (clm_L ((W.mG₁₂ (k + 1)).mono (ℱ.le _)) (W.bG₁₂ (k + 1)) (hdyL k))
  have hρ'L : ∀ k, MemLp (W.ρ' x y k) 2 μ := fun k =>
    (clm_L ((W.mG₂₁ (k + 1)).mono (ℱ.le _)) (W.bG₂₁ (k + 1)) (hdxL k)).add
      (clm_L ((W.mG₂₂ (k + 1)).mono (ℱ.le _)) (W.bG₂₂ (k + 1)) (hdyL k))
  -- martingale property
  have hmart_m : ∀ k j, μ[fun ω => W.m x y M (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j =>
    condExp_sub_add_eq_zero (hML k) (hNx k) (hNy k) (hmart k)
      (condExp_clm_apply_eq_zero ((W.mN₁₁ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₁₁ k)
        (hxm k) (hxL k) (W.mart₁₁ k))
      (condExp_clm_apply_eq_zero ((W.mN₁₂ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₁₂ k)
        (hym k) (hyL k) (W.mart₁₂ k)) j
  have hmart_m' : ∀ k j, μ[fun ω => W.m' x y M' (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j =>
    condExp_sub_add_eq_zero (hM'L k) (hNx' k) (hNy' k) (hmart' k)
      (condExp_clm_apply_eq_zero ((W.mN₂₁ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₂₁ k)
        (hxm k) (hxL k) (W.mart₂₁ k))
      (condExp_clm_apply_eq_zero ((W.mN₂₂ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₂₂ k)
        (hym k) (hyL k) (W.mart₂₂ k)) j
  -- inverting the shift
  have hinv : ∀ k, R k ≤ C * (rms μ (ttsX β x (W.η x y h) k)
      + rms μ (ttsY D β γ x (W.η x y h) y (W.ζ x y g) k) + γ k) := by
    intro k
    set xs := ttsX β x (W.η x y h) k
    set ys := ttsY D β γ x (W.η x y h) y (W.ζ x y g) k
    have hb := (hβ.pos k).le
    have hgk := (hγ.pos k).le
    have pw : ∀ ω, ‖x k ω‖ + ‖y k ω‖ ≤ 2 * ((1 + nD) * ‖xs ω‖ + 1 * ‖ys ω‖
        + ((1 + 2 * nD) * β k) * ‖h k ω‖ + γ k * ‖g k ω‖) := by
      intro ω
      have hGx : ‖W.G₁₁ k ω (x k ω) + W.G₁₂ k ω (y k ω)‖ ≤ CN * (‖x k ω‖ + ‖y k ω‖) :=
        (norm_add_le _ _).trans (by
          have := norm_clm_apply_le (W.bG₁₁ k ω) (x k ω)
          have := norm_clm_apply_le (W.bG₁₂ k ω) (y k ω)
          linarith)
      have hGy : ‖W.G₂₁ k ω (x k ω) + W.G₂₂ k ω (y k ω)‖ ≤ CN * (‖x k ω‖ + ‖y k ω‖) :=
        (norm_add_le _ _).trans (by
          have := norm_clm_apply_le (W.bG₂₁ k ω) (x k ω)
          have := norm_clm_apply_le (W.bG₂₂ k ω) (y k ω)
          linarith)
      have hη : ‖W.η x y h k ω‖ ≤ ‖h k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖) :=
        (norm_sub_le _ _).trans (add_le_add_left hGx _)
      have hζ : ‖W.ζ x y g k ω‖ ≤ ‖g k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖) :=
        (norm_sub_le _ _).trans (add_le_add_left hGy _)
      have h1 : ‖x k ω‖ ≤ ‖xs ω‖ + β k * ‖h k ω‖ + β k * CN * (‖x k ω‖ + ‖y k ω‖) := by
        have e : x k ω = xs ω - β k • W.η x y h k ω := by simp only [xs, ttsX]; abel
        have e' : ‖x k ω‖ = ‖xs ω - β k • W.η x y h k ω‖ := congrArg norm e
        have t := norm_sub_le (xs ω) (β k • W.η x y h k ω)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb] at t
        have := mul_le_mul_of_nonneg_left hη hb
        linarith only [e', t, this, show β k * (‖h k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖)) =
          β k * ‖h k ω‖ + β k * CN * (‖x k ω‖ + ‖y k ω‖) by ring]
      have h2 : ‖y k ω‖ ≤ ‖ys ω‖ + nD * ‖x k ω‖ + γ k * (‖g k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖))
          + β k * nD * (‖h k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖)) := by
        have e : y k ω = ys ω - matCLM D (x k ω) - γ k • W.ζ x y g k ω
            - β k • matCLM D (W.η x y h k ω) := by simp only [ys, ttsY]; abel
        have e' : ‖y k ω‖ = ‖ys ω - matCLM D (x k ω) - γ k • W.ζ x y g k ω
            - β k • matCLM D (W.η x y h k ω)‖ := congrArg norm e
        have t1 := norm_sub_le (ys ω - matCLM D (x k ω) - γ k • W.ζ x y g k ω)
          (β k • matCLM D (W.η x y h k ω))
        have t2 := norm_sub_le (ys ω - matCLM D (x k ω)) (γ k • W.ζ x y g k ω)
        have t3 := norm_sub_le (ys ω) (matCLM D (x k ω))
        have n1 : ‖matCLM D (x k ω)‖ ≤ nD * ‖x k ω‖ := (matCLM D).le_opNorm _
        have n2 : ‖γ k • W.ζ x y g k ω‖ ≤ γ k * (‖g k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgk]
          exact mul_le_mul_of_nonneg_left hζ hgk
        have n3 : ‖β k • matCLM D (W.η x y h k ω)‖ ≤
            β k * nD * (‖h k ω‖ + CN * (‖x k ω‖ + ‖y k ω‖)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, mul_assoc]
          exact mul_le_mul_of_nonneg_left (((matCLM D).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hη hnD)) hb
        linarith
      have := inv_shift_le (norm_nonneg (x k ω)) (norm_nonneg (y k ω)) hnD hCN hb hgk (hsmall k)
        h1 h2
      linarith only [this, show 2 * ((1 + nD) * ‖xs ω‖ + ‖ys ω‖ + (1 + 2 * nD) * β k * ‖h k ω‖
        + γ k * ‖g k ω‖) = 2 * ((1 + nD) * ‖xs ω‖ + 1 * ‖ys ω‖ + ((1 + 2 * nD) * β k) * ‖h k ω‖
        + γ k * ‖g k ω‖) by ring]
    have hxsL : MemLp xs 2 μ := (hxL k).add ((hηL k).const_smul (β k))
    have hysL : MemLp ys 2 μ := ((((hyL k).add ((matCLM D).comp_memLp' (hxL k))).add
      ((hζL k).const_smul (γ k))).add (((matCLM D).comp_memLp' (hηL k)).const_smul (β k)))
    have q1 : 0 ≤ (1 + 2 * nD) * β k := by positivity
    have rx := rms_le_of_norm_le4 (μ := μ) (hxL k) hxsL hysL (hhL k) (hgL k) zero_le_two
      (by positivity : (0 : ℝ) ≤ 1 + nD) zero_le_one q1 hgk
      (fun ω => by have := pw ω; have := norm_nonneg (y k ω); linarith)
    have ry := rms_le_of_norm_le4 (μ := μ) (hyL k) hxsL hysL (hhL k) (hgL k) zero_le_two
      (by positivity : (0 : ℝ) ≤ 1 + nD) zero_le_one q1 hgk
      (fun ω => by have := pw ω; have := norm_nonneg (x k ω); linarith)
    have e1 := mul_le_mul_of_nonneg_left (rh k) q1
    have e2 := mul_le_mul_of_nonneg_left (rg k) hgk
    have e3 : (1 + 2 * nD) * β k * mh ≤ (1 + 2 * nD) * Bq * mh * γ k := by
      have := mul_le_mul_of_nonneg_left (hbq k) (by positivity : (0 : ℝ) ≤ (1 + 2 * nD) * mh)
      linarith only [this, show (1 + 2 * nD) * mh * β k = (1 + 2 * nD) * β k * mh by ring,
        show (1 + 2 * nD) * mh * (Bq * γ k) = (1 + 2 * nD) * Bq * mh * γ k by ring]
    have hP := le_C (q := 8 * (1 + nD) + 8 * ((1 + 2 * nD) * Bq * mh + mg)) (by tauto)
    have hxs0 := rms_nonneg xs (μ := μ)
    have hys0 := rms_nonneg ys (μ := μ)
    have q8 : 0 ≤ 8 * ((1 + 2 * nD) * Bq * mh + mg) := by positivity
    have f1 : 8 * (1 + nD) * rms μ xs ≤ C * rms μ xs :=
      mul_le_mul_of_nonneg_right (by linarith) hxs0
    have f2 : 8 * rms μ ys ≤ C * rms μ ys :=
      mul_le_mul_of_nonneg_right (by linarith) hys0
    have f3 : 8 * ((1 + 2 * nD) * Bq * mh + mg) * γ k ≤ C * γ k :=
      mul_le_mul_of_nonneg_right (by linarith) hgk
    simp only [R]
    nlinarith
  -- the covariance errors
  set δ₁ := fun k => ‖secondMoment μ (M (k + 1)) - Γ₁₁‖
  set δ₂ := fun k => ‖crossMoment μ (M (k + 1)) (M' (k + 1)) - Γ₁₂‖
  set δ₃ := fun k => ‖secondMoment μ (M' (k + 1)) - Γ₂₂‖
  have ru : ∀ k, rms μ (fun ω => W.N₁₁ (k + 1) ω (x k ω) + W.N₁₂ (k + 1) ω (y k ω)) ≤ CN * R k :=
    fun k => (rms_add_le' (hNx k) (hNy k)).trans (by
      have := rms_clm_le ((W.mN₁₁ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₁₁ k) hCN (hxL k)
      have := rms_clm_le ((W.mN₁₂ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₁₂ k) hCN (hyL k)
      simp only [R]; linarith)
  have ru' : ∀ k, rms μ (fun ω => W.N₂₁ (k + 1) ω (x k ω) + W.N₂₂ (k + 1) ω (y k ω)) ≤ CN * R k :=
    fun k => (rms_add_le' (hNx' k) (hNy' k)).trans (by
      have := rms_clm_le ((W.mN₂₁ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₂₁ k) hCN (hxL k)
      have := rms_clm_le ((W.mN₂₂ k).mono (ℱ.le _)).aestronglyMeasurable (W.bN₂₂ k) hCN (hyL k)
      simp only [R]; linarith)
  have hP8 := le_C (q := CN * (2 * mM + 2 * mM') + CN ^ 2) (by tauto)
  have devB : ∀ k {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ mM ∨ a ≤ mM' → b ≤ mM ∨ b ≤ mM' →
      ∀ {u u' : ℝ}, 0 ≤ u → 0 ≤ u' → u ≤ CN * R k → u' ≤ CN * R k →
      a * u' + u * b + u * u' ≤ C * (R k + R k ^ 2) := by
    intro k a b ha hb hab hbb u u' hu hu' hu1 hu'1
    have hRk := hR0 k
    have hab' : a ≤ mM + mM' := by rcases hab with h | h <;> linarith
    have hbb' : b ≤ mM + mM' := by rcases hbb with h | h <;> linarith
    have k1 : a * u' ≤ (mM + mM') * (CN * R k) := mul_le_mul hab' hu'1 hu' (by positivity)
    have k2 : u * b ≤ (CN * R k) * (mM + mM') := mul_le_mul hu1 hbb' hb (by positivity)
    have k3 : u * u' ≤ (CN * R k) * (CN * R k) := mul_le_mul hu1 hu'1 hu' (by positivity)
    have k4 : (CN * (2 * mM + 2 * mM') + CN ^ 2) * (R k + R k ^ 2) ≤ C * (R k + R k ^ 2) :=
      mul_le_mul_of_nonneg_right hP8 (by positivity)
    have n1 : 0 ≤ CN * (2 * mM + 2 * mM') * R k ^ 2 := by positivity
    have n2 : 0 ≤ CN ^ 2 * R k := by positivity
    linarith only [k1, k2, k3, k4, n1, n2,
      show (CN * (2 * mM + 2 * mM') + CN ^ 2) * (R k + R k ^ 2) = CN * (2 * mM + 2 * mM') * R k
        + CN * (2 * mM + 2 * mM') * R k ^ 2 + CN ^ 2 * R k + CN ^ 2 * R k ^ 2 by ring,
      show (mM + mM') * (CN * R k) + CN * R k * (mM + mM') + CN * R k * (CN * R k) =
        CN * (2 * mM + 2 * mM') * R k + CN ^ 2 * R k ^ 2 by ring]
  have dev₁ : ∀ k, ‖secondMoment μ (W.m x y M (k + 1)) - Γ₁₁‖ ≤ δ₁ k + C * (R k + R k ^ 2) := by
    intro k
    have := norm_crossMoment_sub_sub_sub_le (Γ := Γ₁₁) (hML k) ((hNx k).add (hNy k)) (hML k)
      ((hNx k).add (hNy k)) (μ := μ)
    refine this.trans (add_le_add_left (devB k (rms_nonneg _) (rms_nonneg _) (Or.inl (rM k))
      (Or.inl (rM k)) (rms_nonneg _) (rms_nonneg _) (ru k) (ru k)) _)
  have dev₂ : ∀ k, ‖crossMoment μ (W.m x y M (k + 1)) (W.m' x y M' (k + 1)) - Γ₁₂‖ ≤
      δ₂ k + C * (R k + R k ^ 2) := by
    intro k
    have := norm_crossMoment_sub_sub_sub_le (Γ := Γ₁₂) (hML k) ((hNx k).add (hNy k)) (hM'L k)
      ((hNx' k).add (hNy' k)) (μ := μ)
    refine this.trans (add_le_add_left (devB k (rms_nonneg _) (rms_nonneg _) (Or.inl (rM k))
      (Or.inr (rM' k)) (rms_nonneg _) (rms_nonneg _) (ru k) (ru' k)) _)
  have dev₃ : ∀ k, ‖secondMoment μ (W.m' x y M' (k + 1)) - Γ₂₂‖ ≤ δ₃ k + C * (R k + R k ^ 2) := by
    intro k
    have := norm_crossMoment_sub_sub_sub_le (Γ := Γ₂₂) (hM'L k) ((hNx' k).add (hNy' k)) (hM'L k)
      ((hNx' k).add (hNy' k)) (μ := μ)
    refine this.trans (add_le_add_left (devB k (rms_nonneg _) (rms_nonneg _) (Or.inr (rM' k))
      (Or.inr (rM' k)) (rms_nonneg _) (rms_nonneg _) (ru' k) (ru' k)) _)
  have hδ₁ : Tendsto δ₁ atTop (𝓝 0) := by simpa [δ₁] using (hΓ₁₁.sub_const Γ₁₁).norm
  have hδ₂ : Tendsto δ₂ atTop (𝓝 0) := by simpa [δ₂] using (hΓ₁₂.sub_const Γ₁₂).norm
  have hδ₃ : Tendsto δ₃ atTop (𝓝 0) := by simpa [δ₃] using (hΓ₂₂.sub_const Γ₂₂).norm
  exact tendsto_tts_perturbed hβ hγ hβγ hγβ A₁₁ A₁₂ A₂₁ A₂₂ D hD hη hΔ hA₂₂ ℱ (tts_of_mtts hrec)
    (fun k ω => rfl) (fun k ω => rfl) hx0 hx0L hy0 hy0L hηm hηL hζm hζL hmm hmL hm'm hm'L
    hρm hρL hρ'm hρ'L hmart_m hmart_m' hC rη rζ rm rm' rρ rρ' hR1 hinv
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) (fun k => norm_nonneg _) hδ₁ hδ₂ hδ₃
    dev₁ dev₂ dev₃

/-- The noise shifted in time. -/
def TTSMatrixNoise.shift (W : TTSMatrixNoise μ ℱ d₁ d₂) (K : ℕ) :
    TTSMatrixNoise μ (Filtration.shift ℱ K) d₁ d₂ where
  N₁₁ n := W.N₁₁ (K + n)
  N₁₂ n := W.N₁₂ (K + n)
  N₂₁ n := W.N₂₁ (K + n)
  N₂₂ n := W.N₂₂ (K + n)
  G₁₁ n := W.G₁₁ (K + n)
  G₁₂ n := W.G₁₂ (K + n)
  G₂₁ n := W.G₂₁ (K + n)
  G₂₂ n := W.G₂₂ (K + n)
  CN := W.CN
  CN_nonneg := W.CN_nonneg
  bN₁₁ k := W.bN₁₁ (K + k)
  bN₁₂ k := W.bN₁₂ (K + k)
  bN₂₁ k := W.bN₂₁ (K + k)
  bN₂₂ k := W.bN₂₂ (K + k)
  bG₁₁ k := W.bG₁₁ (K + k)
  bG₁₂ k := W.bG₁₂ (K + k)
  bG₂₁ k := W.bG₂₁ (K + k)
  bG₂₂ k := W.bG₂₂ (K + k)
  mN₁₁ k := W.mN₁₁ (K + k)
  mN₁₂ k := W.mN₁₂ (K + k)
  mN₂₁ k := W.mN₂₁ (K + k)
  mN₂₂ k := W.mN₂₂ (K + k)
  mG₁₁ k := W.mG₁₁ (K + k)
  mG₁₂ k := W.mG₁₂ (K + k)
  mG₂₁ k := W.mG₂₁ (K + k)
  mG₂₂ k := W.mG₂₂ (K + k)
  mart₁₁ k := W.mart₁₁ (K + k)
  mart₁₂ k := W.mart₁₂ (K + k)
  mart₂₁ k := W.mart₂₁ (K + k)
  mart₂₂ k := W.mart₂₂ (K + k)

/-- **Theorem 4.1 of `docs/two-time-scale-covariance.md`.** Two time scales with
multiplicative Markov noise in all four blocks: the conclusions of Theorem 2.1 hold, with the
covariances `Γ` of the additive martingale parts. -/
theorem tendsto_mtts [IsProbabilityMeasure μ] {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (hrec : MTTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g W)
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
    (hΓ₂₂ : Tendsto (fun k => secondMoment μ (M' (k + 1))) atTop (𝓝 Γ₂₂)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  -- from some time on the steps are small
  have hsm : Tendsto (fun k => W.CN * ((1 + 2 * ‖matCLM D‖) * β k + γ k)) atTop (𝓝 0) := by
    simpa using ((hβ.tendsto_zero.const_mul (1 + 2 * ‖matCLM D‖)).add hγ.tendsto_zero).const_mul
      W.CN
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hsm.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have adapt := mtts_adapted hrec hx0 hx0L hy0 hy0L hh hhL hg hgL hM hML hM' hM'L
  obtain ⟨a, c, b, hb, hc, ha, lX, lZ, lY⟩ := tendsto_mtts_of_small (μ := μ)
    (ℱ := Filtration.shift ℱ K) (β := fun j => β (K + j)) (γ := fun j => γ (K + j))
    (x := fun j => x (K + j)) (M := fun j => M (K + j)) (h := fun j => h (K + j))
    (y := fun j => y (K + j)) (M' := fun j => M' (K + j)) (g := fun j => g (K + j))
    (W := W.shift K) (hβ.shift K) (hγ.shift K) ((tendsto_shift_iff K (f := fun k => β k / γ k)).mpr hβγ)
    ((tendsto_shift_iff K (f := fun k => γ k ^ 2 / β k)).mpr hγβ) D hD hη hΔ
    hA₂₂ ⟨fun j ω => hrec.1 (K + j) ω, fun j ω => hrec.2 (K + j) ω⟩ (adapt K).1.1 (adapt K).1.2
    (adapt K).2.1 (adapt K).2.2 (fun j => hh (K + j)) (fun j => hhL (K + j))
    (fun j => hhB (K + j)) (fun j => hg (K + j)) (fun j => hgL (K + j)) (fun j => hgB (K + j))
    (fun j => hM (K + j)) (fun j => hML (K + j)) (fun j => hMB (K + j))
    (fun j => hM' (K + j)) (fun j => hM'L (K + j)) (fun j => hM'B (K + j))
    (fun j => hmart (K + j)) (fun j => hmart' (K + j))
    ((tendsto_shift_iff K (f := fun k => secondMoment μ (M (k + 1)))).mpr hΓ₁₁)
    ((tendsto_shift_iff K (f := fun k => crossMoment μ (M (k + 1)) (M' (k + 1)))).mpr hΓ₁₂)
    ((tendsto_shift_iff K (f := fun k => secondMoment μ (M' (k + 1)))).mpr hΓ₂₂)
    (fun j => hK (K + j) (Nat.le_add_right K j))
  exact ⟨a, c, b, hb, hc, ha,
    (tendsto_shift_iff K (f := fun k => (β k)⁻¹ • secondMoment μ (x k))).mp lX,
    (tendsto_shift_iff K (f := fun k => (β k)⁻¹ • crossMoment μ (x k)
      (fun ω => y k ω + matCLM D (x k ω)))).mp lZ,
    (tendsto_shift_iff K (f := fun k => (γ k)⁻¹ • secondMoment μ
      (fun ω => y k ω + matCLM D (x k ω)))).mp lY⟩

/-- **Corollary 4.2 of the write-up.** With multiplicative noise, the slow iterate still has the
asymptotic covariance of the single-time-scale iteration driven by the effective noise
`V - A₁₂ A₂₂⁻¹ W` (only the additive martingale parts enter). -/
theorem tendsto_mtts_slow [IsProbabilityMeasure μ] {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0))
    (Ginv : Matrix (Fin d₂) (Fin d₂) ℝ) (hG : Ginv * A₂₂ = 1) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * (Ginv * A₂₁) - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (hrec : MTTSRecursion A₁₁ A₁₂ A₂₁ A₂₂ β γ x M h y M' g W)
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
    (hΓ₂₂ : Tendsto (fun k => secondMoment μ (M' (k + 1))) atTop (𝓝 Γ₂₂)) :
    ∃ Sig, lyapOp (A₁₁ - A₁₂ * (Ginv * A₂₁) - (βbar / 2) • 1) Sig =
        Γ₁₁ - lmul (A₁₂ * Ginv) (transCLM Γ₁₂) - rmul (A₁₂ * Ginv) Γ₁₂
          + lmul (A₁₂ * Ginv) (rmul (A₁₂ * Ginv) Γ₂₂) ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 Sig) := by
  have hD : A₂₂ * (Ginv * A₂₁) = A₂₁ := by
    have hG' : A₂₂ * Ginv = 1 := Matrix.mul_eq_one_comm.mp hG
    rw [← Matrix.mul_assoc, hG', Matrix.one_mul]
  obtain ⟨a, c, b, hb, hc, ha, hlim, -, -⟩ := tendsto_mtts hβ hγ hβγ hγβ (Ginv * A₂₁) hD hη hΔ
    hA₂₂ hrec hx0 hx0L hy0 hy0L hh hhL hhB hg hgL hgB hM hML hMB hM' hM'L hM'B hmart hmart'
    hΓ₁₁ hΓ₁₂ hΓ₂₂
  have hΓsym : transCLM Γ₂₂ = Γ₂₂ := by
    have h1 : Tendsto (fun k => transCLM (secondMoment μ (M' (k + 1)))) atTop
        (𝓝 (transCLM Γ₂₂)) := (transCLM.continuous.tendsto _).comp hΓ₂₂
    have h2 : (fun k => transCLM (secondMoment μ (M' (k + 1)))) =
        fun k => secondMoment μ (M' (k + 1)) := by
      funext k; exact (crossMoment_swap (hM'L k) (hM'L k)).symm
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hΓ₂₂
  have hbsym := transCLM_eq_of_lyapOp A₂₂ hη hA₂₂ hΓsym hb
  exact ⟨a, effective_lyapunov A₁₂ A₂₂ Ginv hG _ hbsym hb hc ha, hlim⟩

end StochasticApproximation
