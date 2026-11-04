/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.MarkovNoiseCovariance

/-!
# Asymptotic covariance with multiplicative Markov noise

Section 3 of `docs/markov-sa-covariance.md`: the iteration
`θ (k+1) = θ k - β k (A + Ã k) θ k + β k V k`, where the random matrix `Ã k` and the
noise `V k` both have Poisson decompositions
`Ã k = N (k+1) + G k - G (k+1)` and `V k = M (k+1) + h k - h (k+1)`.
The multiplicative part does not change the limit: `β k⁻¹ E[θ k θ kᵀ] → Σ` with the
same Lyapunov equation as for additive noise.

* `clm_apply_eq_sum`, `condExp_clm_apply_eq_zero`: `N (k+1) x` is a martingale difference
  for every `ℱ k`-measurable `x`.
* `secondMoment_step`: one step of the second-moment recursion, for any decomposition
  `u' = (I - β A) u + β m + c` with `m` a martingale difference.
* `mult_shifted_iterate`: Lemma 3.2, the shifted iterate `θ + β (h - G θ)`.
* `tendsto_secondMoment_of_mult_noise_of_small`: Theorem 3.1 when `β k ‖G‖ ≤ 1/2`
  for every `k`.
* `tendsto_secondMoment_of_mult_noise`: Theorem 3.1.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StochasticApproximation

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Random linear maps -/

lemma euclidean_sum_apply {ι : Type*} (s : Finset ι) (f : ι → E d) (j : Fin d) :
  (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j :=
  map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) f s

lemma clm_apply_eq_sum (L : E d →L[ℝ] E d) (x : E d) (j : Fin d) :
  L x j = ∑ i, x i * L (EuclideanSpace.single i 1) j := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext k
    rw [euclidean_sum_apply]
    simp [EuclideanSpace.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum, euclidean_sum_apply]
  simp [map_smul]

lemma stronglyMeasurable_clm_apply {m : MeasurableSpace Ω} {L : Ω → E d →L[ℝ] E d}
  {x : Ω → E d} (hL : StronglyMeasurable[m] L) (hx : StronglyMeasurable[m] x) :
  StronglyMeasurable[m] fun ω => L ω (x ω) :=
  isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable (hL.prodMk hx)

lemma memLp_clm_apply {L : Ω → E d →L[ℝ] E d} {x : Ω → E d} {C : ℝ}
  (hL : AEStronglyMeasurable L μ) (hLB : ∀ ω, ‖L ω‖ ≤ C) (hx : MemLp x 2 μ) :
  MemLp (fun ω => L ω (x ω)) 2 μ :=
  hx.of_le_mul (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hL.prodMk hx.1))
    (Eventually.of_forall fun ω => (L ω).le_of_opNorm_le (hLB ω) _)

lemma norm_clm_apply_le {L : E d →L[ℝ] E d} {C : ℝ} (hL : ‖L‖ ≤ C) (x : E d) :
  ‖L x‖ ≤ C * ‖x‖ :=
  L.le_of_opNorm_le hL x

/-- If the entries of a bounded random linear map `N` have zero conditional expectation,
then `N x` is a martingale difference for every `ℱ`-measurable square-integrable `x`. -/
lemma condExp_clm_apply_eq_zero {ℱ : MeasurableSpace Ω} [IsFiniteMeasure μ]
  {N : Ω → E d →L[ℝ] E d} {x : Ω → E d} {C : ℝ}
  (hNm : AEStronglyMeasurable[m0] N μ) (hNB : ∀ ω, ‖N ω‖ ≤ C)
  (hx : StronglyMeasurable[ℱ] x) (hxL : MemLp x 2 μ)
  (hN : ∀ i j, μ[fun ω => N ω (EuclideanSpace.single i 1) j | ℱ] =ᵐ[μ] 0) (j : Fin d) :
  μ[fun ω => N ω (x ω) j | ℱ] =ᵐ[μ] 0 := by
  have hfun : (fun ω => N ω (x ω) j) =
      ∑ i, fun ω => x ω i * N ω (EuclideanSpace.single i 1) j := by
    funext ω
    rw [clm_apply_eq_sum, Finset.sum_apply]
  have hnm : ∀ i, AEStronglyMeasurable[m0] (fun ω => N ω (EuclideanSpace.single i 1) j) μ :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.apply ℝ (E d) (EuclideanSpace.single i 1)).continuous.comp_aestronglyMeasurable
        hNm)
  have hnB : ∀ i ω, ‖N ω (EuclideanSpace.single i 1) j‖ ≤ C := by
    intro i ω
    calc ‖N ω (EuclideanSpace.single i 1) j‖ ≤ ‖N ω (EuclideanSpace.single i 1)‖ :=
          PiLp.norm_apply_le _ _
      _ ≤ C * ‖EuclideanSpace.single i (1 : ℝ)‖ := norm_clm_apply_le (hNB ω) _
      _ = C := by simp
  have hn : ∀ i, Integrable (fun ω => N ω (EuclideanSpace.single i 1) j) μ := fun i =>
    (memLp_top_of_bound (hnm i) C (Eventually.of_forall (hnB i))).integrable le_top
  have hxi : ∀ i, StronglyMeasurable[ℱ] fun ω => x ω i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_stronglyMeasurable hx
  have hprod : ∀ i,
      Integrable ((fun ω => x ω i) * fun ω => N ω (EuclideanSpace.single i 1) j) μ := by
    intro i
    have hxint : Integrable (fun ω => x ω i) μ := (memLp_apply hxL i).integrable one_le_two
    have := hxint.bdd_mul (hnm i) ⟨C, hnB i⟩
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp [mul_comm]
  have hterm : ∀ i, μ[(fun ω => x ω i) * fun ω => N ω (EuclideanSpace.single i 1) j | ℱ]
      =ᵐ[μ] 0 := by
    intro i
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hxi i) (hprod i) (hn i), hN i j]
      with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  have hsum := condExp_finset_sum (s := univ) (fun i _ => hprod i) ℱ (μ := μ)
  have hall : ∀ᵐ ω ∂μ, ∀ i, (μ[(fun ω => x ω i) * fun ω => N ω (EuclideanSpace.single i 1) j
      | ℱ]) ω = 0 := ae_all_iff.mpr hterm
  rw [hfun]
  filter_upwards [hsum, hall] with ω h1 h2
  have e : (∑ i, fun ω => x ω i * N ω (EuclideanSpace.single i 1) j) =
      ∑ i, ((fun ω => x ω i) * fun ω => N ω (EuclideanSpace.single i 1) j) := rfl
  rw [e, h1, Finset.sum_apply]
  simp [h2]

/-! ### One step of the second-moment recursion -/

/-- One step of the second-moment recursion: if `u' = (I - b A) u + b m + c` with `u`
`ℱ`-measurable and `m` a martingale difference, then
`E[u' u'ᵀ] = (I - b A) E[u uᵀ] (I - b A)ᵀ + b² E[m mᵀ] + R` with `R` bounded by the cross
terms involving `c`. -/
theorem secondMoment_step [IsProbabilityMeasure μ] {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0)
  (A : Matrix (Fin d) (Fin d) ℝ) {b : ℝ} (hb : 0 ≤ b) {u m c : Ω → E d}
  (hu : StronglyMeasurable[ℱ] u) (huL : MemLp u 2 μ) (hmL : MemLp m 2 μ) (hcL : MemLp c 2 μ)
  (hmart : ∀ j, μ[fun ω => m ω j | ℱ] =ᵐ[μ] 0) :
  ‖secondMoment μ (fun ω => u ω - b • matCLM A (u ω) + b • m ω + c ω)
    - (secondMoment μ u - b • lyapOp A (secondMoment μ u) + b ^ 2 • sandwich A (secondMoment μ u)
      + b ^ 2 • secondMoment μ m)‖ ≤
  2 * ((1 + b * ‖matCLM A‖) * √(∫ ω, ‖u ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ))
  + 2 * (b * √(∫ ω, ‖m ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ)) + ∫ ω, ‖c ω‖ ^ 2 ∂μ := by
  obtain ⟨a, ha_def⟩ : ∃ a : Ω → E d, a = fun ω => u ω - b • matCLM A (u ω) := ⟨_, rfl⟩
  obtain ⟨bm, hbm_def⟩ : ∃ bm : Ω → E d, bm = fun ω => b • m ω := ⟨_, rfl⟩
  have haL : MemLp a 2 μ := by
    rw [ha_def]; exact huL.sub (((matCLM A).comp_memLp' huL).const_smul b)
  have hbL : MemLp bm 2 μ := by rw [hbm_def]; exact hmL.const_smul b
  have ham : StronglyMeasurable[ℱ] a := by
    rw [ha_def]
    exact hu.sub (((matCLM A).continuous.comp_stronglyMeasurable hu).const_smul b)
  have hsum : (fun ω => u ω - b • matCLM A (u ω) + b • m ω + c ω) =
      fun ω => a ω + bm ω + c ω := by
    rw [ha_def, hbm_def]
  have hab : MemLp (fun ω => a ω + bm ω) 2 μ := haL.add hbL
  have habc : MemLp (fun ω => a ω + bm ω + c ω) 2 μ := hab.add hcL
  have hexp : secondMoment μ (fun ω => a ω + bm ω + c ω) =
      crossMoment μ a a + crossMoment μ a bm + crossMoment μ a c
      + (crossMoment μ bm a + crossMoment μ bm bm + crossMoment μ bm c)
      + (crossMoment μ c a + crossMoment μ c bm + crossMoment μ c c) := by
    simp only [secondMoment]
    rw [crossMoment_add_left hab hcL habc, crossMoment_add_left haL hbL habc,
      crossMoment_add_right haL hab hcL, crossMoment_add_right haL haL hbL,
      crossMoment_add_right hbL hab hcL, crossMoment_add_right hbL haL hbL,
      crossMoment_add_right hcL hab hcL, crossMoment_add_right hcL haL hbL]
  have hAB : crossMoment μ a bm = 0 := by
    rw [hbm_def, crossMoment_smul_right, crossMoment_eq_zero hℱ ham haL hmL hmart, smul_zero]
  have hBA : crossMoment μ bm a = 0 := by
    rw [hbm_def, crossMoment_smul_left, crossMoment_eq_zero' hℱ ham haL hmL hmart, smul_zero]
  have hAA : crossMoment μ a a = secondMoment μ u - b • lyapOp A (secondMoment μ u)
      + b ^ 2 • sandwich A (secondMoment μ u) := by
    rw [ha_def]; exact secondMoment_sub_smul A b huL
  have hBB : crossMoment μ bm bm = b ^ 2 • secondMoment μ m := by
    rw [hbm_def, secondMoment, crossMoment_smul_left, crossMoment_smul_right, smul_smul, sq]
  have hRform : secondMoment μ (fun ω => u ω - b • matCLM A (u ω) + b • m ω + c ω)
      - (secondMoment μ u - b • lyapOp A (secondMoment μ u)
        + b ^ 2 • sandwich A (secondMoment μ u) + b ^ 2 • secondMoment μ m) =
      crossMoment μ a c + crossMoment μ bm c + crossMoment μ c a + crossMoment μ c bm
        + crossMoment μ c c := by
    rw [hsum, hexp, hAB, hBA, hAA, hBB]
    abel
  rw [hRform]
  have hEa : √(∫ ω, ‖a ω‖ ^ 2 ∂μ) ≤ (1 + b * ‖matCLM A‖) * √(∫ ω, ‖u ω‖ ^ 2 ∂μ) := by
    have hpt : ∀ ω, ‖a ω‖ ^ 2 ≤ (1 + b * ‖matCLM A‖) ^ 2 * ‖u ω‖ ^ 2 := by
      intro ω
      have : ‖a ω‖ ≤ (1 + b * ‖matCLM A‖) * ‖u ω‖ := by
        rw [ha_def]
        calc ‖u ω - b • matCLM A (u ω)‖ ≤ ‖u ω‖ + ‖b • matCLM A (u ω)‖ := norm_sub_le _ _
          _ ≤ ‖u ω‖ + b * (‖matCLM A‖ * ‖u ω‖) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
              gcongr
              exact (matCLM A).le_opNorm _
          _ = (1 + b * ‖matCLM A‖) * ‖u ω‖ := by ring
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hint : ∫ ω, ‖a ω‖ ^ 2 ∂μ ≤ (1 + b * ‖matCLM A‖) ^ 2 * ∫ ω, ‖u ω‖ ^ 2 ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono (memLp_sq_integrable haL) ((memLp_sq_integrable huL).const_mul _) hpt
    calc √(∫ ω, ‖a ω‖ ^ 2 ∂μ) ≤ √((1 + b * ‖matCLM A‖) ^ 2 * ∫ ω, ‖u ω‖ ^ 2 ∂μ) :=
          Real.sqrt_le_sqrt hint
      _ = (1 + b * ‖matCLM A‖) * √(∫ ω, ‖u ω‖ ^ 2 ∂μ) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hEb : √(∫ ω, ‖bm ω‖ ^ 2 ∂μ) = b * √(∫ ω, ‖m ω‖ ^ 2 ∂μ) := by
    have : (fun ω => ‖bm ω‖ ^ 2) = fun ω => b ^ 2 * ‖m ω‖ ^ 2 := by
      funext ω
      rw [hbm_def]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [this, integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb]
  have n1 := norm_crossMoment_le (μ := μ) haL hcL
  have n2 := norm_crossMoment_le (μ := μ) hbL hcL
  have n3 := norm_crossMoment_le (μ := μ) hcL haL
  have n4 := norm_crossMoment_le (μ := μ) hcL hbL
  have n5 := norm_crossMoment_le (μ := μ) hcL hcL
  rw [Real.mul_self_sqrt (integral_norm_sq_nonneg c)] at n5
  have sc0 := Real.sqrt_nonneg (∫ ω, ‖c ω‖ ^ 2 ∂μ)
  have m1 := mul_le_mul_of_nonneg_right hEa sc0
  rw [hEb] at n2 n4
  have t1 := norm_add_le (crossMoment μ a c + crossMoment μ bm c + crossMoment μ c a
    + crossMoment μ c bm) (crossMoment μ c c)
  have t2 := norm_add_le (crossMoment μ a c + crossMoment μ bm c + crossMoment μ c a)
    (crossMoment μ c bm)
  have t3 := norm_add_le (crossMoment μ a c + crossMoment μ bm c) (crossMoment μ c a)
  have t4 := norm_add_le (crossMoment μ a c) (crossMoment μ bm c)
  have e1 : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) * √(∫ ω, ‖a ω‖ ^ 2 ∂μ) =
      √(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) := mul_comm _ _
  have e2 : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) * (b * √(∫ ω, ‖m ω‖ ^ 2 ∂μ)) =
      b * √(∫ ω, ‖m ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) := by ring
  linarith

/-! ### The iterates -/

variable {β : ℕ → ℝ}

/-- The multiplicative-noise recursion. -/
def MultRecursion (A : Matrix (Fin d) (Fin d) ℝ) (β : ℕ → ℝ) (θ M h : ℕ → Ω → E d)
    (N G : ℕ → Ω → E d →L[ℝ] E d) : Prop :=
  ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω)
    - β k • (N (k + 1) ω + G k ω - G (k + 1) ω) (θ k ω)
    + β k • (M (k + 1) ω + h k ω - h (k + 1) ω)

/-- The iterates are adapted and square integrable. -/
lemma mult_iterates_adapted (ℱ : MeasureTheory.Filtration ℕ m0) (A : Matrix (Fin d) (Fin d) ℝ)
  {θ M h : ℕ → Ω → E d} {N G : ℕ → Ω → E d →L[ℝ] E d} {CN CG : ℝ}
  (hθ : MultRecursion A β θ M h N G)
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hN : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N (k + 1))) (hNB : ∀ k ω, ‖N (k + 1) ω‖ ≤ CN)
  (hG : ∀ k, StronglyMeasurable[ℱ k] (G k)) (hGB : ∀ k ω, ‖G k ω‖ ≤ CG) :
  ∀ k, StronglyMeasurable[ℱ k] (θ k) ∧ MemLp (θ k) 2 μ := by
  intro k
  induction k with
  | zero => exact ⟨hθ0, hθ0L⟩
  | succ k ih =>
    have hfun : θ (k + 1) = fun ω => θ k ω - β k • matCLM A (θ k ω)
        - β k • (N (k + 1) ω + G k ω - G (k + 1) ω) (θ k ω)
        + β k • (M (k + 1) ω + h k ω - h (k + 1) ω) := funext (hθ k)
    have hmono := ℱ.mono (Nat.le_succ k)
    have hθm := ih.1.mono hmono
    have hÃ : StronglyMeasurable[ℱ (k + 1)] fun ω => N (k + 1) ω + G k ω - G (k + 1) ω :=
      ((hN k).add ((hG k).mono hmono)).sub (hG (k + 1))
    have hÃB : ∀ ω, ‖N (k + 1) ω + G k ω - G (k + 1) ω‖ ≤ CN + CG + CG := fun ω =>
      (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (hNB k ω) (hGB k ω))) (hGB (k + 1) ω))
    rw [hfun]
    constructor
    · have h2 := ((matCLM A).continuous.comp_stronglyMeasurable ih.1).mono hmono
      have h3 := stronglyMeasurable_clm_apply hÃ hθm
      exact ((hθm.sub (h2.const_smul (β k))).sub (h3.const_smul (β k))).add
        ((((hM k).add ((hh k).mono hmono)).sub (hh (k + 1))).const_smul (β k))
    · have h3 := memLp_clm_apply (hÃ.mono (ℱ.le (k + 1))).aestronglyMeasurable hÃB ih.2
      exact ((ih.2.sub (((matCLM A).comp_memLp' ih.2).const_smul (β k))).sub
        (h3.const_smul (β k))).add ((((hML k).add (hhL k)).sub (hhL (k + 1))).const_smul (β k))

/-- Lemma 3.2 of the write-up: the shifted iterate `u = θ + β (h - G θ)` follows the
additive recursion `u' = (I - β A) u + β (M - N θ) + c` with a remainder `c` of order `β²`. -/
lemma mult_shifted_iterate (A : Matrix (Fin d) (Fin d) ℝ) {θ M h : ℕ → Ω → E d}
  {N G : ℕ → Ω → E d →L[ℝ] E d} (hθ : MultRecursion A β θ M h N G) (k : ℕ) (ω : Ω) :
  θ (k + 1) ω + β (k + 1) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω)) =
    (θ k ω + β k • (h k ω - G k ω (θ k ω)))
      - β k • matCLM A (θ k ω + β k • (h k ω - G k ω (θ k ω)))
      + β k • (M (k + 1) ω - N (k + 1) ω (θ k ω))
      + ((β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω))
        + (β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω))
        - β k • G (k + 1) ω (θ (k + 1) ω - θ k ω)) := by
  have e := hθ k ω
  rw [map_sub (G (k + 1) ω) (θ (k + 1) ω) (θ k ω)]
  generalize θ (k + 1) ω = t at e ⊢
  subst e
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  module

/-- The shifted iterate `θ k + β k (h k - G k θ k)`. -/
noncomputable def multShift (β : ℕ → ℝ) (θ h : ℕ → Ω → E d) (G : ℕ → Ω → E d →L[ℝ] E d) (k : ℕ) :
    Ω → E d :=
  fun ω => θ k ω + β k • (h k ω - G k ω (θ k ω))

/-- `‖θ‖ ≤ 2 ‖u‖ + 2 β ‖h‖` for the shifted iterate `u`, once `β ‖G‖ ≤ 1/2`. -/
lemma norm_le_of_multShift {θ h : ℕ → Ω → E d} {G : ℕ → Ω → E d →L[ℝ] E d} {CG : ℝ}
  {k : ℕ} {ω : Ω}
  (hb : 0 ≤ β k) (hGB : ‖G k ω‖ ≤ CG) (hsmall : β k * CG ≤ 1 / 2) :
  ‖θ k ω‖ ≤ 2 * ‖multShift β θ h G k ω‖ + 2 * β k * ‖h k ω‖ := by
  have e : θ k ω = multShift β θ h G k ω - β k • h k ω + β k • G k ω (θ k ω) := by
    simp only [multShift, smul_sub]; abel
  have h1 : ‖θ k ω‖ ≤ ‖multShift β θ h G k ω‖ + β k * ‖h k ω‖ + β k * (CG * ‖θ k ω‖) := by
    calc ‖θ k ω‖ = ‖multShift β θ h G k ω - β k • h k ω + β k • G k ω (θ k ω)‖ := by rw [← e]
      _ ≤ ‖multShift β θ h G k ω‖ + ‖β k • h k ω‖ + ‖β k • G k ω (θ k ω)‖ :=
          (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ ≤ _ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
          gcongr
          exact norm_clm_apply_le hGB _
  have h2 : β k * (CG * ‖θ k ω‖) ≤ 1 / 2 * ‖θ k ω‖ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  linarith

/-- The pointwise bound `‖c‖ ≤ β² K (‖θ‖ + ‖M‖ + ‖h‖ + ‖h'‖)` on the remainder of
Lemma 3.2. -/
lemma norm_mult_remainder_le (A : Matrix (Fin d) (Fin d) ℝ) {θ M h : ℕ → Ω → E d}
  {N G : ℕ → Ω → E d →L[ℝ] E d} {CN CG Cs B : ℝ}
  (hθ : MultRecursion A β θ M h N G) (k : ℕ) (ω : Ω)
  (hb : 0 ≤ β k) (hbB : β k ≤ B) (hCs : |β (k + 1) - β k| ≤ Cs * β k ^ 2)
  (hCN : 0 ≤ CN) (hCG : 0 ≤ CG) (hB : 0 ≤ B) (hCs0 : 0 ≤ Cs)
  (hNB : ‖N (k + 1) ω‖ ≤ CN) (hGB : ‖G k ω‖ ≤ CG) (hGB' : ‖G (k + 1) ω‖ ≤ CG) :
  ‖(β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω))
      + (β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω))
      - β k • G (k + 1) ω (θ (k + 1) ω - θ k ω)‖ ≤
    β k ^ 2 * ((‖matCLM A‖ * CG + Cs * CG * (1 + B * (‖matCLM A‖ + CN + 2 * CG))
        + CG * (‖matCLM A‖ + CN + 2 * CG))
      + (‖matCLM A‖ + Cs + Cs * CG * B + CG)) *
      (‖θ k ω‖ + (‖M (k + 1) ω‖ + ‖h k ω‖ + ‖h (k + 1) ω‖)) := by
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = ‖matCLM A‖ := ⟨_, rfl⟩
  have hAm0 : 0 ≤ Am := hAm ▸ norm_nonneg _
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = Am + CN + 2 * CG := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ‖M (k + 1) ω‖ + ‖h k ω‖ + ‖h (k + 1) ω‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  rw [← hAm, ← hZ, ← hS]
  set t := ‖θ k ω‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  -- the increment
  have hw : ‖θ (k + 1) ω - θ k ω‖ ≤ β k * (Z * t + S) := by
    have e : θ (k + 1) ω - θ k ω = -(β k • matCLM A (θ k ω))
        - β k • (N (k + 1) ω + G k ω - G (k + 1) ω) (θ k ω)
        + β k • (M (k + 1) ω + h k ω - h (k + 1) ω) := by rw [hθ k ω]; abel
    have hÃ : ‖N (k + 1) ω + G k ω - G (k + 1) ω‖ ≤ CN + CG + CG :=
      (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hNB hGB)) hGB')
    have hV : ‖M (k + 1) ω + h k ω - h (k + 1) ω‖ ≤ S := by
      rw [hS]; exact (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    rw [e]
    calc ‖-(β k • matCLM A (θ k ω)) - β k • (N (k + 1) ω + G k ω - G (k + 1) ω) (θ k ω)
          + β k • (M (k + 1) ω + h k ω - h (k + 1) ω)‖
        ≤ ‖β k • matCLM A (θ k ω)‖ + ‖β k • (N (k + 1) ω + G k ω - G (k + 1) ω) (θ k ω)‖
          + ‖β k • (M (k + 1) ω + h k ω - h (k + 1) ω)‖ := by
          refine (norm_add_le _ _).trans (add_le_add_right ((norm_sub_le _ _).trans ?_) _)
          rw [norm_neg]
      _ ≤ β k * (Am * t) + β k * ((CN + CG + CG) * t) + β k * S := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
          gcongr
          · rw [hAm]; exact (matCLM A).le_opNorm _
          · exact norm_clm_apply_le hÃ _
      _ = β k * (Z * t + S) := by rw [hZ]; ring
  have hθ1 : ‖θ (k + 1) ω‖ ≤ (1 + B * Z) * t + B * S := by
    have h1 : ‖θ (k + 1) ω‖ ≤ t + ‖θ (k + 1) ω - θ k ω‖ := by
      have := norm_add_le (θ k ω) (θ (k + 1) ω - θ k ω)
      rwa [add_sub_cancel] at this
    have h2 : β k * (Z * t + S) ≤ B * (Z * t + S) :=
      mul_le_mul_of_nonneg_right hbB (by positivity)
    nlinarith
  have n1 : ‖(β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω))‖ ≤
      β k ^ 2 * (Am * (‖h k ω‖ + CG * t)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    gcongr
    calc ‖matCLM A (h k ω - G k ω (θ k ω))‖ ≤ Am * ‖h k ω - G k ω (θ k ω)‖ := by
          rw [hAm]; exact (matCLM A).le_opNorm _
      _ ≤ Am * (‖h k ω‖ + CG * t) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add_left (norm_clm_apply_le hGB _) _)
  have n2 : ‖(β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω))‖ ≤
      Cs * β k ^ 2 * (‖h (k + 1) ω‖ + CG * ((1 + B * Z) * t + B * S)) := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    calc ‖h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω)‖ ≤ ‖h (k + 1) ω‖ + CG * ‖θ (k + 1) ω‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_clm_apply_le hGB' _) _)
      _ ≤ _ := by gcongr
  have n3 : ‖β k • G (k + 1) ω (θ (k + 1) ω - θ k ω)‖ ≤ β k * (CG * (β k * (Z * t + S))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    gcongr
    exact (norm_clm_apply_le hGB' _).trans (mul_le_mul_of_nonneg_left hw hCG)
  have tri0 := norm_sub_le ((β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω))
    + (β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω)))
    (β k • G (k + 1) ω (θ (k + 1) ω - θ k ω))
  have tri1 := norm_add_le ((β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω)))
    ((β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω)))
  have tri := tri0.trans (add_le_add_right tri1 _)
  refine tri.trans ?_
  have hSh : ‖h k ω‖ ≤ S := by rw [hS]; linarith [norm_nonneg (M (k + 1) ω), norm_nonneg (h (k + 1) ω)]
  have hSh' : ‖h (k + 1) ω‖ ≤ S := by
    rw [hS]; linarith [norm_nonneg (M (k + 1) ω), norm_nonneg (h k ω)]
  have hb2 := sq_nonneg (β k)
  have p1 : β k ^ 2 * (Am * ‖h k ω‖) ≤ β k ^ 2 * (Am * S) := by gcongr
  have p2 : β k ^ 2 * (Cs * ‖h (k + 1) ω‖) ≤ β k ^ 2 * (Cs * S) := by gcongr
  have p3 : 0 ≤ β k ^ 2 * ((Am + Cs + Cs * CG * B + CG) * t) := by positivity
  have p4 : 0 ≤ β k ^ 2 * ((Am * CG + Cs * CG * (1 + B * Z) + CG * Z) * S) := by positivity
  nlinarith

lemma sq_add4_le (a b c e : ℝ) : (a + (b + c + e)) ^ 2 ≤ 4 * (a ^ 2 + (b ^ 2 + c ^ 2 + e ^ 2)) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e)]

/-- The square of the bound in `norm_mult_remainder_le`. -/
lemma norm_sq_mult_remainder_le (A : Matrix (Fin d) (Fin d) ℝ) {θ M h : ℕ → Ω → E d}
  {N G : ℕ → Ω → E d →L[ℝ] E d} {CN CG Cs B K : ℝ}
  (hθ : MultRecursion A β θ M h N G) (k : ℕ) (ω : Ω)
  (hb : 0 ≤ β k) (hbB : β k ≤ B) (hCs : |β (k + 1) - β k| ≤ Cs * β k ^ 2)
  (hCN : 0 ≤ CN) (hCG : 0 ≤ CG) (hB : 0 ≤ B) (hCs0 : 0 ≤ Cs)
  (hNB : ‖N (k + 1) ω‖ ≤ CN) (hGB : ‖G k ω‖ ≤ CG) (hGB' : ‖G (k + 1) ω‖ ≤ CG)
  (hK : K = (‖matCLM A‖ * CG + Cs * CG * (1 + B * (‖matCLM A‖ + CN + 2 * CG))
        + CG * (‖matCLM A‖ + CN + 2 * CG)) + (‖matCLM A‖ + Cs + Cs * CG * B + CG)) :
  ‖(β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω))
      + (β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω))
      - β k • G (k + 1) ω (θ (k + 1) ω - θ k ω)‖ ^ 2 ≤
    4 * K ^ 2 * β k ^ 4 * (‖θ k ω‖ ^ 2
      + (‖M (k + 1) ω‖ ^ 2 + ‖h k ω‖ ^ 2 + ‖h (k + 1) ω‖ ^ 2)) := by
  have h1 := norm_mult_remainder_le A hθ k ω hb hbB hCs hCN hCG hB hCs0 hNB hGB hGB'
  rw [← hK] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans ?_
  have h3 := sq_add4_le ‖θ k ω‖ ‖M (k + 1) ω‖ ‖h k ω‖ ‖h (k + 1) ω‖
  calc (β k ^ 2 * K * (‖θ k ω‖ + (‖M (k + 1) ω‖ + ‖h k ω‖ + ‖h (k + 1) ω‖))) ^ 2
      = (β k ^ 2 * K) ^ 2 * (‖θ k ω‖ + (‖M (k + 1) ω‖ + ‖h k ω‖ + ‖h (k + 1) ω‖)) ^ 2 := by ring
    _ ≤ (β k ^ 2 * K) ^ 2 * (4 * (‖θ k ω‖ ^ 2
          + (‖M (k + 1) ω‖ ^ 2 + ‖h k ω‖ ^ 2 + ‖h (k + 1) ω‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = _ := by ring

/-! ### Bookkeeping for the remainder -/

/-- The constant of `mult_poly_le`. -/
def multΛ (α γ B : ℝ) : ℝ :=
  1 + α + γ + α * B + γ * B + 2 * α ^ 2 + 2 * γ ^ 2 * B + 2 * α ^ 2 * B + 2 * γ ^ 2 * B ^ 2
    + 2 * α ^ 2 * B ^ 2 + 2 * γ ^ 2 * B ^ 3 + B

/-- Every monomial in `s = √p`, `b` and `σ ≤ α s + γ b` that occurs in the remainder is
`O(√p + p + b)`. -/
lemma mult_poly_le {s p b σ B α γ : ℝ} (hs : 0 ≤ s) (hp : s ^ 2 = p) (hb : 0 ≤ b) (hbB : b ≤ B)
  (hσ0 : 0 ≤ σ) (hσ : σ ≤ α * s + γ * b) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
  {c1 c2 c3 c4 c5 c6 c7 c8 c9 : ℝ} (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
  (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) (h9 : 0 ≤ c9) :
  c1 * (s * σ) + c2 * s + c3 * (b * σ) + c4 * b + c5 * (b * σ ^ 2) + c6 * (b ^ 2 * σ ^ 2)
      + c7 * b ^ 2 + c8 * σ + c9 * σ ^ 2 ≤
    (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9) * multΛ α γ B * (s + p + b) := by
  have hB : 0 ≤ B := hb.trans hbB
  have hp0 : 0 ≤ p := hp ▸ sq_nonneg s
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = multΛ α γ B := ⟨_, rfl⟩
  rw [← hΛ]
  obtain ⟨W, hW⟩ : ∃ W, W = s + p + b := ⟨_, rfl⟩
  rw [← hW]
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have q : 0 ≤ α * B ∧ 0 ≤ γ * B ∧ 0 ≤ α ^ 2 ∧ 0 ≤ γ ^ 2 * B ∧ 0 ≤ α ^ 2 * B ∧
      0 ≤ γ ^ 2 * B ^ 2 ∧ 0 ≤ α ^ 2 * B ^ 2 ∧ 0 ≤ γ ^ 2 * B ^ 3 :=
    ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity,
      by positivity, by positivity⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := q
  have hΛ1 : 1 ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛα : α ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛγ : γ ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛαB : α * B ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛγB : γ * B ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛB : B ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛ2 : 2 * α ^ 2 + 2 * γ ^ 2 * B ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛ3 : B * (2 * α ^ 2) + B * (2 * γ ^ 2 * B) ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛ4 : B ^ 2 * (2 * α ^ 2) + B ^ 2 * (2 * γ ^ 2 * B) ≤ Λ := by rw [hΛ, multΛ]; linarith
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ1
  have hsW : s ≤ W := by rw [hW]; linarith
  have hpW : p ≤ W := by rw [hW]; linarith
  have hbW : b ≤ W := by rw [hW]; linarith
  -- `σ² ≤ 2 α² p + 2 γ² B b`
  have hσ2 : σ ^ 2 ≤ 2 * α ^ 2 * p + 2 * γ ^ 2 * B * b := by
    have e1 : σ ^ 2 ≤ (α * s + γ * b) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    have e2 : (α * s + γ * b) ^ 2 ≤ 2 * α ^ 2 * s ^ 2 + 2 * γ ^ 2 * b ^ 2 := by
      nlinarith [sq_nonneg (α * s - γ * b)]
    have e3 : γ ^ 2 * b ^ 2 ≤ γ ^ 2 * B * b := by
      calc γ ^ 2 * b ^ 2 = γ ^ 2 * (b * b) := by ring
        _ ≤ γ ^ 2 * (B * b) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbB hb) (sq_nonneg γ)
        _ = γ ^ 2 * B * b := by ring
    rw [hp] at e2
    linarith
  -- the monomial bounds
  have m1 : s * σ ≤ Λ * W := by
    have e1 : s * σ ≤ s * (α * s + γ * b) := mul_le_mul_of_nonneg_left hσ hs
    have e2 : γ * b * s ≤ γ * B * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbB hγ) hs
    have e3 : α * p ≤ Λ * p := mul_le_mul_of_nonneg_right hΛα hp0
    have e4 : γ * B * s ≤ Λ * s := mul_le_mul_of_nonneg_right hΛγB hs
    have e5 : Λ * p + Λ * s ≤ Λ * W := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hΛ0
    have e6 : s * (α * s + γ * b) = α * s ^ 2 + γ * b * s := by ring
    rw [hp] at e6
    linarith
  have hWΛ : W ≤ Λ * W := le_mul_of_one_le_left hW0 hΛ1
  have m2 : s ≤ Λ * W := hsW.trans hWΛ
  have m8 : σ ≤ Λ * W := by
    have e1 : α * s ≤ Λ * s := mul_le_mul_of_nonneg_right hΛα hs
    have e2 : γ * b ≤ Λ * b := mul_le_mul_of_nonneg_right hΛγ hb
    have e3 : Λ * s + Λ * b ≤ Λ * W := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hΛ0
    linarith
  have m3 : b * σ ≤ Λ * W := by
    have e1 : b * σ ≤ b * (α * s + γ * b) := mul_le_mul_of_nonneg_left hσ hb
    have e2 : b * (α * s + γ * b) ≤ B * (α * s + γ * b) :=
      mul_le_mul_of_nonneg_right hbB (by positivity)
    have e3 : α * B * s ≤ Λ * s := mul_le_mul_of_nonneg_right hΛαB hs
    have e4 : γ * B * b ≤ Λ * b := mul_le_mul_of_nonneg_right hΛγB hb
    have e5 : Λ * s + Λ * b ≤ Λ * W := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hΛ0
    have e6 : B * (α * s + γ * b) = α * B * s + γ * B * b := by ring
    linarith
  have m4 : b ≤ Λ * W := hbW.trans hWΛ
  have hσW : σ ^ 2 ≤ Λ * W := by
    have e1 : 2 * α ^ 2 * p ≤ (2 * α ^ 2 + 2 * γ ^ 2 * B) * p :=
      mul_le_mul_of_nonneg_right (by linarith) hp0
    have e2 : 2 * γ ^ 2 * B * b ≤ (2 * α ^ 2 + 2 * γ ^ 2 * B) * b :=
      mul_le_mul_of_nonneg_right (by linarith) hb
    have e3 : (2 * α ^ 2 + 2 * γ ^ 2 * B) * p + (2 * α ^ 2 + 2 * γ ^ 2 * B) * b ≤ Λ * W := by
      rw [← mul_add]
      exact mul_le_mul hΛ2 (by linarith) (by positivity) hΛ0
    linarith
  have m5 : b * σ ^ 2 ≤ Λ * W := by
    have e1 : b * σ ^ 2 ≤ B * σ ^ 2 := mul_le_mul_of_nonneg_right hbB (sq_nonneg σ)
    have e2 : B * σ ^ 2 ≤ B * (2 * α ^ 2 * p + 2 * γ ^ 2 * B * b) :=
      mul_le_mul_of_nonneg_left hσ2 hB
    have e3 : B * (2 * α ^ 2 * p + 2 * γ ^ 2 * B * b) ≤
        (B * (2 * α ^ 2) + B * (2 * γ ^ 2 * B)) * (p + b) := by
      have h0 : 0 ≤ B * (2 * α ^ 2) * b + B * (2 * γ ^ 2 * B) * p := by positivity
      have eq : (B * (2 * α ^ 2) + B * (2 * γ ^ 2 * B)) * (p + b) =
          B * (2 * α ^ 2 * p + 2 * γ ^ 2 * B * b)
            + (B * (2 * α ^ 2) * b + B * (2 * γ ^ 2 * B) * p) := by ring
      rw [eq]; exact le_add_of_nonneg_right h0
    have e4 : (B * (2 * α ^ 2) + B * (2 * γ ^ 2 * B)) * (p + b) ≤ Λ * W :=
      mul_le_mul hΛ3 (by linarith) (by positivity) hΛ0
    exact e1.trans (e2.trans (e3.trans e4))
  have m6 : b ^ 2 * σ ^ 2 ≤ Λ * W := by
    have hb2 : b ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hb hbB 2
    have e1 : b ^ 2 * σ ^ 2 ≤ B ^ 2 * σ ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg σ)
    have e2 : B ^ 2 * σ ^ 2 ≤ B ^ 2 * (2 * α ^ 2 * p + 2 * γ ^ 2 * B * b) :=
      mul_le_mul_of_nonneg_left hσ2 (sq_nonneg B)
    have e3 : B ^ 2 * (2 * α ^ 2 * p + 2 * γ ^ 2 * B * b) ≤
        (B ^ 2 * (2 * α ^ 2) + B ^ 2 * (2 * γ ^ 2 * B)) * (p + b) := by
      have h0 : 0 ≤ B ^ 2 * (2 * α ^ 2) * b + B ^ 2 * (2 * γ ^ 2 * B) * p := by positivity
      have eq : (B ^ 2 * (2 * α ^ 2) + B ^ 2 * (2 * γ ^ 2 * B)) * (p + b) =
          B ^ 2 * (2 * α ^ 2 * p + 2 * γ ^ 2 * B * b)
            + (B ^ 2 * (2 * α ^ 2) * b + B ^ 2 * (2 * γ ^ 2 * B) * p) := by ring
      rw [eq]; exact le_add_of_nonneg_right h0
    have e4 : (B ^ 2 * (2 * α ^ 2) + B ^ 2 * (2 * γ ^ 2 * B)) * (p + b) ≤ Λ * W :=
      mul_le_mul hΛ4 (by linarith) (by positivity) hΛ0
    exact e1.trans (e2.trans (e3.trans e4))
  have m7 : b ^ 2 ≤ Λ * W := by
    have e1 : b ^ 2 ≤ B * b := by rw [sq]; exact mul_le_mul_of_nonneg_right hbB hb
    have e2 : B * b ≤ Λ * W := mul_le_mul hΛB hbW hb hΛ0
    linarith
  have k1 := mul_le_mul_of_nonneg_left m1 h1
  have k2 := mul_le_mul_of_nonneg_left m2 h2
  have k3 := mul_le_mul_of_nonneg_left m3 h3
  have k4 := mul_le_mul_of_nonneg_left m4 h4
  have k5 := mul_le_mul_of_nonneg_left m5 h5
  have k6 := mul_le_mul_of_nonneg_left m6 h6
  have k7 := mul_le_mul_of_nonneg_left m7 h7
  have k8 := mul_le_mul_of_nonneg_left m8 h8
  have k9 := mul_le_mul_of_nonneg_left hσW h9
  have e : (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9) * Λ * W =
      c1 * (Λ * W) + c2 * (Λ * W) + c3 * (Λ * W) + c4 * (Λ * W) + c5 * (Λ * W)
        + c6 * (Λ * W) + c7 * (Λ * W) + c8 * (Λ * W) + c9 * (Λ * W) := by ring
  rw [e]
  linarith only [k1, k2, k3, k4, k5, k6, k7, k8, k9]

/-- `‖E[(a - e)(a - e)ᵀ] - E[a aᵀ]‖ ≤ 2 √E‖a‖² √E‖e‖² + E‖e‖²`. -/
lemma norm_secondMoment_sub_le {a e : Ω → E d} (ha : MemLp a 2 μ) (he : MemLp e 2 μ) :
  ‖secondMoment μ (fun ω => a ω - e ω) - secondMoment μ a‖ ≤
    2 * (√(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖e ω‖ ^ 2 ∂μ)) + ∫ ω, ‖e ω‖ ^ 2 ∂μ := by
  obtain ⟨e', he'⟩ : ∃ e' : Ω → E d, e' = fun ω => (-1 : ℝ) • e ω := ⟨_, rfl⟩
  have he'L : MemLp e' 2 μ := by rw [he']; exact he.const_smul (-1 : ℝ)
  have hfun : (fun ω => a ω - e ω) = fun ω => a ω + e' ω := by
    funext ω; rw [he']; simp [sub_eq_add_neg]
  have hn : ∫ ω, ‖e' ω‖ ^ 2 ∂μ = ∫ ω, ‖e ω‖ ^ 2 ∂μ := by rw [he']; simp
  have hae : MemLp (fun ω => a ω + e' ω) 2 μ := ha.add he'L
  rw [hfun, secondMoment, crossMoment_add_left ha he'L hae,
    crossMoment_add_right ha ha he'L, crossMoment_add_right he'L ha he'L]
  have e1 : crossMoment μ a a + crossMoment μ a e' + (crossMoment μ e' a + crossMoment μ e' e')
      - secondMoment μ a = crossMoment μ a e' + crossMoment μ e' a + crossMoment μ e' e' := by
    simp only [secondMoment]; abel
  rw [e1]
  have n1 := norm_crossMoment_le (μ := μ) ha he'L
  have n2 := norm_crossMoment_le (μ := μ) he'L ha
  have n3 := norm_crossMoment_le (μ := μ) he'L he'L
  rw [hn] at n1 n2 n3
  rw [Real.mul_self_sqrt (integral_norm_sq_nonneg e)] at n3
  have t1 := norm_add_le (crossMoment μ a e' + crossMoment μ e' a) (crossMoment μ e' e')
  have t2 := norm_add_le (crossMoment μ a e') (crossMoment μ e' a)
  have e2 : √(∫ ω, ‖e ω‖ ^ 2 ∂μ) * √(∫ ω, ‖a ω‖ ^ 2 ∂μ) =
      √(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖e ω‖ ^ 2 ∂μ) := mul_comm _ _
  linarith

lemma integral_mono_sq {f g : Ω → E d} {c : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
  (h : ∀ ω, ‖f ω‖ ≤ c * ‖g ω‖) :
  ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ c ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono (memLp_sq_integrable hf) ((memLp_sq_integrable hg).const_mul _)
    fun ω => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h ω) 2

lemma sqrt_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  Real.sqrt_le_iff.mpr ⟨hy, h⟩

/-! ### The second-moment recursion -/

set_option maxHeartbeats 1000000 in
/-- Lemma 3.3 of the write-up: the second moments `P k` of the shifted iterates satisfy
the recursion of the additive case, with remainder `O(β² (√‖P‖ + ‖P‖ + β))`. -/
theorem mult_secondMoment_recursion [IsProbabilityMeasure μ] {βbar : ℝ}
  (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ)
  (ℱ : MeasureTheory.Filtration ℕ m0) {θ M h : ℕ → Ω → E d} {N G : ℕ → Ω → E d →L[ℝ] E d}
  {Ch CM CN CG : ℝ} (hCN : 0 ≤ CN) (hCG : 0 ≤ CG)
  (hθ : MultRecursion A β θ M h N G)
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hhB : ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hMB : ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
  (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
  (hN : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N (k + 1))) (hNB : ∀ k ω, ‖N (k + 1) ω‖ ≤ CN)
  (hNmart : ∀ k i j, μ[fun ω => N (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0)
  (hG : ∀ k, StronglyMeasurable[ℱ k] (G k)) (hGB : ∀ k ω, ‖G k ω‖ ≤ CG)
  (hsmall : ∀ k, β k * CG ≤ 1 / 2) :
  ∃ C, 0 ≤ C ∧ ∀ k,
    ‖secondMoment μ (multShift β θ h G (k + 1)) - (secondMoment μ (multShift β θ h G k)
        - β k • lyapOp A (secondMoment μ (multShift β θ h G k))
        + β k ^ 2 • sandwich A (secondMoment μ (multShift β θ h G k))
        + β k ^ 2 • secondMoment μ (M (k + 1)))‖ ≤
    C * β k ^ 2 * (√‖secondMoment μ (multShift β θ h G k)‖
      + ‖secondMoment μ (multShift β θ h G k)‖ + β k) := by
  have hadapt := mult_iterates_adapted ℱ A hθ hθ0 hθ0L hh hhL hM hML hN hNB hG hGB
  obtain ⟨Cs, hCs0, hCs⟩ := hβ.abs_sub_le
  obtain ⟨B0, hB0⟩ := hβ.tendsto_zero.bddAbove_range
  obtain ⟨B, hB_def⟩ : ∃ B, B = max B0 0 := ⟨_, rfl⟩
  have hB : ∀ k, β k ≤ B := fun k => (hB0 ⟨k, rfl⟩).trans (hB_def ▸ le_max_left _ _)
  have hBnn : 0 ≤ B := hB_def ▸ le_max_right _ _
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hhB 0)
  have hCM0 : 0 ≤ CM := (integral_norm_sq_nonneg (μ := μ) (M 1)).trans (hMB 0)
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = ‖matCLM A‖ := ⟨_, rfl⟩
  have hAm0 : 0 ≤ Am := hAm ▸ norm_nonneg _
  -- the constant of `norm_mult_remainder_le`
  obtain ⟨K, hK⟩ : ∃ K, K = (Am * CG + Cs * CG * (1 + B * (Am + CN + 2 * CG))
      + CG * (Am + CN + 2 * CG)) + (Am + Cs + Cs * CG * B + CG) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = CM + Ch + Ch := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = √(8 * d) := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = √(8 * Ch) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := hα ▸ Real.sqrt_nonneg _
  have hγ0 : 0 ≤ γ := hγ ▸ Real.sqrt_nonneg _
  -- the coefficients of the monomials
  obtain ⟨c1, hc1⟩ : ∃ c, c = 2 * (1 + B * Am) * √d * (2 * K) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = 2 * (1 + B * Am) * √d * (2 * K) * √Q := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = 2 * √(2 * CM) * (2 * K) + 2 * (√2 * CN) * (2 * K) * √Q :=
    ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c, c = 2 * √(2 * CM) * (2 * K) * √Q := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ c, c = 2 * (√2 * CN) * (2 * K) := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ c, c = 4 * K ^ 2 := ⟨_, rfl⟩
  obtain ⟨c7, hc7⟩ : ∃ c, c = 4 * K ^ 2 * Q := ⟨_, rfl⟩
  obtain ⟨c8, hc8⟩ : ∃ c, c = 2 * √CM * CN := ⟨_, rfl⟩
  obtain ⟨c9, hc9⟩ : ∃ c, c = CN ^ 2 := ⟨_, rfl⟩
  have hcs : 0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ c3 ∧ 0 ≤ c4 ∧ 0 ≤ c5 ∧ 0 ≤ c6 ∧ 0 ≤ c7 ∧ 0 ≤ c8 ∧ 0 ≤ c9 := by
    rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9]
    exact ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
      by positivity, by positivity, by positivity, by positivity⟩
  obtain ⟨hc1', hc2', hc3', hc4', hc5', hc6', hc7', hc8', hc9'⟩ := hcs
  refine ⟨(c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9) * multΛ α γ B,
    mul_nonneg (by positivity) (by rw [multΛ]; positivity), fun k => ?_⟩
  have hb := hβ.pos k
  have hθk := hadapt k
  have hθ1 := hadapt (k + 1)
  -- the pieces of the decomposition
  obtain ⟨u, hu_def⟩ : ∃ u, u = multShift β θ h G k := ⟨_, rfl⟩
  obtain ⟨ν, hν_def⟩ : ∃ ν : Ω → E d, ν = fun ω => N (k + 1) ω (θ k ω) := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m : Ω → E d, m = fun ω => M (k + 1) ω - ν ω := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : Ω → E d, c = fun ω => (β k ^ 2) • matCLM A (h k ω - G k ω (θ k ω))
      + (β (k + 1) - β k) • (h (k + 1) ω - G (k + 1) ω (θ (k + 1) ω))
      - β k • G (k + 1) ω (θ (k + 1) ω - θ k ω) := ⟨_, rfl⟩
  have hGθL : ∀ n, MemLp (fun ω => G n ω (θ n ω)) 2 μ := fun n =>
    memLp_clm_apply ((hG n).mono (ℱ.le n)).aestronglyMeasurable (hGB n) (hadapt n).2
  have huL : MemLp u 2 μ := by
    rw [hu_def]; exact hθk.2.add (((hhL k).sub (hGθL k)).const_smul (β k))
  have hum : StronglyMeasurable[ℱ k] u := by
    rw [hu_def]
    exact hθk.1.add (((hh k).sub (stronglyMeasurable_clm_apply (hG k) hθk.1)).const_smul (β k))
  have hνL : MemLp ν 2 μ := by
    rw [hν_def]
    exact memLp_clm_apply ((hN k).mono (ℱ.le (k + 1))).aestronglyMeasurable (hNB k) hθk.2
  have hmL : MemLp m 2 μ := by rw [hm_def]; exact (hML k).sub hνL
  have hcL : MemLp c 2 μ := by
    rw [hc_def]
    refine ((((matCLM A).comp_memLp' ((hhL k).sub (hGθL k))).const_smul (β k ^ 2)).add
      (((hhL (k + 1)).sub (hGθL (k + 1))).const_smul (β (k + 1) - β k))).sub
      ((memLp_clm_apply ((hG (k + 1)).mono (ℱ.le (k + 1))).aestronglyMeasurable (hGB (k + 1))
        (hθ1.2.sub hθk.2)).const_smul (β k))
  have hmmart : ∀ j, μ[fun ω => m ω j | ℱ k] =ᵐ[μ] 0 := by
    intro j
    have hν0 : μ[fun ω => ν ω j | ℱ k] =ᵐ[μ] 0 := by
      rw [hν_def]
      exact condExp_clm_apply_eq_zero ((hN k).mono (ℱ.le (k + 1))).aestronglyMeasurable
        (hNB k) hθk.1 hθk.2 (hNmart k) j
    have hsub := condExp_sub ((memLp_apply (hML k) j).integrable one_le_two)
      ((memLp_apply hνL j).integrable one_le_two) (ℱ k) (μ := μ)
    have e : (fun ω => m ω j) = (fun ω => M (k + 1) ω j) - fun ω => ν ω j := by
      funext ω; rw [hm_def]; rfl
    rw [e]
    filter_upwards [hsub, hmart k j, hν0] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    simp
  have hnext : multShift β θ h G (k + 1) =
      fun ω => u ω - β k • matCLM A (u ω) + β k • m ω + c ω := by
    funext ω
    rw [hu_def, hm_def, hν_def, hc_def]
    exact mult_shifted_iterate A hθ k ω
  have hstep := secondMoment_step (ℱ.le k) A hb.le hum huL hmL hcL hmmart
  rw [← hnext] at hstep
  have hdev := norm_secondMoment_sub_le (μ := μ) (hML k) hνL
  rw [← hu_def]
  -- integral bounds
  obtain ⟨P, hP⟩ : ∃ P, P = secondMoment μ u := ⟨_, rfl⟩
  rw [← hP] at hstep ⊢
  obtain ⟨p, hp⟩ : ∃ p, p = ‖P‖ := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 ≤ p := hp ▸ norm_nonneg _
  obtain ⟨sp, hsp⟩ : ∃ sp, sp = √p := ⟨_, rfl⟩
  have hsp0 : 0 ≤ sp := hsp ▸ Real.sqrt_nonneg _
  have hsp2 : sp ^ 2 = p := by rw [hsp, Real.sq_sqrt hp0]
  rw [← hsp]
  have hEu : ∫ ω, ‖u ω‖ ^ 2 ∂μ ≤ d * p := by rw [hp, hP]; exact integral_norm_sq_le huL
  obtain ⟨T, hT⟩ : ∃ T, T = ∫ ω, ‖θ k ω‖ ^ 2 ∂μ := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ integral_norm_sq_nonneg _
  have hTle : T ≤ 8 * d * p + 8 * Ch * β k ^ 2 := by
    have hpt : ∀ ω, ‖θ k ω‖ ^ 2 ≤ 8 * ‖u ω‖ ^ 2 + 8 * β k ^ 2 * ‖h k ω‖ ^ 2 := by
      intro ω
      have := norm_le_of_multShift (θ := θ) (h := h) (ω := ω) hb.le (hGB k ω) (hsmall k)
      rw [← hu_def] at this
      have h2 := norm_sq_le_of_le (norm_nonneg _) this
      calc ‖θ k ω‖ ^ 2 ≤ 2 * (2 * ‖u ω‖) ^ 2 + 2 * (2 * β k * ‖h k ω‖) ^ 2 := h2
        _ = 8 * ‖u ω‖ ^ 2 + 8 * β k ^ 2 * ‖h k ω‖ ^ 2 := by ring
    have hint : T ≤ 8 * ∫ ω, ‖u ω‖ ^ 2 ∂μ + 8 * β k ^ 2 * ∫ ω, ‖h k ω‖ ^ 2 ∂μ := by
      rw [hT, ← integral_const_mul, ← integral_const_mul,
        ← integral_add ((memLp_sq_integrable huL).const_mul _)
          ((memLp_sq_integrable (hhL k)).const_mul _)]
      exact integral_mono (memLp_sq_integrable hθk.2)
        (((memLp_sq_integrable huL).const_mul _).add ((memLp_sq_integrable (hhL k)).const_mul _))
        hpt
    have := mul_le_mul_of_nonneg_left (hhB k) (by positivity : (0 : ℝ) ≤ 8 * β k ^ 2)
    linarith only [hint, hEu, this]
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = √T := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := hσ ▸ Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = T := by rw [hσ, Real.sq_sqrt hT0]
  have hσle : σ ≤ α * sp + γ * β k := by
    rw [hσ]
    refine sqrt_le_of_sq_le (by positivity) ?_
    have e : (α * sp + γ * β k) ^ 2 = 8 * d * p + 8 * Ch * β k ^ 2 + 2 * (α * sp) * (γ * β k) := by
      have h1 : α ^ 2 = 8 * d := by rw [hα, Real.sq_sqrt (by positivity)]
      have h2 : γ ^ 2 = 8 * Ch := by rw [hγ, Real.sq_sqrt (by positivity)]
      have : (α * sp + γ * β k) ^ 2 = α ^ 2 * sp ^ 2 + γ ^ 2 * β k ^ 2
          + 2 * (α * sp) * (γ * β k) := by ring
      rw [this, h1, h2, hsp2]
    have : 0 ≤ 2 * (α * sp) * (γ * β k) := by positivity
    linarith
  have hsEu : √(∫ ω, ‖u ω‖ ^ 2 ∂μ) ≤ √d * sp := by
    rw [hsp, ← Real.sqrt_mul (Nat.cast_nonneg d)]; exact Real.sqrt_le_sqrt hEu
  have hEν : ∫ ω, ‖ν ω‖ ^ 2 ∂μ ≤ CN ^ 2 * σ ^ 2 := by
    rw [hσ2, hT]
    exact integral_mono_sq hνL hθk.2 (fun ω => by rw [hν_def]; exact norm_clm_apply_le (hNB k ω) _)
  have hsEν : √(∫ ω, ‖ν ω‖ ^ 2 ∂μ) ≤ CN * σ :=
    sqrt_le_of_sq_le (by positivity) (by rw [mul_pow]; exact hEν)
  have hsEM : √(∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ) ≤ √CM := Real.sqrt_le_sqrt (hMB k)
  have hsEm : √(∫ ω, ‖m ω‖ ^ 2 ∂μ) ≤ √(2 * CM) + √2 * CN * σ := by
    refine sqrt_le_of_sq_le (by positivity) ?_
    have hpt : ∀ ω, ‖m ω‖ ^ 2 ≤ 2 * ‖M (k + 1) ω‖ ^ 2 + 2 * ‖ν ω‖ ^ 2 := by
      intro ω
      rw [hm_def]
      exact norm_sq_le_of_le (norm_nonneg _) (norm_sub_le _ _)
    have hint : ∫ ω, ‖m ω‖ ^ 2 ∂μ ≤
        2 * ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ + 2 * ∫ ω, ‖ν ω‖ ^ 2 ∂μ := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((memLp_sq_integrable (hML k)).const_mul _)
          ((memLp_sq_integrable hνL).const_mul _)]
      exact integral_mono (memLp_sq_integrable hmL)
        (((memLp_sq_integrable (hML k)).const_mul _).add ((memLp_sq_integrable hνL).const_mul _))
        hpt
    have e : (√(2 * CM) + √2 * CN * σ) ^ 2 =
        2 * CM + 2 * (CN ^ 2 * σ ^ 2) + 2 * √(2 * CM) * (√2 * CN * σ) := by
      have h1 : √(2 * CM) ^ 2 = 2 * CM := Real.sq_sqrt (by positivity)
      have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
      have : (√(2 * CM) + √2 * CN * σ) ^ 2 = √(2 * CM) ^ 2 + √2 ^ 2 * (CN ^ 2 * σ ^ 2)
          + 2 * √(2 * CM) * (√2 * CN * σ) := by ring
      rw [this, h1, h2]
    have h0 : 0 ≤ 2 * √(2 * CM) * (√2 * CN * σ) :=
      mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCN) hσ0)
    rw [e]
    linarith only [hint, hMB k, hEν, h0]
  have hEc : ∫ ω, ‖c ω‖ ^ 2 ∂μ ≤ 4 * K ^ 2 * β k ^ 4 * (σ ^ 2 + Q) := by
    have hpt : ∀ ω, ‖c ω‖ ^ 2 ≤ 4 * K ^ 2 * β k ^ 4 * (‖θ k ω‖ ^ 2
        + (‖M (k + 1) ω‖ ^ 2 + ‖h k ω‖ ^ 2 + ‖h (k + 1) ω‖ ^ 2)) := fun ω => by
      rw [hc_def]
      exact norm_sq_mult_remainder_le A hθ k ω hb.le (hB k) (hCs k) hCN hCG hBnn hCs0
        (hNB k ω) (hGB k ω) (hGB (k + 1) ω) (hAm ▸ hK)
    have i1 := memLp_sq_integrable hθk.2
    have i2 := memLp_sq_integrable (hML k)
    have i3 := memLp_sq_integrable (hhL k)
    have i4 := memLp_sq_integrable (hhL (k + 1))
    have i23 : Integrable (fun ω => ‖M (k + 1) ω‖ ^ 2 + ‖h k ω‖ ^ 2) μ := i2.add i3
    have i234 : Integrable (fun ω => ‖M (k + 1) ω‖ ^ 2 + ‖h k ω‖ ^ 2 + ‖h (k + 1) ω‖ ^ 2) μ :=
      i23.add i4
    have iall : Integrable (fun ω => ‖θ k ω‖ ^ 2
        + (‖M (k + 1) ω‖ ^ 2 + ‖h k ω‖ ^ 2 + ‖h (k + 1) ω‖ ^ 2)) μ := i1.add i234
    have hint := integral_mono (memLp_sq_integrable hcL) (iall.const_mul (4 * K ^ 2 * β k ^ 4)) hpt
    rw [integral_const_mul, integral_add i1 i234, integral_add i23 i4, integral_add i2 i3] at hint
    have hK4 : 0 ≤ 4 * K ^ 2 * β k ^ 4 :=
      mul_nonneg (mul_nonneg zero_le_four (sq_nonneg K)) (pow_nonneg hb.le 4)
    refine hint.trans (mul_le_mul_of_nonneg_left ?_ hK4)
    rw [← hT, hσ2, hQ]
    linarith only [hMB k, hhB k, hhB (k + 1)]
  have hsEc : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) ≤ 2 * K * β k ^ 2 * (σ + √Q) := by
    have hK4 : 0 ≤ 4 * K ^ 2 * β k ^ 4 :=
      mul_nonneg (mul_nonneg zero_le_four (sq_nonneg K)) (pow_nonneg hb.le 4)
    have hsQ := Real.sqrt_nonneg Q
    refine sqrt_le_of_sq_le (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hK0) (sq_nonneg _))
      (add_nonneg hσ0 hsQ)) (hEc.trans ?_)
    have hQ2 : √Q ^ 2 = Q := Real.sq_sqrt hQ0
    have h0 : 0 ≤ 4 * K ^ 2 * β k ^ 4 * (2 * σ * √Q) :=
      mul_nonneg hK4 (mul_nonneg (mul_nonneg zero_le_two hσ0) hsQ)
    have e : (2 * K * β k ^ 2 * (σ + √Q)) ^ 2 =
        4 * K ^ 2 * β k ^ 4 * (σ ^ 2 + Q) + 4 * K ^ 2 * β k ^ 4 * (2 * σ * √Q) := by
      have : (2 * K * β k ^ 2 * (σ + √Q)) ^ 2 = 4 * K ^ 2 * β k ^ 4 * (σ ^ 2 + √Q ^ 2)
          + 4 * K ^ 2 * β k ^ 4 * (2 * σ * √Q) := by ring
      rw [this, hQ2]
    rw [e]
    linarith only [h0]
  -- assemble
  rw [← hm_def] at hdev
  have hsplit : secondMoment μ (multShift β θ h G (k + 1)) - (P - β k • lyapOp A P
      + β k ^ 2 • sandwich A P + β k ^ 2 • secondMoment μ (M (k + 1))) =
      (secondMoment μ (multShift β θ h G (k + 1)) - (P - β k • lyapOp A P
        + β k ^ 2 • sandwich A P + β k ^ 2 • secondMoment μ m))
      + β k ^ 2 • (secondMoment μ m - secondMoment μ (M (k + 1))) := by
    rw [smul_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hdev' := mul_le_mul_of_nonneg_left hdev (sq_nonneg (β k))
  have sEu0 := Real.sqrt_nonneg (∫ ω, ‖u ω‖ ^ 2 ∂μ)
  have sEc0 := Real.sqrt_nonneg (∫ ω, ‖c ω‖ ^ 2 ∂μ)
  have sEm0 := Real.sqrt_nonneg (∫ ω, ‖m ω‖ ^ 2 ∂μ)
  have sEM0 := Real.sqrt_nonneg (∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ)
  have sd0 := Real.sqrt_nonneg (d : ℝ)
  have sQ0 := Real.sqrt_nonneg Q
  have sCM0 := Real.sqrt_nonneg CM
  have s2CM0 := Real.sqrt_nonneg (2 * CM)
  have s20 := Real.sqrt_nonneg (2 : ℝ)
  have hKb : 0 ≤ 2 * K * β k ^ 2 * (σ + √Q) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hK0) (sq_nonneg _)) (add_nonneg hσ0 sQ0)
  have b1 : 2 * ((1 + β k * ‖matCLM A‖) * √(∫ ω, ‖u ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ)) ≤
      β k ^ 2 * (c1 * (sp * σ) + c2 * sp) := by
    have h1 : 1 + β k * ‖matCLM A‖ ≤ 1 + B * Am := by
      rw [← hAm]; linarith only [mul_le_mul_of_nonneg_right (hB k) hAm0]
    have h2 := mul_le_mul (mul_le_mul h1 hsEu sEu0 (by linarith only [mul_nonneg hBnn hAm0]))
      hsEc sEc0 (mul_nonneg (by linarith only [mul_nonneg hBnn hAm0]) (mul_nonneg sd0 hsp0))
    have e : 2 * ((1 + B * Am) * (√d * sp) * (2 * K * β k ^ 2 * (σ + √Q))) =
        β k ^ 2 * (c1 * (sp * σ) + c2 * sp) := by rw [hc1, hc2]; ring
    linarith only [h2, e]
  have b2 : 2 * (β k * √(∫ ω, ‖m ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ)) ≤
      β k ^ 2 * (c3 * (β k * σ) + c4 * β k + c5 * (β k * σ ^ 2)) := by
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul hsEm hsEc sEc0
      (add_nonneg s2CM0 (mul_nonneg (mul_nonneg s20 hCN) hσ0))) hb.le
    have e : 2 * (β k * ((√(2 * CM) + √2 * CN * σ) * (2 * K * β k ^ 2 * (σ + √Q)))) =
        β k ^ 2 * (c3 * (β k * σ) + c4 * β k + c5 * (β k * σ ^ 2)) := by
      rw [hc3, hc4, hc5]; ring
    have e2 : β k * √(∫ ω, ‖m ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) =
        β k * (√(∫ ω, ‖m ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ)) := by ring
    rw [e2]
    linarith only [h2, e]
  have b3 : ∫ ω, ‖c ω‖ ^ 2 ∂μ ≤ β k ^ 2 * (c6 * (β k ^ 2 * σ ^ 2) + c7 * β k ^ 2) := by
    have e : 4 * K ^ 2 * β k ^ 4 * (σ ^ 2 + Q) = β k ^ 2 * (c6 * (β k ^ 2 * σ ^ 2) + c7 * β k ^ 2) := by
      rw [hc6, hc7]; ring
    linarith only [hEc, e]
  have b4 : β k ^ 2 * (2 * (√(∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ) * √(∫ ω, ‖ν ω‖ ^ 2 ∂μ))
      + ∫ ω, ‖ν ω‖ ^ 2 ∂μ) ≤ β k ^ 2 * (c8 * σ + c9 * σ ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have h2 := mul_le_mul hsEM hsEν (Real.sqrt_nonneg _) sCM0
    have e : 2 * (√CM * (CN * σ)) + CN ^ 2 * σ ^ 2 = c8 * σ + c9 * σ ^ 2 := by
      rw [hc8, hc9]; ring
    linarith only [h2, hEν, e]
  have hpoly := mul_le_mul_of_nonneg_left (mult_poly_le hsp0 hsp2 hb.le (hB k) hσ0 hσle hα0 hγ0
    hc1' hc2' hc3' hc4' hc5' hc6' hc7' hc8' hc9') (sq_nonneg (β k))
  have e : (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9) * multΛ α γ B * β k ^ 2 * (sp + p + β k)
      = β k ^ 2 * ((c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9) * multΛ α γ B * (sp + p + β k)) := by
    ring
  rw [e]
  linarith only [hstep, hdev', b1, b2, b3, b4, hpoly]

/-- `E‖θ‖² ≤ 8 d ‖E[u uᵀ]‖ + 8 β² sup E‖h‖²` for the shifted iterate `u`. -/
lemma integral_norm_sq_le_of_multShift {θ h : ℕ → Ω → E d} {G : ℕ → Ω → E d →L[ℝ] E d}
  {CG Ch : ℝ} {k : ℕ} (hb : 0 ≤ β k) (hGB : ∀ ω, ‖G k ω‖ ≤ CG) (hsmall : β k * CG ≤ 1 / 2)
  (hθL : MemLp (θ k) 2 μ) (huL : MemLp (multShift β θ h G k) 2 μ) (hhL : MemLp (h k) 2 μ)
  (hhB : ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch) :
  ∫ ω, ‖θ k ω‖ ^ 2 ∂μ ≤ 8 * d * ‖secondMoment μ (multShift β θ h G k)‖ + 8 * Ch * β k ^ 2 := by
  have hpt : ∀ ω, ‖θ k ω‖ ^ 2 ≤
      8 * ‖multShift β θ h G k ω‖ ^ 2 + 8 * β k ^ 2 * ‖h k ω‖ ^ 2 := by
    intro ω
    have h2 := norm_sq_le_of_le (norm_nonneg _) (norm_le_of_multShift (θ := θ) (h := h) (ω := ω) hb (hGB ω) hsmall)
    calc ‖θ k ω‖ ^ 2 ≤ 2 * (2 * ‖multShift β θ h G k ω‖) ^ 2 + 2 * (2 * β k * ‖h k ω‖) ^ 2 := h2
      _ = 8 * ‖multShift β θ h G k ω‖ ^ 2 + 8 * β k ^ 2 * ‖h k ω‖ ^ 2 := by ring
  have i1 := (memLp_sq_integrable huL).const_mul 8
  have i2 := (memLp_sq_integrable hhL).const_mul (8 * β k ^ 2)
  have i12 : Integrable (fun ω => 8 * ‖multShift β θ h G k ω‖ ^ 2
      + 8 * β k ^ 2 * ‖h k ω‖ ^ 2) μ := i1.add i2
  have hint := integral_mono (memLp_sq_integrable hθL) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hint
  have h1 := integral_norm_sq_le huL
  have h2 := mul_le_mul_of_nonneg_left hhB (by positivity : (0 : ℝ) ≤ 8 * β k ^ 2)
  linarith

/-! ### The main theorem -/

/-- Theorem 3.1 of the write-up when `β k ‖G k‖ ≤ 1/2` for every `k`. -/
theorem tendsto_secondMoment_of_mult_noise_of_small [IsProbabilityMeasure μ] {βbar : ℝ}
  (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
  (ℱ : MeasureTheory.Filtration ℕ m0) {θ M h : ℕ → Ω → E d} {N G : ℕ → Ω → E d →L[ℝ] E d}
  {Γ : Mat d} {Ch CM CN CG : ℝ} (hCN : 0 ≤ CN) (hCG : 0 ≤ CG)
  (hθ : MultRecursion A β θ M h N G)
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hhB : ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hMB : ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
  (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
  (hN : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N (k + 1))) (hNB : ∀ k ω, ‖N (k + 1) ω‖ ≤ CN)
  (hNmart : ∀ k i j, μ[fun ω => N (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0)
  (hG : ∀ k, StronglyMeasurable[ℱ k] (G k)) (hGB : ∀ k ω, ‖G k ω‖ ≤ CG)
  (hsmall : ∀ k, β k * CG ≤ 1 / 2)
  (hΓ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ)) :
  ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
    Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨Sig, hSig⟩ := exists_solution_of_coercive _ (by positivity : (0 : ℝ) < 2 * η)
    (lyapOp_coercive _ hA) Γ
  refine ⟨Sig, hSig, ?_⟩
  have hadapt := mult_iterates_adapted ℱ A hθ hθ0 hθ0L hh hhL hM hML hN hNB hG hGB
  obtain ⟨C, hC0, hCR⟩ := mult_secondMoment_recursion hβ A ℱ hCN hCG hθ hθ0 hθ0L hh hhL hhB
    hM hML hMB hmart hN hNB hNmart hG hGB hsmall
  obtain ⟨P, hP_def⟩ : ∃ P : ℕ → Mat d, P = fun k => secondMoment μ (multShift β θ h G k) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ R : ℕ → Mat d, R = fun k => P (k + 1) - (P k - β k • lyapOp A (P k)
      + β k ^ 2 • sandwich A (P k) + β k ^ 2 • secondMoment μ (M (k + 1))) := ⟨_, rfl⟩
  have hrec : ∀ k, P (k + 1) = P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
      + β k ^ 2 • secondMoment μ (M (k + 1)) + R k := by
    intro k
    simp only [hR_def]
    abel
  have hRb : ∃ C, 0 ≤ C ∧ ∀ k, ‖R k‖ ≤ C * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k) :=
    ⟨C, hC0, fun k => by rw [hR_def, hP_def]; exact hCR k⟩
  have hPlim := tendsto_normalized_second_moment hβ A hη hA hSig hΓ hRb hrec
  have hP0 : Tendsto (fun k => ‖P k‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => β k • ((β k)⁻¹ • P k)) atTop (𝓝 ((0 : ℝ) • Sig)) :=
      hβ.tendsto_zero.smul hPlim
    rw [zero_smul] at h1
    have h2 : (fun k => β k • ((β k)⁻¹ • P k)) = P :=
      funext fun k => by rw [smul_smul, mul_inv_cancel₀ (hβ.pos k).ne', one_smul]
    rw [h2] at h1
    simpa using h1.norm
  -- the moments of `θ` and of the shifted iterates differ by `o(β)`
  obtain ⟨B0, hB0⟩ := hβ.tendsto_zero.bddAbove_range
  obtain ⟨B, hB_def⟩ : ∃ B, B = max B0 0 := ⟨_, rfl⟩
  have hB : ∀ k, β k ≤ B := fun k => (hB0 ⟨k, rfl⟩).trans (hB_def ▸ le_max_left _ _)
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hhB 0)
  obtain ⟨D, hD_def⟩ : ∃ D : ℕ → ℝ, D = fun k => 2 * Ch + 2 * CG ^ 2 * (8 * d * ‖P k‖ + 8 * Ch * B ^ 2) :=
    ⟨_, rfl⟩
  have hD0 : ∀ k, 0 ≤ D k := fun k => by rw [hD_def]; positivity
  have hdiff : ∀ k, ‖(β k)⁻¹ • secondMoment μ (θ k) - (β k)⁻¹ • P k‖ ≤
      2 * (√(d * ‖P k‖) * √(D k)) + β k * D k := by
    intro k
    have hb := hβ.pos k
    obtain ⟨θ', hθ'_def⟩ : ∃ θ' : Ω → E d, θ' = multShift β θ h G k := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : Ω → E d, g = fun ω => (-β k) • (h k ω - G k ω (θ k ω)) :=
      ⟨_, rfl⟩
    have hGθL : MemLp (fun ω => G k ω (θ k ω)) 2 μ :=
      memLp_clm_apply ((hG k).mono (ℱ.le k)).aestronglyMeasurable (hGB k) (hadapt k).2
    have hθ'L : MemLp θ' 2 μ := by
      rw [hθ'_def]; exact (hadapt k).2.add (((hhL k).sub hGθL).const_smul (β k))
    have hgL : MemLp g 2 μ := by rw [hg_def]; exact ((hhL k).sub hGθL).const_smul (-β k)
    have hPk : P k = secondMoment μ θ' := by rw [hP_def, hθ'_def]
    have hθk : θ k = fun ω => θ' ω + g ω := by
      funext ω
      rw [hθ'_def, hg_def, multShift]
      module
    have hexp : secondMoment μ (θ k) =
        secondMoment μ θ' + crossMoment μ θ' g + (crossMoment μ g θ' + crossMoment μ g g) := by
      have hsL : MemLp (fun ω => θ' ω + g ω) 2 μ := hθ'L.add hgL
      rw [hθk, secondMoment, crossMoment_add_left hθ'L hgL hsL,
        crossMoment_add_right hθ'L hθ'L hgL, crossMoment_add_right hgL hθ'L hgL]
      rfl
    have hT := integral_norm_sq_le_of_multShift hb.le (hGB k) (hsmall k) (hadapt k).2
      (hθ'_def ▸ hθ'L) (hhL k) (hhB k)
    rw [← hθ'_def, ← hPk] at hT
    have hEg : ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ β k ^ 2 * D k := by
      have hpt : ∀ ω, ‖g ω‖ ^ 2 ≤ 2 * β k ^ 2 * ‖h k ω‖ ^ 2 + 2 * β k ^ 2 * CG ^ 2 * ‖θ k ω‖ ^ 2 := by
        intro ω
        have h1 : ‖g ω‖ ≤ β k * ‖h k ω‖ + β k * CG * ‖θ k ω‖ := by
          rw [hg_def, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hb]
          calc β k * ‖h k ω - G k ω (θ k ω)‖ ≤ β k * (‖h k ω‖ + CG * ‖θ k ω‖) :=
                mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
                  (add_le_add_left (norm_clm_apply_le (hGB k ω) _) _)) hb.le
            _ = β k * ‖h k ω‖ + β k * CG * ‖θ k ω‖ := by ring
        have := norm_sq_le_of_le (norm_nonneg _) h1
        calc ‖g ω‖ ^ 2 ≤ 2 * (β k * ‖h k ω‖) ^ 2 + 2 * (β k * CG * ‖θ k ω‖) ^ 2 := this
          _ = _ := by ring
      have i1 := (memLp_sq_integrable (hhL k)).const_mul (2 * β k ^ 2)
      have i2 := (memLp_sq_integrable (hadapt k).2).const_mul (2 * β k ^ 2 * CG ^ 2)
      have i12 : Integrable (fun ω => 2 * β k ^ 2 * ‖h k ω‖ ^ 2
          + 2 * β k ^ 2 * CG ^ 2 * ‖θ k ω‖ ^ 2) μ := i1.add i2
      have hint := integral_mono (memLp_sq_integrable hgL) i12 hpt
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hint
      have hbB2 : β k ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hb.le (hB k) 2
      have h1 := mul_le_mul_of_nonneg_left (hhB k) (by positivity : (0 : ℝ) ≤ 2 * β k ^ 2)
      have hT' : ∫ ω, ‖θ k ω‖ ^ 2 ∂μ ≤ 8 * d * ‖P k‖ + 8 * Ch * B ^ 2 := by
        have := mul_le_mul_of_nonneg_left hbB2 (by positivity : (0 : ℝ) ≤ 8 * Ch)
        linarith
      have h2 := mul_le_mul_of_nonneg_left hT' (by positivity : (0 : ℝ) ≤ 2 * β k ^ 2 * CG ^ 2)
      have e : β k ^ 2 * D k = 2 * β k ^ 2 * Ch
          + 2 * β k ^ 2 * CG ^ 2 * (8 * d * ‖P k‖ + 8 * Ch * B ^ 2) := by rw [hD_def]; ring
      linarith
    have hsg : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ β k * √(D k) := by
      calc √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ √(β k ^ 2 * D k) := Real.sqrt_le_sqrt hEg
        _ = β k * √(D k) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb.le]
    have hsθ : √(∫ ω, ‖θ' ω‖ ^ 2 ∂μ) ≤ √(d * ‖P k‖) := by
      rw [hPk]; exact Real.sqrt_le_sqrt (integral_norm_sq_le hθ'L)
    have hsg2 : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) * √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ β k ^ 2 * D k := by
      rw [Real.mul_self_sqrt (integral_norm_sq_nonneg g)]; exact hEg
    have n1 := norm_crossMoment_le (μ := μ) hθ'L hgL
    have n2 := norm_crossMoment_le (μ := μ) hgL hθ'L
    have n3 := norm_crossMoment_le (μ := μ) hgL hgL
    have sg0 := Real.sqrt_nonneg (∫ ω, ‖g ω‖ ^ 2 ∂μ)
    have m1 : √(∫ ω, ‖θ' ω‖ ^ 2 ∂μ) * √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ √(d * ‖P k‖) * (β k * √(D k)) :=
      mul_le_mul hsθ hsg sg0 (Real.sqrt_nonneg _)
    have m2 : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) * √(∫ ω, ‖θ' ω‖ ^ 2 ∂μ) ≤ √(d * ‖P k‖) * (β k * √(D k)) := by
      rw [mul_comm]; exact m1
    have hnorm : ‖secondMoment μ (θ k) - P k‖ ≤
        2 * (√(d * ‖P k‖) * (β k * √(D k))) + β k ^ 2 * D k := by
      have : secondMoment μ (θ k) - P k =
          crossMoment μ θ' g + crossMoment μ g θ' + crossMoment μ g g := by
        rw [hexp, hPk]; abel
      rw [this]
      have t1 := norm_add_le (crossMoment μ θ' g + crossMoment μ g θ') (crossMoment μ g g)
      have t2 := norm_add_le (crossMoment μ θ' g) (crossMoment μ g θ')
      linarith
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]
    calc (β k)⁻¹ * ‖secondMoment μ (θ k) - P k‖
        ≤ (β k)⁻¹ * (2 * (√(d * ‖P k‖) * (β k * √(D k))) + β k ^ 2 * D k) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 2 * (√(d * ‖P k‖) * √(D k)) + β k * D k := by field_simp; ring
  have hDlim : Tendsto D atTop (𝓝 (2 * Ch + 2 * CG ^ 2 * (8 * d * 0 + 8 * Ch * B ^ 2))) := by
    rw [hD_def]
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul hP0).add tendsto_const_nhds))
  have hdiff0 : Tendsto (fun k => 2 * (√(d * ‖P k‖) * √(D k)) + β k * D k) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => √(d * ‖P k‖)) atTop (𝓝 0) := by
      have h1 := hP0.const_mul (d : ℝ)
      rw [mul_zero] at h1
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this
      exact this
    have hsD := (Real.continuous_sqrt.tendsto _).comp hDlim
    have := ((hs.mul hsD).const_mul 2).add (hβ.tendsto_zero.mul hDlim)
    simpa using this
  have hsq := squeeze_zero_norm hdiff hdiff0
  have hsum := hPlim.add hsq
  rw [add_zero] at hsum
  exact hsum.congr fun k => by abel

/-- Step sizes shifted in time satisfy the same condition. -/
lemma StepSizeRate.shift {βbar : ℝ} (hβ : StepSizeRate β βbar) (K : ℕ) :
    StepSizeRate (fun j => β (K + j)) βbar where
  pos _ := hβ.pos _
  tendsto_zero := hβ.tendsto_zero.comp (tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.add_le_add_left h K) fun b => ⟨b, Nat.le_add_left b K⟩)
  inv_diff := hβ.inv_diff.comp (tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.add_le_add_left h K) fun b => ⟨b, Nat.le_add_left b K⟩)
  βbar_nonneg := hβ.βbar_nonneg

/-- A filtration shifted in time. -/
def Filtration.shift (ℱ : MeasureTheory.Filtration ℕ m0) (K : ℕ) :
    MeasureTheory.Filtration ℕ m0 where
  seq j := ℱ (K + j)
  mono' _ _ h := ℱ.mono (Nat.add_le_add_left h K)
  le' _ := ℱ.le _

lemma tendsto_shift_iff {X : Type*} [TopologicalSpace X] {f : ℕ → X} {x : X} (K : ℕ) :
    Tendsto (fun j => f (K + j)) atTop (𝓝 x) ↔ Tendsto f atTop (𝓝 x) := by
  have e : (fun j => f (K + j)) = fun n => f (n + K) := funext fun n => by rw [add_comm]
  rw [e]
  exact tendsto_add_atTop_iff_nat K

/-- **Theorem 3.1 of the write-up.** Linear stochastic approximation with multiplicative
Markov noise, `θ (k+1) = θ k - β k (A + N (k+1) + G k - G (k+1)) θ k + β k V k` with
`V k = M (k+1) + h k - h (k+1)`, has `β k⁻¹ E[θ k θ kᵀ] → Σ`, where `Σ` solves
`(A - β̄/2) Σ + Σ (A - β̄/2)ᵀ = Γ` and `Γ = lim E[M (k+1) M (k+1)ᵀ]`: the multiplicative
noise does not change the asymptotic covariance. -/
theorem tendsto_secondMoment_of_mult_noise [IsProbabilityMeasure μ] {βbar : ℝ}
  (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
  (ℱ : MeasureTheory.Filtration ℕ m0) {θ M h : ℕ → Ω → E d} {N G : ℕ → Ω → E d →L[ℝ] E d}
  {Γ : Mat d}
  (hθ : MultRecursion A β θ M h N G)
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hMB : ∃ CM, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
  (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
  (hN : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N (k + 1)))
  (hNB : ∃ CN, ∀ k ω, ‖N (k + 1) ω‖ ≤ CN)
  (hNmart : ∀ k i j, μ[fun ω => N (k + 1) ω (EuclideanSpace.single i 1) j | ℱ k] =ᵐ[μ] 0)
  (hG : ∀ k, StronglyMeasurable[ℱ k] (G k)) (hGB : ∃ CG, ∀ k ω, ‖G k ω‖ ≤ CG)
  (hΓ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ)) :
  ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
    Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨Ch, hCh⟩ := hhB
  obtain ⟨CM, hCM⟩ := hMB
  obtain ⟨CN0, hCN0⟩ := hNB
  obtain ⟨CG0, hCG0⟩ := hGB
  have hNB : ∀ k ω, ‖N (k + 1) ω‖ ≤ max CN0 0 := fun k ω => (hCN0 k ω).trans (le_max_left _ _)
  have hGB : ∀ k ω, ‖G k ω‖ ≤ max CG0 0 := fun k ω => (hCG0 k ω).trans (le_max_left _ _)
  set CG := max CG0 0 with hCG_def
  have hCG : 0 ≤ CG := le_max_right _ _
  -- from some time on the steps are small
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hβ.tendsto_zero.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * (CG + 1)))))
  have hsmall : ∀ j, β (K + j) * CG ≤ 1 / 2 := by
    intro j
    have h1 := hK (K + j) (Nat.le_add_right K j)
    have hb := hβ.pos (K + j)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hadapt := mult_iterates_adapted ℱ A hθ hθ0 hθ0L hh hhL hM hML hN hNB hG hGB
  obtain ⟨Sig, hSig, hlim⟩ := tendsto_secondMoment_of_mult_noise_of_small (hβ.shift K) A hη hA
    (Filtration.shift ℱ K) (θ := fun j => θ (K + j)) (M := fun j => M (K + j))
    (h := fun j => h (K + j)) (N := fun j => N (K + j)) (G := fun j => G (K + j))
    (le_max_right _ _) hCG (fun j ω => hθ (K + j) ω) (hadapt K).1 (hadapt K).2
    (fun j => hh (K + j)) (fun j => hhL (K + j)) (fun j => hCh (K + j))
    (fun j => hM (K + j)) (fun j => hML (K + j)) (fun j => hCM (K + j))
    (fun j => hmart (K + j)) (fun j => hN (K + j)) (fun j => hNB (K + j))
    (fun j => hNmart (K + j)) (fun j => hG (K + j)) (fun j => hGB (K + j)) hsmall
    ((tendsto_shift_iff K (f := fun k => secondMoment μ (M (k + 1)))).mpr hΓ)
  exact ⟨Sig, hSig, (tendsto_shift_iff K (f := fun k => (β k)⁻¹ • secondMoment μ (θ k))).mp hlim⟩

end StochasticApproximation
