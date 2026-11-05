/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.PoissonNoise

/-!
# Moments of eligibility traces along a finite Markov chain

For a chain `Y` on a finite set with transitions `Q` and a trace
`z (k+1) = c (Y (k+1)) z k + φ (Y (k+1))`, the moments
`m₁ k a y = E[z_k(a) 1{Y_k = y}]` and `m₂ k a b y = E[z_k(a) z_k(b) 1{Y_k = y}]` satisfy exact
affine recursions driven by the transfer operator `(L x) y' = c y' Σ_y Q y y' x y`. When
`Σ_{y'} Q y y' |c y'| ≤ ρ < 1` (for the restart chain, `ρ = λγ`), `L` is a contraction in `ℓ¹`
and the moments converge to the solutions of the stationary moment equations.

* `tendsto_affine_transfer`: `x (k+1) = L x k + b k` with `b k → b` converges to the solution of
  `x = L x + b`.
* `lawAt_succ`, `mom1_succ`, `mom2_succ`: the exact recursions, from the Markov property.
* `tendsto_trace_moments`: the moments converge; the limit of `m₁` is the `TraceMoment` of
  `docs/actor-critic-rates.md`.
-/

open Filter Topology Finset Real MeasureTheory RLTheory Matrix

namespace StochasticApproximation

/-! ### Contractions in `ℓ¹` -/

section Contraction

variable {S : Type*} [Fintype S]

/-- The transfer operator `(L x) y' = c y' Σ_y Q y y' x y`. -/
def transfer (Q : S → S → ℝ) (c : S → ℝ) (x : S → ℝ) (y' : S) : ℝ := c y' * ∑ y, Q y y' * x y

/-- `L` contracts the `ℓ¹` norm when `Σ_{y'} Q y y' |c y'| ≤ ρ`. -/
lemma l1_transfer_le {Q : S → S → ℝ} {c : S → ℝ} {ρ : ℝ} (hQ : ∀ y y', 0 ≤ Q y y')
    (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (x : S → ℝ) :
    ∑ y', |transfer Q c x y'| ≤ ρ * ∑ y, |x y| := by
  have h1 : ∀ y', |transfer Q c x y'| ≤ ∑ y, |c y'| * Q y y' * |x y| := fun y' => by
    unfold transfer
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans ?_
    rw [mul_sum]
    exact le_of_eq (sum_congr rfl fun y _ => by rw [abs_mul, abs_of_nonneg (hQ y y')]; ring)
  calc ∑ y', |transfer Q c x y'| ≤ ∑ y', ∑ y, |c y'| * Q y y' * |x y| := sum_le_sum fun y' _ => h1 y'
    _ = ∑ y, |x y| * ∑ y', Q y y' * |c y'| := by
      rw [sum_comm]
      exact sum_congr rfl fun y _ => by rw [mul_sum]; exact sum_congr rfl fun y' _ => by ring
    _ ≤ ∑ y, |x y| * ρ := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hρ y) (abs_nonneg _)
    _ = ρ * ∑ y, |x y| := by rw [mul_sum]; exact sum_congr rfl fun y _ => by ring

/-- A sequence with `u (k+1) ≤ ρ u k + w k`, `0 ≤ ρ < 1` and `w k → 0` tends to `0`. -/
lemma tendsto_zero_of_le_contract {u w : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hu : ∀ k, 0 ≤ u k) (hrec : ∀ k, u (k + 1) ≤ ρ * u k + w k)
    (hw : Tendsto w atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1ρ : 0 < 1 - ρ := by linarith
  have hδ : 0 < ε / 2 - ρ * ε / 2 := by nlinarith
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hw _ hδ
  have hb : ∀ n, u (K + n) ≤ ρ ^ n * u K + ε / 2 := by
    intro n
    induction n with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ n ih =>
      have h1 := hrec (K + n)
      have h2 : w (K + n) < ε / 2 - ρ * ε / 2 := by
        have := hK (K + n) (by omega)
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans_lt this
      have h3 : ρ * u (K + n) ≤ ρ ^ n * ρ * u K + ρ * ε / 2 := by
        have := mul_le_mul_of_nonneg_left ih hρ0
        linarith [this, show ρ * (ρ ^ n * u K + ε / 2) = ρ ^ n * ρ * u K + ρ * ε / 2 by ring]
      rw [show K + (n + 1) = K + n + 1 by ring, pow_succ]
      linarith
  have hp : Tendsto (fun n => ρ ^ n * u K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (u K)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hp _ (half_pos hε)
  refine ⟨K + N, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = K + n := ⟨k - K, by omega⟩
  have := hN n (by omega)
  rw [Real.dist_eq, sub_zero] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu _)]
  linarith [hb n, le_abs_self (ρ ^ n * u K)]

/-- The fixed-point equation `x = L x + b` has a solution. -/
lemma exists_transfer_fixed {Q : S → S → ℝ} {c : S → ℝ} {ρ : ℝ} (hQ : ∀ y y', 0 ≤ Q y y')
    (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (hρ1 : ρ < 1) (b : S → ℝ) :
    ∃ x : S → ℝ, ∀ y', x y' = transfer Q c x y' + b y' := by
  let Lm : (S → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun x y' => x y' - transfer Q c x y'
      map_add' := fun x x' => by
        funext y'; simp only [transfer, Pi.add_apply, mul_add, sum_add_distrib]; ring
      map_smul' := fun r x => by
        funext y'; simp only [transfer, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        rw [mul_sub, mul_sum]; congr 1; exact sum_congr rfl fun y _ => by ring }
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hfix : ∀ y', x y' = transfer Q c x y' := fun y' => by
      have := congrFun hx y'
      simp only [Lm, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      linarith
    have hle := l1_transfer_le hQ hρ x
    simp only [← hfix] at hle
    have hnn : 0 ≤ ∑ y, |x y| := sum_nonneg fun _ _ => abs_nonneg _
    have h0 : ∑ y, |x y| = 0 := by nlinarith
    funext y
    have := (sum_eq_zero_iff_of_nonneg fun y _ => abs_nonneg (x y)).mp h0 y (mem_univ y)
    simpa using this
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj b
  refine ⟨x, fun y' => ?_⟩
  have := congrFun hx y'
  simp only [Lm, LinearMap.coe_mk, AddHom.coe_mk] at this
  linarith

/-- **Affine iterations of a contraction.** If `x (k+1) = L x k + b k` and `b k → b∞`, then
`x k` converges to the solution of `x = L x + b∞`. -/
theorem tendsto_affine_transfer {Q : S → S → ℝ} {c : S → ℝ} {ρ : ℝ} (hQ : ∀ y y', 0 ≤ Q y y')
    (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {x b : ℕ → S → ℝ}
    {bl : S → ℝ} (hrec : ∀ k y', x (k + 1) y' = transfer Q c (x k) y' + b k y')
    (hb : ∀ y, Tendsto (fun k => b k y) atTop (𝓝 (bl y))) :
    ∃ xl : S → ℝ, (∀ y', xl y' = transfer Q c xl y' + bl y') ∧
      ∀ y, Tendsto (fun k => x k y) atTop (𝓝 (xl y)) := by
  obtain ⟨xl, hxl⟩ := exists_transfer_fixed hQ hρ hρ1 bl
  refine ⟨xl, hxl, ?_⟩
  set u : ℕ → ℝ := fun k => ∑ y, |x k y - xl y| with hu
  set w : ℕ → ℝ := fun k => ∑ y, |b k y - bl y| with hwdef
  have hlin : ∀ k y', x (k + 1) y' - xl y' =
      transfer Q c (fun y => x k y - xl y) y' + (b k y' - bl y') := fun k y' => by
    rw [hrec k y', hxl y']
    simp only [transfer, mul_sub, sum_sub_distrib, mul_sub]
    ring
  have hrecu : ∀ k, u (k + 1) ≤ ρ * u k + w k := fun k => by
    simp only [hu, hwdef, hlin]
    calc ∑ y', |transfer Q c (fun y => x k y - xl y) y' + (b k y' - bl y')|
        ≤ ∑ y', (|transfer Q c (fun y => x k y - xl y) y'| + |b k y' - bl y'|) :=
          sum_le_sum fun _ _ => abs_add_le _ _
      _ = ∑ y', |transfer Q c (fun y => x k y - xl y) y'| + ∑ y', |b k y' - bl y'| :=
          sum_add_distrib
      _ ≤ ρ * ∑ y, |x k y - xl y| + ∑ y', |b k y' - bl y'| := by
          gcongr; exact l1_transfer_le hQ hρ _
  have hw : Tendsto w atTop (𝓝 0) := by
    have := tendsto_finset_sum (univ : Finset S) fun y _ =>
      ((hb y).sub_const (bl y)).abs
    simpa [sub_self, abs_zero, hwdef] using this
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_zero_of_le_contract hρ0 hρ1
    (fun k => sum_nonneg fun _ _ => abs_nonneg _) hrecu hw
  intro y
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hu0
  rw [Real.norm_eq_abs]
  exact single_le_sum (f := fun y => |x k y - xl y|) (fun _ _ => abs_nonneg _) (mem_univ y)

end Contraction

/-! ### Moments along the chain -/

section Process

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → S} {Q : S → S → ℝ}

/-- `momAt Y X k y = E[X_k 1{Y_k = y}]`. -/
noncomputable def momAt (μ : Measure Ω) (Y : ℕ → Ω → S) (X : ℕ → Ω → ℝ) (k : ℕ) (y : S) : ℝ :=
  ∫ ω, {ω | Y k ω = y}.indicator (X k) ω ∂μ

omit [IsProbabilityMeasure μ] [DecidableEq S] in
lemma FiniteMarkov.measurableSet_eq (hY : FiniteMarkov μ ℱ Y Q) (k : ℕ) (y : S) :
    MeasurableSet[ℱ k] {ω | Y k ω = y} :=
  hY.adapted k (measurableSet_singleton y)

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
lemma integrable_of_bdd {k : ℕ} {W : Ω → ℝ} (hW : StronglyMeasurable[ℱ k] W)
    (hWB : ∃ C, ∀ ω, |W ω| ≤ C) : Integrable W μ := by
  obtain ⟨C, hC⟩ := hWB
  exact (memLp_top_of_bound (hW.mono (ℱ.le k)).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top

omit [DecidableEq S] in
/-- A bounded `ℱ k`-measurable variable is integrable, and so is its restriction. -/
lemma integrable_indicator_of_bdd (hY : FiniteMarkov μ ℱ Y Q) {k j : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (y : S) :
    Integrable ({ω | Y j ω = y}.indicator W) μ := by
  obtain ⟨C, hC⟩ := hWB
  have hI : Integrable W μ :=
    (memLp_top_of_bound (hW.mono (ℱ.le k)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top
  exact hI.indicator ((ℱ.le j) _ (hY.measurableSet_eq j y))

omit [IsProbabilityMeasure μ] [DecidableEq S] in
lemma FiniteMarkov.stronglyMeasurable_real₂ (hY : FiniteMarkov μ ℱ Y Q) (F : S → S → ℝ) (k : ℕ) :
    StronglyMeasurable fun ω => F (Y k ω) (Y (k + 1) ω) :=
  (StronglyMeasurable.of_discrete (f := Function.uncurry F)).comp_measurable
    (((hY.adapted k).mono (ℱ.le k) le_rfl).prodMk ((hY.adapted (k + 1)).mono (ℱ.le (k + 1)) le_rfl))

omit [DecidableEq S] in
lemma integrable_mul_next (hY : FiniteMarkov μ ℱ Y Q) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (F : S → S → ℝ) :
    Integrable (fun ω => W ω * F (Y k ω) (Y (k + 1) ω)) μ := by
  obtain ⟨C, hC⟩ := hWB
  have hGi : Integrable (fun ω => F (Y k ω) (Y (k + 1) ω)) μ := by
    refine (memLp_top_of_bound (hY.stronglyMeasurable_real₂ F k).aestronglyMeasurable
      (∑ s, ∑ s', |F s s'|) (Eventually.of_forall fun ω => ?_)).integrable le_top
    rw [Real.norm_eq_abs]
    exact (single_le_sum (f := fun s' => |F (Y k ω) s'|) (fun _ _ => abs_nonneg _)
      (mem_univ _)).trans (single_le_sum (f := fun s => ∑ s', |F s s'|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ _))
  exact hGi.bdd_mul (hW.mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω⟩

omit [DecidableEq S] in
/-- The Markov property, integrated against a bounded `ℱ k`-measurable weight. -/
lemma integral_mul_markov (hY : FiniteMarkov μ ℱ Y Q) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (F : S → S → ℝ) :
    ∫ ω, W ω * F (Y k ω) (Y (k + 1) ω) ∂μ =
      ∫ ω, W ω * ∑ y', Q (Y k ω) y' * F (Y k ω) y' ∂μ := by
  obtain ⟨C, hC⟩ := hWB
  have hGm : StronglyMeasurable fun ω => F (Y k ω) (Y (k + 1) ω) :=
    (hY.stronglyMeasurable₂ (d := 1) (fun s s' => EuclideanSpace.single 0 (F s s')) k
      |>.mono (ℱ.le (k + 1)) |> fun h => by
        have := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp_stronglyMeasurable h
        simpa using this)
  have hGi : Integrable (fun ω => F (Y k ω) (Y (k + 1) ω)) μ := by
    refine (memLp_top_of_bound hGm.aestronglyMeasurable (∑ s, ∑ s', |F s s'|)
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    rw [Real.norm_eq_abs]
    exact (single_le_sum (f := fun s' => |F (Y k ω) s'|) (fun _ _ => abs_nonneg _)
      (mem_univ _)).trans (single_le_sum (f := fun s => ∑ s', |F s s'|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ _))
  have hprod : Integrable (W * fun ω => F (Y k ω) (Y (k + 1) ω)) μ :=
    hGi.bdd_mul (hW.mono (ℱ.le k)).aestronglyMeasurable ⟨C, fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω⟩
  have hc := integral_condExp (μ := μ) (ℱ.le k) (f := W * fun ω => F (Y k ω) (Y (k + 1) ω))
  change ∫ ω, (W * fun ω => F (Y k ω) (Y (k + 1) ω)) ω ∂μ = _
  rw [← hc]
  refine integral_congr_ae ?_
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hW hprod hGi, hY.markov k F] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]

/-- **The Markov step.** `E[W 1{Y_{k+1} = y'}] = Σ_y Q y y' E[W 1{Y_k = y}]` for bounded
`ℱ k`-measurable `W`. -/
lemma integral_indicator_succ (hY : FiniteMarkov μ ℱ Y Q) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (y' : S) :
    ∫ ω, {ω | Y (k + 1) ω = y'}.indicator W ω ∂μ =
      ∑ y, Q y y' * ∫ ω, {ω | Y k ω = y}.indicator W ω ∂μ := by
  set F0 : S → S → ℝ := fun _ y'' => if y'' = y' then 1 else 0 with hF0
  have e1 : ∀ ω, {ω | Y (k + 1) ω = y'}.indicator W ω = W ω * F0 (Y k ω) (Y (k + 1) ω) :=
    fun ω => by
      simp only [hF0, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp
  rw [show (fun ω => {ω | Y (k + 1) ω = y'}.indicator W ω) =
    fun ω => W ω * F0 (Y k ω) (Y (k + 1) ω) from funext e1, integral_mul_markov hY hW hWB F0]
  have e2 : ∀ ω, W ω * ∑ y'', Q (Y k ω) y'' * F0 (Y k ω) y'' =
      ∑ y, Q y y' * {ω | Y k ω = y}.indicator W ω := fun ω => by
    simp only [hF0, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
    rw [sum_eq_single (Y k ω)]
    · simp [mul_comm]
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  rw [show (fun ω => W ω * ∑ y'', Q (Y k ω) y'' * F0 (Y k ω) y'') =
    fun ω => ∑ y, Q y y' * {ω | Y k ω = y}.indicator W ω from funext e2]
  rw [integral_finset_sum _ fun y _ => (integrable_indicator_of_bdd hY hW hWB y).const_mul _]
  exact sum_congr rfl fun y _ => integral_const_mul _ _

/-! #### The trace recursions -/

variable {p : ℕ} {z : ℕ → Ω → E p} {c : S → ℝ} {φ : S → E p}

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] in
lemma coord_stronglyMeasurable (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (k : ℕ) (a : Fin p) :
    StronglyMeasurable[ℱ k] fun ω => z k ω a :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp_stronglyMeasurable (hz k)

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] in
lemma coord_bdd (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C) (k : ℕ) (a : Fin p) :
    ∃ C, ∀ ω, |z k ω a| ≤ C := by
  obtain ⟨C, hC⟩ := hzB k
  exact ⟨C, fun ω => by rw [← Real.norm_eq_abs]; exact (PiLp.norm_apply_le _ a).trans (hC ω)⟩

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] in
lemma coord_mul_bdd (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C) (k : ℕ) (a b : Fin p) :
    ∃ C, ∀ ω, |z k ω a * z k ω b| ≤ C := by
  obtain ⟨C, hC⟩ := coord_bdd hzB k a
  obtain ⟨D, hD⟩ := coord_bdd hzB k b
  exact ⟨C * D, fun ω => by
    rw [abs_mul]; exact mul_le_mul (hC ω) (hD ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))⟩

/-- The law: `P(Y_{k+1} = y') = Σ_y Q y y' P(Y_k = y)`. -/
lemma lawAt_succ (hY : FiniteMarkov μ ℱ Y Q) (k : ℕ) (y' : S) :
    momAt μ Y (fun _ _ => 1) (k + 1) y' = ∑ y, Q y y' * momAt μ Y (fun _ _ => 1) k y :=
  integral_indicator_succ hY (k := k) stronglyMeasurable_const ⟨1, fun _ => by simp⟩ y'

/-- **First moments.** `m₁ (k+1) a = L m₁ k a + φ(·)_a P(Y_{k+1} = ·)`. -/
lemma mom1_succ (hY : FiniteMarkov μ ℱ Y Q) (hz : ∀ k, StronglyMeasurable[ℱ k] (z k))
    (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω)) (k : ℕ)
    (a : Fin p) (y' : S) :
    momAt μ Y (fun k ω => z k ω a) (k + 1) y' =
      transfer Q c (momAt μ Y (fun k ω => z k ω a) k) y'
        + φ y' a * momAt μ Y (fun _ _ => 1) (k + 1) y' := by
  have e : ∀ ω, {ω | Y (k + 1) ω = y'}.indicator (fun ω => z (k + 1) ω a) ω =
      c y' * {ω | Y (k + 1) ω = y'}.indicator (fun ω => z k ω a) ω
        + φ y' a * {ω | Y (k + 1) ω = y'}.indicator (fun _ => (1 : ℝ)) ω := fun ω => by
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · rw [hzrec k ω, h]; simp
    · simp
  have i1 := integrable_indicator_of_bdd hY (coord_stronglyMeasurable hz k a) (coord_bdd hzB k a) y'
    (j := k + 1)
  have i2 := integrable_indicator_of_bdd hY (k := k) (j := k + 1) (W := fun _ => (1 : ℝ))
    stronglyMeasurable_const ⟨1, fun _ => by simp⟩ y'
  unfold momAt
  rw [show (fun ω => {ω | Y (k + 1) ω = y'}.indicator (fun ω => z (k + 1) ω a) ω) = _ from funext e,
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator_succ hY (coord_stronglyMeasurable hz k a) (coord_bdd hzB k a) y']
  rfl

/-- **Second moments.** `m₂ (k+1) a b = L_{c²} m₂ k a b + φ_b L m₁ k a + φ_a L m₁ k b
+ φ_a φ_b P(Y_{k+1} = ·)`. -/
lemma mom2_succ (hY : FiniteMarkov μ ℱ Y Q) (hz : ∀ k, StronglyMeasurable[ℱ k] (z k))
    (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω)) (k : ℕ)
    (a b : Fin p) (y' : S) :
    momAt μ Y (fun k ω => z k ω a * z k ω b) (k + 1) y' =
      transfer Q (fun y => c y ^ 2) (momAt μ Y (fun k ω => z k ω a * z k ω b) k) y'
        + φ y' b * transfer Q c (momAt μ Y (fun k ω => z k ω a) k) y'
        + φ y' a * transfer Q c (momAt μ Y (fun k ω => z k ω b) k) y'
        + φ y' a * φ y' b * momAt μ Y (fun _ _ => 1) (k + 1) y' := by
  set I : (Ω → ℝ) → Ω → ℝ := fun W => {ω | Y (k + 1) ω = y'}.indicator W with hI
  have e : ∀ ω, I (fun ω => z (k + 1) ω a * z (k + 1) ω b) ω =
      c y' ^ 2 * I (fun ω => z k ω a * z k ω b) ω + (φ y' b * c y') * I (fun ω => z k ω a) ω
        + (φ y' a * c y') * I (fun ω => z k ω b) ω + φ y' a * φ y' b * I (fun _ => 1) ω :=
    fun ω => by
      simp only [hI, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs with h
      · rw [hzrec k ω, h]; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      · simp
  have sa := coord_stronglyMeasurable hz k a
  have sb := coord_stronglyMeasurable hz k b
  have sab : StronglyMeasurable[ℱ k] fun ω => z k ω a * z k ω b := sa.mul sb
  have i1 := integrable_indicator_of_bdd hY sab (coord_mul_bdd hzB k a b) y' (j := k + 1)
  have i2 := integrable_indicator_of_bdd hY sa (coord_bdd hzB k a) y' (j := k + 1)
  have i3 := integrable_indicator_of_bdd hY sb (coord_bdd hzB k b) y' (j := k + 1)
  have i4 := integrable_indicator_of_bdd hY (k := k) (j := k + 1) (W := fun _ => (1 : ℝ))
    stronglyMeasurable_const ⟨1, fun _ => by simp⟩ y'
  simp only [hI] at e
  unfold momAt
  rw [show (fun ω => {ω | Y (k + 1) ω = y'}.indicator (fun ω => z (k + 1) ω a * z (k + 1) ω b) ω)
    = _ from funext e]
  have j1 := i1.const_mul (c y' ^ 2)
  have j2 := i2.const_mul (φ y' b * c y')
  have j3 := i3.const_mul (φ y' a * c y')
  have j4 := i4.const_mul (φ y' a * φ y' b)
  rw [integral_add, integral_add, integral_add]
  rotate_left
  · exact j1
  · exact j2
  · exact j1.add j2
  · exact j3
  · exact (j1.add j2).add j3
  · exact j4
  simp only [integral_const_mul]
  rw [integral_indicator_succ hY sab (coord_mul_bdd hzB k a b) y',
    integral_indicator_succ hY sa (coord_bdd hzB k a) y',
    integral_indicator_succ hY sb (coord_bdd hzB k b) y']
  simp only [transfer]
  ring

/-! #### Convergence -/

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] in
lemma tendsto_transfer {x : ℕ → S → ℝ} {xl : S → ℝ} [Fintype S]
    (hx : ∀ y, Tendsto (fun k => x k y) atTop (𝓝 (xl y))) (y' : S) :
    Tendsto (fun k => transfer Q c (x k) y') atTop (𝓝 (transfer Q c xl y')) := by
  unfold transfer
  exact (tendsto_finset_sum _ fun y _ => (hx y).const_mul (Q y y')).const_mul (c y')

/-- **The trace moments converge.** If the law of `Y_k` converges to `ν` and
`Σ_{y'} Q y y' |c y'| ≤ ρ < 1` with `|c| ≤ 1`, the first and second trace moments converge to
the solutions of the stationary moment equations
`m₁ a = L m₁ a + φ_a ν` and `m₂ a b = L_{c²} m₂ a b + φ_b L m₁ a + φ_a L m₁ b + φ_a φ_b ν`. -/
theorem tendsto_trace_moments (hY : FiniteMarkov μ ℱ Y Q) (hQ : ∀ y y', 0 ≤ Q y y') {ρ : ℝ}
    (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc1 : ∀ y, |c y| ≤ 1)
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω)) {ν : S → ℝ}
    (hlaw : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y))) :
    ∃ (m₁ : Fin p → S → ℝ) (m₂ : Fin p → Fin p → S → ℝ),
      (∀ a y', m₁ a y' = transfer Q c (m₁ a) y' + φ y' a * ν y') ∧
      (∀ a b y', m₂ a b y' = transfer Q (fun y => c y ^ 2) (m₂ a b) y'
        + φ y' b * transfer Q c (m₁ a) y' + φ y' a * transfer Q c (m₁ b) y'
        + φ y' a * φ y' b * ν y') ∧
      (∀ a y, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a) k y) atTop (𝓝 (m₁ a y))) ∧
      (∀ a b y, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a * z k ω b) k y) atTop
        (𝓝 (m₂ a b y))) := by
  have hlaw1 : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) (k + 1) y) atTop (𝓝 (ν y)) :=
    fun y => (hlaw y).comp (tendsto_add_atTop_nat 1)
  have h1 : ∀ a, ∃ xl : S → ℝ, (∀ y', xl y' = transfer Q c xl y' + φ y' a * ν y') ∧
      ∀ y, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a) k y) atTop (𝓝 (xl y)) := fun a =>
    tendsto_affine_transfer hQ hρ hρ0 hρ1 (mom1_succ hY hz hzB hzrec · a)
      fun y => (hlaw1 y).const_mul (φ y a)
  choose m₁ hm₁ ht₁ using h1
  have hρ2 : ∀ y, ∑ y', Q y y' * |c y' ^ 2| ≤ ρ := fun y => by
    refine le_trans (sum_le_sum fun y' _ => ?_) (hρ y)
    refine mul_le_mul_of_nonneg_left ?_ (hQ y y')
    rw [abs_pow, sq]
    exact mul_le_of_le_one_left (abs_nonneg _) (hc1 y')
  have h2 : ∀ a b, ∃ xl : S → ℝ, (∀ y', xl y' = transfer Q (fun y => c y ^ 2) xl y'
      + (φ y' b * transfer Q c (m₁ a) y' + φ y' a * transfer Q c (m₁ b) y'
        + φ y' a * φ y' b * ν y')) ∧
      ∀ y, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a * z k ω b) k y) atTop
        (𝓝 (xl y)) := fun a b =>
    tendsto_affine_transfer hQ hρ2 hρ0 hρ1 (fun k y' => by
      rw [mom2_succ hY hz hzB hzrec k a b y']; ring)
      fun y => (((tendsto_transfer (ht₁ a) y).const_mul (φ y b)).add
        ((tendsto_transfer (ht₁ b) y).const_mul (φ y a))).add ((hlaw1 y).const_mul _)
  choose m₂ hm₂ ht₂ using h2
  exact ⟨m₁, m₂, hm₁, fun a b y' => by rw [hm₂ a b y']; ring, ht₁, ht₂⟩

/-! #### The covariance of trace-driven increments -/

omit [DecidableEq S] in
/-- `E[W g(Y_k)] = Σ_y g y E[W 1{Y_k = y}]`. -/
lemma integral_mul_comp_eq_sum (hY : FiniteMarkov μ ℱ Y Q) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (g : S → ℝ) :
    ∫ ω, W ω * g (Y k ω) ∂μ = ∑ y, g y * ∫ ω, {ω | Y k ω = y}.indicator W ω ∂μ := by
  have e : ∀ ω, W ω * g (Y k ω) = ∑ y, g y * {ω | Y k ω = y}.indicator W ω := fun ω => by
    rw [sum_eq_single (Y k ω)]
    · simp [mul_comm]
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  rw [show (fun ω => W ω * g (Y k ω)) = fun ω => ∑ y, g y * {ω | Y k ω = y}.indicator W ω
    from funext e]
  rw [integral_finset_sum _ fun y _ => (integrable_indicator_of_bdd hY hW hWB y).const_mul _]
  exact sum_congr rfl fun y _ => integral_const_mul _ _

omit [DecidableEq S] in
/-- `E[W F(Y_k, Y_{k+1})] = Σ_y (Σ_{y'} Q y y' F y y') E[W 1{Y_k = y}]`. -/
lemma integral_mul_next_eq_sum (hY : FiniteMarkov μ ℱ Y Q) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) (F : S → S → ℝ) :
    ∫ ω, W ω * F (Y k ω) (Y (k + 1) ω) ∂μ =
      ∑ y, (∑ y', Q y y' * F y y') * ∫ ω, {ω | Y k ω = y}.indicator W ω ∂μ := by
  rw [integral_mul_markov hY hW hWB F]
  exact integral_mul_comp_eq_sum hY hW hWB (fun y => ∑ y', Q y y' * F y y')

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] in
lemma tendsto_euclid_of_coord {ι : Type*} [Fintype ι] {f : ℕ → EuclideanSpace ℝ ι}
    {L : EuclideanSpace ℝ ι} (h : ∀ i, Tendsto (fun k => f k i) atTop (𝓝 (L i))) :
    Tendsto f atTop (𝓝 L) := by
  have e := (EuclideanSpace.equiv ι ℝ).symm.continuous.tendsto (EuclideanSpace.equiv ι ℝ L)
  have h2 : Tendsto (fun k => EuclideanSpace.equiv ι ℝ (f k)) atTop
      (𝓝 (EuclideanSpace.equiv ι ℝ L)) := tendsto_pi_nhds.mpr h
  simpa using e.comp h2

/-- The limit covariance of `G(Y_k, Y_{k+1}) z_k + g(Y_k, Y_{k+1})`, from the stationary
moments: with `G j i y y' = (G y y' e_i)_j`,
`Γ_{jl} = Σ_y [Σ_{i,i'} m₂ i i' y Σ_{y'} Q G_{ji} G_{li'} + Σ_i m₁ i y Σ_{y'} Q (G_{ji} g_l
+ g_j G_{li}) + ν y Σ_{y'} Q g_j g_l]`. -/
noncomputable def traceGamma {d : ℕ} (Q : S → S → ℝ) (Gm : S → S → E p →L[ℝ] E d)
    (g : S → S → E d) (ν : S → ℝ) (m₁ : Fin p → S → ℝ) (m₂ : Fin p → Fin p → S → ℝ) : Mat d :=
  fun jl => ∑ i, ∑ i', ∑ y, (∑ y', Q y y' * (Gm y y' (EuclideanSpace.single i 1) jl.1
        * Gm y y' (EuclideanSpace.single i' 1) jl.2)) * m₂ i i' y
    + ∑ i, ∑ y, (∑ y', Q y y' * (Gm y y' (EuclideanSpace.single i 1) jl.1 * g y y' jl.2
        + g y y' jl.1 * Gm y y' (EuclideanSpace.single i 1) jl.2)) * m₁ i y
    + ∑ y, (∑ y', Q y y' * (g y y' jl.1 * g y y' jl.2)) * ν y

/-- **The covariance of trace-driven increments converges.** Under the hypotheses of
`tendsto_trace_moments`, `E[N_k N_kᵀ] → traceGamma` for `N_k = G(Y_k, Y_{k+1}) z_k
+ g(Y_k, Y_{k+1})`, with `(m₁, m₂)` the stationary moments. -/
theorem tendsto_secondMoment_trace_affine {d : ℕ} (hY : FiniteMarkov μ ℱ Y Q)
    (hQ : ∀ y y', 0 ≤ Q y y') {ρ : ℝ} (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hc1 : ∀ y, |c y| ≤ 1) (hz : ∀ k, StronglyMeasurable[ℱ k] (z k))
    (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω)) {ν : S → ℝ}
    (hlaw : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y)))
    (Gm : S → S → E p →L[ℝ] E d) (g : S → S → E d) :
    ∃ (m₁ : Fin p → S → ℝ) (m₂ : Fin p → Fin p → S → ℝ),
      (∀ a y', m₁ a y' = transfer Q c (m₁ a) y' + φ y' a * ν y') ∧
      (∀ a b y', m₂ a b y' = transfer Q (fun y => c y ^ 2) (m₂ a b) y'
        + φ y' b * transfer Q c (m₁ a) y' + φ y' a * transfer Q c (m₁ b) y'
        + φ y' a * φ y' b * ν y') ∧
      Tendsto (fun k => secondMoment μ fun ω => Gm (Y k ω) (Y (k + 1) ω) (z k ω)
        + g (Y k ω) (Y (k + 1) ω)) atTop (𝓝 (traceGamma Q Gm g ν m₁ m₂)) := by
  obtain ⟨m₁, m₂, hm₁, hm₂, ht₁, ht₂⟩ :=
    tendsto_trace_moments hY hQ hρ hρ0 hρ1 hc1 hz hzB hzrec hlaw
  refine ⟨m₁, m₂, hm₁, hm₂, ?_⟩
  set G : Fin d → Fin p → S → S → ℝ := fun j i y y' => Gm y y' (EuclideanSpace.single i 1) j
    with hG
  -- the increment in coordinates
  have hcoord : ∀ k ω j, (Gm (Y k ω) (Y (k + 1) ω) (z k ω) + g (Y k ω) (Y (k + 1) ω)) j =
      ∑ i, z k ω i * G j i (Y k ω) (Y (k + 1) ω) + g (Y k ω) (Y (k + 1) ω) j := fun k ω j => by
    rw [PiLp.add_apply, clm_apply_eq_sum]
  -- integrability of the increment
  have hmem : ∀ k, MemLp (fun ω => Gm (Y k ω) (Y (k + 1) ω) (z k ω)
      + g (Y k ω) (Y (k + 1) ω)) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hzB k
    have h1 : Measurable[ℱ (k + 1)] (Y k) := (hY.adapted k).mono (ℱ.mono (Nat.le_succ k)) le_rfl
    have hL : StronglyMeasurable[ℱ (k + 1)] fun ω => Gm (Y k ω) (Y (k + 1) ω) :=
      (StronglyMeasurable.of_discrete (f := Function.uncurry Gm)).comp_measurable
        (h1.prodMk (hY.adapted (k + 1)))
    have hsm : StronglyMeasurable[ℱ (k + 1)] fun ω => Gm (Y k ω) (Y (k + 1) ω) (z k ω)
        + g (Y k ω) (Y (k + 1) ω) :=
      (stronglyMeasurable_clm_apply (m := ℱ (k + 1)) hL ((hz k).mono (ℱ.mono (Nat.le_succ k)))).add
        (hY.stronglyMeasurable₂ g k)
    refine memLp_of_finite (hsm.mono (ℱ.le (k + 1))).aestronglyMeasurable
      (C := (∑ s, ∑ s', ‖Gm s s'‖) * C + ∑ s, ∑ s', ‖g s s'‖) fun ω => ?_
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_le_sum_sum_norm g _ _))
    exact ((Gm _ _).le_opNorm _).trans (mul_le_mul (norm_le_sum_sum_gen Gm _ _) (hC ω)
      (norm_nonneg _) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _))
  -- each entry is a finite sum of moments
  have hentry : ∀ k (jl : Fin d × Fin d), secondMoment μ (fun ω => Gm (Y k ω) (Y (k + 1) ω) (z k ω)
      + g (Y k ω) (Y (k + 1) ω)) jl =
      ∑ i, ∑ i', ∑ y, (∑ y', Q y y' * (G jl.1 i y y' * G jl.2 i' y y'))
          * momAt μ Y (fun k ω => z k ω i * z k ω i') k y
        + ∑ i, ∑ y, (∑ y', Q y y' * (G jl.1 i y y' * g y y' jl.2 + g y y' jl.1 * G jl.2 i y y'))
          * momAt μ Y (fun k ω => z k ω i) k y
        + ∑ y, (∑ y', Q y y' * (g y y' jl.1 * g y y' jl.2)) * momAt μ Y (fun _ _ => 1) k y := by
    intro k jl
    rw [secondMoment, crossMoment_apply (hmem k) (hmem k)]
    simp only [hcoord]
    have sa := coord_stronglyMeasurable hz k
    have sab : ∀ i i', StronglyMeasurable[ℱ k] fun ω => z k ω i * z k ω i' :=
      fun i i' => (sa i).mul (sa i')
    set FA : Fin p → Fin p → S → S → ℝ := fun i i' y y' => G jl.1 i y y' * G jl.2 i' y y'
      with hFA
    set FB : Fin p → S → S → ℝ := fun i y y' => G jl.1 i y y' * g y y' jl.2
      + g y y' jl.1 * G jl.2 i y y' with hFB
    set FC : S → S → ℝ := fun y y' => g y y' jl.1 * g y y' jl.2 with hFC
    have e : ∀ ω, (∑ i, z k ω i * G jl.1 i (Y k ω) (Y (k + 1) ω) + g (Y k ω) (Y (k + 1) ω) jl.1)
        * (∑ i, z k ω i * G jl.2 i (Y k ω) (Y (k + 1) ω) + g (Y k ω) (Y (k + 1) ω) jl.2) =
        ∑ i, ∑ i', (z k ω i * z k ω i') * FA i i' (Y k ω) (Y (k + 1) ω)
          + ∑ i, z k ω i * FB i (Y k ω) (Y (k + 1) ω)
          + (fun _ => (1 : ℝ)) ω * FC (Y k ω) (Y (k + 1) ω) := fun ω => by
      simp only [hFA, hFB, hFC, one_mul]
      have hAA : (∑ i, z k ω i * G jl.1 i (Y k ω) (Y (k + 1) ω))
          * (∑ i, z k ω i * G jl.2 i (Y k ω) (Y (k + 1) ω)) =
          ∑ i, ∑ i', (z k ω i * z k ω i')
            * (G jl.1 i (Y k ω) (Y (k + 1) ω) * G jl.2 i' (Y k ω) (Y (k + 1) ω)) := by
        rw [sum_mul_sum]
        exact sum_congr rfl fun i _ => sum_congr rfl fun i' _ => by ring
      have h1 : (∑ i, z k ω i * G jl.1 i (Y k ω) (Y (k + 1) ω)) * g (Y k ω) (Y (k + 1) ω) jl.2
          + g (Y k ω) (Y (k + 1) ω) jl.1 * ∑ i, z k ω i * G jl.2 i (Y k ω) (Y (k + 1) ω) =
          ∑ i, z k ω i * (G jl.1 i (Y k ω) (Y (k + 1) ω) * g (Y k ω) (Y (k + 1) ω) jl.2
            + g (Y k ω) (Y (k + 1) ω) jl.1 * G jl.2 i (Y k ω) (Y (k + 1) ω)) := by
        rw [sum_mul, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
      linear_combination hAA + h1
    have iA : Integrable (fun ω => ∑ i, ∑ i', (z k ω i * z k ω i')
        * FA i i' (Y k ω) (Y (k + 1) ω)) μ :=
      integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun i' _ =>
        integrable_mul_next hY (sab i i') (coord_mul_bdd hzB k i i') (FA i i')
    have iB : Integrable (fun ω => ∑ i, z k ω i * FB i (Y k ω) (Y (k + 1) ω)) μ :=
      integrable_finset_sum _ fun i _ => integrable_mul_next hY (sa i) (coord_bdd hzB k i) (FB i)
    have iC : Integrable (fun ω => (fun _ => (1 : ℝ)) ω * FC (Y k ω) (Y (k + 1) ω)) μ :=
      integrable_mul_next hY stronglyMeasurable_const ⟨1, fun _ => by simp⟩ FC
    have iAB : Integrable (fun ω => ∑ i, ∑ i', (z k ω i * z k ω i')
        * FA i i' (Y k ω) (Y (k + 1) ω) + ∑ i, z k ω i * FB i (Y k ω) (Y (k + 1) ω)) μ :=
      iA.add iB
    rw [integral_congr_ae (Eventually.of_forall e), integral_add iAB iC,
      integral_add iA iB, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun i' _ =>
        integrable_mul_next hY (sab i i') (coord_mul_bdd hzB k i i') (FA i i'),
      integral_finset_sum _ fun i _ => integrable_mul_next hY (sa i) (coord_bdd hzB k i) (FB i),
      integral_mul_next_eq_sum hY stronglyMeasurable_const ⟨1, fun _ => by simp⟩ FC]
    congr 2
    · refine sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun i' _ =>
        integrable_mul_next hY (sab i i') (coord_mul_bdd hzB k i i') (FA i i')]
      exact sum_congr rfl fun i' _ =>
        integral_mul_next_eq_sum hY (sab i i') (coord_mul_bdd hzB k i i') (FA i i')
    · exact sum_congr rfl fun i _ =>
        integral_mul_next_eq_sum hY (sa i) (coord_bdd hzB k i) (FB i)
  refine tendsto_euclid_of_coord fun jl => ?_
  simp only [hentry]
  exact ((tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun i' _ =>
      tendsto_finset_sum _ fun y _ => (ht₂ i i' y).const_mul _).add
    (tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun y _ => (ht₁ i y).const_mul _)).add
    (tendsto_finset_sum _ fun y _ => (hlaw y).const_mul _)

/-! #### Corollary 4.5 without the covariance hypothesis -/

omit [IsProbabilityMeasure μ] [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- The trace-noise martingale increment is affine in the trace:
`f k + H (k+1) - H k = G(Y_k, Y_{k+1}) z_k + g(Y_k, Y_{k+1})` with
`G y y' = F y y' + c y' U y' - U y` and `g y y' = e y y' + U y' φ y' + ĥ y' - ĥ y`. -/
lemma traceMart_eq_affine {d : ℕ} (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω))
    (Fm : S → S → E p →L[ℝ] E d) (e : S → S → E d) (U : S → E p →L[ℝ] E d) (hh : S → E d)
    (k : ℕ) (ω : Ω) :
    traceNoise Fm e Y z k ω + tracePoisson U hh Y z (k + 1) ω - tracePoisson U hh Y z k ω =
      (Fm (Y k ω) (Y (k + 1) ω) + c (Y (k + 1) ω) • U (Y (k + 1) ω) - U (Y k ω)) (z k ω)
        + (e (Y k ω) (Y (k + 1) ω) + U (Y (k + 1) ω) (φ (Y (k + 1) ω)) + hh (Y (k + 1) ω)
          - hh (Y k ω)) := by
  simp only [traceNoise, tracePoisson, hzrec k ω, map_add, map_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  abel

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- `E‖g‖² ≤ 2a² E‖x‖² + 2b²` when `‖g‖ ≤ a‖x‖ + b`. -/
lemma integral_sq_le_of_affine {d q : ℕ} {g : Ω → E d} {x : Ω → E q} {a b : ℝ}
    (hg : MemLp g 2 μ) (hx : MemLp x 2 μ) (hgx : ∀ ω, ‖g ω‖ ≤ a * ‖x ω‖ + b) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ 2 * a ^ 2 * ∫ ω, ‖x ω‖ ^ 2 ∂μ + 2 * b ^ 2 := by
  have hpt : ∀ ω, ‖g ω‖ ^ 2 ≤ 2 * a ^ 2 * ‖x ω‖ ^ 2 + 2 * b ^ 2 := fun ω => by
    have h0 : 0 ≤ ‖g ω‖ := norm_nonneg _
    have h1 : 0 ≤ a * ‖x ω‖ := mul_nonneg ha (norm_nonneg _)
    nlinarith [hgx ω, sq_nonneg (a * ‖x ω‖ - b)]
  have i1 : Integrable (fun ω => 2 * a ^ 2 * ‖x ω‖ ^ 2 + 2 * b ^ 2) μ :=
    ((memLp_sq_integrable hx).const_mul _).add (integrable_const _)
  refine (integral_mono (memLp_sq_integrable hg) i1 hpt).trans (le_of_eq ?_)
  rw [integral_add ((memLp_sq_integrable hx).const_mul _) (integrable_const _),
    integral_const_mul]
  simp

omit [DecidableEq S] in
/-- **Corollary 4.5 for traces with bounded second moments.** The trace-noise theorem holds when
each `z k` is bounded (with a bound that may grow with `k`) and `sup_k E‖z_k‖² < ∞`. This covers
the REINFORCE trace (`λ = 1`, reset at restarts), which is not uniformly bounded. -/
theorem tendsto_secondMoment_of_trace_noise_L2 {d : ℕ} {β : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
    (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (hY : FiniteMarkov μ ℱ Y Q) (hz : ∀ k, StronglyMeasurable[ℱ k] (z k))
    (hzk : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C) (hz2 : ∃ C₂, ∀ k, ∫ ω, ‖z k ω‖ ^ 2 ∂μ ≤ C₂)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω))
    (Fm : S → S → E p →L[ℝ] E d) (e : S → S → E d) (U : S → E p →L[ℝ] E d) (hh : S → E d)
    (hU : ∀ y, U y = ∑ y', Q y y' • (Fm y y' + c y' • U y'))
    (hhh : ∀ y, hh y = ∑ y', Q y y' • (e y y' + U y' (φ y') + hh y')) {Γ : Mat d}
    (hΓ : Tendsto (fun k => secondMoment μ (fun ω => traceNoise Fm e Y z k ω
      + tracePoisson U hh Y z (k + 1) ω - tracePoisson U hh Y z k ω)) atTop (𝓝 Γ))
    {θ : ℕ → Ω → E d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω) + β k • traceNoise Fm e Y z k ω)
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨C₂, hC₂⟩ := hz2
  obtain ⟨CU, hCU, hUle⟩ : ∃ C, 0 ≤ C ∧ ∀ s, ‖U s‖ ≤ C :=
    ⟨_, sum_nonneg fun _ _ => norm_nonneg _, norm_le_sum_gen U⟩
  obtain ⟨Ch, hCh, hhle⟩ : ∃ C, 0 ≤ C ∧ ∀ s, ‖hh s‖ ≤ C :=
    ⟨_, sum_nonneg fun _ _ => norm_nonneg _, norm_le_sum_gen hh⟩
  obtain ⟨CG, hCG, hGle⟩ : ∃ C, 0 ≤ C ∧ ∀ s s', ‖Fm s s' + c s' • U s' - U s‖ ≤ C :=
    ⟨_, sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _,
      norm_le_sum_sum_gen (fun s s' => Fm s s' + c s' • U s' - U s)⟩
  obtain ⟨Cg, hCg, hgle⟩ : ∃ C, 0 ≤ C ∧ ∀ s s', ‖e s s' + U s' (φ s') + hh s' - hh s‖ ≤ C :=
    ⟨_, sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _,
      norm_le_sum_sum_gen (fun s s' => e s s' + U s' (φ s') + hh s' - hh s)⟩
  have bH : ∀ k ω, ‖tracePoisson U hh Y z k ω‖ ≤ CU * ‖z k ω‖ + Ch := fun k ω =>
    (norm_add_le _ _).trans (add_le_add (((U (Y k ω)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hUle _) (norm_nonneg _))) (hhle _))
  have bM : ∀ k ω, ‖traceNoise Fm e Y z k ω + tracePoisson U hh Y z (k + 1) ω
      - tracePoisson U hh Y z k ω‖ ≤ CG * ‖z k ω‖ + Cg := fun k ω => by
    rw [traceMart_eq_affine hzrec Fm e U hh k ω]
    exact (norm_add_le _ _).trans (add_le_add (((Fm (Y k ω) (Y (k + 1) ω)
      + c (Y (k + 1) ω) • U (Y (k + 1) ω) - U (Y k ω)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hGle _ _) (norm_nonneg _))) (hgle _ _))
  -- measurability
  have mY : ∀ k, Measurable[ℱ k] (Y k) := hY.adapted
  have smH : ∀ k, StronglyMeasurable[ℱ k] (tracePoisson U hh Y z k) := fun k => by
    unfold tracePoisson
    exact (stronglyMeasurable_clm_apply (m := ℱ k)
      ((StronglyMeasurable.of_discrete (f := U)).comp_measurable (mY k)) (hz k)).add
      (hY.stronglyMeasurable hh k)
  have smf : ∀ k, StronglyMeasurable[ℱ (k + 1)] (traceNoise Fm e Y z k) := by
    intro k
    have h1 : Measurable[ℱ (k + 1)] (Y k) := (mY k).mono (ℱ.mono (Nat.le_succ k)) le_rfl
    have hL : StronglyMeasurable[ℱ (k + 1)] fun ω => Fm (Y k ω) (Y (k + 1) ω) :=
      (StronglyMeasurable.of_discrete (f := Function.uncurry Fm)).comp_measurable
        (h1.prodMk (mY (k + 1)))
    unfold traceNoise
    exact (stronglyMeasurable_clm_apply (m := ℱ (k + 1)) hL
      ((hz k).mono (ℱ.mono (Nat.le_succ k)))).add (hY.stronglyMeasurable₂ e k)
  have smM : ∀ k, StronglyMeasurable[ℱ (k + 1)] fun ω => traceNoise Fm e Y z k ω
      + tracePoisson U hh Y z (k + 1) ω - tracePoisson U hh Y z k ω := fun k =>
    ((smf k).add (smH (k + 1))).sub ((smH k).mono (ℱ.mono (Nat.le_succ k)))
  -- integrability at each step
  have hzL : ∀ k, MemLp (z k) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hzk k
    exact memLp_of_finite ((hz k).mono (ℱ.le k)).aestronglyMeasurable hC
  have hHL : ∀ k, MemLp (tracePoisson U hh Y z k) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hzk k
    exact memLp_of_finite ((smH k).mono (ℱ.le k)).aestronglyMeasurable (C := CU * C + Ch)
      fun ω => (bH k ω).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hC ω) hCU) _)
  have hML : ∀ k, MemLp (fun ω => traceNoise Fm e Y z k ω + tracePoisson U hh Y z (k + 1) ω
      - tracePoisson U hh Y z k ω) 2 μ := fun k => by
    obtain ⟨C, hC⟩ := hzk k
    exact memLp_of_finite ((smM k).mono (ℱ.le (k + 1))).aestronglyMeasurable (C := CG * C + Cg)
      fun ω => (bM k ω).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hC ω) hCG) _)
  -- uniform second-moment bounds
  have hHB : ∀ k, ∫ ω, ‖tracePoisson U hh Y z k ω‖ ^ 2 ∂μ ≤ 2 * CU ^ 2 * C₂ + 2 * Ch ^ 2 :=
    fun k => (integral_sq_le_of_affine (hHL k) (hzL k) (bH k) hCU hCh).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (hC₂ k) (by positivity)) _)
  have hMB : ∀ k, ∫ ω, ‖traceNoise Fm e Y z k ω + tracePoisson U hh Y z (k + 1) ω
      - tracePoisson U hh Y z k ω‖ ^ 2 ∂μ ≤ 2 * CG ^ 2 * C₂ + 2 * Cg ^ 2 :=
    fun k => (integral_sq_le_of_affine (hML k) (hzL k) (bM k) hCG hCg).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (hC₂ k) (by positivity)) _)
  refine tendsto_secondMoment_of_markov_noise hβ A hη hA ℱ
    (M := fun n ω => traceNoise Fm e Y z n.pred ω + tracePoisson U hh Y z n ω
      - tracePoisson U hh Y z n.pred ω) (h := tracePoisson U hh Y z) ?_ hθ0 hθ0L smH hHL
    ⟨_, hHB⟩ smM hML ⟨_, hMB⟩
    (fun k j => condExp_traceMart_eq_zero hY hz hzk hzrec Fm e U hh hU hhh k j) hΓ
  intro k ω
  rw [hθ k ω]
  congr 2
  simp only [Nat.pred_succ]
  abel

omit [DecidableEq S] in
/-- `E[W] = Σ_y E[W 1{Y_k = y}]`. -/
lemma integral_eq_sum_momAt (hY : FiniteMarkov μ ℱ Y Q) {k : ℕ} {W : Ω → ℝ}
    (hW : StronglyMeasurable[ℱ k] W) (hWB : ∃ C, ∀ ω, |W ω| ≤ C) :
    ∫ ω, W ω ∂μ = ∑ y, ∫ ω, {ω | Y k ω = y}.indicator W ω ∂μ := by
  have := integral_mul_comp_eq_sum hY hW hWB (fun _ => 1)
  simpa using this

/-- **Corollary 4.5 with `Γ` identified.** Linear stochastic approximation driven by trace noise
along a finite chain whose law converges to `ν`, with `Σ_{y'} Q y y' |c y'| ≤ ρ < 1`,
`|c| ≤ 1` and a bounded initial trace, satisfies Theorem 2.1 with `Γ = traceGamma`, computed
from the stationary moments of the trace. No uniform bound on the traces is assumed, so the
REINFORCE trace (`λ = 1`, reset at restarts) is covered. -/
theorem tendsto_secondMoment_of_trace_noise_stationary {d : ℕ} {β : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
    (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (hY : FiniteMarkov μ ℱ Y Q) (hQ : ∀ y y', 0 ≤ Q y y') {ρ : ℝ}
    (hρ : ∀ y, ∑ y', Q y y' * |c y'| ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc1 : ∀ y, |c y| ≤ 1)
    {ν : S → ℝ} (hlaw : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y)))
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hz0 : ∃ C, ∀ ω, ‖z 0 ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = c (Y (k + 1) ω) • z k ω + φ (Y (k + 1) ω))
    (Fm : S → S → E p →L[ℝ] E d) (e : S → S → E d) (U : S → E p →L[ℝ] E d) (hh : S → E d)
    (hU : ∀ y, U y = ∑ y', Q y y' • (Fm y y' + c y' • U y'))
    (hhh : ∀ y, hh y = ∑ y', Q y y' • (e y y' + U y' (φ y') + hh y'))
    {θ : ℕ → Ω → E d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω) + β k • traceNoise Fm e Y z k ω)
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ) :
    ∃ (m₁ : Fin p → S → ℝ) (m₂ : Fin p → Fin p → S → ℝ),
      (∀ a y', m₁ a y' = transfer Q c (m₁ a) y' + φ y' a * ν y') ∧
      (∀ a b y', m₂ a b y' = transfer Q (fun y => c y ^ 2) (m₂ a b) y'
        + φ y' b * transfer Q c (m₁ a) y' + φ y' a * transfer Q c (m₁ b) y'
        + φ y' a * φ y' b * ν y') ∧
      ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig =
          traceGamma Q (fun y y' => Fm y y' + c y' • U y' - U y)
            (fun y y' => e y y' + U y' (φ y') + hh y' - hh y) ν m₁ m₂ ∧
        Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  -- each trace is bounded: `‖z (k+1)‖ ≤ ‖z k‖ + Σ‖φ‖`
  have hzk : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C := by
    intro k
    induction k with
    | zero => exact hz0
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C + ∑ s, ‖φ s‖, fun ω => ?_⟩
      rw [hzrec k ω]
      refine (norm_add_le _ _).trans (add_le_add ?_ (norm_le_sum_gen φ _))
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hc1 _)).trans (hC ω)
  obtain ⟨m₁, m₂, hm₁, hm₂, hΓ⟩ := tendsto_secondMoment_trace_affine hY hQ hρ hρ0 hρ1 hc1 hz
    hzk hzrec hlaw (fun y y' => Fm y y' + c y' • U y' - U y)
    (fun y y' => e y y' + U y' (φ y') + hh y' - hh y)
  -- the second moments of the trace converge, hence are bounded
  obtain ⟨n₁, n₂, -, -, -, ht₂⟩ := tendsto_trace_moments hY hQ hρ hρ0 hρ1 hc1 hz hzk hzrec hlaw
  have hsq : ∀ k, ∫ ω, ‖z k ω‖ ^ 2 ∂μ =
      ∑ a, ∑ y, momAt μ Y (fun k ω => z k ω a * z k ω a) k y := fun k => by
    have e1 : ∀ ω, ‖z k ω‖ ^ 2 = ∑ a, z k ω a * z k ω a := fun ω => by
      rw [EuclideanSpace.norm_sq_eq]
      exact sum_congr rfl fun a _ => by rw [Real.norm_eq_abs, sq_abs, sq]
    have sm : ∀ a, StronglyMeasurable[ℱ k] fun ω => z k ω a * z k ω a := fun a =>
      (coord_stronglyMeasurable hz k a).mul (coord_stronglyMeasurable hz k a)
    rw [show (fun ω => ‖z k ω‖ ^ 2) = fun ω => ∑ a, z k ω a * z k ω a from funext e1,
      integral_finset_sum _ fun a _ => integrable_of_bdd (sm a) (coord_mul_bdd hzk k a a)]
    exact sum_congr rfl fun a _ => integral_eq_sum_momAt hY (sm a) (coord_mul_bdd hzk k a a)
  have hconv : Tendsto (fun k => ∫ ω, ‖z k ω‖ ^ 2 ∂μ) atTop
      (𝓝 (∑ a, ∑ y, n₂ a a y)) := by
    simp only [hsq]
    exact tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun y _ => ht₂ a a y
  obtain ⟨C₂, hC₂⟩ := hconv.bddAbove_range
  refine ⟨m₁, m₂, hm₁, hm₂, ?_⟩
  refine tendsto_secondMoment_of_trace_noise_L2 hβ A hη hA hY hz hzk
    ⟨C₂, fun k => hC₂ ⟨k, rfl⟩⟩ hzrec Fm e U hh hU hhh ?_ hθ hθ0 hθ0L
  simpa only [traceMart_eq_affine hzrec] using hΓ

end Process

end StochasticApproximation
