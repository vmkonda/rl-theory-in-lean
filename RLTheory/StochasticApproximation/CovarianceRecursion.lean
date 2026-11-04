/-
SPDX-License-Identifier: MIT
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup

import RLTheory.Defs
import RLTheory.Data.Matrix.PosDef

/-!
# Deterministic core of the Markov-noise covariance theorem

Deterministic lemmas behind the asymptotic covariance of linear stochastic approximation
(`docs/markov-sa-covariance.md`, Section 2):

* `StepSizeRate`: the step-size condition `β (k+1)⁻¹ - β k⁻¹ → β̄` (Assumption 1.1) and its
  consequences (Lemma 2.2), including `∑ β k = ∞`.
* `bdd_of_le_contraction`, `tendsto_zero_of_le_contraction`: scalar recursions
  `y (k+1) ≤ (1 - a β k) y k + β k ε k` (the cores of Lemmas 2.6 and 2.7).
* `tendsto_zero_of_coercive_recursion`: `e (k+1) = e k - β k • L (e k) + β k • δ k` with `L`
  coercive and `δ k → 0` forces `e k → 0` (Lemma 2.7).
* `lyapOp`: the Lyapunov operator `X ↦ A X + X Aᵀ` on `d × d` matrices with the Frobenius
  inner product; it is coercive when `A` is positive definite in the asymmetric sense.
* `norm_le_of_second_moment_recursion`: the a priori bound `‖P k‖ = O(β k)` (Lemma 2.6).
* `tendsto_normalized_second_moment`: the deterministic part of Theorem 2.1, from the
  second-moment recursion to `P k / β k → Σ`; `exists_solution_of_coercive` gives `Σ`.
-/

open Filter Topology Finset Real Matrix
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

/-! ### Step sizes -/

/-- The step-size condition of Konda (2002), Assumption 7.5. -/
structure StepSizeRate (β : ℕ → ℝ) (βbar : ℝ) : Prop where
  pos : ∀ k, 0 < β k
  tendsto_zero : Tendsto β atTop (𝓝 0)
  inv_diff : Tendsto (fun k => (β (k + 1))⁻¹ - (β k)⁻¹) atTop (𝓝 βbar)
  βbar_nonneg : 0 ≤ βbar

variable {β : ℕ → ℝ} {βbar : ℝ}

lemma StepSizeRate.ratio_eq (h : StepSizeRate β βbar) (k : ℕ) :
  β k / β (k + 1) = 1 + β k * ((β (k + 1))⁻¹ - (β k)⁻¹) := by
  have h0 := (h.pos k).ne'
  have h1 := (h.pos (k + 1)).ne'
  field_simp
  ring

/-- `β (k+1) / β k → 1`. -/
lemma StepSizeRate.tendsto_ratio (h : StepSizeRate β βbar) :
  Tendsto (fun k => β (k + 1) / β k) atTop (𝓝 1) := by
  have h2 : Tendsto (fun k => β k / β (k + 1)) atTop (𝓝 1) := by
    have := (h.tendsto_zero.mul h.inv_diff).const_add 1
    simp only [zero_mul, add_zero] at this
    exact this.congr fun k => (h.ratio_eq k).symm
  have := h2.inv₀ one_ne_zero
  simp only [inv_one] at this
  refine this.congr fun k => ?_
  rw [inv_div]

/-- `|β (k+1) - β k| ≤ C β k ^ 2`. -/
lemma StepSizeRate.abs_sub_le (h : StepSizeRate β βbar) :
  ∃ C, 0 ≤ C ∧ ∀ k, |β (k + 1) - β k| ≤ C * β k ^ 2 := by
  obtain ⟨D, hD⟩ := h.inv_diff.abs.bddAbove_range
  obtain ⟨R, hR⟩ := h.tendsto_ratio.bddAbove_range
  refine ⟨max D 0 * max R 0, by positivity, fun k => ?_⟩
  have h0 := h.pos k
  have h1 := h.pos (k + 1)
  have hd : |(β (k + 1))⁻¹ - (β k)⁻¹| ≤ max D 0 := (hD ⟨k, rfl⟩).trans (le_max_left _ _)
  have hr : β (k + 1) ≤ max R 0 * β k := by
    have := (hR ⟨k, rfl⟩).trans (le_max_left R 0)
    rwa [div_le_iff₀ h0] at this
  have key : β (k + 1) - β k = -(β k * β (k + 1)) * ((β (k + 1))⁻¹ - (β k)⁻¹) := by
    field_simp
    ring
  rw [key, abs_mul, abs_neg, abs_of_pos (mul_pos h0 h1)]
  calc β k * β (k + 1) * |(β (k + 1))⁻¹ - (β k)⁻¹|
      ≤ β k * (max R 0 * β k) * max D 0 := by
        gcongr
    _ = max D 0 * max R 0 * β k ^ 2 := by ring

/-- The step sizes are not summable. -/
lemma StepSizeRate.tendsto_sum (h : StepSizeRate β βbar) :
  Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop := by
  set c := βbar + 1
  have hc : 0 < c := by linarith [h.βbar_nonneg]
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (h.inv_diff.eventually (gt_mem_nhds (show βbar < c by linarith)))
  set b := (β K)⁻¹ + c
  have hK0 : 0 < (β K)⁻¹ := inv_pos.mpr (h.pos K)
  have hb : 0 < b := by positivity
  have hinv : ∀ j : ℕ, (β (K + j))⁻¹ ≤ (β K)⁻¹ + c * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hK (K + j) (by omega)
      rw [show K + (j + 1) = K + j + 1 by ring]
      push_cast
      linarith
  have hlow : ∀ j : ℕ, b⁻¹ * (1 / ((j : ℝ) + 1)) ≤ β (K + j) := by
    intro j
    have hpos := h.pos (K + j)
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hle : (β (K + j))⁻¹ ≤ b * ((j : ℝ) + 1) := by
      calc (β (K + j))⁻¹ ≤ (β K)⁻¹ + c * j := hinv j
        _ ≤ b * ((j : ℝ) + 1) := by simp only [b]; nlinarith
    rw [show b⁻¹ * (1 / ((j : ℝ) + 1)) = (b * ((j : ℝ) + 1))⁻¹ by field_simp]
    exact (inv_le_comm₀ hpos (by positivity)).mp hle
  have harm := (Real.tendsto_sum_range_one_div_nat_succ_atTop).const_mul_atTop (inv_pos.mpr hb)
  have hcomp : ∀ n, b⁻¹ * ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ≤ ∑ k ∈ range (K + n), β k := by
    intro n
    rw [mul_sum, Finset.sum_range_add]
    have hnn : 0 ≤ ∑ k ∈ range K, β k := sum_nonneg fun k _ => (h.pos k).le
    have := sum_le_sum fun j (_ : j ∈ range n) => hlow j
    linarith
  have hmono : Monotone fun n => ∑ k ∈ range n, β k :=
    fun m n hmn => sum_le_sum_of_subset_of_nonneg (range_mono hmn) fun k _ _ => (h.pos k).le
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨n0, hn0⟩ := (harm.eventually_ge_atTop M).exists
  refine ⟨K + n0, fun n hn => ?_⟩
  exact hn0.trans ((hcomp n0).trans (hmono hn))

/-! ### Scalar recursions -/

/-- A sequence obeying `y (k+1) ≤ (1 - a β k) y k + C β k` eventually is bounded above. -/
lemma bdd_of_le_contraction {y β : ℕ → ℝ} {a C : ℝ} (ha : 0 < a)
  (hβ : ∀ k, 0 ≤ β k)
  (hrec : ∀ᶠ k in atTop, y (k + 1) ≤ (1 - a * β k) * y k + C * β k)
  (hsmall : ∀ᶠ k in atTop, a * β k ≤ 1) :
  ∃ M, ∀ k, y k ≤ M := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hrec.and hsmall)
  set Y := max (y K) (C / a)
  have htail : ∀ j, y (K + j) ≤ Y := by
    intro j
    induction j with
    | zero => exact le_max_left _ _
    | succ j ih =>
      obtain ⟨h1, h2⟩ := hK (K + j) (by omega)
      have hY : C / a ≤ Y := le_max_right _ _
      have hb := hβ (K + j)
      have hCY : C * β (K + j) ≤ a * β (K + j) * Y := by
        have := mul_le_mul_of_nonneg_left hY (mul_nonneg ha.le hb)
        have e : a * β (K + j) * (C / a) = C * β (K + j) := by field_simp; ring
        linarith
      have := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr h2)
      rw [show K + (j + 1) = K + j + 1 by ring]
      nlinarith
  refine ⟨max Y (∑ k ∈ range K, |y k|), fun k => ?_⟩
  by_cases hk : K ≤ k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact (htail j).trans (le_max_left _ _)
  · push_neg at hk
    calc y k ≤ |y k| := le_abs_self _
      _ ≤ ∑ k ∈ range K, |y k| :=
          single_le_sum (f := fun k => |y k|) (fun i _ => abs_nonneg _) (mem_range.mpr hk)
      _ ≤ _ := le_max_right _ _

/-- `u (k+1) ≤ (1 - a β k) u k + β k ε k` with `ε k → 0`, `∑ β k = ∞` and `u ≥ 0` forces
`u k → 0`. -/
lemma tendsto_zero_of_le_contraction {u β ε : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
  (hu : ∀ k, 0 ≤ u k) (hβ : ∀ k, 0 ≤ β k)
  (hβsum : Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop)
  (hε : Tendsto ε atTop (𝓝 0))
  (hrec : ∀ᶠ k in atTop, u (k + 1) ≤ (1 - a * β k) * u k + β k * ε k)
  (hsmall : ∀ᶠ k in atTop, a * β k ≤ 1) :
  Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hε' : ∀ᶠ k in atTop, ε k ≤ a * (η / 2) :=
    (hε.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < a * (η / 2)))).mono
      fun k hk => hk.le
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((hrec.and hsmall).and hε')
  set w : ℕ → ℝ := fun k => max (u k - η / 2) 0 with hw_def
  have hw : ∀ j, w (K + j) ≤ w K * exp (-(a * ∑ i ∈ range j, β (K + i))) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨⟨h1, h2⟩, h3⟩ := hK (K + j) (by omega)
      have hb := hβ (K + j)
      have step : w (K + j + 1) ≤ (1 - a * β (K + j)) * w (K + j) := by
        have e1 : u (K + j + 1) - η / 2 ≤ (1 - a * β (K + j)) * (u (K + j) - η / 2) := by
          nlinarith [mul_le_mul_of_nonneg_left h3 hb]
        have e2 : (1 - a * β (K + j)) * (u (K + j) - η / 2) ≤ (1 - a * β (K + j)) * w (K + j) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
        have e3 : 0 ≤ (1 - a * β (K + j)) * w (K + j) :=
          mul_nonneg (by linarith) (le_max_right _ _)
        exact max_le (e1.trans e2) e3
      have hexp : 1 - a * β (K + j) ≤ exp (-(a * β (K + j))) := by
        have := Real.add_one_le_exp (-(a * β (K + j)))
        linarith
      calc w (K + (j + 1)) = w (K + j + 1) := by rw [add_assoc]
        _ ≤ (1 - a * β (K + j)) * w (K + j) := step
        _ ≤ exp (-(a * β (K + j))) * (w K * exp (-(a * ∑ i ∈ range j, β (K + i)))) :=
            mul_le_mul hexp ih (le_max_right _ _) (exp_pos _).le
        _ = w K * exp (-(a * ∑ i ∈ range (j + 1), β (K + i))) := by
            rw [sum_range_succ, mul_add, neg_add, exp_add]
            ring
  -- the partial sums of the shifted step sizes diverge
  have hS : Tendsto (fun j => ∑ i ∈ range j, β (K + i)) atTop atTop := by
    have hshift : Tendsto (fun j => ∑ k ∈ range (K + j), β k) atTop atTop :=
      hβsum.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
        fun m => ⟨m, by omega⟩)
    have := tendsto_atTop_add_const_right atTop (-∑ k ∈ range K, β k) hshift
    refine this.congr fun j => ?_
    rw [Finset.sum_range_add]
    ring
  have hlim : Tendsto (fun j => w K * exp (-(a * ∑ i ∈ range j, β (K + i)))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hS.const_mul_atTop ha)
    simpa using this.const_mul (w K)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hη)))
  refine ⟨K + J, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 := (hw (J + j)).trans_lt (hJ (J + j) (by omega))
  rw [← add_assoc] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu _)]
  have := le_max_left (u (K + J + j) - η / 2) 0
  linarith

/-! ### Coercive linear recursions -/

/-- One step of a coercive recursion contracts: `‖v - b • L v‖ ≤ (1 - a b / 2) ‖v‖`. -/
lemma norm_sub_smul_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (L : V →L[ℝ] V) {a b : ℝ} (hL : ∀ v, a * ‖v‖ ^ 2 ≤ ⟪L v, v⟫) (hb : 0 ≤ b)
  (h1 : b * ‖L‖ ^ 2 ≤ a) (h2 : a / 2 * b ≤ 1) (v : V) :
  ‖v - b • L v‖ ≤ (1 - a / 2 * b) * ‖v‖ := by
  have hLv : ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
  have hm2 : ‖L v‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hLv 2
  have hx : ⟪v, L v⟫ = ⟪L v, v⟫ := real_inner_comm _ _
  have hcoer := hL v
  have hsq : ‖v - b • L v‖ ^ 2 ≤ ((1 - a / 2 * b) * ‖v‖) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb,
      hx, mul_pow]
    have t1 := mul_le_mul_of_nonneg_left hcoer (by positivity : (0 : ℝ) ≤ 2 * b)
    have t2 := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ b ^ 2)
    have t3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ b * ‖v‖ ^ 2)
    nlinarith [sq_nonneg (a * b * ‖v‖)]
  have hc : 0 ≤ (1 - a / 2 * b) * ‖v‖ := mul_nonneg (by linarith) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).mp hsq

/-- Lemma 2.7 of the write-up: a recursion driven by a coercive operator with vanishing
perturbations converges to zero. -/
theorem tendsto_zero_of_coercive_recursion {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] (L : V →L[ℝ] V) {a : ℝ} (ha : 0 < a)
  (hL : ∀ v, a * ‖v‖ ^ 2 ≤ ⟪L v, v⟫)
  {e δ : ℕ → V} (hβ : ∀ k, 0 ≤ β k) (hβ0 : Tendsto β atTop (𝓝 0))
  (hβsum : Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop)
  (hδ : Tendsto δ atTop (𝓝 0))
  (hrec : ∀ k, e (k + 1) = e k - β k • L (e k) + β k • δ k) :
  Tendsto e atTop (𝓝 0) := by
  have hsmall : ∀ᶠ k in atTop, β k * ‖L‖ ^ 2 ≤ a ∧ a / 2 * β k ≤ 1 := by
    have hpos : (0 : ℝ) < min (a / (‖L‖ ^ 2 + 1)) (2 / a) := by positivity
    refine (hβ0.eventually (gt_mem_nhds hpos)).mono fun k hk => ?_
    have hk1 := hk.trans_le (min_le_left _ _)
    have hk2 := hk.trans_le (min_le_right _ _)
    constructor
    · have : β k * (‖L‖ ^ 2 + 1) ≤ a := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖L‖ ^ 2 + 1)).mp hk1
        linarith
      nlinarith [hβ k]
    · have := (lt_div_iff₀ ha).mp hk2
      linarith
  have hrec' : ∀ᶠ k in atTop,
      ‖e (k + 1)‖ ≤ (1 - a / 2 * β k) * ‖e k‖ + β k * ‖δ k‖ := by
    refine hsmall.mono fun k ⟨h1, h2⟩ => ?_
    rw [hrec k]
    calc ‖e k - β k • L (e k) + β k • δ k‖
        ≤ ‖e k - β k • L (e k)‖ + ‖β k • δ k‖ := norm_add_le _ _
      _ ≤ (1 - a / 2 * β k) * ‖e k‖ + β k * ‖δ k‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ k)]
          gcongr
          exact norm_sub_smul_le L hL (hβ k) h1 h2 (e k)
  have := tendsto_zero_of_le_contraction (half_pos ha) (fun k => norm_nonneg (e k)) hβ hβsum
    (tendsto_zero_iff_norm_tendsto_zero.mp hδ) hrec' (hsmall.mono fun k h => h.2)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr this

/-! ### The Lyapunov operator -/

variable {d : ℕ}

/-- `d × d` matrices with the Frobenius inner product. -/
abbrev Mat (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

/-- The Lyapunov operator `X ↦ A X + X Aᵀ`. -/
noncomputable def lyapOp (A : Matrix (Fin d) (Fin d) ℝ) : Mat d →L[ℝ] Mat d :=
  LinearMap.toContinuousLinearMap
  { toFun := fun X => fun ij => ∑ k, A ij.1 k * X (k, ij.2) + ∑ k, X (ij.1, k) * A ij.2 k
    map_add' := by
      intro X Y
      funext ij
      simp [mul_add, add_mul, sum_add_distrib]
      ring
    map_smul' := by
      intro c X
      funext ij
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_add, mul_sum, mul_sum]
      congr 1 <;> exact sum_congr rfl fun _ _ => by ring }

/-- If `x ⬝ A x ≥ η |x|²` for all `x`, the Lyapunov operator is coercive with constant `2 η`. -/
theorem lyapOp_coercive (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ}
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (X : Mat d) :
  2 * η * ‖X‖ ^ 2 ≤ ⟪lyapOp A X, X⟫ := by
  simp only [lyapOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.inner_apply, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, RCLike.inner_apply,
    conj_trivial, Real.norm_eq_abs, sq_abs]
  -- apply the hypothesis to every column and every row of `X`
  have hc := sum_le_sum fun j (_ : j ∈ univ) => hA (fun i => X (i, j))
  have hr := sum_le_sum fun i (_ : i ∈ univ) => hA (fun j => X (i, j))
  simp only [dotProduct, mulVec] at hc hr
  have e1 : ∑ x, ∑ y, X (x, y) * (∑ k, A x k * X (k, y) + ∑ k, X (x, k) * A y k) =
      (∑ j, ∑ i, X (i, j) * ∑ k, A i k * X (k, j)) +
        ∑ i, ∑ j, X (i, j) * ∑ k, A j k * X (i, k) := by
    simp only [mul_add, sum_add_distrib]
    congr 1
    · rw [sum_comm]
    · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      congr 1
      exact sum_congr rfl fun k _ => by ring
  have e2 : 2 * η * ∑ x, ∑ y, X (x, y) ^ 2 =
      (∑ j, η * ∑ i, X (i, j) * X (i, j)) + ∑ i, η * ∑ j, X (i, j) * X (i, j) := by
    simp only [sq, ← mul_sum]
    rw [show ∑ j, ∑ i, X (i, j) * X (i, j) = ∑ i, ∑ j, X (i, j) * X (i, j) from sum_comm]
    ring
  rw [e1, e2]
  linarith

/-- The sandwich map `X ↦ A X Aᵀ`. -/
noncomputable def sandwich (A : Matrix (Fin d) (Fin d) ℝ) : Mat d →L[ℝ] Mat d :=
  LinearMap.toContinuousLinearMap
  { toFun := fun X => fun ij => ∑ k, ∑ l, A ij.1 k * X (k, l) * A ij.2 l
    map_add' := by
      intro X Y
      funext ij
      simp [mul_add, add_mul, sum_add_distrib]
    map_smul' := by
      intro c X
      funext ij
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by rw [mul_sum]; exact sum_congr rfl fun l _ => by ring }

/-- Shifting `A` by a multiple of the identity shifts the Lyapunov operator. -/
lemma lyapOp_sub_smul_one (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (X : Mat d) :
  lyapOp (A - c • 1) X = lyapOp A X - (2 * c) • X := by
  funext ij
  simp only [lyapOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, sub_mul, mul_sub, sum_sub_distrib, mul_ite, ite_mul, mul_one,
    mul_zero, zero_mul, sum_ite_eq, mem_univ, if_true]
  ring

/-- The quadratic-form bound for `A - c • 1` gives one for `A`. -/
lemma quadForm_of_shift (A : Matrix (Fin d) (Fin d) ℝ) {η c : ℝ}
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - c • 1) *ᵥ x)) (x : Fin d → ℝ) :
  (η + c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have := hA x
  rw [sub_mulVec, smul_mulVec_assoc, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at this
  linarith

/-- Sharper one-step bound: `‖v - b • L v‖ ≤ |1 - a b + b² ‖L‖² / 2| ‖v‖`. -/
lemma norm_sub_smul_le' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (L : V →L[ℝ] V) {a b : ℝ} (hL : ∀ v, a * ‖v‖ ^ 2 ≤ ⟪L v, v⟫) (hb : 0 ≤ b) (v : V) :
  ‖v - b • L v‖ ≤ |1 - a * b + b ^ 2 * ‖L‖ ^ 2 / 2| * ‖v‖ := by
  have hLv : ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
  have hm2 : ‖L v‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hLv 2
  have hx : ⟪v, L v⟫ = ⟪L v, v⟫ := real_inner_comm _ _
  have hcoer := hL v
  have hsq : ‖v - b • L v‖ ^ 2 ≤ ((1 - a * b + b ^ 2 * ‖L‖ ^ 2 / 2) * ‖v‖) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb,
      hx, mul_pow]
    have t1 := mul_le_mul_of_nonneg_left hcoer (by positivity : (0 : ℝ) ≤ 2 * b)
    have t2 := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ b ^ 2)
    nlinarith [sq_nonneg ((a * b - b ^ 2 * ‖L‖ ^ 2 / 2) * ‖v‖)]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs, abs_mul,
    abs_of_nonneg (norm_nonneg v)] at this

/-- A coercive operator on a finite-dimensional space is onto: the Lyapunov equation
`L Sig = Γ` has a solution. -/
lemma exists_solution_of_coercive {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (L : V →L[ℝ] V) {a : ℝ} (ha : 0 < a)
  (hL : ∀ v, a * ‖v‖ ^ 2 ≤ ⟪L v, v⟫) (Γ : V) : ∃ Sig, L Sig = Γ := by
  have hinj : Function.Injective (L : V →ₗ[ℝ] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := hL v
    simp only [ContinuousLinearMap.coe_coe] at hv
    rw [hv, inner_zero_left] at h
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  exact (LinearMap.injective_iff_surjective.mp hinj) Γ

/-! ### The second-moment recursion -/

/-- The one-step bound behind Lemma 2.6, with the coefficient computed. -/
lemma coef_le {a b s Q1 η βbar : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ha : 0 ≤ a) (hQ1 : 0 ≤ Q1)
  (hβbar : 0 ≤ βbar) (hs_lo : -1 ≤ s) (hs_hi : s ≤ βbar + 1) (hsa : s - a ≤ -(3 * η / 2))
  (hbQ : b * (Q1 + a + (βbar + 1) * Q1) ≤ η) :
  (1 + b * s) * (1 - a * b + b ^ 2 * Q1) ≤ 1 - η / 2 * b := by
  have e : (1 + b * s) * (1 - a * b + b ^ 2 * Q1) =
      1 + b * (s - a) + b ^ 2 * (Q1 - a * s) + b ^ 3 * (s * Q1) := by ring
  have t1 : b * (s - a) ≤ b * (-(3 * η / 2)) := mul_le_mul_of_nonneg_left hsa hb0
  have t2 : b ^ 2 * (Q1 - a * s) ≤ b ^ 2 * (Q1 + a) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    nlinarith
  have t3 : b ^ 3 * (s * Q1) ≤ b ^ 2 * ((βbar + 1) * Q1) := by
    have hsQ : s * Q1 ≤ (βbar + 1) * Q1 := mul_le_mul_of_nonneg_right hs_hi hQ1
    have hb3 : b ^ 3 ≤ b ^ 2 := by nlinarith [sq_nonneg b]
    have hnn : 0 ≤ (βbar + 1) * Q1 := by positivity
    calc b ^ 3 * (s * Q1) ≤ b ^ 3 * ((βbar + 1) * Q1) :=
          mul_le_mul_of_nonneg_left hsQ (by positivity)
      _ ≤ b ^ 2 * ((βbar + 1) * Q1) := mul_le_mul_of_nonneg_right hb3 hnn
  have t4 : b ^ 2 * (Q1 + a + (βbar + 1) * Q1) ≤ b * η := by
    have := mul_le_mul_of_nonneg_left hbQ hb0
    nlinarith
  rw [e]
  nlinarith

lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : √x ≤ 1 + x :=
  Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

/-- The per-step inequality of Lemma 2.6 in normalized form `y = ‖P‖ / β`. -/
lemma normalized_step {a b b' s y G C K Ks η Pn Pn' : ℝ}
  (hb : 0 < b) (hb' : 0 < b') (hb1 : b ≤ 1) (hy : 0 ≤ y) (hG : 0 ≤ G) (hC : 0 ≤ C)
  (hratio : b / b' = 1 + b * s) (hr2 : 1 + b * s ≤ 2)
  (hcoef : (1 + b * s) * (1 - a * b + b ^ 2 * (K / 2 + Ks + C)) ≤ 1 - η / 2 * b)
  (hPn : Pn = b * y)
  (hstep : Pn' ≤ (1 - a * b + b ^ 2 * K / 2) * Pn + b ^ 2 * Ks * Pn + b ^ 2 * G
    + C * b ^ 2 * (√Pn + b)) :
  Pn' / b' ≤ (1 - η / 2 * b) * y + 2 * (G + 2 * C) * b := by
  have hsq := mul_le_mul_of_nonneg_left (sqrt_le_one_add (show 0 ≤ Pn by rw [hPn]; positivity))
    (by positivity : (0 : ℝ) ≤ C * b ^ 2)
  set X := (1 - a * b + b ^ 2 * (K / 2 + Ks + C)) * y + b * (G + C + C * b) with hX
  have hbound : Pn' ≤ b * X := by
    have e1 : b * X = (1 - a * b + b ^ 2 * K / 2) * Pn + b ^ 2 * Ks * Pn + b ^ 2 * G
        + C * b ^ 2 * (1 + Pn) + C * b ^ 2 * b := by
      rw [hX, hPn]; ring
    have e2 : C * b ^ 2 * (√Pn + b) = C * b ^ 2 * √Pn + C * b ^ 2 * b := by ring
    linarith
  have hrpos : 0 ≤ 1 + b * s := by rw [← hratio]; positivity
  have hdiv : Pn' / b' = (b / b') * (Pn' / b) := by field_simp; ring
  have hXle : Pn' / b ≤ X := by rw [div_le_iff₀ hb]; linarith
  have hsplit : (1 + b * s) * X = (1 + b * s) * (1 - a * b + b ^ 2 * (K / 2 + Ks + C)) * y
      + (1 + b * s) * (b * (G + C + C * b)) := by rw [hX]; ring
  have h1 := mul_le_mul_of_nonneg_right hcoef hy
  have h2 : (1 + b * s) * (b * (G + C + C * b)) ≤ 2 * (b * (G + 2 * C)) := by
    have hCb : C * b ≤ C := by nlinarith
    exact mul_le_mul hr2 (mul_le_mul_of_nonneg_left (by linarith) hb.le) (by positivity)
      (by norm_num)
  calc Pn' / b' = (b / b') * (Pn' / b) := hdiv
    _ ≤ (1 + b * s) * X := by rw [hratio]; exact mul_le_mul_of_nonneg_left hXle hrpos
    _ ≤ (1 - η / 2 * b) * y + 2 * (b * (G + 2 * C)) := by linarith
    _ = (1 - η / 2 * b) * y + 2 * (G + 2 * C) * b := by ring

/-- Lemma 2.6 of the write-up (a priori bound): the second moments are `O(β k)`.
The recursion is `(I - β A) P (I - β A)ᵀ + β² Γ + R` written out. -/
theorem norm_le_of_second_moment_recursion (hβ : StepSizeRate β βbar)
  (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
  {P Γs R : ℕ → Mat d} {Γ : Mat d}
  (hΓ : Tendsto Γs atTop (𝓝 Γ))
  (hR : ∃ C, 0 ≤ C ∧ ∀ k, ‖R k‖ ≤ C * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k))
  (hrec : ∀ k, P (k + 1) = P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
    + β k ^ 2 • Γs k + R k) :
  ∃ M, 0 ≤ M ∧ ∀ k, ‖P k‖ ≤ M * β k := by
  obtain ⟨C, hC0, hRb⟩ := hR
  have hβb := hβ.βbar_nonneg
  obtain ⟨a, ha_def⟩ : ∃ a, a = 2 * η + βbar := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have hcoer : ∀ v, a * ‖v‖ ^ 2 ≤ ⟪lyapOp A v, v⟫ := by
    intro v
    have := lyapOp_coercive A (quadForm_of_shift A hA) v
    calc a * ‖v‖ ^ 2 = 2 * (η + βbar / 2) * ‖v‖ ^ 2 := by rw [ha_def]; ring
      _ ≤ _ := this
  obtain ⟨K, hK⟩ : ∃ K, K = ‖lyapOp A‖ ^ 2 := ⟨_, rfl⟩
  -- the `‖P‖` part of the remainder is absorbed into the sandwich term
  obtain ⟨Ks, hKs⟩ : ∃ Ks, Ks = ‖sandwich A‖ + C := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  obtain ⟨G0, hG0⟩ := hΓ.norm.bddAbove_range
  obtain ⟨G, hG_def⟩ : ∃ G, G = max G0 0 := ⟨_, rfl⟩
  have hG : ∀ k, ‖Γs k‖ ≤ G := fun k => (hG0 ⟨k, rfl⟩).trans (hG_def ▸ le_max_left _ _)
  have hGnn : 0 ≤ G := hG_def ▸ le_max_right _ _
  obtain ⟨Q1, hQ1_def⟩ : ∃ Q1, Q1 = K / 2 + Ks + C := ⟨_, rfl⟩
  have hQ1 : 0 ≤ Q1 := by rw [hQ1_def]; positivity
  obtain ⟨Q, hQ_def⟩ : ∃ Q, Q = Q1 + a + (βbar + 1) * Q1 := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := by rw [hQ_def]; positivity
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℕ → ℝ, ε = fun k => ((β (k + 1))⁻¹ - (β k)⁻¹) - βbar := ⟨_, rfl⟩
  have hε : Tendsto (fun k => |ε k|) atTop (𝓝 0) := by
    have := (hβ.inv_diff.sub_const βbar).abs
    simpa [hε_def] using this
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = min (min 1 (1 / a)) (min (η / (Q + 1)) (1 / (βbar + 1))) :=
    ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; positivity
  have hev : ∀ᶠ k in atTop, |ε k| ≤ min (η / 2) 1 ∧ β k ≤ m :=
    (hε.eventually (ge_mem_nhds (by positivity))).and
      (hβ.tendsto_zero.eventually (ge_mem_nhds hm))
  have hy0 : ∀ k, 0 ≤ ‖P k‖ / β k := fun k => div_nonneg (norm_nonneg _) (hβ.pos k).le
  have hrecy : ∀ᶠ k in atTop, ‖P (k + 1)‖ / β (k + 1) ≤
      (1 - η / 2 * β k) * (‖P k‖ / β k) + (2 * (G + 2 * C)) * β k := by
    refine hev.mono fun k ⟨h1, h2⟩ => ?_
    have hb := hβ.pos k
    have hb' := hβ.pos (k + 1)
    have hm1 : m ≤ 1 := hm_def ▸ (min_le_left _ _).trans (min_le_left _ _)
    have hma : m ≤ 1 / a := hm_def ▸ (min_le_left _ _).trans (min_le_right _ _)
    have hmQ : m ≤ η / (Q + 1) := hm_def ▸ (min_le_right _ _).trans (min_le_left _ _)
    have hmβ : m ≤ 1 / (βbar + 1) := hm_def ▸ (min_le_right _ _).trans (min_le_right _ _)
    have hb1 : β k ≤ 1 := h2.trans hm1
    have hab : a * β k ≤ 1 := by
      have := h2.trans hma
      rw [le_div_iff₀ ha0] at this
      linarith
    have hbQ : β k * (Q1 + a + (βbar + 1) * Q1) ≤ η := by
      have := h2.trans hmQ
      rw [le_div_iff₀ (by positivity)] at this
      rw [← hQ_def]
      nlinarith
    have hbβ : β k * (βbar + 1) ≤ 1 := by
      have := h2.trans hmβ
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hε1 : |ε k| ≤ η / 2 := h1.trans (min_le_left _ _)
    have hε2 : |ε k| ≤ 1 := h1.trans (min_le_right _ _)
    have hratio : β k / β (k + 1) = 1 + β k * (βbar + ε k) := by
      rw [hβ.ratio_eq k, hε_def]
      ring
    have hlo := neg_abs_le (ε k)
    have hhi := le_abs_self (ε k)
    have hs_lo : -1 ≤ βbar + ε k := by linarith
    have hs_hi : βbar + ε k ≤ βbar + 1 := by linarith
    have hsa : βbar + ε k - a ≤ -(3 * η / 2) := by rw [ha_def]; linarith
    have hcoef := coef_le hb.le hb1 ha0.le hQ1 hβb hs_lo hs_hi hsa hbQ
    rw [hQ1_def] at hcoef
    have hr2 : 1 + β k * (βbar + ε k) ≤ 2 := by nlinarith
    have hc : 0 ≤ 1 - a * β k + β k ^ 2 * K / 2 := by
      have : 0 ≤ β k ^ 2 * K / 2 := by positivity
      linarith
    have hstep : ‖P (k + 1)‖ ≤ (1 - a * β k + β k ^ 2 * K / 2) * ‖P k‖
        + β k ^ 2 * Ks * ‖P k‖ + β k ^ 2 * G + C * β k ^ 2 * (√‖P k‖ + β k) := by
      rw [hrec k]
      have n1 := norm_sub_smul_le' (lyapOp A) hcoer hb.le (P k)
      rw [← hK, abs_of_nonneg hc] at n1
      have n2 : ‖β k ^ 2 • sandwich A (P k)‖ ≤ β k ^ 2 * ‖sandwich A‖ * ‖P k‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_assoc]
        exact mul_le_mul_of_nonneg_left ((sandwich A).le_opNorm _) (sq_nonneg _)
      have e2 : β k ^ 2 * Ks * ‖P k‖ = β k ^ 2 * ‖sandwich A‖ * ‖P k‖ + C * β k ^ 2 * ‖P k‖ := by
        rw [hKs]; ring
      have e4 : C * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k) =
          C * β k ^ 2 * (√‖P k‖ + β k) + C * β k ^ 2 * ‖P k‖ := by ring
      have n3 : ‖β k ^ 2 • Γs k‖ ≤ β k ^ 2 * G := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hG k) (sq_nonneg _)
      have n4 := hRb k
      have t := norm_add_le (P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
        + β k ^ 2 • Γs k) (R k)
      have t' := norm_add_le (P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k))
        (β k ^ 2 • Γs k)
      have t'' := norm_add_le (P k - β k • lyapOp A (P k)) (β k ^ 2 • sandwich A (P k))
      linarith
    exact normalized_step hb hb' hb1 (hy0 k) hGnn hC0 hratio hr2 hcoef
      (by field_simp) hstep
  have hsmall : ∀ᶠ k in atTop, η / 2 * β k ≤ 1 := by
    refine hev.mono fun k ⟨_, h2⟩ => ?_
    have hma : m ≤ 1 / a := hm_def ▸ (min_le_left _ _).trans (min_le_right _ _)
    have := h2.trans hma
    rw [le_div_iff₀ ha0, ha_def] at this
    have e : β k * (2 * η + βbar) = 4 * (η / 2 * β k) + βbar * β k := by ring
    have hnn : 0 ≤ βbar * β k := mul_nonneg hβb (hβ.pos k).le
    have hnn' : 0 ≤ η / 2 * β k := by have := hβ.pos k; positivity
    linarith
  obtain ⟨M, hM⟩ := bdd_of_le_contraction (y := fun k => ‖P k‖ / β k) (half_pos hη)
    (fun k => (hβ.pos k).le) hrecy hsmall
  refine ⟨max M 0, le_max_right _ _, fun k => ?_⟩
  have hb := hβ.pos k
  have e : ‖P k‖ = ‖P k‖ / β k * β k := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right ((hM k).trans (le_max_left _ _)) hb.le


/-- Theorem 2.1 of the write-up, deterministic part: if the second moments follow the
recursion `P (k+1) = (I - β A) P (I - β A)ᵀ + β² Γ k + R k` (written out), with `Γ k → Γ`
and `‖R k‖ ≤ C β² (√‖P‖ + ‖P‖ + β)`, then `P k / β k → Σ`, the solution of the Lyapunov equation
`(A - β̄/2) Σ + Σ (A - β̄/2)ᵀ = Γ`. -/
theorem tendsto_normalized_second_moment (hβ : StepSizeRate β βbar)
  (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
  {P Γs R : ℕ → Mat d} {Γ Sig : Mat d}
  (hSig : lyapOp (A - (βbar / 2) • 1) Sig = Γ)
  (hΓ : Tendsto Γs atTop (𝓝 Γ))
  (hR : ∃ C, 0 ≤ C ∧ ∀ k, ‖R k‖ ≤ C * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k))
  (hrec : ∀ k, P (k + 1) = P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
    + β k ^ 2 • Γs k + R k) :
  Tendsto (fun k => (β k)⁻¹ • P k) atTop (𝓝 Sig) := by
  obtain ⟨M, hM0, hM⟩ := norm_le_of_second_moment_recursion hβ A hη hA hΓ hR hrec
  obtain ⟨C, hC0, hRb⟩ := hR
  have hLc : ∀ v, 2 * η * ‖v‖ ^ 2 ≤ ⟪lyapOp (A - (βbar / 2) • 1) v, v⟫ :=
    lyapOp_coercive _ hA
  have hLeq : ∀ X, lyapOp (A - (βbar / 2) • 1) X = lyapOp A X - βbar • X := by
    intro X
    rw [lyapOp_sub_smul_one]
    congr 2
    ring
  obtain ⟨S, hS_def⟩ : ∃ S : ℕ → Mat d, S = fun k => (β k)⁻¹ • P k := ⟨_, rfl⟩
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℕ → Mat d, δ = fun k =>
      (β k)⁻¹ • (S (k + 1) - S k) + lyapOp (A - (βbar / 2) • 1) (S k) - Γ := ⟨_, rfl⟩
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℕ → ℝ, ε = fun k => ((β (k + 1))⁻¹ - (β k)⁻¹) - βbar := ⟨_, rfl⟩
  -- the recursion for S - Σ
  have hrec_e : ∀ k, S (k + 1) - Sig = (S k - Sig) - β k • lyapOp (A - (βbar / 2) • 1)
      (S k - Sig) + β k • δ k := by
    intro k
    have hb := (hβ.pos k).ne'
    rw [hδ_def, map_sub, hSig]
    simp only [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hb, one_smul]
    abel
  -- an exact formula for the perturbation
  have hδeq : ∀ k, δ k = (ε k * (β k)⁻¹) • P k - (βbar + ε k) • lyapOp A (P k)
      + (β k / β (k + 1)) • sandwich A (P k) + ((β k / β (k + 1)) • Γs k - Γ)
      + (β k * β (k + 1))⁻¹ • R k := by
    intro k
    have hb := (hβ.pos k).ne'
    have hb' := (hβ.pos (k + 1)).ne'
    rw [hδ_def, hS_def]
    simp only
    rw [map_smul, hLeq, hrec k, hε_def]
    funext ij
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  -- each term of the perturbation tends to zero
  have hratio : Tendsto (fun k => β k / β (k + 1)) atTop (𝓝 1) := by
    have := hβ.tendsto_ratio.inv₀ one_ne_zero
    simp only [inv_one] at this
    exact this.congr fun k => by rw [inv_div]
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := hβ.inv_diff.sub_const βbar
    simpa [hε_def] using this
  set KL := ‖lyapOp A‖
  set Ks := ‖sandwich A‖
  have hbound : ∀ k, ‖δ k‖ ≤ |ε k| * M + |βbar + ε k| * KL * M * β k
      + β k / β (k + 1) * Ks * M * β k + ‖(β k / β (k + 1)) • Γs k - Γ‖
      + β k / β (k + 1) * C * (√(M * β k) + M * β k + β k) := by
    intro k
    have hb := hβ.pos k
    have hb' := hβ.pos (k + 1)
    have hr0 : 0 ≤ β k / β (k + 1) := by positivity
    have hPk := hM k
    rw [hδeq k]
    have n1 : ‖(ε k * (β k)⁻¹) • P k‖ ≤ |ε k| * M := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hb]
      calc |ε k| * (β k)⁻¹ * ‖P k‖ ≤ |ε k| * (β k)⁻¹ * (M * β k) :=
            mul_le_mul_of_nonneg_left hPk (by positivity)
        _ = |ε k| * M := by field_simp; ring
    have n2 : ‖(βbar + ε k) • lyapOp A (P k)‖ ≤ |βbar + ε k| * KL * M * β k := by
      rw [norm_smul, Real.norm_eq_abs, mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc ‖lyapOp A (P k)‖ ≤ KL * ‖P k‖ := (lyapOp A).le_opNorm _
        _ ≤ KL * (M * β k) := mul_le_mul_of_nonneg_left hPk (norm_nonneg _)
    have n3 : ‖(β k / β (k + 1)) • sandwich A (P k)‖ ≤ β k / β (k + 1) * Ks * M * β k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hr0
      calc ‖sandwich A (P k)‖ ≤ Ks * ‖P k‖ := (sandwich A).le_opNorm _
        _ ≤ Ks * (M * β k) := mul_le_mul_of_nonneg_left hPk (norm_nonneg _)
    have n5 : ‖(β k * β (k + 1))⁻¹ • R k‖ ≤ β k / β (k + 1) * C * (√(M * β k) + M * β k + β k) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hsq : √‖P k‖ ≤ √(M * β k) := Real.sqrt_le_sqrt hPk
      calc (β k * β (k + 1))⁻¹ * ‖R k‖ ≤ (β k * β (k + 1))⁻¹ * (C * β k ^ 2 * (√‖P k‖ + ‖P k‖ + β k)) :=
            mul_le_mul_of_nonneg_left (hRb k) (by positivity)
        _ = β k / β (k + 1) * C * (√‖P k‖ + ‖P k‖ + β k) := by field_simp; ring
        _ ≤ β k / β (k + 1) * C * (√(M * β k) + M * β k + β k) := by gcongr
    have t1 := norm_add_le ((ε k * (β k)⁻¹) • P k - (βbar + ε k) • lyapOp A (P k)
      + (β k / β (k + 1)) • sandwich A (P k) + ((β k / β (k + 1)) • Γs k - Γ))
      ((β k * β (k + 1))⁻¹ • R k)
    have t2 := norm_add_le ((ε k * (β k)⁻¹) • P k - (βbar + ε k) • lyapOp A (P k)
      + (β k / β (k + 1)) • sandwich A (P k)) ((β k / β (k + 1)) • Γs k - Γ)
    have t3 := norm_add_le ((ε k * (β k)⁻¹) • P k - (βbar + ε k) • lyapOp A (P k))
      ((β k / β (k + 1)) • sandwich A (P k))
    have t4 := norm_sub_le ((ε k * (β k)⁻¹) • P k) ((βbar + ε k) • lyapOp A (P k))
    linarith
  have hb0 := hβ.tendsto_zero
  have hlim : Tendsto (fun k => |ε k| * M + |βbar + ε k| * KL * M * β k
      + β k / β (k + 1) * Ks * M * β k + ‖(β k / β (k + 1)) • Γs k - Γ‖
      + β k / β (k + 1) * C * (√(M * β k) + M * β k + β k)) atTop (𝓝 0) := by
    have l1 : Tendsto (fun k => |ε k| * M) atTop (𝓝 0) := by
      simpa using hε.abs.mul_const M
    have l2 : Tendsto (fun k => |βbar + ε k| * KL * M * β k) atTop (𝓝 0) := by
      simpa using (((hε.const_add βbar).abs.mul_const KL).mul_const M).mul hb0
    have l3 : Tendsto (fun k => β k / β (k + 1) * Ks * M * β k) atTop (𝓝 0) := by
      simpa using ((hratio.mul_const Ks).mul_const M).mul hb0
    have l4 : Tendsto (fun k => ‖(β k / β (k + 1)) • Γs k - Γ‖) atTop (𝓝 0) := by
      have := ((hratio.smul hΓ).sub_const Γ).norm
      simpa using this
    have l5 : Tendsto (fun k => β k / β (k + 1) * C * (√(M * β k) + M * β k + β k)) atTop (𝓝 0) := by
      have hs : Tendsto (fun k => √(M * β k)) atTop (𝓝 0) := by
        have h := hb0.const_mul M
        rw [mul_zero] at h
        have := (Real.continuous_sqrt.tendsto 0).comp h
        simpa using this
      simpa using (hratio.mul_const C).mul ((hs.add (hb0.const_mul M)).add hb0)
    simpa using (((l1.add l2).add l3).add l4).add l5
  have hδ : Tendsto δ atTop (𝓝 0) := squeeze_zero_norm hbound hlim
  have he := tendsto_zero_of_coercive_recursion (lyapOp (A - (βbar / 2) • 1))
    (by positivity : (0 : ℝ) < 2 * η) hLc (e := fun k => S k - Sig) (fun k => (hβ.pos k).le)
    hb0 hβ.tendsto_sum hδ hrec_e
  have := tendsto_sub_nhds_zero_iff.mp he
  simpa [hS_def] using this

end StochasticApproximation
