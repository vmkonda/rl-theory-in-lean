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

end StochasticApproximation
