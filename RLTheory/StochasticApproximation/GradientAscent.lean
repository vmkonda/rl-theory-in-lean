/-
SPDX-License-Identifier: MIT
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

import RLTheory.Defs

/-!
# Biased gradient ascent on a nonconvex objective

Pathwise convergence of gradient ascent with a biased, noisy search direction:
`θ (k + 1) = θ k + β k • (c k • (J' (θ k) + b k) + e k)`.

If `J` is bounded above and satisfies the quadratic lower bound
`J y ≥ J x + ⟪J' x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2`, the step sizes are not summable,
the noise series `∑ β k * ⟪J' (θ k), e k⟫` converges and the second-order terms are
summable, then `‖J' (θ k)‖ - ‖b k‖` is frequently below any `δ > 0`.

This is the deterministic core of the proof of convergence of actor-critic algorithms
(Konda, *Actor-Critic Algorithms*, Theorem 5.5): the bias `b k` is the error of the critic,
and the conclusion says the actor visits every neighbourhood of
`{θ | ‖∇J θ‖ ≤ ‖bias θ‖}` infinitely often.
-/

open Real Finset Filter RLTheory
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

variable {d : ℕ}

/-- A function with `L`-Lipschitz gradient satisfies the quadratic lower bound used below. -/
lemma quadratic_lower_bound_of_lipschitz {J : E d → ℝ} {J' : E d → E d} {L : NNReal}
  (hJ : ∀ x, HasGradientAt J (J' x) x) (hL : LipschitzWith L J') (x y : E d) :
  J x + ⟪J' x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 ≤ J y := by
  set v := y - x with hv
  let h : ℝ → ℝ := fun t => J (x + t • v) - t * ⟪J' x, v⟫ + L / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t, HasDerivAt h
      (⟪J' (x + t • v), v⟫ - ⟪J' x, v⟫ + L * t * ‖v‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hJt : HasDerivAt (fun t => J (x + t • v)) ⟪J' (x + t • v), v⟫ t := by
      have := (hJ (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => t * ⟪J' x, v⟫) ⟪J' x, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪J' x, v⟫
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul ((L : ℝ) / 2)).mul_const (‖v‖ ^ 2)
      convert this using 1
      push_cast
      ring
    exact (hJt.sub h2).add h3
  have hnonneg : ∀ t, 0 ≤ t →
      0 ≤ ⟪J' (x + t • v), v⟫ - ⟪J' x, v⟫ + L * t * ‖v‖ ^ 2 := by
    intro t ht
    have hlip : ‖J' (x + t • v) - J' x‖ ≤ L * (t * ‖v‖) := by
      have := hL.dist_le_mul (x + t • v) x
      simpa [dist_eq_norm, norm_smul, abs_of_nonneg ht] using this
    have hcs := abs_real_inner_le_norm (J' (x + t • v) - J' x) v
    rw [← inner_sub_left]
    nlinarith [neg_abs_le ⟪J' (x + t • v) - J' x, v⟫, norm_nonneg v,
      mul_le_mul_of_nonneg_right hlip (norm_nonneg v)]
  have hmono : MonotoneOn h (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      exact hnonneg t (le_of_lt ht)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  simp only [h, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow] at this
  rw [hv, add_sub_cancel] at this
  linarith

/-- One step of the ascent inequality. -/
lemma le_of_step {J : E d → ℝ} {J' : E d → E d} {L : ℝ}
  (hJ : ∀ x y, J x + ⟪J' x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 ≤ J y)
  {x g b e : E d} {β c c₁ δ : ℝ} (hβ : 0 ≤ β) (hc : c₁ ≤ c) (hc₁ : 0 < c₁) (hδ : 0 < δ)
  (hgb : δ ≤ ‖g‖ - ‖b‖) (hg : g = J' x) :
  J x + c₁ * δ ^ 2 * β + β * ⟪g, e⟫ - L / 2 * (β ^ 2 * ‖c • (g + b) + e‖ ^ 2) ≤
    J (x + β • (c • (g + b) + e)) := by
  have h := hJ x (x + β • (c • (g + b) + e))
  rw [add_sub_cancel_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← hg] at h
  refine le_trans ?_ h
  have hinner : ⟪g, β • (c • (g + b) + e)⟫ =
      β * (c * (‖g‖ ^ 2 + ⟪g, b⟫)) + β * ⟪g, e⟫ := by
    rw [real_inner_smul_right, inner_add_right, real_inner_smul_right, inner_add_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [hinner]
  have hcs : -(‖g‖ * ‖b‖) ≤ ⟪g, b⟫ := by
    have := abs_real_inner_le_norm g b
    linarith [neg_abs_le ⟪g, b⟫]
  have hgpos : δ ≤ ‖g‖ := by linarith [norm_nonneg b]
  have key : c₁ * δ ^ 2 ≤ c * (‖g‖ ^ 2 + ⟪g, b⟫) := by
    have h1 : δ ^ 2 ≤ ‖g‖ * (‖g‖ - ‖b‖) := by
      calc δ ^ 2 = δ * δ := sq δ
        _ ≤ ‖g‖ * (‖g‖ - ‖b‖) := mul_le_mul hgpos hgb hδ.le (norm_nonneg g)
    have h2 : ‖g‖ * (‖g‖ - ‖b‖) ≤ ‖g‖ ^ 2 + ⟪g, b⟫ := by nlinarith
    have h3 : 0 ≤ ‖g‖ ^ 2 + ⟪g, b⟫ := by nlinarith [sq_nonneg δ]
    calc c₁ * δ ^ 2 ≤ c₁ * (‖g‖ ^ 2 + ⟪g, b⟫) := by
          exact mul_le_mul_of_nonneg_left (h1.trans h2) hc₁.le
      _ ≤ c * (‖g‖ ^ 2 + ⟪g, b⟫) := mul_le_mul_of_nonneg_right hc h3
  have := mul_le_mul_of_nonneg_left key hβ
  nlinarith

/-- **Biased gradient ascent.** Along the iterates, `‖J' (θ k)‖ - ‖b k‖` is frequently
below every `δ > 0`, i.e. `liminf (‖J' (θ k)‖ - ‖b k‖) ≤ 0`. -/
theorem frequently_norm_grad_sub_norm_bias_lt
  {J : E d → ℝ} {J' : E d → E d}
  (hJbdd : BddAbove (Set.range J))
  (hJ : ∃ L, 0 ≤ L ∧ ∀ x y, J x + ⟪J' x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 ≤ J y)
  {θ : ℕ → E d} {β c : ℕ → ℝ} {b e : ℕ → E d}
  (hθ : ∀ k, θ (k + 1) = θ k + β k • (c k • (J' (θ k) + b k) + e k))
  (hβ : ∀ k, 0 ≤ β k)
  (hβsum : Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop)
  (hc : ∃ c₁, 0 < c₁ ∧ ∀ k, c₁ ≤ c k)
  (hsq : Summable fun k => β k ^ 2 * ‖c k • (J' (θ k) + b k) + e k‖ ^ 2)
  (he : ∃ l, Tendsto (fun n => ∑ k ∈ range n, β k * ⟪J' (θ k), e k⟫) atTop (𝓝 l)) :
  ∀ δ > 0, ∃ᶠ k in atTop, ‖J' (θ k)‖ - ‖b k‖ < δ := by
  intro δ hδ
  by_contra hcon
  rw [not_frequently] at hcon
  simp only [not_lt] at hcon
  obtain ⟨K, hK⟩ := eventually_atTop.mp hcon
  obtain ⟨L, hL, hJL⟩ := hJ
  obtain ⟨c₁, hc₁, hc₁le⟩ := hc
  obtain ⟨M, hM⟩ := hJbdd
  obtain ⟨l, hl⟩ := he
  set B := fun n => ∑ k ∈ range n, β k
  set S := fun n => ∑ k ∈ range n, β k * ⟪J' (θ k), e k⟫
  set Q := fun n => ∑ k ∈ range n, β k ^ 2 * ‖c k • (J' (θ k) + b k) + e k‖ ^ 2
  -- telescoped ascent inequality
  have htel : ∀ m, J (θ K) + c₁ * δ ^ 2 * (B (K + m) - B K) + (S (K + m) - S K) -
      L / 2 * (Q (K + m) - Q K) ≤ J (θ (K + m)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hstep := le_of_step hJL (x := θ (K + m)) (g := J' (θ (K + m)))
        (b := b (K + m)) (e := e (K + m)) (hβ (K + m)) (hc₁le (K + m)) hc₁ hδ
        (hK (K + m) (by omega)) rfl
      rw [← hθ] at hstep
      simp only [B, S, Q, ← add_assoc, sum_range_succ] at ih hstep ⊢
      linarith
  -- the noise partial sums are bounded below
  obtain ⟨Cs, hCs⟩ : ∃ Cs, ∀ n, Cs ≤ S n := by
    have := hl.bddBelow_range
    obtain ⟨Cs, hCs⟩ := this
    exact ⟨Cs, fun n => hCs ⟨n, rfl⟩⟩
  -- the second-order partial sums are bounded above
  have hQ : ∀ n, Q n ≤ ∑' k, β k ^ 2 * ‖c k • (J' (θ k) + b k) + e k‖ ^ 2 :=
    fun n => hsq.sum_le_tsum _ (fun k _ => by positivity)
  have hQ0 : 0 ≤ Q K := sum_nonneg fun k _ => by positivity
  -- but the step sizes diverge, so `J (θ (K + m))` is unbounded
  set T := ∑' k, β k ^ 2 * ‖c k • (J' (θ k) + b k) + e k‖ ^ 2
  have hgoal : Tendsto (fun m => c₁ * δ ^ 2 * (B (K + m) - B K)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by positivity)
    apply tendsto_atTop_add_const_right _ (-B K)
    exact hβsum.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
      fun m => ⟨m, by omega⟩)
  obtain ⟨m, hm⟩ := (hgoal.eventually_gt_atTop (M - J (θ K) - (Cs - S K) + L / 2 * T)).exists
  have h1 := htel m
  have h2 := hM ⟨θ (K + m), rfl⟩
  have h3 := hCs (K + m)
  have h4 : L / 2 * (Q (K + m) - Q K) ≤ L / 2 * T :=
    mul_le_mul_of_nonneg_left (by linarith [hQ (K + m)]) (by positivity)
  linarith

/-- If the bias is eventually at most `ε`, then `‖J' (θ k)‖` is frequently below `ε + δ`. -/
theorem frequently_norm_grad_lt_of_bias_le
  {J : E d → ℝ} {J' : E d → E d}
  (hJbdd : BddAbove (Set.range J))
  (hJ : ∃ L, 0 ≤ L ∧ ∀ x y, J x + ⟪J' x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 ≤ J y)
  {θ : ℕ → E d} {β c : ℕ → ℝ} {b e : ℕ → E d}
  (hθ : ∀ k, θ (k + 1) = θ k + β k • (c k • (J' (θ k) + b k) + e k))
  (hβ : ∀ k, 0 ≤ β k)
  (hβsum : Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop)
  (hc : ∃ c₁, 0 < c₁ ∧ ∀ k, c₁ ≤ c k)
  (hsq : Summable fun k => β k ^ 2 * ‖c k • (J' (θ k) + b k) + e k‖ ^ 2)
  (he : ∃ l, Tendsto (fun n => ∑ k ∈ range n, β k * ⟪J' (θ k), e k⟫) atTop (𝓝 l))
  {ε : ℝ} (hb : ∀ᶠ k in atTop, ‖b k‖ ≤ ε) :
  ∀ δ > 0, ∃ᶠ k in atTop, ‖J' (θ k)‖ < ε + δ := by
  intro δ hδ
  have h := frequently_norm_grad_sub_norm_bias_lt hJbdd hJ hθ hβ hβsum hc hsq he δ hδ
  exact (h.and_eventually hb).mono fun k ⟨h1, h2⟩ => by linarith

/-- With asymptotically vanishing bias, `liminf ‖J' (θ k)‖ = 0`. -/
theorem frequently_norm_grad_lt_of_tendsto_bias
  {J : E d → ℝ} {J' : E d → E d}
  (hJbdd : BddAbove (Set.range J))
  (hJ : ∃ L, 0 ≤ L ∧ ∀ x y, J x + ⟪J' x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 ≤ J y)
  {θ : ℕ → E d} {β c : ℕ → ℝ} {b e : ℕ → E d}
  (hθ : ∀ k, θ (k + 1) = θ k + β k • (c k • (J' (θ k) + b k) + e k))
  (hβ : ∀ k, 0 ≤ β k)
  (hβsum : Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop)
  (hc : ∃ c₁, 0 < c₁ ∧ ∀ k, c₁ ≤ c k)
  (hsq : Summable fun k => β k ^ 2 * ‖c k • (J' (θ k) + b k) + e k‖ ^ 2)
  (he : ∃ l, Tendsto (fun n => ∑ k ∈ range n, β k * ⟪J' (θ k), e k⟫) atTop (𝓝 l))
  (hb : Tendsto b atTop (𝓝 0)) :
  ∀ δ > 0, ∃ᶠ k in atTop, ‖J' (θ k)‖ < δ := by
  intro δ hδ
  have hb' : ∀ᶠ k in atTop, ‖b k‖ ≤ δ / 2 := by
    have := (tendsto_zero_iff_norm_tendsto_zero.mp hb).eventually (gt_mem_nhds (half_pos hδ))
    exact this.mono fun k hk => hk.le
  have h := frequently_norm_grad_lt_of_bias_le hJbdd hJ hθ hβ hβsum hc hsq he hb'
    (δ / 2) (half_pos hδ)
  exact h.mono fun k hk => by linarith

end StochasticApproximation
