/-
SPDX-License-Identifier: MIT
-/
import RLTheory.MarkovDecisionProcess.PolicyGradient
import RLTheory.Analysis.Normed.Lipschitz
import RLTheory.StochasticApproximation.GradientAscent

/-!
# The discounted policy gradient is Lipschitz

For a policy family whose score is bounded and Lipschitz (`PolicyFamily.Regular`), the
policy gradient `∇ J(θ) = (1 - γ)⁻¹ ∑ η_θ Q_θ ψ_θ` is Lipschitz in `θ`
(`PolicyFamily.isLip_gradJ`), so `J` satisfies the quadratic lower bound required by
the biased gradient ascent theorem (`PolicyFamily.quadratic_lower_bound_J`). The softmax
family is regular (`softmaxFamily_regular`).

The proof avoids second derivatives: the gradient is a finite sum of products of
bounded Lipschitz factors. Value functions are Lipschitz because their gradients are
bounded (`PolicyFamily.hasGradientAt_V`), and the resolvent entries `R θ s j` are
themselves value functions, for the reward that is `1` at state `j`
(`TabularMDP.V_indicatorReward`).
-/

open Real Finset Matrix StochasticMatrix RLTheory StochasticApproximation
open scoped InnerProductSpace RealInnerProductSpace

namespace ReinforcementLearning

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable {A : Type u} [Fintype A]
variable {n : ℕ}

variable (M : TabularMDP (S := S) (A := A))

section Bounds

variable {pi : S → A → ℝ}

omit [DecidableEq S] [Nonempty S] in
lemma TabularMDP.exists_abs_r_le : ∃ ρ, 0 ≤ ρ ∧ ∀ sa, |M.r sa| ≤ ρ := by
  obtain ⟨ρ, hρ⟩ := (Set.finite_range fun sa => |M.r sa|).bddAbove
  refine ⟨max ρ 0, le_max_right _ _, fun sa => (hρ ⟨sa, rfl⟩).trans (le_max_left _ _)⟩

omit [DecidableEq S] [Nonempty S] in
lemma TabularMDP.abs_stateReward_le (hpi : ∀ s, StochasticVec (pi s)) {ρ : ℝ}
  (hρ : ∀ sa, |M.r sa| ≤ ρ) (s : S) : |M.stateReward pi s| ≤ ρ := by
  calc |∑ a, pi s a * M.r (s, a)| ≤ ∑ a, |pi s a * M.r (s, a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, pi s a * ρ := sum_le_sum fun a _ => by
        rw [abs_mul, abs_of_nonneg ((hpi s).nonneg a)]
        exact mul_le_mul_of_nonneg_left (hρ _) ((hpi s).nonneg a)
    _ = ρ := by rw [← sum_mul, (hpi s).rowsum, one_mul]

lemma TabularMDP.norm_resolvent_smul_le (hpi : ∀ s, StochasticVec (pi s))
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : S → F} {B : ℝ} (hf : ∀ s, ‖f s‖ ≤ B) (s : S) :
  ‖∑ s', M.resolvent pi s s' • f s'‖ ≤ (1 - M.γ)⁻¹ * B := by
  calc ‖∑ s', M.resolvent pi s s' • f s'‖ ≤ ∑ s', ‖M.resolvent pi s s' • f s'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ s', M.resolvent pi s s' * B := sum_le_sum fun s' _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (M.resolvent_nonneg hpi s s')]
        exact mul_le_mul_of_nonneg_left (hf s') (M.resolvent_nonneg hpi s s')
    _ = (1 - M.γ)⁻¹ * B := by rw [← sum_mul, M.sum_resolvent hpi]

omit [Nonempty S] in
lemma TabularMDP.V_eq_sum (s : S) :
  M.V pi s = ∑ s', M.resolvent pi s s' • M.stateReward pi s' := rfl

lemma TabularMDP.abs_V_le (hpi : ∀ s, StochasticVec (pi s)) {ρ : ℝ}
  (hρ : ∀ sa, |M.r sa| ≤ ρ) (s : S) : |M.V pi s| ≤ (1 - M.γ)⁻¹ * ρ := by
  rw [M.V_eq_sum, ← Real.norm_eq_abs]
  exact M.norm_resolvent_smul_le hpi (fun s => by
    rw [Real.norm_eq_abs]; exact M.abs_stateReward_le hpi hρ s) s

lemma TabularMDP.abs_Q_le (hpi : ∀ s, StochasticVec (pi s)) {ρ : ℝ}
  (hρ : ∀ sa, |M.r sa| ≤ ρ) (sa : S × A) :
  |M.Q pi sa| ≤ ρ + M.γ * ((1 - M.γ)⁻¹ * ρ) := by
  have hγ := M.hγ
  have hsum : |∑ s', M.P sa s' * M.V pi s'| ≤ (1 - M.γ)⁻¹ * ρ := by
    calc |∑ s', M.P sa s' * M.V pi s'| ≤ ∑ s', |M.P sa s' * M.V pi s'| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', M.P sa s' * ((1 - M.γ)⁻¹ * ρ) := sum_le_sum fun s' _ => by
          rw [abs_mul, abs_of_nonneg ((M.hP sa).nonneg s')]
          exact mul_le_mul_of_nonneg_left (M.abs_V_le hpi hρ s') ((M.hP sa).nonneg s')
      _ = (1 - M.γ)⁻¹ * ρ := by rw [← sum_mul, (M.hP sa).rowsum, one_mul]
  calc |M.Q pi sa| ≤ |M.r sa| + |M.γ * ∑ s', M.P sa s' * M.V pi s'| := abs_add_le _ _
    _ ≤ ρ + M.γ * ((1 - M.γ)⁻¹ * ρ) := by
        rw [abs_mul, abs_of_nonneg hγ.1]
        exact add_le_add (hρ sa) (mul_le_mul_of_nonneg_left hsum hγ.1)

/-- The same MDP with a different reward. -/
def TabularMDP.withReward (r' : S × A → ℝ) : TabularMDP (S := S) (A := A) :=
  { M with r := r' }

/-- The reward that is `1` at state `j`, whatever the decision. -/
def indicatorReward (j : S) : S × A → ℝ := fun sa => if sa.1 = j then 1 else 0

omit [Nonempty S] in
/-- Resolvent entries are value functions for an indicator reward. -/
lemma TabularMDP.V_indicatorReward (hpi : ∀ s, StochasticVec (pi s)) (s j : S) :
  (M.withReward (indicatorReward j)).V pi s = M.resolvent pi s j := by
  have hr : (M.withReward (indicatorReward j)).stateReward pi =
      fun s' => if s' = j then 1 else 0 := by
    funext s'
    simp only [TabularMDP.stateReward, TabularMDP.withReward, indicatorReward]
    by_cases h : s' = j
    · simp [h, (hpi j).rowsum]
    · simp [h]
  simp only [TabularMDP.V, hr]
  rw [show (M.withReward (indicatorReward j)).resolvent pi = M.resolvent pi from rfl]
  simp [mulVec, dotProduct]

lemma TabularMDP.resolvent_le (hpi : ∀ s, StochasticVec (pi s)) (s j : S) :
  M.resolvent pi s j ≤ (1 - M.γ)⁻¹ := by
  rw [← M.sum_resolvent hpi s]
  exact single_le_sum (fun j _ => M.resolvent_nonneg hpi s j) (mem_univ j)

end Bounds

section Lipschitz

variable (pf : PolicyFamily (S := S) (A := A) n)

/-- A policy family whose score is bounded and Lipschitz, uniformly in the state and
decision. -/
structure PolicyFamily.Regular : Prop where
  score_bdd : ∃ C, 0 ≤ C ∧ ∀ θ s a, ‖pf.score θ s a‖ ≤ C
  score_lip : ∀ s a, IsLip fun θ => pf.score θ s a

variable {pf}

omit [DecidableEq S] [Nonempty S] in
omit [Fintype S] in
lemma PolicyFamily.isBdd_pi (s : S) (a : A) : IsBdd fun θ => pf.pi θ s a :=
  ⟨1, zero_le_one, fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg ((pf.stochastic θ s).nonneg a)]
    have := pf.stochastic θ s
    exact StochasticVec.le_one _ a⟩

omit [Fintype S] [DecidableEq S] [Nonempty S] in
lemma PolicyFamily.isLip_pi (hψ : ∃ C, 0 ≤ C ∧ ∀ θ s a, ‖pf.score θ s a‖ ≤ C)
  (s : S) (a : A) : IsLip fun θ => pf.pi θ s a := by
  obtain ⟨C, hC, hψ⟩ := hψ
  refine IsLip.of_hasGradientAt (fun θ => pf.hasGradientAt_pi θ s a) hC fun θ => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((pf.stochastic θ s).nonneg a)]
  have := pf.stochastic θ s
  calc pf.pi θ s a * ‖pf.score θ s a‖ ≤ 1 * C :=
        mul_le_mul (StochasticVec.le_one _ a) (hψ θ s a) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

variable (hreg : pf.Regular)
include hreg

omit [Fintype S] [DecidableEq S] [Nonempty S] in
lemma PolicyFamily.Regular.isBdd_score (s : S) (a : A) : IsBdd fun θ => pf.score θ s a := by
  obtain ⟨C, hC, hψ⟩ := hreg.score_bdd
  exact ⟨C, hC, fun θ => hψ θ s a⟩

omit hreg in
lemma PolicyFamily.isBdd_V (s : S) : IsBdd fun θ => M.V (pf.pi θ) s := by
  obtain ⟨ρ, hρ0, hρ⟩ := M.exists_abs_r_le
  have hγ : 0 < 1 - M.γ := by linarith [M.hγ.2]
  exact ⟨(1 - M.γ)⁻¹ * ρ, by positivity, fun θ => by
    rw [Real.norm_eq_abs]; exact M.abs_V_le (pf.stochastic θ) hρ s⟩

omit hreg in
lemma PolicyFamily.isBdd_Q (sa : S × A) : IsBdd fun θ => M.Q (pf.pi θ) sa := by
  obtain ⟨ρ, hρ0, hρ⟩ := M.exists_abs_r_le
  have hγ : 0 < 1 - M.γ := by linarith [M.hγ.2]
  have := M.hγ.1
  exact ⟨ρ + M.γ * ((1 - M.γ)⁻¹ * ρ), by positivity, fun θ => by
    rw [Real.norm_eq_abs]; exact M.abs_Q_le (pf.stochastic θ) hρ sa⟩

/-- Value functions are Lipschitz in the parameter. -/
lemma PolicyFamily.Regular.isLip_V (s : S) : IsLip fun θ => M.V (pf.pi θ) s := by
  obtain ⟨ρ, hρ0, hρ⟩ := M.exists_abs_r_le
  obtain ⟨C, hC, hψ⟩ := hreg.score_bdd
  have hγ : 0 < 1 - M.γ := by linarith [M.hγ.2]
  have := M.hγ.1
  set Qb := ρ + M.γ * ((1 - M.γ)⁻¹ * ρ)
  have hQb : 0 ≤ Qb := by positivity
  refine IsLip.of_hasGradientAt (fun θ => pf.hasGradientAt_V M θ s)
    (C := (1 - M.γ)⁻¹ * (Qb * C)) (by positivity) fun θ => ?_
  have hpi := pf.stochastic θ
  refine M.norm_resolvent_smul_le hpi (fun s' => ?_) s
  calc ‖∑ a, (pf.pi θ s' a * M.Q (pf.pi θ) (s', a)) • pf.score θ s' a‖
      ≤ ∑ a, ‖(pf.pi θ s' a * M.Q (pf.pi θ) (s', a)) • pf.score θ s' a‖ := norm_sum_le _ _
    _ ≤ ∑ a, pf.pi θ s' a * (Qb * C) := sum_le_sum fun a _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hpi s').nonneg a),
          mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (M.abs_Q_le hpi hρ _) (hψ θ s' a) (norm_nonneg _) hQb)
          ((hpi s').nonneg a)
    _ = Qb * C := by rw [← sum_mul, (hpi s').rowsum, one_mul]

lemma PolicyFamily.Regular.isLip_Q (sa : S × A) : IsLip fun θ => M.Q (pf.pi θ) sa := by
  have h := (IsLip.const (E := E n) (M.r sa)).add
    ((IsLip.sum univ fun s' _ => (hreg.isLip_V M s').const_smul (M.P sa s')).const_smul M.γ)
  refine h.comp_of_eq (funext fun θ => ?_)
  simp [TabularMDP.Q, smul_eq_mul]

lemma PolicyFamily.Regular.isLip_resolvent (s j : S) :
  IsLip fun θ => M.resolvent (pf.pi θ) s j :=
  (hreg.isLip_V (M.withReward (indicatorReward j)) s).comp_of_eq
    (funext fun θ => M.V_indicatorReward (pf.stochastic θ) s j)

omit hreg in
lemma PolicyFamily.isBdd_visitation (s : S) : IsBdd fun θ => M.visitation (pf.pi θ) s := by
  refine ⟨1, zero_le_one, fun θ => ?_⟩
  have h := M.stochastic_visitation (pf.stochastic θ)
  rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg s)]
  exact StochasticVec.le_one _ s

lemma PolicyFamily.Regular.isLip_visitation (s' : S) :
  IsLip fun θ => M.visitation (pf.pi θ) s' := by
  have h := (IsLip.sum univ fun s _ => (hreg.isLip_resolvent M s s').const_smul (M.p₀ s)).const_smul
    (1 - M.γ)
  refine h.comp_of_eq (funext fun θ => ?_)
  simp [TabularMDP.visitation, vecMul, dotProduct, smul_eq_mul]

lemma PolicyFamily.Regular.isLip_occupancy (sa : S × A) :
  IsLip fun θ => M.occupancy (pf.pi θ) sa :=
  (hreg.isLip_visitation M sa.1).mul (pf.isBdd_visitation M sa.1)
    (pf.isLip_pi hreg.score_bdd sa.1 sa.2) (pf.isBdd_pi sa.1 sa.2)

omit hreg in
lemma PolicyFamily.isBdd_occupancy (sa : S × A) : IsBdd fun θ => M.occupancy (pf.pi θ) sa :=
  (pf.isBdd_visitation M sa.1).mul (pf.isBdd_pi sa.1 sa.2)

/-- The policy gradient as a function of the parameter. -/
noncomputable def PolicyFamily.gradJ (pf : PolicyFamily (S := S) (A := A) n) (θ : E n) : E n :=
  (1 - M.γ)⁻¹ • ∑ sa, (M.occupancy (pf.pi θ) sa * M.Q (pf.pi θ) sa) • pf.score θ sa.1 sa.2

omit hreg in
lemma PolicyFamily.hasGradientAt_J' (θ : E n) :
  HasGradientAt (fun θ => M.J (pf.pi θ)) (pf.gradJ M θ) θ :=
  pf.hasGradientAt_J M θ

/-- **The policy gradient is Lipschitz.** -/
theorem PolicyFamily.Regular.isLip_gradJ : IsLip (pf.gradJ M) := by
  refine (IsLip.sum univ fun sa _ => ?_).const_smul (1 - M.γ)⁻¹
  exact ((hreg.isLip_occupancy M sa).mul (pf.isBdd_occupancy M sa)
      (hreg.isLip_Q M sa) (pf.isBdd_Q M sa)).smul
    ((pf.isBdd_occupancy M sa).mul (pf.isBdd_Q M sa))
    (hreg.score_lip sa.1 sa.2) (hreg.isBdd_score sa.1 sa.2)

/-- The discounted objective satisfies the quadratic lower bound of the gradient ascent
theorem. -/
theorem PolicyFamily.Regular.quadratic_lower_bound_J :
  ∃ L, 0 ≤ L ∧ ∀ x y, M.J (pf.pi x) + ⟪pf.gradJ M x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 ≤
    M.J (pf.pi y) := by
  obtain ⟨K, hK⟩ := (hreg.isLip_gradJ M).lipschitzWith
  exact ⟨K, K.2, quadratic_lower_bound_of_lipschitz (J := fun θ => M.J (pf.pi θ))
    (pf.hasGradientAt_J' M) hK⟩

/-- **Actor convergence, pathwise.** Biased stochastic gradient ascent on the discounted
objective of a regular policy family visits every neighbourhood of
`{θ | ‖∇ J θ‖ ≤ ‖bias‖}` infinitely often. -/
theorem PolicyFamily.Regular.frequently_norm_gradJ_sub_norm_bias_lt
  {θ : ℕ → E n} {β c : ℕ → ℝ} {b e : ℕ → E n}
  (hθ : ∀ k, θ (k + 1) = θ k + β k • (c k • (pf.gradJ M (θ k) + b k) + e k))
  (hβ : ∀ k, 0 ≤ β k)
  (hβsum : Filter.Tendsto (fun n => ∑ k ∈ range n, β k) Filter.atTop Filter.atTop)
  (hc : ∃ c₁, 0 < c₁ ∧ ∀ k, c₁ ≤ c k)
  (hsq : Summable fun k => β k ^ 2 * ‖c k • (pf.gradJ M (θ k) + b k) + e k‖ ^ 2)
  (he : ∃ l, Filter.Tendsto (fun n => ∑ k ∈ range n, β k * ⟪pf.gradJ M (θ k), e k⟫)
    Filter.atTop (nhds l)) :
  ∀ δ > 0, ∃ᶠ k in Filter.atTop, ‖pf.gradJ M (θ k)‖ - ‖b k‖ < δ :=
  frequently_norm_grad_sub_norm_bias_lt (pf.bddAbove_J M) (hreg.quadratic_lower_bound_J M)
    hθ hβ hβsum hc hsq he

end Lipschitz

section Softmax

variable (φ : S → A → E n)

omit [DecidableEq S] [Nonempty S] in
lemma exists_norm_feature_le : ∃ Φ, 0 ≤ Φ ∧ ∀ s a, ‖φ s a‖ ≤ Φ := by
  obtain ⟨Φ, hΦ⟩ := (Set.finite_range fun sa : S × A => ‖φ sa.1 sa.2‖).bddAbove
  exact ⟨max Φ 0, le_max_right _ _, fun s a => (hΦ ⟨(s, a), rfl⟩).trans (le_max_left _ _)⟩

omit [DecidableEq S] [Nonempty S] in
/-- The softmax family is regular: its score is bounded by `2 Φ` and Lipschitz. -/
theorem softmaxFamily_regular [Nonempty A] : (softmaxFamily (S := S) (A := A) φ).Regular := by
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_norm_feature_le φ
  have hbdd : ∃ C, 0 ≤ C ∧ ∀ θ s a, ‖(softmaxFamily φ).score θ s a‖ ≤ C := by
    refine ⟨Φ + Φ, by positivity, fun θ s a => ?_⟩
    rw [softmaxFamily_score]
    refine (norm_sub_le _ _).trans (add_le_add (hΦ s a) ?_)
    calc ‖∑ b, softmax φ θ s b • φ s b‖ ≤ ∑ b, ‖softmax φ θ s b • φ s b‖ := norm_sum_le _ _
      _ ≤ ∑ b, softmax φ θ s b * Φ := sum_le_sum fun b _ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (softmax_pos φ θ s b).le]
          exact mul_le_mul_of_nonneg_left (hΦ s b) (softmax_pos φ θ s b).le
      _ = Φ := by rw [← sum_mul, (softmax_stochastic φ θ s).rowsum, one_mul]
  refine ⟨hbdd, fun s a => ?_⟩
  have h := (IsLip.const (E := E n) (φ s a)).sub (IsLip.sum univ fun b _ =>
    ((softmaxFamily φ).isLip_pi hbdd s b).smul ((softmaxFamily φ).isBdd_pi s b)
      (IsLip.const (φ s b)) (IsBdd.const (φ s b)))
  exact h.comp_of_eq (funext fun θ => (softmaxFamily_score φ θ s a).symm)

end Softmax

end ReinforcementLearning
