/-
SPDX-License-Identifier: MIT
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import RLTheory.Defs
import RLTheory.Analysis.Calculus.Gradient
import RLTheory.Data.Matrix.Stochastic
import RLTheory.MarkovDecisionProcess.MarkovDecisionProcess

/-!
# Parameterized policies for finite MDPs

Matrix-level setup for policy-gradient methods (Konda, *Actor-Critic Algorithms*, Ch. 2).

* `TabularMDP` : a finite MDP with real-valued transition and reward arrays.
* `PolicyFamily` : a differentiable family `θ ↦ pi θ` of strictly positive randomized
  stationary policies, together with its score function `ψ θ = ∇ log pi θ`.
* `softmaxFamily` : the Gibbs / softmax policy family with linear features.

Since every policy in a `PolicyFamily` charges every action, the support of the induced
chain on `S × A` does not depend on `θ`, so irreducibility and aperiodicity can be checked
for a single parameter (`PolicyFamily.irreducible_saMat`, `PolicyFamily.aperiodic_saMat`).
-/

open Real Finset Matrix StochasticMatrix RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace ReinforcementLearning

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable {n : ℕ}

section TabularMDP

/-- A finite MDP given by real-valued transition probabilities `P (s, a) s'`. -/
structure TabularMDP where
  P : S × A → S → ℝ
  hP : ∀ sa, StochasticVec (P sa)
  r : S × A → ℝ
  p₀ : S → ℝ
  hp₀ : StochasticVec p₀
  γ : ℝ
  hγ : 0 ≤ γ ∧ γ < 1

variable (M : TabularMDP (S := S) (A := A))

/-- State-to-state transition matrix under the policy `pi`. -/
def TabularMDP.stateMat (pi : S → A → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' => ∑ a, pi s a * M.P (s, a) s'

/-- Expected one-step reward under the policy `pi`. -/
def TabularMDP.stateReward (pi : S → A → ℝ) : S → ℝ :=
  fun s => ∑ a, pi s a * M.r (s, a)

/-- Transition matrix of the state-action chain under the policy `pi`. -/
def TabularMDP.saMat (pi : S → A → ℝ) : Matrix (S × A) (S × A) ℝ :=
  Matrix.of fun y z => M.P y z.1 * pi z.1 z.2

omit [DecidableEq S] [Nonempty S] [DecidableEq A] [Nonempty A] in
lemma TabularMDP.rowStochastic_stateMat {pi : S → A → ℝ}
  (hpi : ∀ s, StochasticVec (pi s)) : RowStochastic (M.stateMat pi) := by
  constructor
  intro s
  constructor
  · intro s'
    simp only [TabularMDP.stateMat, Matrix.of_apply]
    exact sum_nonneg fun a _ => mul_nonneg ((hpi s).nonneg a) ((M.hP (s, a)).nonneg s')
  · have hP : ∀ sa, ∑ s', M.P sa s' = 1 := fun sa => (M.hP sa).rowsum
    simp only [TabularMDP.stateMat, Matrix.of_apply]
    rw [sum_comm]
    simp [← mul_sum, hP, (hpi s).rowsum]

omit [DecidableEq S] [Nonempty S] [DecidableEq A] [Nonempty A] in
lemma TabularMDP.rowStochastic_saMat {pi : S → A → ℝ}
  (hpi : ∀ s, StochasticVec (pi s)) : RowStochastic (M.saMat pi) := by
  constructor
  intro y
  constructor
  · intro z
    simp only [TabularMDP.saMat, Matrix.of_apply]
    exact mul_nonneg ((M.hP y).nonneg _) ((hpi _).nonneg _)
  · have hpi' : ∀ s, ∑ a, pi s a = 1 := fun s => (hpi s).rowsum
    simp only [TabularMDP.saMat, Matrix.of_apply, Fintype.sum_prod_type]
    simp [← mul_sum, hpi', (M.hP y).rowsum]

/-- Two entrywise nonnegative matrices with the same positivity pattern have powers
with the same positivity pattern. -/
lemma pow_pos_iff_of_pos_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B C : Matrix ι ι ℝ} (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
  (h : ∀ i j, 0 < B i j ↔ 0 < C i j) (n : ℕ) :
  ∀ i j, 0 < (B ^ n) i j ↔ 0 < (C ^ n) i j := by
  have hnonneg : ∀ {D : Matrix ι ι ℝ}, (∀ i j, 0 ≤ D i j) → ∀ m i j, 0 ≤ (D ^ m) i j := by
    intro D hD m
    induction m with
    | zero => intro i j; by_cases hij : i = j <;> simp [hij]
    | succ m ih =>
      intro i j
      rw [pow_succ, mul_apply]
      exact sum_nonneg fun k _ => mul_nonneg (ih i k) (hD k j)
  have hmul : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → (0 < a * b ↔ 0 < a ∧ 0 < b) := by
    intro a b ha hb
    refine ⟨fun hab => ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩,
      fun ⟨ha', hb'⟩ => mul_pos ha' hb'⟩
    · rintro rfl; simp at hab
    · rintro rfl; simp at hab
  induction n with
  | zero => intro i j; by_cases hij : i = j <;> simp [hij]
  | succ n ih =>
    intro i j
    rw [pow_succ, pow_succ, mul_apply, mul_apply,
      sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hnonneg hB n i k) (hB k j)),
      sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hnonneg hC n i k) (hC k j))]
    simp only [hmul (hnonneg hB n _ _) (hB _ _), hmul (hnonneg hC n _ _) (hC _ _), ih, h]

end TabularMDP

section PolicyFamily

/-- A differentiable family of strictly positive randomized stationary policies,
parameterized by `θ ∈ ℝⁿ`. Strict positivity (as in Assumption 2.8 of Konda's thesis) makes
`log pi` and the score well defined; it holds for softmax policies. -/
structure PolicyFamily (n : ℕ) where
  pi : E n → S → A → ℝ
  stochastic : ∀ θ s, StochasticVec (pi θ s)
  pos : ∀ θ s a, 0 < pi θ s a
  differentiable : ∀ s a, Differentiable ℝ fun θ => pi θ s a

variable (pf : PolicyFamily (S := S) (A := A) n)

/-- The score function `ψ θ s a = ∇_θ log pi θ s a`. -/
noncomputable def PolicyFamily.score (θ : E n) (s : S) (a : A) : E n :=
  gradient (fun θ => Real.log (pf.pi θ s a)) θ

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] [Nonempty A] in
/-- Likelihood-ratio identity: `∇ pi = pi • ψ`. -/
lemma PolicyFamily.hasGradientAt_pi (θ : E n) (s : S) (a : A) :
  HasGradientAt (fun θ => pf.pi θ s a) (pf.pi θ s a • pf.score θ s a) θ := by
  have hf := (pf.differentiable s a θ).hasGradientAt
  have hne := (pf.pos θ s a).ne'
  have hscore : pf.score θ s a = (pf.pi θ s a)⁻¹ • gradient (fun θ => pf.pi θ s a) θ :=
    (hf.log' hne).gradient
  rw [hscore, smul_smul, mul_inv_cancel₀ hne, one_smul]
  exact hf

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] [Nonempty A] in
/-- The score has zero mean under the policy, so state-dependent baselines are free. -/
lemma PolicyFamily.sum_smul_score_eq_zero (θ : E n) (s : S) :
  ∑ a, pf.pi θ s a • pf.score θ s a = 0 := by
  have h := HasGradientAt.sum' (u := univ) fun a _ => pf.hasGradientAt_pi θ s a
  have hone : (fun θ => ∑ a, pf.pi θ s a) = fun _ => (1 : ℝ) := by
    funext θ
    exact (pf.stochastic θ s).rowsum
  rw [hone] at h
  exact h.unique (hasGradientAt_const θ 1)

instance TabularMDP.instRowStochastic_stateMat (M : TabularMDP (S := S) (A := A))
  (θ : E n) : RowStochastic (M.stateMat (pf.pi θ)) :=
  M.rowStochastic_stateMat (pf.stochastic θ)

instance TabularMDP.instRowStochastic_saMat (M : TabularMDP (S := S) (A := A))
  (θ : E n) : RowStochastic (M.saMat (pf.pi θ)) :=
  M.rowStochastic_saMat (pf.stochastic θ)

omit [Nonempty S] [Nonempty A] in
lemma PolicyFamily.saMat_pow_pos_iff (M : TabularMDP (S := S) (A := A)) (θ₀ θ : E n) (m : ℕ) :
  ∀ y z, 0 < (M.saMat (pf.pi θ₀) ^ m) y z ↔ 0 < (M.saMat (pf.pi θ) ^ m) y z := by
  apply pow_pos_iff_of_pos_iff
  · intro y z
    exact mul_nonneg ((M.hP y).nonneg _) (pf.pos θ₀ _ _).le
  · intro y z
    exact mul_nonneg ((M.hP y).nonneg _) (pf.pos θ _ _).le
  · intro y z
    simp only [TabularMDP.saMat, Matrix.of_apply]
    rw [mul_pos_iff_of_pos_right (pf.pos θ₀ _ _), mul_pos_iff_of_pos_right (pf.pos θ _ _)]

omit [Nonempty S] [Nonempty A] in
/-- The support of the state-action chain does not depend on `θ`, so irreducibility at
one parameter gives irreducibility at every parameter. -/
lemma PolicyFamily.irreducible_saMat (M : TabularMDP (S := S) (A := A)) (θ₀ θ : E n)
  [StochasticMatrix.Irreducible (M.saMat (pf.pi θ₀))] : StochasticMatrix.Irreducible (M.saMat (pf.pi θ)) := by
  constructor
  intro i j
  obtain ⟨m, hm⟩ := (inferInstance : StochasticMatrix.Irreducible (M.saMat (pf.pi θ₀))).irreducible i j
  exact ⟨m, (pf.saMat_pow_pos_iff M θ₀ θ m i j).mp hm⟩

omit [Nonempty S] [Nonempty A] in
lemma PolicyFamily.aperiodic_saMat (M : TabularMDP (S := S) (A := A)) (θ₀ θ : E n)
  [StochasticMatrix.Aperiodic (M.saMat (pf.pi θ₀))] : StochasticMatrix.Aperiodic (M.saMat (pf.pi θ)) := by
  constructor
  intro i
  have heq : return_times (M.saMat (pf.pi θ)) i = return_times (M.saMat (pf.pi θ₀)) i := by
    ext m
    simp [return_times, pf.saMat_pow_pos_iff M θ₀ θ m i i]
  rw [heq]
  infer_instance

end PolicyFamily

section Softmax

/-- Softmax (Gibbs) policy with linear features `φ s a ∈ ℝⁿ`. -/
noncomputable def softmax (φ : S → A → E n) (θ : E n) (s : S) (a : A) : ℝ :=
  exp ⟪θ, φ s a⟫ / ∑ b, exp ⟪θ, φ s b⟫

variable (φ : S → A → E n)

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] in
lemma softmax_denom_pos (θ : E n) (s : S) : 0 < ∑ b, exp ⟪θ, φ s b⟫ :=
  sum_pos (fun _ _ => exp_pos _) univ_nonempty

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] in
lemma softmax_pos (θ : E n) (s : S) (a : A) : 0 < softmax φ θ s a :=
  div_pos (exp_pos _) (softmax_denom_pos φ θ s)

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] in
lemma softmax_stochastic (θ : E n) (s : S) : StochasticVec (softmax φ θ s) := by
  constructor
  · exact fun a => (softmax_pos φ θ s a).le
  · simp only [softmax]
    rw [← sum_div, div_self (softmax_denom_pos φ θ s).ne']

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] in
lemma differentiable_softmax (s : S) (a : A) :
  Differentiable ℝ fun θ => softmax φ θ s a := by
  intro θ
  have hnum := (hasGradientAt_inner_const (φ s a) θ).exp'
  have hden := HasGradientAt.sum' (u := univ) fun b _ =>
    (hasGradientAt_inner_const (φ s b) θ).exp'
  show DifferentiableAt ℝ (fun θ => exp ⟪θ, φ s a⟫ * (∑ b, exp ⟪θ, φ s b⟫)⁻¹) θ
  exact hnum.differentiableAt.mul (hden.differentiableAt.inv (softmax_denom_pos φ θ s).ne')

noncomputable def softmaxFamily : PolicyFamily (S := S) (A := A) n where
  pi := softmax φ
  stochastic := softmax_stochastic φ
  pos := softmax_pos φ
  differentiable := differentiable_softmax φ

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq A] in
/-- The softmax score is the centered feature. -/
lemma softmaxFamily_score (θ : E n) (s : S) (a : A) :
  (softmaxFamily φ).score θ s a = φ s a - ∑ b, softmax φ θ s b • φ s b := by
  have hlog : (fun θ => Real.log (softmax φ θ s a)) =
      fun θ => ⟪θ, φ s a⟫ - Real.log (∑ b, exp ⟪θ, φ s b⟫) := by
    funext θ
    rw [softmax, Real.log_div (exp_pos _).ne' (softmax_denom_pos φ θ s).ne', Real.log_exp]
  have hZ := HasGradientAt.sum' (u := univ) fun b _ =>
    (hasGradientAt_inner_const (φ s b) θ).exp'
  have h := (hasGradientAt_inner_const (φ s a) θ).sub' (hZ.log' (softmax_denom_pos φ θ s).ne')
  simp only [PolicyFamily.score, softmaxFamily]
  rw [hlog, h.gradient, smul_sum]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [smul_smul, softmax, div_eq_inv_mul]

end Softmax

section Bridge

variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

lemma sum_probability_singleton' {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] (μ : MeasureTheory.ProbabilityMeasure ι) :
  ∑ i, μ {i} = 1 := by
  have : ∑ i, μ.1 {i} = 1 := by simp
  have := congrArg ENNReal.toNNReal this
  conv_rhs at this => simp
  rw [ENNReal.toNNReal_sum] at this
  rw [← this]
  apply sum_congr rfl
  intro i _
  exact_mod_cast rfl
  simp

/-- Forget the measure-theoretic structure of an `MDPSpec`. -/
noncomputable def MDPSpec.toTabular (mdp : MDPSpec (S := S) (A := A))
  (hγ : 0 ≤ mdp.γ ∧ mdp.γ < 1) : TabularMDP (S := S) (A := A) where
  P sa s' := (mdp.P sa {s'} : ℝ)
  hP sa := ⟨fun _ => NNReal.coe_nonneg _, by exact_mod_cast sum_probability_singleton' (mdp.P sa)⟩
  r := mdp.r
  p₀ s := (mdp.p₀ {s} : ℝ)
  hp₀ := ⟨fun _ => NNReal.coe_nonneg _, by exact_mod_cast sum_probability_singleton' mdp.p₀⟩
  γ := mdp.γ
  hγ := hγ

omit [Nonempty S] [Nonempty A] in
/-- The existing state-action chain of a `FiniteMDP` is the tabular `saMat`. -/
lemma FiniteMDP.MRP_P_eq_saMat (MDP : FiniteMDP (S := S) (A := A)) :
  MDP.MRP.P = (MDP.toMDPSpec.toTabular MDP.hγ).saMat (fun s a => (MDP.pi s {a} : ℝ)) := by
  ext y ⟨s, a⟩
  rw [FiniteMDP.MRP.P_apply]
  simp [TabularMDP.saMat, MDPSpec.toTabular]

end Bridge

end ReinforcementLearning
