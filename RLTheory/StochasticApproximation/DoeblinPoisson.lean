/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.ParamMarkovNoise

/-!
# Lipschitz Poisson solutions for a Doeblin chain

A finite kernel of the form `P_t(s, s') = α ν_t(s') + (1 - α) Q_t(s, s')`, with `0 < α ≤ 1` and
`ν_t`, `Q_t` stochastic, is uniformly ergodic: with probability `α` the chain restarts from
`ν_t`. The restart chain of the actor-critic has this form with `α = 1 - γ`.

For such a kernel the Poisson equation has an explicit solution. `U_t` solves
`U = H_t + (1 - α) Q_t U`, a contraction by `1 - α` in the sup norm. Then
`f(t) = α ν_t U_t` is the stationary mean of `H_t`, and `V_t = U_t - H_t + f(t) = P_t U_t`.
If `H`, `Q` and `ν` are Lipschitz in `t`, so are `U` and `V`.

* `doeblinU`, `doeblinF`, `doeblinV`: the Poisson pair and the mean.
* `doeblin_poisson`: its properties, the hypotheses of `tendsto_secondMoment_of_param_chain`.
* `tendsto_secondMoment_of_doeblin_chain`: Assumption 2.2 for θ-dependent Doeblin sampling.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

section Doeblin

variable {d : ℕ} {S : Type*} [Fintype S]

/-- The averaging operator of a kernel, on `S → E d` with the sup norm. -/
noncomputable def kerOp (q : S → S → ℝ) (U : S → E d) : S → E d := fun s => ∑ s', q s s' • U s'

lemma kerOp_smul (q : S → S → ℝ) (c : ℝ) (U : S → E d) :
    kerOp q (c • U) = c • kerOp q U := by
  funext s; simp [kerOp, Finset.smul_sum, smul_smul, mul_comm]

lemma kerOp_sub (q : S → S → ℝ) (U W : S → E d) :
    kerOp q (U - W) = kerOp q U - kerOp q W := by
  funext s; simp [kerOp, smul_sub, Finset.sum_sub_distrib]

lemma norm_kerOp_apply_le {q : S → S → ℝ} (hq0 : ∀ s s', 0 ≤ q s s')
    (hq1 : ∀ s, ∑ s', q s s' = 1) (U : S → E d) (s : S) : ‖kerOp q U s‖ ≤ ‖U‖ := by
  calc ‖kerOp q U s‖ ≤ ∑ s', ‖q s s' • U s'‖ := norm_sum_le _ _
    _ = ∑ s', q s s' * ‖U s'‖ := by
        refine sum_congr rfl fun s' _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq0 s s')]
    _ ≤ ∑ s', q s s' * ‖U‖ := sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm U s') (hq0 s s')
    _ = ‖U‖ := by rw [← sum_mul, hq1, one_mul]

lemma norm_kerOp_le {q : S → S → ℝ} (hq0 : ∀ s s', 0 ≤ q s s')
    (hq1 : ∀ s, ∑ s', q s s' = 1) (U : S → E d) : ‖kerOp q U‖ ≤ ‖U‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg U)).mpr (norm_kerOp_apply_le hq0 hq1 U)

lemma norm_kerOp_sub_kernel_apply_le {q q' : S → S → ℝ} {L : ℝ}
    (hq : ∀ s, ∑ s', |q s s' - q' s s'| ≤ L) (U : S → E d) (s : S) :
    ‖kerOp q U s - kerOp q' U s‖ ≤ L * ‖U‖ := by
  have e : kerOp q U s - kerOp q' U s = ∑ s', (q s s' - q' s s') • U s' := by
    simp [kerOp, sub_smul, Finset.sum_sub_distrib]
  rw [e]
  calc ‖∑ s', (q s s' - q' s s') • U s'‖ ≤ ∑ s', ‖(q s s' - q' s s') • U s'‖ := norm_sum_le _ _
    _ = ∑ s', |q s s' - q' s s'| * ‖U s'‖ := by
        refine sum_congr rfl fun s' _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ s', |q s s' - q' s s'| * ‖U‖ := sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm U s') (abs_nonneg _)
    _ ≤ L * ‖U‖ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hq s) (norm_nonneg _)

/-- The Poisson solution `U_t`, solving `U = H_t + (1 - α) Q_t U`. -/
noncomputable def doeblinU (α : ℝ) (Q : E d → S → S → ℝ) (H : E d → S → E d) (t : E d) :
    S → E d :=
  Function.invFun (fun U : S → E d => U - (1 - α) • kerOp (Q t) U) (H t)

/-- The stationary mean `f(t) = α ν_t U_t`. -/
noncomputable def doeblinF (α : ℝ) (ν : E d → S → ℝ) (Q : E d → S → S → ℝ)
    (H : E d → S → E d) (t : E d) : E d :=
  α • ∑ s, ν t s • doeblinU α Q H t s

/-- The second member `V_t = U_t - H_t + f(t)` of the Poisson pair. -/
noncomputable def doeblinV (α : ℝ) (ν : E d → S → ℝ) (Q : E d → S → S → ℝ)
    (H : E d → S → E d) (t : E d) (s : S) : E d :=
  doeblinU α Q H t s - H t s + doeblinF α ν Q H t

variable {α : ℝ} {Q : E d → S → S → ℝ} {H : E d → S → E d}

/-- `U_t` solves its fixed-point equation. -/
lemma doeblinU_spec (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (t : E d) :
    doeblinU α Q H t - (1 - α) • kerOp (Q t) (doeblinU α Q H t) = H t := by
  set Lm : (S → E d) →ₗ[ℝ] (S → E d) :=
    { toFun := fun U => U - (1 - α) • kerOp (Q t) U
      map_add' := fun U W => by
        funext s; simp only [kerOp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add,
          Finset.sum_add_distrib]; abel
      map_smul' := fun c U => by
        have hk : kerOp (Q t) (c • U) = c • kerOp (Q t) U := by
          funext s; simp [kerOp, Finset.smul_sum, smul_smul, mul_comm]
        simp only [RingHom.id_apply]
        rw [hk, smul_sub, smul_comm c (1 - α)] } with hLm
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro U hU
    have e : U = (1 - α) • kerOp (Q t) U := sub_eq_zero.mp hU
    have h1 : ‖U‖ ≤ (1 - α) * ‖U‖ := by
      calc ‖U‖ = ‖(1 - α) • kerOp (Q t) U‖ := by rw [← e]
        _ = (1 - α) * ‖kerOp (Q t) U‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        _ ≤ (1 - α) * ‖U‖ :=
            mul_le_mul_of_nonneg_left (norm_kerOp_le (hQ0 t) (hQ1 t) U) (by linarith)
    have : ‖U‖ ≤ 0 := by nlinarith [norm_nonneg U]
    exact norm_le_zero_iff.mp this
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  exact Function.invFun_eq (f := fun U : S → E d => U - (1 - α) • kerOp (Q t) U) (hsurj (H t))

lemma doeblinU_eq (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (t : E d) (s : S) :
    doeblinU α Q H t s = H t s + (1 - α) • ∑ s', Q t s s' • doeblinU α Q H t s' := by
  have := congrFun (doeblinU_spec (H := H) hα0 hα1 hQ0 hQ1 t) s
  simp only [Pi.sub_apply, Pi.smul_apply, kerOp] at this
  rw [← this]; abel

/-- `‖U_t‖ ≤ C_H / α`. -/
lemma norm_doeblinU_le (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) {CH : ℝ} (hCH : 0 ≤ CH) (hHb : ∀ t s, ‖H t s‖ ≤ CH)
    (t : E d) : ‖doeblinU α Q H t‖ ≤ CH / α := by
  set U := doeblinU α Q H t
  have e : U = H t + (1 - α) • kerOp (Q t) U := by
    rw [← doeblinU_spec (H := H) hα0 hα1 hQ0 hQ1 t]; abel
  have hH : ‖H t‖ ≤ CH := (pi_norm_le_iff_of_nonneg hCH).mpr (hHb t)
  have h1 : ‖U‖ ≤ CH + (1 - α) * ‖U‖ := by
    calc ‖U‖ = ‖H t + (1 - α) • kerOp (Q t) U‖ := by rw [← e]
      _ ≤ ‖H t‖ + ‖(1 - α) • kerOp (Q t) U‖ := norm_add_le _ _
      _ ≤ CH + (1 - α) * ‖U‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          exact add_le_add hH
            (mul_le_mul_of_nonneg_left (norm_kerOp_le (hQ0 t) (hQ1 t) U) (by linarith))
  rw [le_div_iff₀ hα0]
  linarith

/-- `U` is Lipschitz in the parameter. -/
lemma norm_doeblinU_sub_le (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) {CH LH LQ : ℝ} (hCH : 0 ≤ CH) (hLH : 0 ≤ LH)
    (hLQ : 0 ≤ LQ) (hHb : ∀ t s, ‖H t s‖ ≤ CH)
    (hHL : ∀ t t' s, ‖H t s - H t' s‖ ≤ LH * ‖t - t'‖)
    (hQL : ∀ t t' s, ∑ s', |Q t s s' - Q t' s s'| ≤ LQ * ‖t - t'‖) (t t' : E d) :
    ‖doeblinU α Q H t - doeblinU α Q H t'‖ ≤ (LH + LQ * (CH / α)) / α * ‖t - t'‖ := by
  set U := doeblinU α Q H t
  set U' := doeblinU α Q H t'
  set δ := ‖t - t'‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have e : U - U' = (H t - H t') + (1 - α) • kerOp (Q t) (U - U')
      + (1 - α) • (kerOp (Q t) U' - kerOp (Q t') U') := by
    have h1 := doeblinU_spec (H := H) hα0 hα1 hQ0 hQ1 t
    have h2 := doeblinU_spec (H := H) hα0 hα1 hQ0 hQ1 t'
    rw [← h1, ← h2, kerOp_sub]
    simp only [U, U', smul_sub]
    abel
  have hCU := norm_doeblinU_le (H := H) hα0 hα1 hQ0 hQ1 hCH hHb t'
  have tH : ‖H t - H t'‖ ≤ LH * δ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => by simpa using hHL t t' s
  have tQ : ‖kerOp (Q t) U' - kerOp (Q t') U'‖ ≤ LQ * δ * (CH / α) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
    refine (norm_kerOp_sub_kernel_apply_le (hQL t t') U' s).trans ?_
    exact mul_le_mul_of_nonneg_left hCU (by positivity)
  have h1α : 0 ≤ 1 - α := by linarith
  have hD : ‖U - U'‖ ≤ LH * δ + (1 - α) * ‖U - U'‖ + (1 - α) * (LQ * δ * (CH / α)) := by
    calc ‖U - U'‖ = ‖(H t - H t') + (1 - α) • kerOp (Q t) (U - U')
          + (1 - α) • (kerOp (Q t) U' - kerOp (Q t') U')‖ := by rw [← e]
      _ ≤ ‖H t - H t'‖ + ‖(1 - α) • kerOp (Q t) (U - U')‖
          + ‖(1 - α) • (kerOp (Q t) U' - kerOp (Q t') U')‖ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ _ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1α]
          gcongr
          exact norm_kerOp_le (hQ0 t) (hQ1 t) _
  have h3 : (1 - α) * (LQ * δ * (CH / α)) ≤ LQ * δ * (CH / α) := by
    have : 0 ≤ LQ * δ * (CH / α) := by positivity
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hα0]
  nlinarith

lemma norm_mean_le {ν : S → ℝ} (hν0 : ∀ s, 0 ≤ ν s) (hν1 : ∑ s, ν s = 1) (W : S → E d) :
    ‖∑ s, ν s • W s‖ ≤ ‖W‖ := by
  calc ‖∑ s, ν s • W s‖ ≤ ∑ s, ‖ν s • W s‖ := norm_sum_le _ _
    _ = ∑ s, ν s * ‖W s‖ := by
        refine sum_congr rfl fun s _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hν0 s)]
    _ ≤ ∑ s, ν s * ‖W‖ := sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm W s) (hν0 s)
    _ = ‖W‖ := by rw [← sum_mul, hν1, one_mul]

lemma norm_mean_sub_le {ν ν' : S → ℝ} {L : ℝ} (hν : ∑ s, |ν s - ν' s| ≤ L) (W : S → E d) :
    ‖∑ s, ν s • W s - ∑ s, ν' s • W s‖ ≤ L * ‖W‖ := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ s, (ν s • W s - ν' s • W s)‖ ≤ ∑ s, ‖ν s • W s - ν' s • W s‖ := norm_sum_le _ _
    _ = ∑ s, |ν s - ν' s| * ‖W s‖ := by
        refine sum_congr rfl fun s _ => ?_
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ s, |ν s - ν' s| * ‖W‖ := sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm W s) (abs_nonneg _)
    _ ≤ L * ‖W‖ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hν (norm_nonneg _)

variable {ν : E d → S → ℝ}

/-- `V_t = P_t U_t` with `P_t = α ν_t + (1 - α) Q_t`. -/
lemma doeblinV_eq (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (t : E d) (s : S) :
    doeblinV α ν Q H t s = ∑ s', (α * ν t s' + (1 - α) * Q t s s') • doeblinU α Q H t s' := by
  rw [doeblinV, doeblinF, doeblinU_eq (H := H) hα0 hα1 hQ0 hQ1 t s]
  simp only [add_smul, ← smul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  module

/-- **`f` is the stationary mean.** For any stationary law `ρ` of `P_t`,
`f(t) = Σ_s ρ(s) H_t(s)`. -/
lemma doeblinF_eq_mean (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (t : E d) {ρ : S → ℝ}
    (hρ : ∀ s', ∑ s, ρ s * (α * ν t s' + (1 - α) * Q t s s') = ρ s') (hρ1 : ∑ s, ρ s = 1) :
    doeblinF α ν Q H t = ∑ s, ρ s • H t s := by
  set U := doeblinU α Q H t
  have key : ∑ s, ρ s • doeblinV α ν Q H t s = ∑ s', ρ s' • U s' := by
    simp_rw [doeblinV_eq (ν := ν) (H := H) hα0 hα1 hQ0 hQ1 t, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun s' _ => ?_
    rw [← Finset.sum_smul, hρ s']
  have key2 : ∑ s, ρ s • doeblinV α ν Q H t s =
      ∑ s, ρ s • U s - ∑ s, ρ s • H t s + doeblinF α ν Q H t := by
    simp only [doeblinV, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hρ1, one_smul, U]
  have h := key2.symm.trans key
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at h
  rw [← h]
  abel

lemma norm_doeblinF_le (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (hν0 : ∀ t s, 0 ≤ ν t s) (hν1 : ∀ t, ∑ s, ν t s = 1)
    {CH : ℝ} (hCH : 0 ≤ CH) (hHb : ∀ t s, ‖H t s‖ ≤ CH) (t : E d) :
    ‖doeblinF α ν Q H t‖ ≤ CH := by
  rw [doeblinF, norm_smul, Real.norm_eq_abs, abs_of_pos hα0]
  have h1 := (norm_mean_le (hν0 t) (hν1 t) (doeblinU α Q H t)).trans
    (norm_doeblinU_le (H := H) hα0 hα1 hQ0 hQ1 hCH hHb t)
  calc α * ‖∑ s, ν t s • doeblinU α Q H t s‖ ≤ α * (CH / α) :=
        mul_le_mul_of_nonneg_left h1 hα0.le
    _ = CH := by field_simp

lemma norm_doeblinV_le (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (hν0 : ∀ t s, 0 ≤ ν t s) (hν1 : ∀ t, ∑ s, ν t s = 1)
    {CH : ℝ} (hCH : 0 ≤ CH) (hHb : ∀ t s, ‖H t s‖ ≤ CH) (t : E d) (s : S) :
    ‖doeblinV α ν Q H t s‖ ≤ CH / α + 2 * CH := by
  have h1 := (norm_le_pi_norm (doeblinU α Q H t) s).trans
    (norm_doeblinU_le (H := H) hα0 hα1 hQ0 hQ1 hCH hHb t)
  have h2 := norm_doeblinF_le (ν := ν) (H := H) hα0 hα1 hQ0 hQ1 hν0 hν1 hCH hHb t
  have h3 := norm_sub_le (doeblinU α Q H t s) (H t s)
  have h4 := norm_add_le (doeblinU α Q H t s - H t s) (doeblinF α ν Q H t)
  have := hHb t s
  rw [doeblinV]
  linarith

/-- `V` is Lipschitz in the parameter. -/
lemma norm_doeblinV_sub_le (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (hν0 : ∀ t s, 0 ≤ ν t s) (hν1 : ∀ t, ∑ s, ν t s = 1)
    {CH LH LQ Lν : ℝ} (hCH : 0 ≤ CH) (hLH : 0 ≤ LH) (hLQ : 0 ≤ LQ) (hLν : 0 ≤ Lν)
    (hHb : ∀ t s, ‖H t s‖ ≤ CH) (hHL : ∀ t t' s, ‖H t s - H t' s‖ ≤ LH * ‖t - t'‖)
    (hQL : ∀ t t' s, ∑ s', |Q t s s' - Q t' s s'| ≤ LQ * ‖t - t'‖)
    (hνL : ∀ t t', ∑ s, |ν t s - ν t' s| ≤ Lν * ‖t - t'‖) (t t' : E d) (s : S) :
    ‖doeblinV α ν Q H t s - doeblinV α ν Q H t' s‖ ≤
      ((1 + α) * ((LH + LQ * (CH / α)) / α) + LH + α * Lν * (CH / α)) * ‖t - t'‖ := by
  set U := doeblinU α Q H t
  set U' := doeblinU α Q H t'
  set LU := (LH + LQ * (CH / α)) / α
  set δ := ‖t - t'‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hU := norm_doeblinU_sub_le (H := H) hα0 hα1 hQ0 hQ1 hCH hLH hLQ hHb hHL hQL t t'
  have hCU := norm_doeblinU_le (H := H) hα0 hα1 hQ0 hQ1 hCH hHb t'
  have tU : ‖U s - U' s‖ ≤ LU * δ := (norm_le_pi_norm (U - U') s).trans hU
  have tF : ‖doeblinF α ν Q H t - doeblinF α ν Q H t'‖ ≤ α * (LU * δ + Lν * δ * (CH / α)) := by
    have e : doeblinF α ν Q H t - doeblinF α ν Q H t' = α • (∑ s, ν t s • (U - U') s
        + (∑ s, ν t s • U' s - ∑ s, ν t' s • U' s)) := by
      simp only [doeblinF, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, U, U']
      module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hα0]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
      ((norm_mean_le (hν0 t) (hν1 t) _).trans hU) ?_)) hα0.le
    exact (norm_mean_sub_le (hνL t t') U').trans (mul_le_mul_of_nonneg_left hCU (by positivity))
  have e : doeblinV α ν Q H t s - doeblinV α ν Q H t' s =
      (U s - U' s) - (H t s - H t' s) + (doeblinF α ν Q H t - doeblinF α ν Q H t') := by
    simp only [doeblinV, U, U']; abel
  rw [e]
  have h1 := norm_add_le ((U s - U' s) - (H t s - H t' s))
    (doeblinF α ν Q H t - doeblinF α ν Q H t')
  have h2 := norm_sub_le (U s - U' s) (H t s - H t' s)
  have h3 := hHL t t' s
  have e2 : ((1 + α) * LU + LH + α * Lν * (CH / α)) * δ =
      LU * δ + LH * δ + α * (LU * δ + Lν * δ * (CH / α)) := by ring
  rw [e2]
  linarith

end Doeblin

section Chain

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

set_option maxHeartbeats 4000000 in
/-- **Assumption 2.2 for θ-dependent Doeblin sampling.** Let `θ_{k+1} = θ_k + β_k H(θ_k, ξ_{k+1})`,
where the finite chain `ξ` has conditional law `P_{θ_k}(ξ_k, ·)` with
`P_t(s, s') = α ν_t(s') + (1 - α) Q_t(s, s')`, `0 < α ≤ 1`. Suppose `H` is bounded and Lipschitz
in `t`, `ν` and `Q` are Lipschitz in `t` in total variation, and the mean drift `f(t)` is the mean
of `H_t` under a stationary law of `P_t`, dissipative and linear to first order. If the covariance
of `M_{k+1} = U_{θ_k}(ξ_{k+1}) - V_{θ_k}(ξ_k)` converges to `Γ`, for the Poisson pair of
`doeblinU`, `doeblinV`, then `(θ_k - θ*)/√β_k` has the asymptotic covariance `Σ` with
`(A - (β̄/2) I) Σ + Σ (A - (β̄/2) I)ᵀ = Γ`. -/
theorem tendsto_secondMoment_of_doeblin_chain {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar)
    (A : Matrix (Fin d) (Fin d) ℝ) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hA : ∀ x, η₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d} {ξ : ℕ → Ω → S} {θh : E d}
    {f : E d → E d} {H : E d → S → E d} {α : ℝ} {ν : E d → S → ℝ} {Q : E d → S → S → ℝ}
    {ρ : E d → S → ℝ} {η K L CH LH LQ Lν : ℝ} (h2η : βbar < 2 * η) (hK0 : 0 ≤ K) (hL : 0 ≤ L)
    (hdis : ∀ x, ⟪x - θh, f x⟫_ℝ ≤ -η * ‖x - θh‖ ^ 2) (hlin : ∀ x, ‖f x‖ ≤ K * ‖x - θh‖)
    (hf : ∀ x, ‖f x + matCLM A (x - θh)‖ ≤ L * ‖x - θh‖ ^ 2) (hfc : Continuous f) {Γ : Mat d}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hQ0 : ∀ t s s', 0 ≤ Q t s s')
    (hQ1 : ∀ t s, ∑ s', Q t s s' = 1) (hν0 : ∀ t s, 0 ≤ ν t s) (hν1 : ∀ t, ∑ s, ν t s = 1)
    (hCH : 0 ≤ CH) (hLH : 0 ≤ LH) (hLQ : 0 ≤ LQ) (hLν : 0 ≤ Lν)
    (hHb : ∀ t s, ‖H t s‖ ≤ CH) (hHL : ∀ t t' s, ‖H t s - H t' s‖ ≤ LH * ‖t - t'‖)
    (hQL : ∀ t t' s, ∑ s', |Q t s s' - Q t' s s'| ≤ LQ * ‖t - t'‖)
    (hνL : ∀ t t', ∑ s, |ν t s - ν t' s| ≤ Lν * ‖t - t'‖)
    (hρ : ∀ t s', ∑ s, ρ t s * (α * ν t s' + (1 - α) * Q t s s') = ρ t s')
    (hρ1 : ∀ t, ∑ s, ρ t s = 1) (hfρ : ∀ t, f t = ∑ s, ρ t s • H t s)
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • H (θ k ω) (ξ (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    (hθ0 : ∃ C, ∀ ω, ‖θ 0 ω - θh‖ ≤ C)
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => α * ν (θ k ω) s + (1 - α) * Q (θ k ω) (ξ k ω) s)
    (hΓ : Tendsto (fun k => secondMoment μ (fun ω => doeblinU α Q H (θ k ω) (ξ (k + 1) ω)
      - doeblinV α ν Q H (θ k ω) (ξ k ω))) atTop (𝓝 Γ)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (fun ω => θ k ω - θh)) atTop (𝓝 Sig) := by
  have hfeq : ∀ t, doeblinF α ν Q H t = f t := fun t => by
    rw [hfρ t]; exact doeblinF_eq_mean hα0 hα1 hQ0 hQ1 t (hρ t) (hρ1 t)
  have hUL := norm_doeblinU_sub_le (H := H) hα0 hα1 hQ0 hQ1 hCH hLH hLQ hHb hHL hQL
  refine tendsto_secondMoment_of_param_chain hβ A hη₀ hA ℱ (U := doeblinU α Q H)
    (V := doeblinV α ν Q H) (P := fun t s s' => α * ν t s' + (1 - α) * Q t s s')
    h2η hK0 hL hdis hlin hf hfc hθ hθm hξm hθ0 hlaw ?_
    (doeblinV_eq hα0 hα1 hQ0 hQ1)
    (fun s => continuous_of_lipschitz_bound (F := fun t => doeblinU α Q H t s)
      (fun t t' => (norm_le_pi_norm (doeblinU α Q H t - doeblinU α Q H t') s).trans (hUL t t')))
    (fun t s => (norm_le_pi_norm _ s).trans (norm_doeblinU_le hα0 hα1 hQ0 hQ1 hCH hHb t))
    (norm_doeblinV_le hα0 hα1 hQ0 hQ1 hν0 hν1 hCH hHb)
    (norm_doeblinV_sub_le hα0 hα1 hQ0 hQ1 hν0 hν1 hCH hLH hLQ hLν hHb hHL hQL hνL) hHb hΓ
  intro t s
  rw [doeblinV, hfeq]
  abel

end Chain

end StochasticApproximation
