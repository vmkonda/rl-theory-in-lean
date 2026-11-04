/-
SPDX-License-Identifier: MIT
-/
import RLTheory.MarkovDecisionProcess.PolicyFamily

/-!
# Policy gradient theorem for discounted finite MDPs

Finite-MDP version of Konda, *Actor-Critic Algorithms*, Theorem 2.13.

For a policy `pi`, with `P_pi = M.stateMat pi` and `r_pi = M.stateReward pi`:

* `resolvent pi = (1 - γ P_pi)⁻¹`
* `V pi = (1 - γ P_pi)⁻¹ r_pi`
* `Q pi (s, a) = r (s, a) + γ ∑ s', P (s, a) s' * V pi s'`
* `J pi = p₀ ⬝ V pi`
* `visitation pi = (1 - γ) p₀ᵀ (1 - γ P_pi)⁻¹`, the normalized discounted state visitation
* `occupancy pi (s, a) = visitation pi s * pi s a`

Main result (`PolicyFamily.hasGradientAt_J`):
`∇ J(θ) = (1 - γ)⁻¹ ∑_{s,a} occupancy θ (s, a) * Q θ (s, a) • ψ θ s a`.
-/

open Real Finset Matrix StochasticMatrix RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace ReinforcementLearning

universe u
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable {A : Type u} [Fintype A]
variable {n : ℕ}

variable (M : TabularMDP (S := S) (A := A))

section FixedPolicy

variable (pi : S → A → ℝ)

noncomputable def TabularMDP.resolvent : Matrix S S ℝ :=
  (1 - M.γ • M.stateMat pi)⁻¹

noncomputable def TabularMDP.V : S → ℝ :=
  M.resolvent pi *ᵥ M.stateReward pi

noncomputable def TabularMDP.Q (sa : S × A) : ℝ :=
  M.r sa + M.γ * ∑ s', M.P sa s' * M.V pi s'

noncomputable def TabularMDP.J : ℝ :=
  M.p₀ ⬝ᵥ M.V pi

noncomputable def TabularMDP.visitation : S → ℝ :=
  (1 - M.γ) • (M.p₀ ᵥ* M.resolvent pi)

noncomputable def TabularMDP.occupancy (sa : S × A) : ℝ :=
  M.visitation pi sa.1 * pi sa.1 sa.2

variable {pi}

/-- `1 - γ P_pi` is invertible since `P_pi` is row stochastic and `γ < 1`. -/
lemma TabularMDP.isUnit_one_sub_smul_stateMat (hpi : ∀ s, StochasticVec (pi s)) :
  IsUnit (1 - M.γ • M.stateMat pi) := by
  have hP := M.rowStochastic_stateMat hpi
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hfix : ∀ s, v s = M.γ * ∑ s', M.stateMat pi s s' * v s' := by
    intro s
    have h := congrFun hv s
    simp only [mulVec, dotProduct, Pi.zero_apply, sub_apply, smul_apply, smul_eq_mul,
      sub_mul, sum_sub_distrib, one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq,
      mem_univ, if_true, mul_assoc, ← mul_sum] at h
    linarith
  obtain ⟨s₀, -, hs₀⟩ := exists_max_image univ (fun s => |v s|) univ_nonempty
  have hle : |v s₀| ≤ M.γ * |v s₀| := by
    calc |v s₀| = M.γ * |∑ s', M.stateMat pi s₀ s' * v s'| := by
          rw [hfix s₀, abs_mul, abs_of_nonneg M.hγ.1]
      _ ≤ M.γ * ∑ s', M.stateMat pi s₀ s' * |v s₀| := by
          refine mul_le_mul_of_nonneg_left ?_ M.hγ.1
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s' _ => ?_)
          rw [abs_mul, abs_of_nonneg ((hP.stochastic s₀).nonneg s')]
          exact mul_le_mul_of_nonneg_left (hs₀ s' (mem_univ _))
            ((hP.stochastic s₀).nonneg s')
      _ = M.γ * |v s₀| := by rw [← sum_mul, (hP.stochastic s₀).rowsum, one_mul]
  have h0 : |v s₀| = 0 := by
    have := M.hγ.2
    have := abs_nonneg (v s₀)
    nlinarith
  funext s
  exact abs_eq_zero.mp (le_antisymm (h0 ▸ hs₀ s (mem_univ _)) (abs_nonneg _))

lemma TabularMDP.isUnit_det (hpi : ∀ s, StochasticVec (pi s)) :
  IsUnit (1 - M.γ • M.stateMat pi).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (M.isUnit_one_sub_smul_stateMat hpi)

lemma TabularMDP.one_sub_mul_resolvent (hpi : ∀ s, StochasticVec (pi s)) :
  (1 - M.γ • M.stateMat pi) * M.resolvent pi = 1 :=
  mul_nonsing_inv _ (M.isUnit_det hpi)

lemma TabularMDP.resolvent_mul_one_sub (hpi : ∀ s, StochasticVec (pi s)) :
  M.resolvent pi * (1 - M.γ • M.stateMat pi) = 1 :=
  nonsing_inv_mul _ (M.isUnit_det hpi)

/-- Entrywise form of `R = 1 + γ P R`. -/
lemma TabularMDP.resolvent_apply (hpi : ∀ s, StochasticVec (pi s)) (s j : S) :
  M.resolvent pi s j =
    (1 : Matrix S S ℝ) s j + M.γ * ∑ s', M.stateMat pi s s' * M.resolvent pi s' j := by
  have h := congrFun (congrFun (M.one_sub_mul_resolvent hpi) s) j
  simp only [sub_apply, smul_apply, smul_eq_mul, mul_apply, sub_mul, sum_sub_distrib,
    one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true, mul_assoc,
    ← mul_sum] at h
  rw [one_apply]
  linarith

omit [DecidableEq S] in
/-- Minimum principle: a solution of `u = b + γ P u` with `b ≥ 0` is nonnegative. -/
lemma TabularMDP.nonneg_of_eq_add (hpi : ∀ s, StochasticVec (pi s)) {u b : S → ℝ}
  (hb : ∀ s, 0 ≤ b s) (hu : ∀ s, u s = b s + M.γ * ∑ s', M.stateMat pi s s' * u s') :
  ∀ s, 0 ≤ u s := by
  have hP := M.rowStochastic_stateMat hpi
  obtain ⟨s₀, -, hs₀⟩ := exists_min_image univ u univ_nonempty
  suffices h : 0 ≤ u s₀ from fun s => h.trans (hs₀ s (mem_univ _))
  have hge : u s₀ ≤ ∑ s', M.stateMat pi s₀ s' * u s' := by
    calc u s₀ = ∑ s', M.stateMat pi s₀ s' * u s₀ := by
          rw [← sum_mul, (hP.stochastic s₀).rowsum, one_mul]
      _ ≤ ∑ s', M.stateMat pi s₀ s' * u s' :=
          sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hs₀ s' (mem_univ _))
            ((hP.stochastic s₀).nonneg s')
  have h1 := hu s₀
  have h2 := hb s₀
  have h3 := mul_le_mul_of_nonneg_left hge M.hγ.1
  have := M.hγ.2
  by_contra hneg
  push_neg at hneg
  nlinarith

lemma TabularMDP.resolvent_nonneg (hpi : ∀ s, StochasticVec (pi s)) (s j : S) :
  0 ≤ M.resolvent pi s j := by
  refine M.nonneg_of_eq_add hpi (u := fun s => M.resolvent pi s j)
    (b := fun s => (1 : Matrix S S ℝ) s j) (fun s => ?_) (fun s => M.resolvent_apply hpi s j) s
  by_cases h : s = j <;> simp [one_apply, h]

/-- Rows of the resolvent sum to `(1 - γ)⁻¹`. -/
lemma TabularMDP.sum_resolvent (hpi : ∀ s, StochasticVec (pi s)) (s : S) :
  ∑ j, M.resolvent pi s j = (1 - M.γ)⁻¹ := by
  have hP := M.rowStochastic_stateMat hpi
  have hγ := M.hγ
  set c := (1 - M.γ)⁻¹
  have hc : c = 1 + M.γ * c := by
    simp only [c]
    field_simp [show (1 - M.γ) ≠ 0 by linarith]
  have hu : ∀ s, ∑ j, M.resolvent pi s j =
      1 + M.γ * ∑ s', M.stateMat pi s s' * ∑ j, M.resolvent pi s' j := by
    intro s
    simp_rw [M.resolvent_apply hpi s, sum_add_distrib, ← mul_sum, mul_sum]
    rw [sum_comm]
    simp [one_apply]
  have hw : ∀ s, (∑ j, M.resolvent pi s j - c) =
      0 + M.γ * ∑ s', M.stateMat pi s s' * (∑ j, M.resolvent pi s' j - c) := by
    intro s
    have hrow : ∑ s', M.stateMat pi s s' = 1 := (hP.stochastic s).rowsum
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hrow, one_mul, zero_add]
    rw [hu s]
    linarith
  have hw' : ∀ s, (c - ∑ j, M.resolvent pi s j) =
      0 + M.γ * ∑ s', M.stateMat pi s s' * (c - ∑ j, M.resolvent pi s' j) := by
    intro s
    have h := hw s
    simp only [mul_sub, sum_sub_distrib, zero_add] at h ⊢
    linarith
  have h1 := M.nonneg_of_eq_add hpi (fun _ => le_refl 0) hw s
  have h2 := M.nonneg_of_eq_add hpi (fun _ => le_refl 0) hw' s
  linarith

lemma TabularMDP.bellman (hpi : ∀ s, StochasticVec (pi s)) :
  M.V pi = M.stateReward pi + M.γ • (M.stateMat pi *ᵥ M.V pi) := by
  have h : (1 - M.γ • M.stateMat pi) *ᵥ M.V pi = M.stateReward pi := by
    rw [TabularMDP.V, mulVec_mulVec, M.one_sub_mul_resolvent hpi, one_mulVec]
  rw [sub_mulVec, one_mulVec, smul_mulVec_assoc] at h
  rw [← h]
  abel

lemma TabularMDP.bellman_apply (hpi : ∀ s, StochasticVec (pi s)) (s : S) :
  M.V pi s = M.stateReward pi s + M.γ * ∑ s', M.stateMat pi s s' * M.V pi s' := by
  have h := congrFun (M.bellman hpi) s
  simpa [mulVec, dotProduct] using h

lemma TabularMDP.V_eq_sum_Q (hpi : ∀ s, StochasticVec (pi s)) (s : S) :
  M.V pi s = ∑ a, pi s a * M.Q pi (s, a) := by
  rw [M.bellman_apply hpi s]
  simp only [TabularMDP.Q, TabularMDP.stateReward, TabularMDP.stateMat, Matrix.of_apply,
    mul_add, sum_add_distrib, mul_sum, sum_mul]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun s' _ => ?_
  ring

lemma TabularMDP.stochastic_visitation (hpi : ∀ s, StochasticVec (pi s)) :
  StochasticVec (M.visitation pi) := by
  have hγ := M.hγ
  constructor
  · intro s'
    simp only [TabularMDP.visitation, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]
    exact mul_nonneg (by linarith)
      (sum_nonneg fun s _ => mul_nonneg (M.hp₀.nonneg s) (M.resolvent_nonneg hpi s s'))
  · simp only [TabularMDP.visitation, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]
    rw [← mul_sum, sum_comm]
    simp_rw [← mul_sum, M.sum_resolvent hpi, ← sum_mul, M.hp₀.rowsum, one_mul]
    field_simp [show (1 - M.γ) ≠ 0 by linarith]

lemma TabularMDP.stochastic_occupancy (hpi : ∀ s, StochasticVec (pi s)) :
  StochasticVec (M.occupancy pi) := by
  have hv := M.stochastic_visitation hpi
  constructor
  · intro sa
    exact mul_nonneg (hv.nonneg _) ((hpi _).nonneg _)
  · simp only [TabularMDP.occupancy, Fintype.sum_prod_type]
    simp_rw [← mul_sum, (hpi _).rowsum, mul_one, hv.rowsum]

end FixedPolicy

section Gradient

/-- Vector-valued version of `R (1 - γ P) = 1`: the unique solution of
`G = b + γ P G` is `G = R b`. -/
lemma TabularMDP.eq_resolvent_smul {pi : S → A → ℝ} (hpi : ∀ s, StochasticVec (pi s))
  {G b : S → E n} (hG : ∀ s, G s = b s + M.γ • ∑ s', M.stateMat pi s s' • G s') (s : S) :
  G s = ∑ s', M.resolvent pi s s' • b s' := by
  have hb : ∀ s', b s' = G s' - M.γ • ∑ k, M.stateMat pi s' k • G k :=
    fun s' => eq_sub_of_add_eq (hG s').symm
  have hR := congrFun (congrFun (M.resolvent_mul_one_sub hpi) s)
  simp only [mul_apply, sub_apply, smul_apply, smul_eq_mul, mul_sub, sum_sub_distrib,
    one_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true] at hR
  simp_rw [hb, smul_sub, sum_sub_distrib, smul_sum, smul_smul]
  rw [sum_comm (f := fun s' k => (M.resolvent pi s s' * (M.γ * M.stateMat pi s' k)) • G k)]
  rw [← sum_sub_distrib]
  simp_rw [← sum_smul]
  have : ∀ k, (M.resolvent pi s k -
      ∑ s', M.resolvent pi s s' * (M.γ * M.stateMat pi s' k)) = if s = k then 1 else 0 := by
    intro k
    rw [← hR k]
  simp_rw [← sub_smul, this, ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, if_true]

/-- The determinant of a matrix with differentiable entries is differentiable. -/
lemma differentiable_det_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : E n → Matrix ι ι ℝ} (h : ∀ i j, Differentiable ℝ fun θ => B θ i j) :
  Differentiable ℝ fun θ => (B θ).det := by
  intro θ
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finset_prod fun i _ => (h (σ i) i θ).hasFDerivAt).differentiableAt

/-- Cramer's rule: entries of the inverse of a matrix with differentiable entries and unit
determinant are differentiable. -/
lemma differentiable_inv_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : E n → Matrix ι ι ℝ} (h : ∀ i j, Differentiable ℝ fun θ => B θ i j)
  (hB : ∀ θ, IsUnit (B θ).det) (i j : ι) :
  Differentiable ℝ fun θ => (B θ)⁻¹ i j := by
  have hdet := differentiable_det_of_entries h
  have hadj : Differentiable ℝ fun θ => (B θ).adjugate i j := by
    simp only [adjugate_apply]
    apply differentiable_det_of_entries
    intro k l
    by_cases hk : k = j
    · simp [updateRow_apply, hk]
    · simpa [updateRow_apply, hk] using h k l
  intro θ
  simp only [Matrix.inv_def, smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((hdet θ).inv (hB θ).ne_zero).mul (hadj θ)

variable (pf : PolicyFamily (S := S) (A := A) n)

omit [DecidableEq S] [Nonempty S] in
lemma PolicyFamily.hasGradientAt_stateMat (θ : E n) (s s' : S) :
  HasGradientAt (fun θ => M.stateMat (pf.pi θ) s s')
    (∑ a, M.P (s, a) s' • (pf.pi θ s a • pf.score θ s a)) θ := by
  simp only [TabularMDP.stateMat, Matrix.of_apply]
  exact HasGradientAt.sum' fun a _ => (pf.hasGradientAt_pi θ s a).mul_const' _

omit [DecidableEq S] [Nonempty S] in
lemma PolicyFamily.hasGradientAt_stateReward (θ : E n) (s : S) :
  HasGradientAt (fun θ => M.stateReward (pf.pi θ) s)
    (∑ a, M.r (s, a) • (pf.pi θ s a • pf.score θ s a)) θ := by
  simp only [TabularMDP.stateReward]
  exact HasGradientAt.sum' fun a _ => (pf.hasGradientAt_pi θ s a).mul_const' _

lemma PolicyFamily.differentiable_resolvent (s j : S) :
  Differentiable ℝ fun θ => M.resolvent (pf.pi θ) s j := by
  refine differentiable_inv_of_entries (B := fun θ => 1 - M.γ • M.stateMat (pf.pi θ))
    (fun i k => ?_) (fun θ => M.isUnit_det (pf.stochastic θ)) s j
  simp only [sub_apply, smul_apply, smul_eq_mul]
  exact (differentiable_const _).sub ((differentiable_const _).mul
    fun θ => (pf.hasGradientAt_stateMat M θ i k).differentiableAt)

lemma PolicyFamily.differentiable_V (s : S) :
  Differentiable ℝ fun θ => M.V (pf.pi θ) s := by
  simp only [TabularMDP.V, mulVec, dotProduct]
  intro θ
  exact DifferentiableAt.fun_sum fun s' _ => (pf.differentiable_resolvent M s s' θ).mul
    (pf.hasGradientAt_stateReward M θ s').differentiableAt

/-- Per-state policy gradient: `∇ V(s) = ∑ s', (1 - γ P_θ)⁻¹ s s' * ∑ a, pi Q ψ`. -/
lemma PolicyFamily.hasGradientAt_V (θ : E n) (s : S) :
  HasGradientAt (fun θ => M.V (pf.pi θ) s)
    (∑ s', M.resolvent (pf.pi θ) s s' •
      ∑ a, (pf.pi θ s' a * M.Q (pf.pi θ) (s', a)) • pf.score θ s' a) θ := by
  set G : S → E n := fun s => gradient (fun θ => M.V (pf.pi θ) s) θ with hGdef
  have hG : ∀ s, HasGradientAt (fun θ => M.V (pf.pi θ) s) (G s) θ :=
    fun s => (pf.differentiable_V M s θ).hasGradientAt
  set b : S → E n := fun s' =>
    ∑ a, (pf.pi θ s' a * M.Q (pf.pi θ) (s', a)) • pf.score θ s' a with hbdef
  have hfix : ∀ s, G s = b s + M.γ • ∑ s', M.stateMat (pf.pi θ) s s' • G s' := by
    intro s
    have hfun : (fun θ => M.V (pf.pi θ) s) = fun θ => M.stateReward (pf.pi θ) s +
        M.γ * ∑ s', M.stateMat (pf.pi θ) s s' * M.V (pf.pi θ) s' :=
      funext fun θ => M.bellman_apply (pf.stochastic θ) s
    have hrhs := (pf.hasGradientAt_stateReward M θ s).add'
      ((HasGradientAt.sum' (u := univ) fun s' _ =>
        (pf.hasGradientAt_stateMat M θ s s').mul' (hG s')).const_mul' M.γ)
    rw [← hfun] at hrhs
    rw [(hG s).unique hrhs]
    simp only [hbdef, TabularMDP.Q, smul_add, sum_add_distrib, mul_add, add_smul]
    have h1 : ∑ a, M.r (s, a) • pf.pi θ s a • pf.score θ s a =
        ∑ a, (pf.pi θ s a * M.r (s, a)) • pf.score θ s a :=
      sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]
    have h2 : M.γ • ∑ s', M.V (pf.pi θ) s' • ∑ a, M.P (s, a) s' • pf.pi θ s a • pf.score θ s a =
        ∑ a, (pf.pi θ s a * (M.γ * ∑ s', M.P (s, a) s' * M.V (pf.pi θ) s')) •
          pf.score θ s a := by
      simp_rw [smul_sum, smul_smul, mul_sum, sum_smul]
      rw [sum_comm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun s' _ => ?_
      congr 1
      ring
    rw [h1, h2]
    abel
  rw [← M.eq_resolvent_smul (pf.stochastic θ) hfix s]
  exact hG s

lemma PolicyFamily.differentiable_J :
  Differentiable ℝ fun θ => M.J (pf.pi θ) := by
  simp only [TabularMDP.J, dotProduct]
  intro θ
  exact DifferentiableAt.fun_sum fun s _ =>
    (differentiableAt_const _).mul (pf.differentiable_V M s θ)

/-- The discounted objective is bounded above, uniformly over all policies. -/
lemma PolicyFamily.bddAbove_J : BddAbove (Set.range fun θ => M.J (pf.pi θ)) := by
  obtain ⟨C, hC⟩ := (Set.finite_range M.r).bddAbove
  have hr : ∀ sa, M.r sa ≤ C := fun sa => hC ⟨sa, rfl⟩
  have hγ : 0 < 1 - M.γ := by linarith [M.hγ.2]
  refine ⟨(1 - M.γ)⁻¹ * C, ?_⟩
  rintro _ ⟨θ, rfl⟩
  have hpi := pf.stochastic θ
  have hrpi : ∀ s, M.stateReward (pf.pi θ) s ≤ C := by
    intro s
    calc M.stateReward (pf.pi θ) s ≤ ∑ a, pf.pi θ s a * C :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hr _) ((hpi s).nonneg a)
      _ = C := by rw [← sum_mul, (hpi s).rowsum, one_mul]
  have hV : ∀ s, M.V (pf.pi θ) s ≤ (1 - M.γ)⁻¹ * C := by
    intro s
    calc M.V (pf.pi θ) s = ∑ s', M.resolvent (pf.pi θ) s s' * M.stateReward (pf.pi θ) s' := rfl
      _ ≤ ∑ s', M.resolvent (pf.pi θ) s s' * C :=
          sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hrpi s')
            (M.resolvent_nonneg hpi s s')
      _ = (1 - M.γ)⁻¹ * C := by rw [← sum_mul, M.sum_resolvent hpi]
  calc M.J (pf.pi θ) = ∑ s, M.p₀ s * M.V (pf.pi θ) s := rfl
    _ ≤ ∑ s, M.p₀ s * ((1 - M.γ)⁻¹ * C) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hV s) (M.hp₀.nonneg s)
    _ = (1 - M.γ)⁻¹ * C := by rw [← sum_mul, M.hp₀.rowsum, one_mul]

/-- **Policy gradient theorem** (discounted reward, finite MDP). -/
theorem PolicyFamily.hasGradientAt_J (θ : E n) :
  HasGradientAt (fun θ => M.J (pf.pi θ))
    ((1 - M.γ)⁻¹ • ∑ sa, (M.occupancy (pf.pi θ) sa * M.Q (pf.pi θ) sa) •
      pf.score θ sa.1 sa.2) θ := by
  have hγ : (1 - M.γ) ≠ 0 := by linarith [M.hγ.2]
  have h := HasGradientAt.sum' (u := univ) fun s _ =>
    (pf.hasGradientAt_V M θ s).const_mul' (M.p₀ s)
  simp only [TabularMDP.J, dotProduct]
  convert h using 1
  simp only [TabularMDP.occupancy, TabularMDP.visitation, Fintype.sum_prod_type,
    Pi.smul_apply, smul_eq_mul, vecMul, dotProduct, smul_sum, smul_smul]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun s' _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_smul]
  congr 1
  rw [eq_inv_mul_iff_mul_eq₀ hγ]
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun s _ => ?_
  ring

/-- Subtracting any state-dependent baseline leaves the gradient unchanged. -/
theorem PolicyFamily.hasGradientAt_J_baseline (b : S → ℝ) (θ : E n) :
  HasGradientAt (fun θ => M.J (pf.pi θ))
    ((1 - M.γ)⁻¹ • ∑ sa, (M.occupancy (pf.pi θ) sa * (M.Q (pf.pi θ) sa - b sa.1)) •
      pf.score θ sa.1 sa.2) θ := by
  convert pf.hasGradientAt_J M θ using 2
  simp only [mul_sub, sub_smul, sum_sub_distrib, sub_eq_self]
  simp only [TabularMDP.occupancy, Fintype.sum_prod_type]
  refine sum_eq_zero fun s _ => ?_
  have : ∀ a, M.visitation (pf.pi θ) s * pf.pi θ s a * b s =
      (M.visitation (pf.pi θ) s * b s) * pf.pi θ s a := fun a => by ring
  simp_rw [this, ← smul_smul, ← smul_sum, pf.sum_smul_score_eq_zero, smul_zero]

end Gradient

end ReinforcementLearning
