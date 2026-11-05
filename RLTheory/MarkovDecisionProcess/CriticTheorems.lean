/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TraceMoments

/-!
# The critic theorems of `docs/actor-critic-rates.md`

Section 4 of the write-up compares actor-critic with actor-only through stationary
expectations of the state-action chain with restarts and of its eligibility traces. This file
formalizes those identities in a finite model.

* `ScoreChain`: a chain on `Bool × S × A` (restart flag, state, action) whose next action is
  drawn from the policy given the next state, `Q y (f', s', a') = kap y f' s' · pol s' a'`.
  The restart chain of the write-up is the case `kap y false s' = γ P(s' | s, a)`,
  `kap y true s' = (1 - γ) p₀(s')`.
* Trace moments `m y = E[z_k 1{Y_k = y}]` enter through their recursion
  `m y' = ν y' φ y' + λ c y' Σ_y Q y y' m y`; `ScoreChain.tendsto_traceMoment` derives it from
  the process: the moments of the trace along the chain converge to a solution.
* `restart_contraction`, `tendsto_law_restart`, `tendsto_traceMoment_of_restart`: for the restart
  chain the contraction holds, the law converges to a stationary `ν`, and the trace moments
  converge, from the model alone.
* `exists_poisson_U`, `exists_poisson_h`, `centering_eq_noise_mean`,
  `tendsto_secondMoment_of_restart_noise_centered`: the Poisson solutions of Lemma 4.4 exist
  for the restart chain (the second when the noise is centered), so the trace-noise covariance
  theorem holds along the restart chain with no hypothesis beyond the model and centering.
* `ScoreChain.sum_Q_c_eq_zero`, `ScoreChain.sum_mul_trace_eq`: the two facts behind all proofs,
  both consequences of the score having mean zero over actions.
* `compatible_critic_direction`, `compatible_critic_noise`: Theorem 4.2.
* `value_critic_fixed_point`, `value_critic_direction`: Theorem 4.4.
* `td1_critic_direction`, `td1_selector`, `td1_noise_coboundary`: Theorem 4.1.
* `td0_gain`, `sum_carry_centered`, `td0_noise_split`: the stationary identities behind
  Theorem 4.5 (TD(0) with a tabular critic has smaller noise covariance than REINFORCE).
* `tendsto_secondMoment_of_coboundary`: noises that differ by a coboundary give the same
  asymptotic covariance.
-/

open Finset Real Filter Topology MeasureTheory RLTheory Matrix
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

variable {S Ac : Type*} [Fintype S] [Fintype Ac]

/-- A chain on (restart flag, state, action) in which the next action is drawn from the policy
given the next state. -/
structure ScoreChain (S Ac : Type*) where
  pol : S → Ac → ℝ
  kap : Bool × S × Ac → Bool → S → ℝ
  /-- The trace discount as a function of the flag and the state, for instance
  `1{not a restart}`; the trace parameter `λ` is kept separate. -/
  c : Bool → S → ℝ

namespace ScoreChain

variable (M : ScoreChain S Ac)

/-- The transition probabilities. -/
def Q (y y' : Bool × S × Ac) : ℝ := M.kap y y'.1 y'.2.1 * M.pol y'.2.1 y'.2.2

/-- The trace discount at a pair. -/
def cY (y : Bool × S × Ac) : ℝ := M.c y.1 y.2.1

/-- A function has mean zero over actions under the policy. -/
def MeanZero {X : Type*} [AddCommGroup X] [Module ℝ X] (F : Bool × S × Ac → X) : Prop :=
  ∀ f s, ∑ a, M.pol s a • F (f, s, a) = 0

lemma sum_prod3 {X : Type*} [AddCommMonoid X] (F : Bool × S × Ac → X) :
    ∑ y, F y = ∑ f, ∑ s, ∑ a, F (f, s, a) := by
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun f _ => by rw [Fintype.sum_prod_type]

/-- **The first fact.** If `F` has mean zero over actions, then `E[c(Y') F(Y') | Y = y] = 0`:
the next action is drawn afresh. -/
lemma sum_Q_c_eq_zero {X : Type*} [AddCommGroup X] [Module ℝ X] {F : Bool × S × Ac → X}
    (hF : M.MeanZero F) (y : Bool × S × Ac) : ∑ y', (M.Q y y' * M.cY y') • F y' = 0 := by
  rw [sum_prod3]
  refine sum_eq_zero fun f _ => sum_eq_zero fun s _ => ?_
  have : ∑ a, (M.Q y (f, s, a) * M.cY (f, s, a)) • F (f, s, a) =
      (M.kap y f s * M.c f s) • ∑ a, M.pol s a • F (f, s, a) := by
    rw [smul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [Q, cY, smul_smul]
    congr 1
    ring
  rw [this, hF f s, smul_zero]

/-- A stationary law factorizes as `ν (f, s, a) = νₛ (f, s) π(a | s)`. -/
lemma stationary_factor {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    (f : Bool) (s : S) (a : Ac) :
    ν (f, s, a) = (∑ y, ν y * M.kap y f s) * M.pol s a := by
  rw [← hν (f, s, a), sum_mul]
  exact sum_congr rfl fun y _ => by simp only [Q]; ring

/-- Under a stationary law, a function with mean zero over actions, multiplied by a function of
the flag and the state, has mean zero. -/
lemma sum_stationary_eq_zero {X : Type*} [AddCommGroup X] [Module ℝ X]
    {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    {F : Bool × S × Ac → X} (hF : M.MeanZero F) : ∑ y, ν y • F y = 0 := by
  rw [sum_prod3]
  refine sum_eq_zero fun f _ => sum_eq_zero fun s _ => ?_
  have : ∑ a, ν (f, s, a) • F (f, s, a) = (∑ y, ν y * M.kap y f s) • ∑ a, M.pol s a • F (f, s, a) := by
    rw [smul_sum]
    exact sum_congr rfl fun a _ => by rw [M.stationary_factor hν, MulAction.mul_smul]
  rw [this, hF f s, smul_zero]

/-- The trace-moment recursion `m y' = ν y' φ y' + λ c y' Σ_y Q y y' m y`. -/
def TraceMoment {p : ℕ} (ν : Bool × S × Ac → ℝ) (lam : ℝ) (φ : Bool × S × Ac → E p)
    (m : Bool × S × Ac → E p) : Prop :=
  ∀ y', m y' = ν y' • φ y' + (lam * M.cY y') • ∑ y, M.Q y y' • m y

/-- **The second fact.** If `F` has mean zero over actions, then `E[F(Y_k) z_k] = E[F(Y_k) φ(Y_k)]`:
the part of the trace carried over from the past does not see the current action. -/
lemma sum_mul_trace_eq {p : ℕ} {ν : Bool × S × Ac → ℝ} {lam : ℝ} {φ m : Bool × S × Ac → E p}
    (hm : M.TraceMoment ν lam φ m) {F : Bool × S × Ac → ℝ} (hF : M.MeanZero F) :
    ∑ y, F y • m y = ∑ y, (ν y * F y) • φ y := by
  have e : ∀ y', F y' • m y' = (ν y' * F y') • φ y'
      + ∑ y, (lam * ((M.Q y y' * M.cY y') * F y')) • m y := by
    intro y'
    conv_lhs => rw [hm y']
    rw [smul_add, smul_smul, smul_sum]
    congr 1
    · rw [mul_comm]
    · rw [smul_sum]
      refine sum_congr rfl fun y _ => ?_
      rw [smul_smul, smul_smul]
      congr 1
      ring
  have hsplit : ∑ y', F y' • m y' = ∑ y', (ν y' * F y') • φ y'
      + lam • ∑ y, (∑ y', (M.Q y y' * M.cY y') • F y') • m y := by
    rw [sum_congr rfl fun y' _ => e y', sum_add_distrib, sum_comm (s := univ) (t := univ)]
    congr 1
    rw [smul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [smul_smul, ← sum_smul, mul_sum]
    congr 1
  rw [hsplit]
  simp only [M.sum_Q_c_eq_zero hF, zero_smul, sum_const_zero, smul_zero, add_zero]

/-- `E[z_k d_k]` for a TD error `d (Y_k, Y_{k+1})`: `Σ_y Σ_{y'} Q y y' d y y' m y`. -/
noncomputable def tdSum {p : ℕ} (m : Bool × S × Ac → E p) (d : Bool × S × Ac → Bool × S × Ac → ℝ) : E p :=
  ∑ y, ∑ y', (M.Q y y' * d y y') • m y

/-- The TD error of a critic with value estimate `v`: `d = g + c' v' - v`. -/
def tdErr (g v : Bool × S × Ac → ℝ) (y y' : Bool × S × Ac) : ℝ := g y + M.cY y' * v y' - v y

lemma tdSum_eq {p : ℕ} (m : Bool × S × Ac → E p) (d : Bool × S × Ac → Bool × S × Ac → ℝ) :
    M.tdSum m d = ∑ y, (∑ y', M.Q y y' * d y y') • m y := by
  unfold tdSum
  exact sum_congr rfl fun y _ => by rw [sum_smul]

/-- `Σ_{y'} Q y y' (g y + c' v' - v y) = g y + Σ_{y'} Q y y' c' v' - v y` for a stochastic `Q`. -/
lemma sum_Q_tdErr (hQ : ∀ y, ∑ y', M.Q y y' = 1) (g v : Bool × S × Ac → ℝ) (y : Bool × S × Ac) :
    ∑ y', M.Q y y' * M.tdErr g v y y' = g y + ∑ y', M.Q y y' * M.cY y' * v y' - v y := by
  simp only [tdErr, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul, hQ y, one_mul]
  congr 1
  congr 1
  exact sum_congr rfl fun y' _ => by ring

omit [Fintype S] in
lemma meanZero_inner {n : ℕ} {ψ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ) (w : E n) :
    M.MeanZero fun y => ⟪ψ y, w⟫ := by
  intro f s
  have := congrArg (fun x => ⟪x, w⟫) (hψ f s)
  simp only [sum_inner, inner_smul_left, inner_zero_left] at this
  simpa [smul_eq_mul] using this

/-! ### Theorem 4.2: the compatible critic -/

/-- With the compatible features `φ = ψ`, the TD mean is `E[z d] = E[z g] - C r` with
`C r = E[⟪ψ, r⟫ ψ]`: the TD matrix is `-C` for every `λ`. -/
theorem compatible_tdSum (hQ : ∀ y, ∑ y', M.Q y y' = 1) {n : ℕ} {ψ : Bool × S × Ac → E n}
    (hψ : M.MeanZero ψ) {ν : Bool × S × Ac → ℝ} {lam : ℝ} {m : Bool × S × Ac → E n}
    (hm : M.TraceMoment ν lam ψ m) (g : Bool × S × Ac → ℝ) (r : E n) :
    M.tdSum m (M.tdErr g fun y => ⟪ψ y, r⟫) =
      ∑ y, g y • m y - ∑ y, ν y • (⟪ψ y, r⟫ • ψ y) := by
  rw [tdSum_eq]
  simp only [M.sum_Q_tdErr hQ]
  have h0 : ∀ y, ∑ y', M.Q y y' * M.cY y' * ⟪ψ y', r⟫ = 0 := fun y => by
    have := M.sum_Q_c_eq_zero (M.meanZero_inner hψ r) y
    simpa [smul_eq_mul] using this
  simp only [h0, add_zero, sub_smul, sum_sub_distrib]
  congr 1
  rw [M.sum_mul_trace_eq hm (M.meanZero_inner hψ r)]
  exact sum_congr rfl fun y _ => by rw [smul_smul, mul_comm]

/-- **Theorem 4.2 (direction).** If the compatible critic is at its TD fixed point
`E[z d] = 0`, the actor's mean direction `C r = E[⟪ψ, r⟫ ψ]` equals the actor-only direction
`E[g z]` with the same trace. -/
theorem compatible_critic_direction (hQ : ∀ y, ∑ y', M.Q y y' = 1) {n : ℕ}
    {ψ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ) {ν : Bool × S × Ac → ℝ} {lam : ℝ}
    {m : Bool × S × Ac → E n} (hm : M.TraceMoment ν lam ψ m) (g : Bool × S × Ac → ℝ) (r : E n)
    (hfix : M.tdSum m (M.tdErr g fun y => ⟪ψ y, r⟫) = 0) :
    ∑ y, ν y • (⟪ψ y, r⟫ • ψ y) = ∑ y, g y • m y := by
  rw [M.compatible_tdSum hQ hψ hm g r] at hfix
  exact (sub_eq_zero.mp hfix).symm

/-- **Theorem 4.2 (noise).** The TD matrix of the compatible critic is `-C`, so the effective
noise `V - C A_c⁻¹ W` equals `V + W`; at the root `r̂ = 0`, where `V = 0`, it is the critic's
`W = g z`, the actor-only noise. -/
theorem compatible_critic_tdMatrix (hQ : ∀ y, ∑ y', M.Q y y' = 1) {n : ℕ}
    {ψ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ) {ν : Bool × S × Ac → ℝ} {lam : ℝ}
    {m : Bool × S × Ac → E n} (hm : M.TraceMoment ν lam ψ m) (r : E n) :
    M.tdSum m (M.tdErr (fun _ => 0) fun y => ⟪ψ y, r⟫) = -∑ y, ν y • (⟪ψ y, r⟫ • ψ y) := by
  rw [M.compatible_tdSum hQ hψ hm]
  simp

/-! ### Theorem 4.4: critics that represent the value function -/

/-- **Theorem 4.4 (fixed point).** Let the critic features be the score `ψ` and state features
`φ̄`, and let `V = ⟪φ̄, u⟫` satisfy the Bellman equation in the form that the advantage
`A = g + E[c' V'] - V` has mean zero over actions. If `w` is the least-squares fit of `A` on the
score, `E[(A - ⟪ψ, w⟫) ψ] = 0`, then `(w, u)` solves both blocks of the TD(`λ`) equations, for
every `λ`. -/
theorem value_critic_fixed_point (hQ : ∀ y, ∑ y', M.Q y y' = 1) {n q : ℕ}
    {ψ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ) (φb : S → E q) {ν : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') {lam : ℝ} {mψ : Bool × S × Ac → E n}
    {me : Bool × S × Ac → E q} (hmψ : M.TraceMoment ν lam ψ mψ)
    (hme : M.TraceMoment ν lam (fun y => φb y.2.1) me) (g : Bool × S × Ac → ℝ) (w : E n)
    (u : E q)
    (hA : M.MeanZero fun y => g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫ - ⟪φb y.2.1, u⟫)
    (hw : ∑ y, ν y • ((g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫ - ⟪φb y.2.1, u⟫
      - ⟪ψ y, w⟫) • ψ y) = 0) :
    M.tdSum mψ (M.tdErr g fun y => ⟪ψ y, w⟫ + ⟪φb y.2.1, u⟫) = 0 ∧
      M.tdSum me (M.tdErr g fun y => ⟪ψ y, w⟫ + ⟪φb y.2.1, u⟫) = 0 := by
  set A := fun y => g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫ - ⟪φb y.2.1, u⟫ with hAdef
  set e := fun y => A y - ⟪ψ y, w⟫ with hedef
  have he : M.MeanZero e := by
    intro f s
    have h1 := hA f s
    have h2 := M.meanZero_inner hψ w f s
    simp only [hedef, smul_sub, sum_sub_distrib]
    rw [h1, h2, sub_zero]
  have hd : ∀ y, ∑ y', M.Q y y' * M.tdErr g (fun y => ⟪ψ y, w⟫ + ⟪φb y.2.1, u⟫) y y' = e y := by
    intro y
    rw [M.sum_Q_tdErr hQ]
    have h0 : ∑ y', M.Q y y' * M.cY y' * ⟪ψ y', w⟫ = 0 := by
      have := M.sum_Q_c_eq_zero (M.meanZero_inner hψ w) y
      simpa [smul_eq_mul] using this
    simp only [mul_add, sum_add_distrib, h0, zero_add, hedef, hAdef]
    ring
  constructor
  · rw [tdSum_eq]
    simp only [hd]
    rw [M.sum_mul_trace_eq hmψ he]
    rw [← hw]
    exact sum_congr rfl fun y _ => by rw [smul_smul, mul_comm]
  · rw [tdSum_eq]
    simp only [hd]
    rw [M.sum_mul_trace_eq hme he]
    have hF : M.MeanZero fun y => e y • φb y.2.1 := by
      intro f s
      have := he f s
      simp only [smul_smul]
      rw [← sum_smul]
      simp only [smul_eq_mul] at this
      rw [this, zero_smul]
    have := M.sum_stationary_eq_zero hν hF
    rw [← this]
    exact sum_congr rfl fun y _ => by rw [smul_smul]

/-- **Theorem 4.4 (direction).** At that fixed point the actor's mean direction is
`E[(⟪ψ, w⟫ + V) ψ] = E[Q ψ]`, the policy gradient, for every `λ`. -/
theorem value_critic_direction {n q : ℕ} {ψ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ)
    (φb : S → E q) {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    (g : Bool × S × Ac → ℝ) (w : E n) (u : E q)
    (hw : ∑ y, ν y • ((g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫ - ⟪φb y.2.1, u⟫
      - ⟪ψ y, w⟫) • ψ y) = 0) :
    ∑ y, ν y • ((⟪ψ y, w⟫ + ⟪φb y.2.1, u⟫) • ψ y) =
      ∑ y, ν y • ((g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫) • ψ y) := by
  have hV : ∑ y, ν y • (⟪φb y.2.1, u⟫ • ψ y) = 0 := by
    refine M.sum_stationary_eq_zero hν fun f s => ?_
    have := hψ f s
    simp only [smul_smul]
    simp_rw [mul_comm (M.pol s _), ← smul_smul]
    rw [← smul_sum, this, smul_zero]
  have e : ∀ y, ν y • ((g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫) • ψ y) =
      ν y • ((g y + ∑ y', M.Q y y' * M.cY y' * ⟪φb y'.2.1, u⟫ - ⟪φb y.2.1, u⟫ - ⟪ψ y, w⟫) • ψ y)
        + ν y • ((⟪ψ y, w⟫ + ⟪φb y.2.1, u⟫) • ψ y) := by
    intro y
    rw [← smul_add, ← add_smul]
    congr 2
    ring
  simp only [e, sum_add_distrib, hw, zero_add]

/-! ### Theorem 4.1: the TD(1) critic -/

/-- With `λ = 1`, `E[c(Y_{k+1}) F(Y_{k+1}) z_k] = E[F(Y_k) (z_k - φ(Y_k))]`. -/
lemma td1_shift {p : ℕ} {ν : Bool × S × Ac → ℝ} {φ m : Bool × S × Ac → E p}
    (hm : M.TraceMoment ν 1 φ m) (F : Bool × S × Ac → ℝ) :
    ∑ y, (∑ y', M.Q y y' * M.cY y' * F y') • m y = ∑ y', F y' • (m y' - ν y' • φ y') := by
  have e : ∀ y', m y' - ν y' • φ y' = M.cY y' • ∑ y, M.Q y y' • m y := fun y' => by
    rw [hm y', one_mul, add_sub_cancel_left]
  simp only [e, smul_sum, smul_smul, sum_smul]
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun y' _ => by ring_nf

/-- With `λ = 1` and `q` the expected reward-to-go, `q = g + E[c' q']`, the TD mean of a critic
with value estimate `v` is `E[z d] = E[(q - v) φ]`: TD(1) is least-squares regression of the
returns. -/
theorem td1_tdSum (hQ : ∀ y, ∑ y', M.Q y y' = 1) {p : ℕ} {ν : Bool × S × Ac → ℝ}
    {φ m : Bool × S × Ac → E p} (hm : M.TraceMoment ν 1 φ m) (g q v : Bool × S × Ac → ℝ)
    (hq : ∀ y, q y = g y + ∑ y', M.Q y y' * M.cY y' * q y') :
    M.tdSum m (M.tdErr g v) = ∑ y, (ν y * (q y - v y)) • φ y := by
  rw [tdSum_eq]
  simp only [M.sum_Q_tdErr hQ]
  have hg : ∀ y, g y = q y - ∑ y', M.Q y y' * M.cY y' * q y' := fun y => by rw [hq y]; ring
  have e : ∀ y, (g y + ∑ y', M.Q y y' * M.cY y' * v y' - v y) • m y =
      (q y - v y) • m y - (∑ y', M.Q y y' * M.cY y' * q y') • m y
        + (∑ y', M.Q y y' * M.cY y' * v y') • m y := by
    intro y; rw [hg y, ← sub_smul, ← add_smul]; congr 1; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, M.td1_shift hm]
  simp only [smul_sub, sub_smul, sum_sub_distrib, smul_smul]
  have : ∀ y, (ν y * (q y - v y)) • φ y = (q y * ν y) • φ y - (v y * ν y) • φ y := fun y => by
    rw [← sub_smul]; congr 1; ring
  simp only [this, sum_sub_distrib]
  abel

/-- **Theorem 4.1 (direction).** If a TD(1) critic with features `(ψ, φ̄)` is at its fixed
point, its score block `E[z^ψ d] = 0` alone gives that the actor's mean direction `E[v ψ]` equals
the actor-only (REINFORCE) direction `E[g z^ψ] = E[q ψ]`, whatever the extra features. -/
theorem td1_critic_direction (hQ : ∀ y, ∑ y', M.Q y y' = 1) {n : ℕ} {ν : Bool × S × Ac → ℝ}
    {ψ mψ : Bool × S × Ac → E n} (hmψ : M.TraceMoment ν 1 ψ mψ) (g q v : Bool × S × Ac → ℝ)
    (hq : ∀ y, q y = g y + ∑ y', M.Q y y' * M.cY y' * q y')
    (hfix : M.tdSum mψ (M.tdErr g v) = 0) :
    ∑ y, ν y • (v y • ψ y) = ∑ y, g y • mψ y := by
  have h1 := M.td1_tdSum hQ hmψ g q v hq
  have h2 := M.td1_tdSum hQ hmψ g q (fun _ => 0) hq
  rw [hfix] at h1
  have e2 : M.tdSum mψ (M.tdErr g fun _ => 0) = ∑ y, g y • mψ y := by
    rw [tdSum_eq]
    refine sum_congr rfl fun y _ => ?_
    rw [M.sum_Q_tdErr hQ]; simp
  rw [e2] at h2
  have hA : ∑ y, (ν y * (q y - v y)) • ψ y = ∑ y, (ν y * q y) • ψ y - ∑ y, ν y • (v y • ψ y) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun y _ => by rw [smul_smul, ← sub_smul]; congr 1; ring
  have hB : ∑ y, (ν y * (q y - 0)) • ψ y = ∑ y, (ν y * q y) • ψ y := by simp
  rw [h2, hB]
  rw [hA] at h1
  exact (sub_eq_zero.mp h1.symm).symm

/-- **Theorem 4.1 (selector).** The score block of the TD(1) matrix applied to `x` is `-C x`, so
`-C A_c⁻¹ W` is the score block of `W`. -/
theorem td1_selector (hQ : ∀ y, ∑ y', M.Q y y' = 1) {n : ℕ} {ν : Bool × S × Ac → ℝ}
    {ψ mψ : Bool × S × Ac → E n} (hmψ : M.TraceMoment ν 1 ψ mψ) (vx : Bool × S × Ac → ℝ) :
    M.tdSum mψ (M.tdErr (fun _ => 0) vx) = -∑ y, ν y • (vx y • ψ y) := by
  have := M.td1_tdSum hQ hmψ (fun _ => 0) (fun _ => 0) vx (fun y => by simp)
  rw [this, ← sum_neg_distrib]
  exact sum_congr rfl fun y _ => by rw [smul_smul, ← neg_smul]; congr 1; ring

/-! ### Theorem 4.5: the TD(0) critic with tabular state features -/

/-- The moment of the carried trace `B_k = c_k Z_{k-1}`: `E[B_k 1{Y_k = y}] = m y - ν y φ y`. -/
noncomputable def carry {p : ℕ} (ν : Bool × S × Ac → ℝ) (φ m : Bool × S × Ac → E p) (y : Bool × S × Ac) : E p :=
  m y - ν y • φ y

/-- The state marginal `Σ_{f,a} F (f, s, a)`. -/
def stateSum {X : Type*} [AddCommMonoid X] (F : Bool × S × Ac → X) (s : S) : X :=
  ∑ f, ∑ a, F (f, s, a)

/-- The conditional mean of the carried trace given the state, `b s = E[B_k | s_k = s]`. -/
noncomputable def carryMean {p : ℕ} (ν : Bool × S × Ac → ℝ) (φ m : Bool × S × Ac → E p) (s : S) :
    E p :=
  (stateSum ν s)⁻¹ • stateSum (carry ν φ m) s

/-- The weight of a continuing step into the state `s'`: `E[c_{k+1} 1{s_{k+1} = s'} | Y_k = y]`. -/
def into (y : Bool × S × Ac) (s' : S) : ℝ := ∑ f', ∑ a', M.Q y (f', s', a') * M.cY (f', s', a')

omit [Fintype S] [Fintype Ac] in
lemma carry_eq {p : ℕ} [Fintype S] [Fintype Ac] {ν : Bool × S × Ac → ℝ}
    {φ m : Bool × S × Ac → E p} (hm : M.TraceMoment ν 1 φ m) (y' : Bool × S × Ac) :
    carry ν φ m y' = M.cY y' • ∑ y, M.Q y y' • m y := by
  unfold carry
  rw [hm y', one_mul, add_sub_cancel_left]

/-- The carried trace does not see the current action: its moment factors through the policy. -/
lemma carry_factor {p : ℕ} {ν : Bool × S × Ac → ℝ} {φ m : Bool × S × Ac → E p}
    (hm : M.TraceMoment ν 1 φ m) (f : Bool) (s : S) (a : Ac) :
    carry ν φ m (f, s, a) = M.pol s a • (M.c f s • ∑ y, M.kap y f s • m y) := by
  rw [M.carry_eq hm, smul_sum, smul_sum, smul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [Q, cY, smul_smul]
  congr 1
  ring

/-- **The centering fact.** The carried trace minus its conditional mean given the state is
uncorrelated with every function of the state and the action:
`E[w(s_k, a_k) (B_k - b(s_k))] = 0`. -/
lemma sum_carry_centered {p : ℕ} {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    {φ m : Bool × S × Ac → E p} (hm : M.TraceMoment ν 1 φ m) (hpol : ∀ s, ∑ a, M.pol s a = 1)
    (hνS : ∀ s, stateSum ν s ≠ 0) (w : Bool × S × Ac → ℝ)
    (hw : ∀ f₁ f₂ s a, w (f₁, s, a) = w (f₂, s, a)) :
    ∑ y, w y • (carry ν φ m y - ν y • carryMean ν φ m y.2.1) = 0 := by
  set β : Bool → S → E p := fun f s => M.c f s • ∑ y, M.kap y f s • m y with hβ
  set α : Bool → S → ℝ := fun f s => ∑ y, ν y * M.kap y f s with hα
  have hc : ∀ f s a, carry ν φ m (f, s, a) = M.pol s a • β f s := fun f s a => M.carry_factor hm f s a
  have hn : ∀ f s a, ν (f, s, a) = α f s * M.pol s a := fun f s a => M.stationary_factor hν f s a
  have hmS : ∀ s, stateSum (carry ν φ m) s = ∑ f, β f s := fun s => by
    unfold stateSum
    refine sum_congr rfl fun f _ => ?_
    simp only [hc, ← sum_smul, hpol, one_smul]
  have hνs : ∀ s, stateSum ν s = ∑ f, α f s := fun s => by
    unfold stateSum
    refine sum_congr rfl fun f _ => ?_
    simp only [hn, ← mul_sum, hpol, mul_one]
  have h0 : ∀ s, ∑ f, (β f s - α f s • carryMean ν φ m s) = 0 := fun s => by
    rw [sum_sub_distrib, ← sum_smul, ← hνs, ← hmS, carryMean, smul_smul,
      mul_inv_cancel₀ (hνS s), one_smul, sub_self]
  rw [sum_prod3, sum_comm]
  refine sum_eq_zero fun s _ => ?_
  have e : ∀ f a, w (f, s, a) • (carry ν φ m (f, s, a) - ν (f, s, a) • carryMean ν φ m s) =
      (w (false, s, a) * M.pol s a) • (β f s - α f s • carryMean ν φ m s) := fun f a => by
    rw [hc, hn, hw f false]
    simp only [smul_sub, smul_smul]
    congr 2
    ring
  simp only [e]
  rw [sum_comm]
  refine sum_eq_zero fun a _ => ?_
  rw [← smul_sum, h0 s, smul_zero]

/-- **Theorem 4.5 (the gain).** For the TD(0) critic with features `(ψ, e_s)` at `r̂ = (0, V)`,
`-C A_c⁻¹ = (I, -K)` with `K = X T⁻¹`, where `T s s' = E[1{s_k = s}(c_{k+1} 1{s_{k+1} = s'} -
1{s_k = s'})]` and `X s' = E[ψ_k c_{k+1} 1{s_{k+1} = s'}]` (the term `E[ψ_k 1{s_k = s'}]`
vanishes when `ψ` has mean zero over actions). The columns of `K` are minus the conditional means of the REINFORCE carried trace:
`Σ_s T s s' b s = -X s'`, that is `K e_s = -E[c_k Z_{k-1} | s_k = s]`. This needs the step law
to depend on the pair only through the state and the action. -/
theorem td0_gain [DecidableEq S] {n : ℕ} {ν : Bool × S × Ac → ℝ} (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y')
    {ψ m : Bool × S × Ac → E n} (hm : M.TraceMoment ν 1 ψ m)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hνS : ∀ s, stateSum ν s ≠ 0)
    (hkap : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a)) (s' : S) :
    ∑ s, ((∑ f, ∑ a, ν (f, s, a) * M.into (f, s, a) s')
        - if s = s' then stateSum ν s else 0) • carryMean ν ψ m s
      = -∑ y, (ν y * M.into y s') • ψ y := by
  have hw : ∀ f₁ f₂ s a, M.into (f₁, s, a) s' = M.into (f₂, s, a) s' := fun f₁ f₂ s a => by
    simp only [into, Q, hkap f₁ f₂ s a]
  have hB := M.sum_carry_centered hν hm hpol hνS (fun y => M.into y s') hw
  simp only [sub_smul, sum_sub_distrib, ite_smul, zero_smul, sum_ite_eq', mem_univ, if_true]
  have hb : stateSum ν s' • carryMean ν ψ m s' = stateSum (carry ν ψ m) s' := by
    rw [carryMean, smul_smul, mul_inv_cancel₀ (hνS s'), one_smul]
  have hmy : ∀ y, ν y • ψ y + carry ν ψ m y = m y := fun y => by
    simp only [carry, add_sub_cancel]
  have hmS : stateSum (carry ν ψ m) s' = ∑ y, M.into y s' • (ν y • ψ y + carry ν ψ m y) := by
    simp only [hmy]
    unfold stateSum
    simp only [M.carry_eq hm, into, sum_smul, smul_sum, smul_smul]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun f' _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun a' _ => sum_congr rfl fun y _ => by rw [mul_comm]
  have hL : ∑ s, (∑ f, ∑ a, ν (f, s, a) * M.into (f, s, a) s') • carryMean ν ψ m s =
      ∑ y, (ν y * M.into y s') • carryMean ν ψ m y.2.1 := by
    rw [sum_prod3, sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_smul]
    exact sum_congr rfl fun f _ => by rw [sum_smul]
  rw [hb, hmS, hL]
  have e : ∀ y, (ν y * M.into y s') • carryMean ν ψ m y.2.1
      - M.into y s' • (ν y • ψ y + carry ν ψ m y) =
      -((ν y * M.into y s') • ψ y)
        - M.into y s' • (carry ν ψ m y - ν y • carryMean ν ψ m y.2.1) := by
    intro y
    simp only [smul_add, smul_sub, smul_smul]
    rw [mul_comm (M.into y s')]
    abel
  rw [← sum_sub_distrib, sum_congr rfl fun y _ => e y, sum_sub_distrib, hB, sub_zero,
    sum_neg_distrib]

/-! ### Lemma 4.6: the gain of the tabular TD(`λ`) critic -/

/-- A vector fixed point of a contracting transfer operator is zero:
if `d y' = (λ c y') Σ_y Q y y' d y` and `Σ_{y'} Q y y' |λ c y'| ≤ ρ < 1`, then `d = 0`. -/
lemma eq_zero_of_transfer_fixed {n : ℕ} (hQ : ∀ y y', 0 ≤ M.Q y y') {lam ρ : ℝ}
    (hρ : ∀ y, ∑ y', M.Q y y' * |lam * M.cY y'| ≤ ρ) (hρ1 : ρ < 1) {d : Bool × S × Ac → E n}
    (hd : ∀ y', d y' = (lam * M.cY y') • ∑ y, M.Q y y' • d y) : d = 0 := by
  funext y
  ext j
  set x : Bool × S × Ac → ℝ := fun y => d y j with hx
  have hfix : ∀ y', x y' = transfer M.Q (fun y => lam * M.cY y) x y' := fun y' => by
    simp only [hx, transfer]
    conv_lhs => rw [hd y']
    simp only [PiLp.smul_apply, smul_eq_mul, euclid_sum_apply']
  have hle := l1_transfer_le hQ hρ x
  simp only [← hfix] at hle
  have hnn : 0 ≤ ∑ y, |x y| := sum_nonneg fun _ _ => abs_nonneg _
  have h0 : ∑ y, |x y| = 0 := by nlinarith
  have := (sum_eq_zero_iff_of_nonneg fun y _ => abs_nonneg (x y)).mp h0 y (mem_univ y)
  simpa [hx] using this

omit [Fintype Ac] in
lemma stateSum_stationary_meanZero {n : ℕ} [Fintype Ac] {ν : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') {ψ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ)
    (s : S) : stateSum (fun y => ν y • ψ y) s = 0 := by
  unfold stateSum
  refine sum_eq_zero fun f _ => ?_
  have : ∑ a, ν (f, s, a) • ψ (f, s, a) = (∑ y, ν y * M.kap y f s) • ∑ a, M.pol s a • ψ (f, s, a) := by
    rw [smul_sum]
    exact sum_congr rfl fun a _ => by rw [M.stationary_factor hν, MulAction.mul_smul]
  rw [this, hψ f s, smul_zero]

/-- **The moment of the critic's carried trace.** With `m_R = E[(z^ψ_k - ψ_k) 1{Y_k = ·}]`,
`m_e(s) = E[z^e_k(s) 1{Y_k = ·}]` the TD(`λ`) trace moments and `b` the conditional mean of the
REINFORCE carried trace, `m_R + (1-λ) Σ_s m_e(s) b(s) = λ m_B + (1-λ) ν b`, pointwise. Both sides
solve the same contracting fixed-point equation. -/
theorem carried_trace_moment [DecidableEq S] {n : ℕ} {ν : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') (hQ : ∀ y y', 0 ≤ M.Q y y') {lam ρ : ℝ}
    (hρ : ∀ y, ∑ y', M.Q y y' * |lam * M.cY y'| ≤ ρ) (hρ1 : ρ < 1)
    {ψ mψ mZ : Bool × S × Ac → E n} (hmψ : M.TraceMoment ν lam ψ mψ)
    (hmZ : M.TraceMoment ν 1 ψ mZ) (me : S → Bool × S × Ac → ℝ)
    (hme : ∀ s y', me s y' = ν y' * (if y'.2.1 = s then 1 else 0)
      + lam * M.cY y' * ∑ y, M.Q y y' * me s y)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hνS : ∀ s, stateSum ν s ≠ 0)
    (hkap : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a)) (y : Bool × S × Ac) :
    (mψ y - ν y • ψ y) + (1 - lam) • ∑ s, me s y • carryMean ν ψ mZ s =
      lam • carry ν ψ mZ y + ((1 - lam) * ν y) • carryMean ν ψ mZ y.2.1 := by
  set b := carryMean ν ψ mZ with hb
  set W : Bool × S × Ac → E n := fun y => ∑ s, me s y • b s with hW
  set uL : Bool × S × Ac → E n := fun y => (mψ y - ν y • ψ y) + (1 - lam) • W y with huL
  set uR : Bool × S × Ac → E n := fun y => lam • carry ν ψ mZ y + ((1 - lam) * ν y) • b y.2.1
    with huR
  -- both solve `u y' = (λ c y') Σ_y Q y y' (ν ψ + u) y + (1-λ) ν y' b(y')`
  have hL : ∀ y', uL y' = (lam * M.cY y') • ∑ y, M.Q y y' • (ν y • ψ y + uL y)
      + ((1 - lam) * ν y') • b y'.2.1 := fun y' => by
    have h1 : mψ y' - ν y' • ψ y' = (lam * M.cY y') • ∑ y, M.Q y y' • mψ y := by
      rw [hmψ y']; abel
    have h2 : W y' = ν y' • b y'.2.1 + (lam * M.cY y') • ∑ y, M.Q y y' • W y := by
      have hme' : ∀ s, me s y' = ν y' * (if y'.2.1 = s then 1 else 0)
          + lam * M.cY y' * ∑ y, M.Q y y' * me s y := fun s => hme s y'
      simp only [hW, hme', add_smul, sum_add_distrib, MulAction.mul_smul]
      congr 1
      · rw [sum_eq_single y'.2.1]
        · simp
        · intro s _ hs; simp [Ne.symm hs]
        · simp
      · rw [smul_sum]
        simp only [smul_sum, sum_smul, smul_smul]
        rw [sum_comm]
    have h3 : ∑ y, M.Q y y' • (ν y • ψ y + uL y) =
        ∑ y, M.Q y y' • mψ y + (1 - lam) • ∑ y, M.Q y y' • W y := by
      rw [smul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun y _ => ?_
      simp only [huL]
      rw [smul_comm (1 - lam) (M.Q y y') (W y), ← smul_add]
      congr 1
      abel
    show (mψ y' - ν y' • ψ y') + (1 - lam) • W y' = _
    rw [h3, h1, h2]
    module
  have hR : ∀ y', uR y' = (lam * M.cY y') • ∑ y, M.Q y y' • (ν y • ψ y + uR y)
      + ((1 - lam) * ν y') • b y'.2.1 := fun y' => by
    have hc : carry ν ψ mZ y' = M.cY y' • ∑ y, M.Q y y' • (ν y • ψ y + carry ν ψ mZ y) := by
      rw [M.carry_eq hmZ]
      congr 1
      exact sum_congr rfl fun y _ => by simp [carry]
    have hw : ∀ f₁ f₂ s a, M.Q (f₁, s, a) y' = M.Q (f₂, s, a) y' := fun f₁ f₂ s a => by
      simp only [Q, hkap f₁ f₂ s a]
    have hcent := M.sum_carry_centered hν hmZ hpol hνS (fun y => M.Q y y') hw
    have h3 : ∑ y, M.Q y y' • (ν y • ψ y + uR y) =
        ∑ y, M.Q y y' • (ν y • ψ y + carry ν ψ mZ y)
          - (1 - lam) • ∑ y, M.Q y y' • (carry ν ψ mZ y - ν y • b y.2.1) := by
      rw [smul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun y _ => ?_
      simp only [huR]
      rw [smul_comm (1 - lam) (M.Q y y'), ← smul_sub]
      congr 1
      module
    show lam • carry ν ψ mZ y' + ((1 - lam) * ν y') • b y'.2.1 = _
    rw [h3, hcent, smul_zero, sub_zero, hc]
    module
  -- the difference is a fixed point of the contraction
  have hd : ∀ y', (uL - uR) y' = (lam * M.cY y') • ∑ y, M.Q y y' • (uL - uR) y := fun y' => by
    simp only [Pi.sub_apply]
    rw [hL y', hR y']
    simp only [smul_sub, sum_sub_distrib, smul_add, sum_add_distrib]
    abel
  have h0 := M.eq_zero_of_transfer_fixed hQ hρ hρ1 hd
  exact sub_eq_zero.mp (congrFun h0 y)

omit [Fintype Ac] in
lemma sum_ind_smul [DecidableEq S] [Fintype Ac] {X : Type*} [AddCommGroup X] [Module ℝ X]
    (F : Bool × S × Ac → X) (s' : S) :
    ∑ y, (if y.2.1 = s' then (1 : ℝ) else 0) • F y = stateSum F s' := by
  rw [sum_prod3]
  unfold stateSum
  refine sum_congr rfl fun f _ => ?_
  simp only [ite_smul, one_smul, zero_smul]
  rw [sum_comm]
  simp [sum_ite_eq']

omit [Fintype Ac] in
/-- `λ Σ_y (Σ_{y' ∈ s'} Q y y' c y') x y = Σ_{y' ∈ s'} (λ c y') Σ_y Q y y' x y`. -/
lemma smul_sum_into {X : Type*} [AddCommGroup X] [Module ℝ X] [Fintype Ac] (lam : ℝ)
    (x : Bool × S × Ac → X) (s' : S) :
    lam • ∑ y, M.into y s' • x y = stateSum (fun y' => (lam * M.cY y') • ∑ y, M.Q y y' • x y) s' := by
  unfold stateSum into
  simp only [smul_sum, sum_smul, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun y _ => by congr 1; ring

/-- **Lemma 4.6 (the gain of the tabular TD(`λ`) critic).** For the TD(`λ`) critic with features
`(ψ, e_s)` at `r̂ = (0, V)`, `-C A_c⁻¹ = (I, -K_λ)` with `K_λ T_λ = X_λ`, where
`T_λ s s' = E[z^e_k(s) (c_{k+1} 1{s_{k+1} = s'} - 1{s_k = s'})]` and
`X_λ s' = E[z^ψ_k (c_{k+1} 1{s_{k+1} = s'} - 1{s_k = s'})]`. The columns `K_λ e_s = -(1-λ) b(s)` solve
this equation: `Σ_s T_λ s s' (-(1-λ) b s) = X_λ s'`. Here `λ ≠ 0`; the case `λ = 0` is `td0_gain`. -/
theorem tdlam_gain [DecidableEq S] {n : ℕ} {ν : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') (hQ : ∀ y y', 0 ≤ M.Q y y') {lam ρ : ℝ}
    (hlam : lam ≠ 0) (hρ : ∀ y, ∑ y', M.Q y y' * |lam * M.cY y'| ≤ ρ) (hρ1 : ρ < 1)
    {ψ mψ mZ : Bool × S × Ac → E n} (hψ : M.MeanZero ψ) (hmψ : M.TraceMoment ν lam ψ mψ)
    (hmZ : M.TraceMoment ν 1 ψ mZ) (me : S → Bool × S × Ac → ℝ)
    (hme : ∀ s y', me s y' = ν y' * (if y'.2.1 = s then 1 else 0)
      + lam * M.cY y' * ∑ y, M.Q y y' * me s y)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hνS : ∀ s, stateSum ν s ≠ 0)
    (hkap : ∀ f₁ f₂ s a, M.kap (f₁, s, a) = M.kap (f₂, s, a)) (s' : S) :
    ∑ s, (∑ y, me s y * (M.into y s' - if y.2.1 = s' then 1 else 0)) •
        (-(1 - lam) • carryMean ν ψ mZ s) =
      ∑ y, (M.into y s' - if y.2.1 = s' then 1 else 0) • mψ y := by
  set b := carryMean ν ψ mZ with hb
  set P : E n := stateSum (fun y => mψ y - ν y • ψ y) s' with hP
  set Es : S → ℝ := fun s => stateSum (me s) s' with hEs
  -- `λ X = (1 - λ) P`
  have hX : lam • ∑ y, (M.into y s' - if y.2.1 = s' then 1 else 0) • mψ y = (1 - lam) • P := by
    simp only [sub_smul, sum_sub_distrib, smul_sub]
    rw [M.smul_sum_into lam mψ s', sum_ind_smul]
    have h1 : stateSum (fun y' => (lam * M.cY y') • ∑ y, M.Q y y' • mψ y) s' = P := by
      simp only [hP]
      unfold stateSum
      dsimp only
      exact sum_congr rfl fun f _ => sum_congr rfl fun a _ => by rw [hmψ (f, s', a)]; abel
    have h2 : stateSum mψ s' = P := by
      have := M.stateSum_stationary_meanZero hν hψ s'
      simp only [hP, stateSum, sum_sub_distrib] at this ⊢
      rw [this, sub_zero]
    rw [h1, h2]
    module
  -- `λ T s s' = (1 - λ) E s - [s = s'] ν(s)`
  have hT : ∀ s, lam * ∑ y, me s y * (M.into y s' - if y.2.1 = s' then 1 else 0) =
      (1 - lam) * Es s - (if s = s' then stateSum ν s else 0) := fun s => by
    have := M.smul_sum_into lam (me s) s'
    simp only [smul_eq_mul] at this
    simp only [mul_sub, sum_sub_distrib]
    rw [show ∑ y, me s y * M.into y s' = ∑ y, M.into y s' * me s y from
      sum_congr rfl fun _ _ => mul_comm _ _, this]
    have h3 := sum_ind_smul (fun y => me s y) s'
    simp only [smul_eq_mul] at h3
    rw [show ∑ y, me s y * (if y.2.1 = s' then 1 else 0) = stateSum (me s) s' by
      rw [← h3]; exact sum_congr rfl fun _ _ => mul_comm _ _]
    have h4 : stateSum (fun y' => lam * M.cY y' * ∑ y, M.Q y y' * me s y) s' =
        Es s - (if s = s' then stateSum ν s else 0) := by
      have hpt : ∀ f a, lam * M.cY (f, s', a) * ∑ y, M.Q y (f, s', a) * me s y =
          me s (f, s', a) - ν (f, s', a) * (if s' = s then 1 else 0) := fun f a => by
        rw [hme s (f, s', a)]; ring
      simp only [hEs]
      unfold stateSum
      dsimp only
      simp only [hpt, sum_sub_distrib, ← sum_mul]
      by_cases h : s = s'
      · subst h; simp
      · simp [Ne.symm h, h]
    rw [h4]
    ring
  -- the state sum of `carried_trace_moment`
  have hU : P + (1 - lam) • ∑ s, Es s • b s = stateSum (carry ν ψ mZ) s' := by
    have hpt := M.carried_trace_moment hν hQ hρ hρ1 hmψ hmZ me hme hpol hνS hkap
    have e : stateSum (fun y => (mψ y - ν y • ψ y) + (1 - lam) • ∑ s, me s y • b s) s' =
        stateSum (fun y => lam • carry ν ψ mZ y + ((1 - lam) * ν y) • b y.2.1) s' := by
      unfold stateSum
      exact sum_congr rfl fun f _ => sum_congr rfl fun a _ => hpt (f, s', a)
    have swap : ∀ G : S → Bool → Ac → E n,
        ∑ f, ∑ a, ∑ s, G s f a = ∑ s, ∑ f, ∑ a, G s f a := fun G => by
      calc ∑ f, ∑ a, ∑ s, G s f a = ∑ f, ∑ s, ∑ a, G s f a :=
            sum_congr rfl fun f _ => sum_comm
        _ = _ := sum_comm
    have l : stateSum (fun y => (mψ y - ν y • ψ y) + (1 - lam) • ∑ s, me s y • b s) s' =
        P + (1 - lam) • ∑ s, Es s • b s := by
      simp only [hP, hEs]
      unfold stateSum
      dsimp only
      simp only [sum_add_distrib, ← smul_sum, sum_smul]
      rw [swap (fun s f a => me s (f, s', a) • b s)]
    have r : stateSum (fun y => lam • carry ν ψ mZ y + ((1 - lam) * ν y) • b y.2.1) s' =
        stateSum (carry ν ψ mZ) s' := by
      have hm : stateSum ν s' • b s' = stateSum (carry ν ψ mZ) s' := by
        rw [hb, carryMean, smul_smul, mul_inv_cancel₀ (hνS s'), one_smul]
      unfold stateSum at hm ⊢
      simp only [sum_add_distrib, ← smul_sum, MulAction.mul_smul, ← sum_smul] at hm ⊢
      rw [hm]
      module
    rw [← l, e, r]
  -- assemble: multiply by `λ`
  apply smul_right_injective (E n) hlam
  simp only
  rw [hX, smul_sum]
  have e : ∀ s, lam • ((∑ y, me s y * (M.into y s' - if y.2.1 = s' then 1 else 0)) •
      (-(1 - lam) • b s)) = ((1 - lam) * Es s - (if s = s' then stateSum ν s else 0)) •
      (-(1 - lam) • b s) := fun s => by rw [smul_smul, hT s]
  rw [sum_congr rfl fun s _ => e s]
  have key : ∑ s, ((1 - lam) * Es s - (if s = s' then stateSum ν s else 0)) • (-(1 - lam) • b s)
      = (-(1 - lam) * (1 - lam)) • ∑ s, Es s • b s + (1 - lam) • (stateSum ν s' • b s') := by
    simp only [sub_smul, sum_sub_distrib, ite_smul, zero_smul, sum_ite_eq', mem_univ, if_true]
    rw [smul_sum]
    have : ∀ s, ((1 - lam) * Es s) • (-(1 - lam) • b s) = (-(1 - lam) * (1 - lam)) • (Es s • b s) :=
      fun s => by module
    rw [sum_congr rfl fun s _ => this s]
    module
  have hm : stateSum ν s' • b s' = stateSum (carry ν ψ mZ) s' := by
    rw [hb, carryMean, smul_smul, mul_inv_cancel₀ (hνS s'), one_smul]
  rw [key, hm, ← hU]
  module

/-! ### The restart chain contracts -/

omit [Fintype S] [Fintype Ac] in
lemma Q_nonneg (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (y y' : Bool × S × Ac) : 0 ≤ M.Q y y' :=
  mul_nonneg (hkap _ _ _) (hpol0 _ _)

/-- **The restart chain contracts.** If a restart resets the trace (`c true = 0`), `|c| ≤ 1`, the
probability of continuing is at most `γ` (`Σ_{s'} kap y false s' ≤ γ`), and the policy is a
probability distribution, then `Σ_{y'} Q y y' |λ c y'| ≤ |λ| γ`. For the restart chain of the
write-up, `kap y false s' = γ P(s' | s, a)` and `c false = 1`, so this is the contraction
hypothesis of `tendsto_traceMoment` with `ρ = |λ| γ < 1`, for every `λ ∈ [-1, 1]` and `γ < 1`. -/
theorem restart_contraction (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol : ∀ s, ∑ a, M.pol s a = 1) (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1)
    {γ : ℝ} (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) (lam : ℝ) (y : Bool × S × Ac) :
    ∑ y', M.Q y y' * |lam * M.cY y'| ≤ |lam| * γ := by
  rw [sum_prod3, Fintype.sum_bool]
  simp only [Q, cY, hc0, mul_zero, abs_zero, sum_const_zero, zero_add]
  have e : ∀ s', ∑ a, M.kap y false s' * M.pol s' a * |lam * M.c false s'| =
      M.kap y false s' * |lam * M.c false s'| := fun s' => by
    rw [← sum_mul, ← mul_sum, hpol, mul_one]
  simp only [e]
  calc ∑ s', M.kap y false s' * |lam * M.c false s'| ≤ ∑ s', M.kap y false s' * |lam| :=
        sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hc1 s')) (hkap _ _ _)
    _ = |lam| * ∑ s', M.kap y false s' := by rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ |lam| * γ := mul_le_mul_of_nonneg_left (hγ y) (abs_nonneg _)

/-! ### The trace moments of the process -/

/-- **The trace moments come from the process.** Along a chain `Y` with transitions `Q` whose
law converges to `ν`, the moments `E[z_k(a) 1{Y_k = y}]` of the trace
`z (k+1) = λ c(Y (k+1)) z k + φ(Y (k+1))` converge to a solution of the `TraceMoment` recursion,
provided `Σ_{y'} Q y y' |λ c y'| ≤ ρ < 1` (for the restart chain, `ρ = λγ`). -/
theorem tendsto_traceMoment [MeasurableSpace (Bool × S × Ac)]
    [DiscreteMeasurableSpace (Bool × S × Ac)] [DecidableEq S] [DecidableEq Ac] {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → Bool × S × Ac} (hY : FiniteMarkov μ ℱ Y M.Q)
    (hQ : ∀ y y', 0 ≤ M.Q y y') {lam ρ : ℝ} (hρ : ∀ y, ∑ y', M.Q y y' * |lam * M.cY y'| ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {p : ℕ} {φ : Bool × S × Ac → E p} {z : ℕ → Ω → E p}
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = (lam * M.cY (Y (k + 1) ω)) • z k ω + φ (Y (k + 1) ω))
    {ν : Bool × S × Ac → ℝ}
    (hlaw : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y))) :
    ∃ m : Bool × S × Ac → E p, M.TraceMoment ν lam φ m ∧
      ∀ y a, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a) k y) atTop (𝓝 (m y a)) := by
  have hlaw1 : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) (k + 1) y) atTop (𝓝 (ν y)) :=
    fun y => (hlaw y).comp (tendsto_add_atTop_nat 1)
  have h1 : ∀ a, ∃ xl : Bool × S × Ac → ℝ,
      (∀ y', xl y' = transfer M.Q (fun y => lam * M.cY y) xl y' + φ y' a * ν y') ∧
      ∀ y, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a) k y) atTop (𝓝 (xl y)) := fun a =>
    tendsto_affine_transfer hQ hρ hρ0 hρ1
      (mom1_succ (c := fun y => lam * M.cY y) hY hz hzB hzrec · a)
      fun y => (hlaw1 y).const_mul (φ y a)
  choose m₁ hm₁ ht₁ using h1
  refine ⟨fun y => (fun a => m₁ a y : E p), fun y' => ?_, fun y a => ht₁ a y⟩
  ext a
  show m₁ a y' = _
  rw [hm₁ a y']
  simp only [transfer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, euclid_sum_apply']
  rw [mul_sum]
  ring_nf

/-- **Trace moments of the restart chain.** For a restart-type chain (a restart resets the trace,
`|c| ≤ 1`, continuation probability at most `γ < 1`), the trace moments converge to a solution of
the `TraceMoment` recursion for every `|λ| ≤ 1`, including the REINFORCE trace `λ = 1`. -/
theorem tendsto_traceMoment_restart [MeasurableSpace (Bool × S × Ac)]
    [DiscreteMeasurableSpace (Bool × S × Ac)] [DecidableEq S] [DecidableEq Ac] {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → Bool × S × Ac} (hY : FiniteMarkov μ ℱ Y M.Q)
    (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {lam : ℝ}
    (hlam : |lam| ≤ 1) {p : ℕ} {φ : Bool × S × Ac → E p} {z : ℕ → Ω → E p}
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = (lam * M.cY (Y (k + 1) ω)) • z k ω + φ (Y (k + 1) ω))
    {ν : Bool × S × Ac → ℝ}
    (hlaw : ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y))) :
    ∃ m : Bool × S × Ac → E p, M.TraceMoment ν lam φ m ∧
      ∀ y a, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a) k y) atTop (𝓝 (m y a)) :=
  M.tendsto_traceMoment hY (M.Q_nonneg hkap hpol0) (M.restart_contraction hkap hpol hc0 hc1 hγ lam)
    (mul_nonneg (abs_nonneg _) hγ0)
    (lt_of_le_of_lt (mul_le_of_le_one_left hγ0 hlam) hγ1) hz hzB hzrec hlaw

/-- **The law of the restart chain converges.** If the restart distribution does not depend on
the current pair (`kap y true s` is the same for all `y`), the continuation probability is at
most `γ < 1`, and the policy is a probability distribution, then `P(Y_k = y)` converges to a
stationary law `ν` with total mass `1`, from any initial law. Restarts are a Doeblin minorization:
`P(Y_{k+1} = ·) = L P(Y_k = ·) + b` with `L` the continuation part, an `ℓ¹` contraction by `γ`,
and `b` the restart law. -/
theorem tendsto_law_restart [MeasurableSpace (Bool × S × Ac)]
    [DiscreteMeasurableSpace (Bool × S × Ac)] [DecidableEq S] [DecidableEq Ac] {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → Bool × S × Ac} (hY : FiniteMarkov μ ℱ Y M.Q)
    (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) :
    ∃ ν : Bool × S × Ac → ℝ, (∀ y', ∑ y, ν y * M.Q y y' = ν y') ∧ ∑ y, ν y = 1 ∧
      ∀ y, Tendsto (fun k => momAt μ Y (fun _ _ => 1) k y) atTop (𝓝 (ν y)) := by
  set cc : Bool × S × Ac → ℝ := fun y => if y.1 then 0 else 1 with hcc
  set b : Bool × S × Ac → ℝ := fun y => if y.1 then M.Q y y else 0 with hb
  set P : ℕ → Bool × S × Ac → ℝ := fun k y => momAt μ Y (fun _ _ => 1) k y with hP
  -- total mass one
  have hmass : ∀ k, ∑ y, P k y = 1 := fun k => by
    have := integral_eq_sum_momAt (μ := μ) hY (k := k) (W := fun _ => (1 : ℝ))
      stronglyMeasurable_const ⟨1, fun _ => by simp⟩
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_univ_eq_one] at this
    exact this.symm
  -- the restart row does not depend on the current pair
  have hQr : ∀ y s a, M.Q y (true, s, a) = M.Q (true, s, a) (true, s, a) := fun y s a => by
    simp only [Q, hrest y (true, s, a) s]
  -- the affine recursion
  have hsplit : ∀ (x : Bool × S × Ac → ℝ) (y' : Bool × S × Ac),
      ∑ y, M.Q y y' * x y = transfer M.Q cc x y' + b y' * ∑ y, x y := by
    rintro x ⟨f, s, a⟩
    cases f
    · simp [transfer, hcc, hb]
    · simp only [transfer, hcc, hb, if_true, zero_mul, mul_sum, sum_const_zero, zero_add]
      exact sum_congr rfl fun y _ => by rw [hQr y s a]
  have hrec : ∀ k y', P (k + 1) y' = transfer M.Q cc (P k) y' + b y' := fun k y' => by
    simp only [hP]
    rw [lawAt_succ hY k y', hsplit, show ∑ y, momAt μ Y (fun _ _ => 1) k y = 1 from hmass k,
      mul_one]
  -- continuation is a contraction
  have hρ : ∀ y, ∑ y', M.Q y y' * |cc y'| ≤ γ := fun y => by
    rw [sum_prod3, Fintype.sum_bool]
    simp only [hcc, if_true, abs_zero, mul_zero, sum_const_zero, zero_add, Bool.false_eq_true,
      if_false, abs_one, mul_one, Q]
    refine le_trans (le_of_eq ?_) (hγ y)
    exact sum_congr rfl fun s _ => by rw [← mul_sum, hpol, mul_one]
  obtain ⟨ν, hν, hlim⟩ := tendsto_affine_transfer (M.Q_nonneg hkap hpol0) hρ hγ0 hγ1 hrec
    (fun y => tendsto_const_nhds (x := b y))
  have hνm : ∑ y, ν y = 1 := by
    have h := tendsto_finset_sum (univ : Finset (Bool × S × Ac)) fun y _ => hlim y
    have h1 : (fun k => ∑ y, P k y) = fun _ => (1 : ℝ) := funext hmass
    simp only [hP] at h1
    rw [h1] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  refine ⟨ν, fun y' => ?_, hνm, hlim⟩
  have := hsplit ν y'
  rw [hνm, mul_one] at this
  rw [hν y', ← this]
  exact sum_congr rfl fun y _ => mul_comm _ _

/-- **Trace moments of the restart chain, from the model alone.** For the restart chain, the law
of `Y_k` converges to a stationary `ν` (`tendsto_law_restart`) and the trace moments converge to
a solution of the `TraceMoment` recursion for `ν`, for every `|λ| ≤ 1`. -/
theorem tendsto_traceMoment_of_restart [MeasurableSpace (Bool × S × Ac)]
    [DiscreteMeasurableSpace (Bool × S × Ac)] [DecidableEq S] [DecidableEq Ac] {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → Bool × S × Ac} (hY : FiniteMarkov μ ℱ Y M.Q)
    (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {lam : ℝ}
    (hlam : |lam| ≤ 1) {p : ℕ} {φ : Bool × S × Ac → E p} {z : ℕ → Ω → E p}
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hzB : ∀ k, ∃ C, ∀ ω, ‖z k ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = (lam * M.cY (Y (k + 1) ω)) • z k ω + φ (Y (k + 1) ω)) :
    ∃ ν : Bool × S × Ac → ℝ, (∀ y', ∑ y, ν y * M.Q y y' = ν y') ∧ ∑ y, ν y = 1 ∧
      ∃ m : Bool × S × Ac → E p, M.TraceMoment ν lam φ m ∧
        ∀ y a, Tendsto (fun k => momAt μ Y (fun k ω => z k ω a) k y) atTop (𝓝 (m y a)) := by
  obtain ⟨ν, hν, hνm, hlaw⟩ := M.tendsto_law_restart hY hkap hpol0 hpol hrest hγ0 hγ1 hγ
  exact ⟨ν, hν, hνm, M.tendsto_traceMoment_restart hY hkap hpol0 hpol hc0 hc1 hγ0 hγ1 hγ hlam hz
    hzB hzrec hlaw⟩

omit [Fintype S] [Fintype Ac] in
lemma abs_lam_cY_le (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1) {lam : ℝ}
    (hlam : |lam| ≤ 1) (y : Bool × S × Ac) : |lam * M.cY y| ≤ 1 := by
  obtain ⟨f, s, a⟩ := y
  rw [abs_mul]
  cases f
  · exact mul_le_one₀ hlam (abs_nonneg _) (hc1 s)
  · simp [cY, hc0]

/-- **Corollary 4.5 for the restart chain.** Linear stochastic approximation driven by trace
noise `F(Y_k, Y_{k+1}) z_k + e(Y_k, Y_{k+1})` along the restart chain, with the trace
`z (k+1) = λ c(Y (k+1)) z k + φ(Y (k+1))`, `|λ| ≤ 1`, and a bounded initial trace, satisfies
Theorem 2.1: `β_k⁻¹ E[θ_k θ_kᵀ]` converges to the solution of the Lyapunov equation with
`Γ = traceGamma`. The stationary law `ν` and the trace moments are those of the chain; the only
data assumed besides the model are the Poisson solutions `U`, `ĥ` of Lemma 4.4. -/
theorem tendsto_secondMoment_of_restart_noise [MeasurableSpace (Bool × S × Ac)]
    [DiscreteMeasurableSpace (Bool × S × Ac)] [DecidableEq S] [DecidableEq Ac] {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → Bool × S × Ac} (hY : FiniteMarkov μ ℱ Y M.Q)
    (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {lam : ℝ}
    (hlam : |lam| ≤ 1) {p d : ℕ} {φ : Bool × S × Ac → E p} {z : ℕ → Ω → E p}
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hz0 : ∃ C, ∀ ω, ‖z 0 ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = (lam * M.cY (Y (k + 1) ω)) • z k ω + φ (Y (k + 1) ω))
    (Fm : Bool × S × Ac → Bool × S × Ac → E p →L[ℝ] E d) (e : Bool × S × Ac → Bool × S × Ac → E d)
    (U : Bool × S × Ac → E p →L[ℝ] E d) (hh : Bool × S × Ac → E d)
    (hU : ∀ y, U y = ∑ y', M.Q y y' • (Fm y y' + (lam * M.cY y') • U y'))
    (hhh : ∀ y, hh y = ∑ y', M.Q y y' • (e y y' + U y' (φ y') + hh y'))
    {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ}
    (hη : 0 < η) (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    {θ : ℕ → Ω → E d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω) + β k • traceNoise Fm e Y z k ω)
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ) :
    ∃ ν : Bool × S × Ac → ℝ, (∀ y', ∑ y, ν y * M.Q y y' = ν y') ∧ ∑ y, ν y = 1 ∧
      ∃ (m₁ : Fin p → Bool × S × Ac → ℝ) (m₂ : Fin p → Fin p → Bool × S × Ac → ℝ),
        (∀ a y', m₁ a y' = transfer M.Q (fun y => lam * M.cY y) (m₁ a) y' + φ y' a * ν y') ∧
        (∀ a b y', m₂ a b y' = transfer M.Q (fun y => (lam * M.cY y) ^ 2) (m₂ a b) y'
          + φ y' b * transfer M.Q (fun y => lam * M.cY y) (m₁ a) y'
          + φ y' a * transfer M.Q (fun y => lam * M.cY y) (m₁ b) y' + φ y' a * φ y' b * ν y') ∧
        ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig =
            traceGamma M.Q (fun y y' => Fm y y' + (lam * M.cY y') • U y' - U y)
              (fun y y' => e y y' + U y' (φ y') + hh y' - hh y) ν m₁ m₂ ∧
          Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨ν, hν, hνm, hlaw⟩ := M.tendsto_law_restart hY hkap hpol0 hpol hrest hγ0 hγ1 hγ
  refine ⟨ν, hν, hνm, ?_⟩
  exact tendsto_secondMoment_of_trace_noise_stationary (c := fun y => lam * M.cY y) hβ A hη hA hY
    (M.Q_nonneg hkap hpol0) (M.restart_contraction hkap hpol hc0 hc1 hγ lam)
    (mul_nonneg (abs_nonneg _) hγ0) (lt_of_le_of_lt (mul_le_of_le_one_left hγ0 hlam) hγ1)
    (M.abs_lam_cY_le hc0 hc1 hlam) hlaw hz hz0 hzrec Fm e U hh hU hhh hθ hθ0 hθ0L

/-! ### The Poisson solutions of Lemma 4.4 for the restart chain -/

/-- `U = Σ_{y'} Q(·, y') (F(·, y') + λ c(y') U(y'))` has a solution: the map is a row
contraction by `|λ| γ`. -/
theorem exists_poisson_U (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {lam : ℝ}
    (hlam : |lam| ≤ 1) {p d : ℕ} (Fm : Bool × S × Ac → Bool × S × Ac → E p →L[ℝ] E d) :
    ∃ U : Bool × S × Ac → E p →L[ℝ] E d,
      ∀ y, U y = ∑ y', M.Q y y' • (Fm y y' + (lam * M.cY y') • U y') := by
  obtain ⟨U, hU⟩ := exists_row_fixed (M.Q_nonneg hkap hpol0)
    (M.restart_contraction hkap hpol hc0 hc1 hγ lam)
    (lt_of_le_of_lt (mul_le_of_le_one_left hγ0 hlam) hγ1) (fun y => ∑ y', M.Q y y' • Fm y y')
  refine ⟨U, fun y => ?_⟩
  rw [hU y]
  simp only [smul_add, sum_add_distrib, smul_smul]

omit [Fintype S] [Fintype Ac] in
lemma Q_restart_row (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    (y : Bool × S × Ac) (s : S) (a : Ac) : M.Q y (true, s, a) = M.Q (true, s, a) (true, s, a) := by
  simp only [Q, hrest y (true, s, a) s]

lemma continuation_le (hpol : ∀ s, ∑ a, M.pol s a = 1) {γ : ℝ}
    (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) (y : Bool × S × Ac) :
    ∑ y', M.Q y y' * |(fun y : Bool × S × Ac => if y.1 then (0 : ℝ) else 1) y'| ≤ γ := by
  rw [sum_prod3, Fintype.sum_bool]
  simp only [if_true, abs_zero, mul_zero, sum_const_zero, zero_add, Bool.false_eq_true,
    if_false, abs_one, mul_one, Q]
  refine le_trans (le_of_eq ?_) (hγ y)
  exact sum_congr rfl fun s _ => by rw [← mul_sum, hpol, mul_one]

/-- **The Poisson equation of the restart chain.** If the forcing
`w y = Σ_{y'} Q y y' (e(y, y') + U(y') φ(y'))` has mean zero under the stationary law `ν`, then
`ĥ = Σ_{y'} Q(·, y') (e(·, y') + U(y') φ(y') + ĥ(y'))` has a solution. The proof solves the
continuation part, a contraction by `γ`, and shows that the restart part contributes the
constant `Σ_ν w = 0`. -/
theorem exists_poisson_h (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    {γ : ℝ} (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {ν : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') (hνm : ∑ y, ν y = 1) {p d : ℕ}
    (φ : Bool × S × Ac → E p) (e : Bool × S × Ac → Bool × S × Ac → E d)
    (U : Bool × S × Ac → E p →L[ℝ] E d)
    (hcent : ∑ y, ν y • ∑ y', M.Q y y' • (e y y' + U y' (φ y')) = 0) :
    ∃ hh : Bool × S × Ac → E d,
      ∀ y, hh y = ∑ y', M.Q y y' • (e y y' + U y' (φ y') + hh y') := by
  set cc : Bool × S × Ac → ℝ := fun y => if y.1 then 0 else 1 with hcc
  set w : Bool × S × Ac → E d := fun y => ∑ y', M.Q y y' • (e y y' + U y' (φ y')) with hw
  obtain ⟨hk, hhk⟩ := exists_row_fixed (M.Q_nonneg hkap hpol0) (M.continuation_le hpol hγ) hγ1 w
  set κ : E d := ∑ y', (if y'.1 then M.Q y' y' else 0) • hk y' with hκ
  have hsplit : ∀ y, ∑ y', M.Q y y' • hk y' = ∑ y', (M.Q y y' * cc y') • hk y' + κ := fun y => by
    rw [hκ, ← sum_add_distrib]
    refine sum_congr rfl fun y' _ => ?_
    obtain ⟨f, s, a⟩ := y'
    cases f
    · simp [hcc]
    · simp [hcc, M.Q_restart_row hrest y s a]
  have hk2 : ∀ y, hk y = w y + ∑ y', M.Q y y' • hk y' - κ := fun y => by
    rw [hsplit y, hhk y]; abel
  have hκ0 : κ = 0 := by
    have h1 : ∑ y, ν y • hk y = ∑ y, ν y • w y + ∑ y, ν y • ∑ y', M.Q y y' • hk y'
        - (∑ y, ν y) • κ := by
      rw [sum_smul, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by rw [hk2 y]; simp only [smul_sub, smul_add]
    have h2 : ∑ y, ν y • ∑ y', M.Q y y' • hk y' = ∑ y', ν y' • hk y' := by
      simp only [smul_sum, smul_smul]
      rw [sum_comm]
      exact sum_congr rfl fun y' _ => by rw [← sum_smul, hν y']
    rw [h2, hνm, one_smul] at h1
    have h3 : ∑ y, ν y • w y = 0 := hcent
    rw [h3, zero_add] at h1
    have := congrArg (· - ∑ y', ν y' • hk y') h1
    simp only [sub_self] at this
    rw [show ∑ y', ν y' • hk y' - κ - ∑ y', ν y' • hk y' = -κ by abel] at this
    exact neg_eq_zero.mp this.symm
  refine ⟨hk, fun y => ?_⟩
  rw [hk2 y, hκ0, sub_zero, hw]
  simp only [smul_add, sum_add_distrib]

omit [Fintype S] [Fintype Ac] in
/-- **The centering condition is the mean of the noise.** With `m` the stationary trace moments
and `U` the Poisson solution, `Σ_y ν y Σ_{y'} Q y y' (e + U(y') φ(y'))` equals the stationary mean
`Σ_{y,y'} Q y y' (F(y, y') m(y) + ν(y) e(y, y'))` of the noise `F(Y_k, Y_{k+1}) z_k + e(Y_k, Y_{k+1})`.
So `tendsto_secondMoment_of_restart_noise_centered` needs exactly centered noise. -/
lemma centering_eq_noise_mean [Fintype S] [Fintype Ac] {ν : Bool × S × Ac → ℝ}
    (hν : ∀ y', ∑ y, ν y * M.Q y y' = ν y') {lam : ℝ} {p d : ℕ} {φ m : Bool × S × Ac → E p}
    (hm : M.TraceMoment ν lam φ m) (Fm : Bool × S × Ac → Bool × S × Ac → E p →L[ℝ] E d)
    (e : Bool × S × Ac → Bool × S × Ac → E d) (U : Bool × S × Ac → E p →L[ℝ] E d)
    (hU : ∀ y, U y = ∑ y', M.Q y y' • (Fm y y' + (lam * M.cY y') • U y')) :
    ∑ y, ν y • ∑ y', M.Q y y' • (e y y' + U y' (φ y')) =
      ∑ y, ∑ y', M.Q y y' • (Fm y y' (m y) + ν y • e y y') := by
  -- the `U φ` part, by stationarity
  have hA : ∑ y, ν y • ∑ y', M.Q y y' • U y' (φ y') = ∑ y', U y' (ν y' • φ y') := by
    simp only [smul_sum, smul_smul]
    rw [sum_comm]
    exact sum_congr rfl fun y' _ => by rw [← sum_smul, hν y', map_smul]
  -- the trace-moment recursion
  have hB : ∀ y', U y' (ν y' • φ y') =
      U y' (m y') - ∑ y, (M.Q y y' * (lam * M.cY y')) • U y' (m y) := fun y' => by
    have := hm y'
    rw [show ν y' • φ y' = m y' - (lam * M.cY y') • ∑ y, M.Q y y' • m y by rw [this]; abel,
      map_sub, map_smul, map_sum, smul_sum]
    congr 1
    exact sum_congr rfl fun y _ => by rw [map_smul, smul_smul, mul_comm]
  -- the equation for `U`
  have hC : ∀ y, U y (m y) = ∑ y', M.Q y y' • Fm y y' (m y)
      + ∑ y', (M.Q y y' * (lam * M.cY y')) • U y' (m y) := fun y => by
    conv_lhs => rw [hU y]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, smul_add, sum_add_distrib, smul_smul]
  have hD : ∑ y', U y' (m y') = ∑ y, ∑ y', M.Q y y' • Fm y y' (m y)
      + ∑ y', ∑ y, (M.Q y y' * (lam * M.cY y')) • U y' (m y) := by
    simp only [hC, sum_add_distrib]
    rw [sum_comm (s := univ) (t := univ) (f := fun y y' => (M.Q y y' * (lam * M.cY y')) • U y' (m y))]
  have hE : ∑ y, ν y • ∑ y', M.Q y y' • e y y' = ∑ y, ∑ y', M.Q y y' • (ν y • e y y') := by
    simp only [smul_sum]
    exact sum_congr rfl fun y _ => sum_congr rfl fun y' _ => smul_comm _ _ _
  calc ∑ y, ν y • ∑ y', M.Q y y' • (e y y' + U y' (φ y'))
      = ∑ y, ν y • ∑ y', M.Q y y' • e y y' + ∑ y, ν y • ∑ y', M.Q y y' • U y' (φ y') := by
        simp only [smul_add, sum_add_distrib]
    _ = ∑ y, ∑ y', M.Q y y' • (ν y • e y y') + ∑ y, ∑ y', M.Q y y' • Fm y y' (m y) := by
        rw [hE, hA]
        simp only [hB, sum_sub_distrib, hD]
        abel
    _ = _ := by
        rw [add_comm, ← sum_add_distrib]
        exact sum_congr rfl fun y _ => by rw [← sum_add_distrib]; simp only [smul_add]

/-- **Corollary 4.5 for the restart chain, from the model.** For trace-driven linear stochastic
approximation along the restart chain (`|λ| ≤ 1`, bounded initial trace), the stationary law
`ν` and the Poisson solution `U` exist, and if the noise is centered under `ν` the Poisson
solution `ĥ` exists and `β_k⁻¹ E[θ_k θ_kᵀ]` converges to the solution of the Lyapunov equation
with `Γ = traceGamma`, computed from the stationary trace moments. -/
theorem tendsto_secondMoment_of_restart_noise_centered [MeasurableSpace (Bool × S × Ac)]
    [DiscreteMeasurableSpace (Bool × S × Ac)] [DecidableEq S] [DecidableEq Ac] {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ m0} {Y : ℕ → Ω → Bool × S × Ac} (hY : FiniteMarkov μ ℱ Y M.Q)
    (hkap : ∀ y f s, 0 ≤ M.kap y f s) (hpol0 : ∀ s a, 0 ≤ M.pol s a)
    (hpol : ∀ s, ∑ a, M.pol s a = 1) (hrest : ∀ y₁ y₂ s, M.kap y₁ true s = M.kap y₂ true s)
    (hc0 : ∀ s, M.c true s = 0) (hc1 : ∀ s, |M.c false s| ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ : ∀ y, ∑ s', M.kap y false s' ≤ γ) {lam : ℝ}
    (hlam : |lam| ≤ 1) {p d : ℕ} {φ : Bool × S × Ac → E p} {z : ℕ → Ω → E p}
    (hz : ∀ k, StronglyMeasurable[ℱ k] (z k)) (hz0 : ∃ C, ∀ ω, ‖z 0 ω‖ ≤ C)
    (hzrec : ∀ k ω, z (k + 1) ω = (lam * M.cY (Y (k + 1) ω)) • z k ω + φ (Y (k + 1) ω))
    (Fm : Bool × S × Ac → Bool × S × Ac → E p →L[ℝ] E d) (e : Bool × S × Ac → Bool × S × Ac → E d)
    {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ}
    (hη : 0 < η) (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    {θ : ℕ → Ω → E d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω) + β k • traceNoise Fm e Y z k ω)
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ) :
    ∃ ν : Bool × S × Ac → ℝ, (∀ y', ∑ y, ν y * M.Q y y' = ν y') ∧ ∑ y, ν y = 1 ∧
      ∃ U : Bool × S × Ac → E p →L[ℝ] E d,
        (∀ y, U y = ∑ y', M.Q y y' • (Fm y y' + (lam * M.cY y') • U y')) ∧
        (∑ y, ν y • ∑ y', M.Q y y' • (e y y' + U y' (φ y')) = 0 →
          ∃ hh : Bool × S × Ac → E d,
            (∀ y, hh y = ∑ y', M.Q y y' • (e y y' + U y' (φ y') + hh y')) ∧
            ∃ (m₁ : Fin p → Bool × S × Ac → ℝ) (m₂ : Fin p → Fin p → Bool × S × Ac → ℝ),
              (∀ a y', m₁ a y' = transfer M.Q (fun y => lam * M.cY y) (m₁ a) y' + φ y' a * ν y') ∧
              (∀ a b y', m₂ a b y' = transfer M.Q (fun y => (lam * M.cY y) ^ 2) (m₂ a b) y'
                + φ y' b * transfer M.Q (fun y => lam * M.cY y) (m₁ a) y'
                + φ y' a * transfer M.Q (fun y => lam * M.cY y) (m₁ b) y'
                + φ y' a * φ y' b * ν y') ∧
              ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig =
                  traceGamma M.Q (fun y y' => Fm y y' + (lam * M.cY y') • U y' - U y)
                    (fun y y' => e y y' + U y' (φ y') + hh y' - hh y) ν m₁ m₂ ∧
                Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig)) := by
  obtain ⟨ν, hν, hνm, hlaw⟩ := M.tendsto_law_restart hY hkap hpol0 hpol hrest hγ0 hγ1 hγ
  obtain ⟨U, hU⟩ := M.exists_poisson_U hkap hpol0 hpol hc0 hc1 hγ0 hγ1 hγ hlam Fm
  refine ⟨ν, hν, hνm, U, hU, fun hcent => ?_⟩
  obtain ⟨hh, hhh⟩ := M.exists_poisson_h hkap hpol0 hpol hrest hγ1 hγ hν hνm φ e U hcent
  exact ⟨hh, hhh, tendsto_secondMoment_of_trace_noise_stationary (c := fun y => lam * M.cY y) hβ
    A hη hA hY (M.Q_nonneg hkap hpol0) (M.restart_contraction hkap hpol hc0 hc1 hγ lam)
    (mul_nonneg (abs_nonneg _) hγ0) (lt_of_le_of_lt (mul_le_of_le_one_left hγ0 hlam) hγ1)
    (M.abs_lam_cY_le hc0 hc1 hlam) hlaw hz hz0 hzrec Fm e U hh hU hhh hθ hθ0 hθ0L⟩

end ScoreChain

/-- **Theorem 4.5, pathwise.** With the REINFORCE trace `z' = c' z + ψ'` and the TD error
`δ = g + c' v' - v` of the value function, the actor-only noise `g z` splits as the TD(0)
actor-critic noise `v ψ + δ (ψ + b)` (with `K e_s = -b`, `td0_gain`), plus `δ (z - ψ - b)`,
minus the coboundary `H' - H` with `H = v (z - ψ)`. -/
theorem td0_noise_split {n : ℕ} (z z' ψ ψ' b : E n) (g v v' c' : ℝ) (hz : z' = c' • z + ψ') :
    g • z = (v • ψ + (g + c' * v' - v) • (ψ + b)) + (g + c' * v' - v) • (z - ψ - b)
      - (v' • (z' - ψ') - v • (z - ψ)) := by
  rw [hz]
  module

/-- **Theorem 4.1 (noise), pathwise.** With the TD(1) trace `z' = c' z + ψ'`, the actor-critic
effective noise at the root, `v ψ + d z` with `d = g + c' v' - v`, equals the actor-only noise
`g z` plus the coboundary `H' - H` with `H = v (z - ψ)`. -/
theorem td1_noise_coboundary {n : ℕ} (z z' ψ ψ' : E n) (g v v' c' : ℝ) (hz : z' = c' • z + ψ') :
    v • ψ + (g + c' * v' - v) • z = g • z + (v' • (z' - ψ') - v • (z - ψ)) := by
  rw [hz]
  module

/-- Noises that differ by a coboundary `H (k+1) - H k` bounded in `L²` give the same asymptotic
covariance: Theorem 2.1 of the single-time-scale note holds with the same `Γ`. Together with
`td1_noise_coboundary` this gives the noise part of Theorem 4.1. -/
theorem tendsto_secondMoment_of_coboundary {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {β : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
    (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ M h H : ℕ → Ω → E d} {Γ : Mat d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω - β k • matCLM A (θ k ω)
      + β k • (M (k + 1) ω + h k ω - h (k + 1) ω + (H (k + 1) ω - H k ω)))
    (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
    (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
    (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
    (hH : ∀ k, StronglyMeasurable[ℱ k] (H k)) (hHL : ∀ k, MemLp (H k) 2 μ)
    (hHB : ∃ CH, ∀ k, ∫ ω, ‖H k ω‖ ^ 2 ∂μ ≤ CH)
    (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
    (hMB : ∃ CM, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
    (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hΓ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨Ch, hCh⟩ := hhB
  obtain ⟨CH, hCH⟩ := hHB
  refine tendsto_secondMoment_of_markov_noise hβ A hη hA ℱ (h := fun k ω => h k ω - H k ω)
    (fun k ω => by rw [hθ k ω]; simp only [smul_sub, smul_add]; abel) hθ0 hθ0L (fun k => (hh k).sub (hH k))
    (fun k => (hhL k).sub (hHL k)) ⟨2 * Ch + 2 * CH, fun k => ?_⟩ hM hML hMB hmart hΓ
  have hpt : ∀ ω, ‖h k ω - H k ω‖ ^ 2 ≤ 2 * ‖h k ω‖ ^ 2 + 2 * ‖H k ω‖ ^ 2 := fun ω =>
    norm_sq_le_of_le (norm_nonneg _) (norm_sub_le _ _)
  have i1 := (memLp_sq_integrable (hhL k)).const_mul 2
  have i2 := (memLp_sq_integrable (hHL k)).const_mul 2
  have i12 : Integrable (fun ω => 2 * ‖h k ω‖ ^ 2 + 2 * ‖H k ω‖ ^ 2) μ := i1.add i2
  have hsubL : MemLp (fun ω => h k ω - H k ω) 2 μ := (hhL k).sub (hHL k)
  have hint := integral_mono (memLp_sq_integrable hsubL) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hint
  have h1 := hCh k
  have h2 := hCH k
  show ∫ ω, ‖h k ω - H k ω‖ ^ 2 ∂μ ≤ 2 * Ch + 2 * CH
  linarith

end StochasticApproximation
