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
