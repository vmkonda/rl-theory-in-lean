/-
SPDX-License-Identifier: MIT
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Process.Filtration

import RLTheory.StochasticApproximation.CovarianceRecursion

/-!
# Asymptotic covariance of linear stochastic approximation with Markov noise

The probabilistic part of the Markov-noise covariance theorem
(`docs/markov-sa-covariance.md`, Theorem 2.1): for
`θ (k+1) = θ k - β k A θ k + β k V k` with `V k = M (k+1) + h k - h (k+1)` (martingale
difference plus telescoping part), `β k⁻¹ E[θ k θ kᵀ]` converges to the solution of the
Lyapunov equation with right-hand side `Γ = lim E[M M ᵀ]`.

* `outer`, `secondMoment`, `crossMoment`: outer products and their expectations, as
  `d × d` matrices with the Frobenius norm.
* `norm_crossMoment_le`: Cauchy–Schwarz, `‖E[a cᵀ]‖ ≤ √E‖a‖² √E‖c‖²`.
* `crossMoment_eq_zero`: the cross term with a martingale difference vanishes.
* `shifted_iterate`, `iterates_adapted`: Lemma 2.3 and adaptedness of the iterates.
* `secondMoment_recursion`: Lemma 2.4, the second-moment recursion with its remainder bound.
* `tendsto_secondMoment_of_markov_noise`: Theorem 2.1.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StochasticApproximation

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Outer products -/

/-- The outer product `x yᵀ`. -/
def outer (x y : E d) : Mat d := fun ij => x ij.1 * y ij.2

lemma norm_outer (x y : E d) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
  have h : ‖outer x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [outer, Real.norm_eq_abs, sq_abs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

lemma continuous_outer : Continuous fun p : E d × E d => outer p.1 p.2 := by
  apply continuous_pi
  intro ij
  exact ((continuous_apply ij.1).comp continuous_fst).mul ((continuous_apply ij.2).comp continuous_snd)

/-- `x ↦ A x` as a continuous linear map on `E d`. -/
noncomputable def matCLM (A : Matrix (Fin d) (Fin d) ℝ) : E d →L[ℝ] E d :=
  LinearMap.toContinuousLinearMap
  { toFun := fun x => ((A *ᵥ x : Fin d → ℝ) : E d)
    map_add' := fun x y => mulVec_add A x y
    map_smul' := fun c x => mulVec_smul A c x }

lemma matCLM_apply (A : Matrix (Fin d) (Fin d) ℝ) (x : E d) (i : Fin d) :
  matCLM A x i = ∑ k, A i k * x k := rfl

/-- `(x - β A x)(x - β A x)ᵀ = X - β (A X + X Aᵀ) + β² A X Aᵀ` with `X = x xᵀ`. -/
lemma outer_sub_smul_mulVec (A : Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (x : E d) :
  outer (x - b • matCLM A x) (x - b • matCLM A x) =
    outer x x - b • lyapOp A (outer x x) + b ^ 2 • sandwich A (outer x x) := by
  funext ij
  simp only [outer, lyapOp, sandwich, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, matCLM_apply]
  have h1 : ∑ k, A ij.1 k * (x k * x ij.2) = (∑ k, A ij.1 k * x k) * x ij.2 := by
    rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
  have h2 : ∑ k, x ij.1 * x k * A ij.2 k = x ij.1 * ∑ k, A ij.2 k * x k := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  have h3 : ∑ k, ∑ l, A ij.1 k * (x k * x l) * A ij.2 l =
      (∑ k, A ij.1 k * x k) * ∑ l, A ij.2 l * x l := by
    rw [sum_mul_sum]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [h1, h2, h3]
  ring

/-! ### Moments -/

instance : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩

/-- `E[a cᵀ]`. -/
noncomputable def crossMoment (μ : Measure Ω) (a c : Ω → E d) : Mat d :=
  ∫ ω, outer (a ω) (c ω) ∂μ

/-- `E[a aᵀ]`. -/
noncomputable def secondMoment (μ : Measure Ω) (a : Ω → E d) : Mat d := crossMoment μ a a

lemma aestronglyMeasurable_outer {a c : Ω → E d} (ha : AEStronglyMeasurable a μ)
  (hc : AEStronglyMeasurable c μ) : AEStronglyMeasurable (fun ω => outer (a ω) (c ω)) μ :=
  continuous_outer.comp_aestronglyMeasurable (ha.prodMk hc)

lemma integrable_outer {a c : Ω → E d} (ha : MemLp a 2 μ) (hc : MemLp c 2 μ) :
  Integrable (fun ω => outer (a ω) (c ω)) μ := by
  refine Integrable.mono' (g := fun ω => ‖a ω‖ * ‖c ω‖) (ha.norm.integrable_mul hc.norm)
    (aestronglyMeasurable_outer ha.1 hc.1) (Eventually.of_forall fun ω => ?_)
  rw [norm_outer]

/-- Cauchy–Schwarz for `E[‖a‖ ‖c‖]`. -/
lemma integral_norm_mul_le {a c : Ω → E d} (ha : MemLp a 2 μ) (hc : MemLp c 2 μ) :
  ∫ ω, ‖a ω‖ * ‖c ω‖ ∂μ ≤ √(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) := by
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun ω => ‖a ω‖) (g := fun ω => ‖c ω‖)
    (Eventually.of_forall fun ω => norm_nonneg _) (Eventually.of_forall fun ω => norm_nonneg _)
    (by simpa using ha.norm) (by simpa using hc.norm)
  simp only [Real.rpow_two] at this
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- `‖E[a cᵀ]‖ ≤ √E‖a‖² √E‖c‖²`. -/
lemma norm_crossMoment_le {a c : Ω → E d} (ha : MemLp a 2 μ) (hc : MemLp c 2 μ) :
  ‖crossMoment μ a c‖ ≤ √(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp_rw [norm_outer]
  exact integral_norm_mul_le ha hc

lemma crossMoment_apply {a c : Ω → E d} (ha : MemLp a 2 μ) (hc : MemLp c 2 μ)
  (ij : Fin d × Fin d) :
  crossMoment μ a c ij = ∫ ω, a ω ij.1 * c ω ij.2 ∂μ := by
  have := (EuclideanSpace.proj (𝕜 := ℝ) ij).integral_comp_comm (integrable_outer ha hc)
  show EuclideanSpace.proj (𝕜 := ℝ) ij (∫ ω, outer (a ω) (c ω) ∂μ) = _
  rw [← this]
  rfl

lemma memLp_apply {a : Ω → E d} (ha : MemLp a 2 μ) (i : Fin d) :
  MemLp (fun ω => a ω i) 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' ha

/-- The cross moment of an `ℱ`-measurable vector with a martingale difference vanishes
(tower property). -/
lemma crossMoment_eq_zero {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0) [IsFiniteMeasure μ]
  {a c : Ω → E d} (ha : StronglyMeasurable[ℱ] a) (haL : MemLp a 2 μ) (hcL : MemLp c 2 μ)
  (hc : ∀ j, μ[fun ω => c ω j | ℱ] =ᵐ[μ] 0) :
  crossMoment μ a c = 0 := by
  funext ij
  rw [crossMoment_apply haL hcL]
  have hai : StronglyMeasurable[ℱ] fun ω => a ω ij.1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) ij.1).continuous.comp_stronglyMeasurable ha
  have hint : Integrable ((fun ω => a ω ij.1) * fun ω => c ω ij.2) μ :=
    (memLp_apply haL ij.1).integrable_mul (memLp_apply hcL ij.2)
  have hcj : Integrable (fun ω => c ω ij.2) μ := (memLp_apply hcL ij.2).integrable one_le_two
  have h1 := condExp_mul_of_stronglyMeasurable_left hai hint hcj
  calc ∫ ω, a ω ij.1 * c ω ij.2 ∂μ
      = ∫ ω, (μ[(fun ω => a ω ij.1) * fun ω => c ω ij.2 | ℱ]) ω ∂μ :=
        (integral_condExp hℱ).symm
    _ = ∫ ω, a ω ij.1 * (μ[fun ω => c ω ij.2 | ℱ]) ω ∂μ := integral_congr_ae h1
    _ = 0 := by
        have h0 : (fun ω => a ω ij.1 * (μ[fun ω => c ω ij.2 | ℱ]) ω) =ᵐ[μ] fun _ => (0 : ℝ) := by
          filter_upwards [hc ij.2] with ω hω
          rw [hω]
          simp
        rw [integral_congr_ae h0]
        simp

/-- The same with the factors in the other order. -/
lemma crossMoment_eq_zero' {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0) [IsFiniteMeasure μ]
  {a c : Ω → E d} (ha : StronglyMeasurable[ℱ] a) (haL : MemLp a 2 μ) (hcL : MemLp c 2 μ)
  (hc : ∀ j, μ[fun ω => c ω j | ℱ] =ᵐ[μ] 0) :
  crossMoment μ c a = 0 := by
  have h := crossMoment_eq_zero hℱ ha haL hcL hc
  funext ij
  have := congrFun h (ij.2, ij.1)
  rw [crossMoment_apply hcL haL]
  rw [crossMoment_apply haL hcL] at this
  simpa [mul_comm] using this

/-! ### Algebra of moments -/

lemma outer_add_left (x y z : E d) : outer (x + y) z = outer x z + outer y z := by
  funext ij; simp [outer, add_mul]

lemma outer_add_right (x y z : E d) : outer x (y + z) = outer x y + outer x z := by
  funext ij; simp [outer, mul_add]

lemma outer_smul_left (r : ℝ) (x y : E d) : outer (r • x) y = r • outer x y := by
  funext ij; simp [outer, mul_assoc]

lemma outer_smul_right (r : ℝ) (x y : E d) : outer x (r • y) = r • outer x y := by
  funext ij; simp [outer]; ring

lemma crossMoment_add_left {a b c : Ω → E d} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
  (hc : MemLp c 2 μ) :
  crossMoment μ (fun ω => a ω + b ω) c = crossMoment μ a c + crossMoment μ b c := by
  simp only [crossMoment, outer_add_left]
  exact integral_add (integrable_outer ha hc) (integrable_outer hb hc)

lemma crossMoment_add_right {a b c : Ω → E d} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
  (hc : MemLp c 2 μ) :
  crossMoment μ a (fun ω => b ω + c ω) = crossMoment μ a b + crossMoment μ a c := by
  simp only [crossMoment, outer_add_right]
  exact integral_add (integrable_outer ha hb) (integrable_outer ha hc)

lemma crossMoment_smul_left (r : ℝ) (a c : Ω → E d) :
  crossMoment μ (fun ω => r • a ω) c = r • crossMoment μ a c := by
  simp only [crossMoment, outer_smul_left]
  exact integral_smul r _

lemma crossMoment_smul_right (r : ℝ) (a c : Ω → E d) :
  crossMoment μ a (fun ω => r • c ω) = r • crossMoment μ a c := by
  simp only [crossMoment, outer_smul_right]
  exact integral_smul r _

/-- `E‖a‖² = tr E[a aᵀ] ≤ d ‖E[a aᵀ]‖`. -/
lemma integral_norm_sq_le {a : Ω → E d} (ha : MemLp a 2 μ) :
  ∫ ω, ‖a ω‖ ^ 2 ∂μ ≤ d * ‖secondMoment μ a‖ := by
  have hsum : (fun ω => ‖a ω‖ ^ 2) = fun ω => ∑ i, a ω i * a ω i := by
    funext ω
    rw [EuclideanSpace.norm_sq_eq]
    exact sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, sq]
  rw [hsum, integral_finset_sum univ (f := fun i ω => a ω i * a ω i) fun i _ =>
    (memLp_apply ha i).integrable_mul (memLp_apply ha i)]
  calc ∑ i, ∫ ω, a ω i * a ω i ∂μ = ∑ i : Fin d, secondMoment μ a (i, i) :=
        sum_congr rfl fun i _ => (crossMoment_apply ha ha (i, i)).symm
    _ ≤ ∑ _i : Fin d, ‖secondMoment μ a‖ := sum_le_sum fun i _ => by
        have := PiLp.norm_apply_le (secondMoment μ a) (i, i)
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
    _ = d * ‖secondMoment μ a‖ := by simp

lemma integral_norm_sq_nonneg (a : Ω → E d) : 0 ≤ ∫ ω, ‖a ω‖ ^ 2 ∂μ :=
  integral_nonneg fun ω => by positivity

/-! ### The iterates -/

/-- The iterates are adapted and square integrable. -/
lemma iterates_adapted (ℱ : MeasureTheory.Filtration ℕ m0) (A : Matrix (Fin d) (Fin d) ℝ)
  {β : ℕ → ℝ} {θ M h : ℕ → Ω → E d}
  (hθ : ∀ k ω, θ (k + 1) ω =
    θ k ω - β k • matCLM A (θ k ω) + β k • (M (k + 1) ω + h k ω - h (k + 1) ω))
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ) :
  ∀ k, StronglyMeasurable[ℱ k] (θ k) ∧ MemLp (θ k) 2 μ := by
  intro k
  induction k with
  | zero => exact ⟨hθ0, hθ0L⟩
  | succ k ih =>
    have hfun : θ (k + 1) = fun ω =>
        θ k ω - β k • matCLM A (θ k ω) + β k • (M (k + 1) ω + h k ω - h (k + 1) ω) :=
      funext (hθ k)
    rw [hfun]
    have hmono := ℱ.mono (Nat.le_succ k)
    constructor
    · have h1 := ih.1.mono hmono
      have h2 := ((matCLM A).continuous.comp_stronglyMeasurable ih.1).mono hmono
      have h3 := (hh k).mono hmono
      exact (h1.sub (h2.const_smul (β k))).add ((((hM k).add h3).sub (hh (k + 1))).const_smul (β k))
    · exact (ih.2.sub (((matCLM A).comp_memLp' ih.2).const_smul (β k))).add
        ((((hML k).add (hhL k)).sub (hhL (k + 1))).const_smul (β k))

/-- Lemma 2.3 of the write-up: removing the telescoping part of the noise. -/
lemma shifted_iterate (A : Matrix (Fin d) (Fin d) ℝ) {β : ℕ → ℝ} {θ M h : ℕ → Ω → E d}
  (hθ : ∀ k ω, θ (k + 1) ω =
    θ k ω - β k • matCLM A (θ k ω) + β k • (M (k + 1) ω + h k ω - h (k + 1) ω)) (k : ℕ) (ω : Ω) :
  θ (k + 1) ω + β (k + 1) • h (k + 1) ω =
    ((θ k ω + β k • h k ω) - β k • matCLM A (θ k ω + β k • h k ω)) + β k • M (k + 1) ω
      + ((β k ^ 2) • matCLM A (h k ω) + (β (k + 1) - β k) • h (k + 1) ω) := by
  rw [hθ k ω, map_add, map_smul]
  simp only [smul_add, smul_sub, sub_smul, smul_smul, sq]
  abel

/-! ### Second moments of the shifted iterates -/

lemma memLp_sq_integrable {a : Ω → E d} (ha : MemLp a 2 μ) :
  Integrable (fun ω => ‖a ω‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm ha.1).mp ha

/-- `E[(x - β A x)(x - β A x)ᵀ] = P - β (A P + P Aᵀ) + β² A P Aᵀ`. -/
lemma secondMoment_sub_smul (A : Matrix (Fin d) (Fin d) ℝ) (b : ℝ) {x : Ω → E d}
  (hx : MemLp x 2 μ) :
  secondMoment μ (fun ω => x ω - b • matCLM A (x ω)) =
    secondMoment μ x - b • lyapOp A (secondMoment μ x)
      + b ^ 2 • sandwich A (secondMoment μ x) := by
  have hX := integrable_outer hx hx
  simp only [secondMoment, crossMoment, outer_sub_smul_mulVec]
  have h1 : Integrable (fun ω => lyapOp A (outer (x ω) (x ω))) μ := (lyapOp A).integrable_comp hX
  have h2 : Integrable (fun ω => sandwich A (outer (x ω) (x ω))) μ :=
    (sandwich A).integrable_comp hX
  have h1' : Integrable (fun ω => b • lyapOp A (outer (x ω) (x ω))) μ := Integrable.smul b h1
  have h2' : Integrable (fun ω => b ^ 2 • sandwich A (outer (x ω) (x ω))) μ :=
    Integrable.smul (b ^ 2) h2
  have h3 : Integrable (fun ω => outer (x ω) (x ω) - b • lyapOp A (outer (x ω) (x ω))) μ :=
    hX.sub h1'
  rw [integral_add h3 h2', integral_sub hX h1', integral_smul, integral_smul,
    (lyapOp A).integral_comp_comm hX, (sandwich A).integral_comp_comm hX]

lemma norm_sq_le_of_le {x : ℝ} {a b : ℝ} (hx : 0 ≤ x) (h : x ≤ a + b) :
  x ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The remainder of the second-moment recursion (Lemma 2.4 of the write-up). -/
theorem secondMoment_recursion [IsProbabilityMeasure μ] {β : ℕ → ℝ} {βbar : ℝ}
  (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ)
  (ℱ : MeasureTheory.Filtration ℕ m0) {θ M h : ℕ → Ω → E d}
  (hθ : ∀ k ω, θ (k + 1) ω =
    θ k ω - β k • matCLM A (θ k ω) + β k • (M (k + 1) ω + h k ω - h (k + 1) ω))
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hMB : ∃ CM, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
  (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0) :
  ∃ C, 0 ≤ C ∧ ∀ k,
    ‖secondMoment μ (fun ω => θ (k + 1) ω + β (k + 1) • h (k + 1) ω)
      - (secondMoment μ (fun ω => θ k ω + β k • h k ω)
        - β k • lyapOp A (secondMoment μ (fun ω => θ k ω + β k • h k ω))
        + β k ^ 2 • sandwich A (secondMoment μ (fun ω => θ k ω + β k • h k ω))
        + β k ^ 2 • secondMoment μ (M (k + 1)))‖ ≤
    C * β k ^ 2 * (√‖secondMoment μ (fun ω => θ k ω + β k • h k ω)‖ + β k) := by
  have hadapt := iterates_adapted ℱ A hθ hθ0 hθ0L hh hhL hM hML
  obtain ⟨Ch, hCh⟩ := hhB
  obtain ⟨CM, hCM⟩ := hMB
  obtain ⟨Cs, hCs0, hCs⟩ := hβ.abs_sub_le
  obtain ⟨B0, hB0⟩ := hβ.tendsto_zero.bddAbove_range
  obtain ⟨B, hB_def⟩ : ∃ B, B = max B0 0 := ⟨_, rfl⟩
  have hB : ∀ k, β k ≤ B := fun k => (hB0 ⟨k, rfl⟩).trans (hB_def ▸ le_max_left _ _)
  have hBnn : 0 ≤ B := hB_def ▸ le_max_right _ _
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hCh 0)
  have hCM0 : 0 ≤ CM := (integral_norm_sq_nonneg (μ := μ) (M 1)).trans (hCM 0)
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = ‖matCLM A‖ := ⟨_, rfl⟩
  have hAm0 : 0 ≤ Am := hAm ▸ norm_nonneg _
  obtain ⟨Kc, hKc_def⟩ : ∃ Kc, Kc = 2 * (Am ^ 2 + Cs ^ 2) * Ch := ⟨_, rfl⟩
  have hKc : 0 ≤ Kc := by rw [hKc_def]; positivity
  obtain ⟨C, hC_def⟩ : ∃ C, C = 2 * (1 + B * Am) * √d * √Kc + 2 * √CM * √Kc + Kc * B :=
    ⟨_, rfl⟩
  refine ⟨C, by rw [hC_def]; positivity, fun k => ?_⟩
  have hb := hβ.pos k
  obtain ⟨θ', hθ'_def⟩ : ∃ θ' : Ω → E d, θ' = fun ω => θ k ω + β k • h k ω := ⟨_, rfl⟩
  have hθ'L : MemLp θ' 2 μ := by
    rw [hθ'_def]; exact (hadapt k).2.add ((hhL k).const_smul (β k))
  have hθ'm : StronglyMeasurable[ℱ k] θ' := by
    rw [hθ'_def]; exact (hadapt k).1.add ((hh k).const_smul (β k))
  obtain ⟨a, ha_def⟩ : ∃ a : Ω → E d, a = fun ω => θ' ω - β k • matCLM A (θ' ω) := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Ω → E d, b = fun ω => β k • M (k + 1) ω := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : Ω → E d,
      c = fun ω => (β k ^ 2) • matCLM A (h k ω) + (β (k + 1) - β k) • h (k + 1) ω := ⟨_, rfl⟩
  have haL : MemLp a 2 μ := by
    rw [ha_def]; exact hθ'L.sub (((matCLM A).comp_memLp' hθ'L).const_smul (β k))
  have hbL : MemLp b 2 μ := by rw [hb_def]; exact (hML k).const_smul (β k)
  have hcL : MemLp c 2 μ := by
    rw [hc_def]
    exact (((matCLM A).comp_memLp' (hhL k)).const_smul (β k ^ 2)).add
      ((hhL (k + 1)).const_smul (β (k + 1) - β k))
  have ham : StronglyMeasurable[ℱ k] a := by
    rw [ha_def]
    exact hθ'm.sub (((matCLM A).continuous.comp_stronglyMeasurable hθ'm).const_smul (β k))
  have hnext : (fun ω => θ (k + 1) ω + β (k + 1) • h (k + 1) ω) = fun ω => a ω + b ω + c ω := by
    funext ω
    rw [ha_def, hb_def, hc_def, hθ'_def]
    exact shifted_iterate A hθ k ω
  -- expand the second moment of a + b + c
  have hab : MemLp (fun ω => a ω + b ω) 2 μ := haL.add hbL
  have habc : MemLp (fun ω => a ω + b ω + c ω) 2 μ := hab.add hcL
  have hexp : secondMoment μ (fun ω => a ω + b ω + c ω) =
      crossMoment μ a a + crossMoment μ a b + crossMoment μ a c
      + (crossMoment μ b a + crossMoment μ b b + crossMoment μ b c)
      + (crossMoment μ c a + crossMoment μ c b + crossMoment μ c c) := by
    simp only [secondMoment]
    rw [crossMoment_add_left hab hcL habc, crossMoment_add_left haL hbL habc,
      crossMoment_add_right haL hab hcL, crossMoment_add_right haL haL hbL,
      crossMoment_add_right hbL hab hcL, crossMoment_add_right hbL haL hbL,
      crossMoment_add_right hcL hab hcL, crossMoment_add_right hcL haL hbL]
  have hAB : crossMoment μ a b = 0 := by
    rw [hb_def, crossMoment_smul_right,
      crossMoment_eq_zero (ℱ.le k) ham haL (hML k) (hmart k), smul_zero]
  have hBA : crossMoment μ b a = 0 := by
    rw [hb_def, crossMoment_smul_left,
      crossMoment_eq_zero' (ℱ.le k) ham haL (hML k) (hmart k), smul_zero]
  have hAA : crossMoment μ a a = secondMoment μ θ' - β k • lyapOp A (secondMoment μ θ')
      + β k ^ 2 • sandwich A (secondMoment μ θ') := by
    rw [ha_def]; exact secondMoment_sub_smul A (β k) hθ'L
  have hBB : crossMoment μ b b = β k ^ 2 • secondMoment μ (M (k + 1)) := by
    rw [hb_def, secondMoment, crossMoment_smul_left, crossMoment_smul_right, smul_smul, sq]
  rw [← hθ'_def]
  have hRform : secondMoment μ (fun ω => θ (k + 1) ω + β (k + 1) • h (k + 1) ω)
      - (secondMoment μ θ' - β k • lyapOp A (secondMoment μ θ')
        + β k ^ 2 • sandwich A (secondMoment μ θ') + β k ^ 2 • secondMoment μ (M (k + 1))) =
      crossMoment μ a c + crossMoment μ b c + crossMoment μ c a + crossMoment μ c b
        + crossMoment μ c c := by
    rw [hnext, hexp, hAB, hBA, hAA, hBB]
    abel
  rw [hRform]
  -- bounds on the three second moments
  obtain ⟨P, hP_def⟩ : ∃ P, P = secondMoment μ θ' := ⟨_, rfl⟩
  rw [← hP_def]
  have hEa : ∫ ω, ‖a ω‖ ^ 2 ∂μ ≤ (1 + β k * Am) ^ 2 * (d * ‖P‖) := by
    have hpt : ∀ ω, ‖a ω‖ ^ 2 ≤ (1 + β k * Am) ^ 2 * ‖θ' ω‖ ^ 2 := by
      intro ω
      have : ‖a ω‖ ≤ (1 + β k * Am) * ‖θ' ω‖ := by
        rw [ha_def]
        calc ‖θ' ω - β k • matCLM A (θ' ω)‖ ≤ ‖θ' ω‖ + ‖β k • matCLM A (θ' ω)‖ :=
              norm_sub_le _ _
          _ ≤ ‖θ' ω‖ + β k * (Am * ‖θ' ω‖) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb, hAm]
              gcongr
              exact (matCLM A).le_opNorm _
          _ = (1 + β k * Am) * ‖θ' ω‖ := by ring
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    calc ∫ ω, ‖a ω‖ ^ 2 ∂μ ≤ ∫ ω, (1 + β k * Am) ^ 2 * ‖θ' ω‖ ^ 2 ∂μ :=
          integral_mono (memLp_sq_integrable haL) ((memLp_sq_integrable hθ'L).const_mul _) hpt
      _ = (1 + β k * Am) ^ 2 * ∫ ω, ‖θ' ω‖ ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (1 + β k * Am) ^ 2 * (d * ‖P‖) := by
          rw [hP_def]
          exact mul_le_mul_of_nonneg_left (integral_norm_sq_le hθ'L) (sq_nonneg _)
  have hEb : ∫ ω, ‖b ω‖ ^ 2 ∂μ ≤ β k ^ 2 * CM := by
    have : (fun ω => ‖b ω‖ ^ 2) = fun ω => β k ^ 2 * ‖M (k + 1) ω‖ ^ 2 := by
      funext ω
      rw [hb_def]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [this, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hCM k) (sq_nonneg _)
  have hEc : ∫ ω, ‖c ω‖ ^ 2 ∂μ ≤ Kc * β k ^ 4 := by
    have hpt : ∀ ω, ‖c ω‖ ^ 2 ≤
        β k ^ 4 * (2 * Am ^ 2 * ‖h k ω‖ ^ 2 + 2 * Cs ^ 2 * ‖h (k + 1) ω‖ ^ 2) := by
      intro ω
      have h1 : ‖c ω‖ ≤ β k ^ 2 * (Am * ‖h k ω‖) + Cs * β k ^ 2 * ‖h (k + 1) ω‖ := by
        rw [hc_def]
        calc ‖(β k ^ 2) • matCLM A (h k ω) + (β (k + 1) - β k) • h (k + 1) ω‖
            ≤ ‖(β k ^ 2) • matCLM A (h k ω)‖ + ‖(β (k + 1) - β k) • h (k + 1) ω‖ :=
              norm_add_le _ _
          _ ≤ β k ^ 2 * (Am * ‖h k ω‖) + Cs * β k ^ 2 * ‖h (k + 1) ω‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (sq_nonneg _), hAm]
              gcongr
              · exact (matCLM A).le_opNorm _
              · exact hCs k
      have := norm_sq_le_of_le (norm_nonneg _) h1
      have e : 2 * (β k ^ 2 * (Am * ‖h k ω‖)) ^ 2 + 2 * (Cs * β k ^ 2 * ‖h (k + 1) ω‖) ^ 2 =
          β k ^ 4 * (2 * Am ^ 2 * ‖h k ω‖ ^ 2 + 2 * Cs ^ 2 * ‖h (k + 1) ω‖ ^ 2) := by ring
      linarith
    calc ∫ ω, ‖c ω‖ ^ 2 ∂μ
        ≤ ∫ ω, β k ^ 4 * (2 * Am ^ 2 * ‖h k ω‖ ^ 2 + 2 * Cs ^ 2 * ‖h (k + 1) ω‖ ^ 2) ∂μ :=
          integral_mono (memLp_sq_integrable hcL)
            ((((memLp_sq_integrable (hhL k)).const_mul _).add
              ((memLp_sq_integrable (hhL (k + 1))).const_mul _)).const_mul _) hpt
      _ = β k ^ 4 * (2 * Am ^ 2 * ∫ ω, ‖h k ω‖ ^ 2 ∂μ
            + 2 * Cs ^ 2 * ∫ ω, ‖h (k + 1) ω‖ ^ 2 ∂μ) := by
          rw [integral_const_mul, integral_add ((memLp_sq_integrable (hhL k)).const_mul _)
            ((memLp_sq_integrable (hhL (k + 1))).const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ β k ^ 4 * (2 * Am ^ 2 * Ch + 2 * Cs ^ 2 * Ch) := by
          gcongr
          · exact hCh k
          · exact hCh (k + 1)
      _ = Kc * β k ^ 4 := by rw [hKc_def]; ring
  -- square roots of the bounds
  have hsa : √(∫ ω, ‖a ω‖ ^ 2 ∂μ) ≤ (1 + B * Am) * √d * √‖P‖ := by
    calc √(∫ ω, ‖a ω‖ ^ 2 ∂μ) ≤ √((1 + β k * Am) ^ 2 * (d * ‖P‖)) := Real.sqrt_le_sqrt hEa
      _ = (1 + β k * Am) * √d * √‖P‖ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
            Real.sqrt_mul (Nat.cast_nonneg d), mul_assoc]
      _ ≤ (1 + B * Am) * √d * √‖P‖ := by gcongr; exact hB k
  have hsb : √(∫ ω, ‖b ω‖ ^ 2 ∂μ) ≤ β k * √CM := by
    calc √(∫ ω, ‖b ω‖ ^ 2 ∂μ) ≤ √(β k ^ 2 * CM) := Real.sqrt_le_sqrt hEb
      _ = β k * √CM := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb.le]
  have hsc : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) ≤ β k ^ 2 * √Kc := by
    calc √(∫ ω, ‖c ω‖ ^ 2 ∂μ) ≤ √(Kc * β k ^ 4) := Real.sqrt_le_sqrt hEc
      _ = β k ^ 2 * √Kc := by
          rw [Real.sqrt_mul hKc, show β k ^ 4 = (β k ^ 2) ^ 2 by ring,
            Real.sqrt_sq (sq_nonneg _), mul_comm]
  have hsc2 : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) ≤ Kc * β k ^ 4 := by
    rw [Real.mul_self_sqrt (integral_norm_sq_nonneg c)]
    exact hEc
  -- assemble
  have n1 := norm_crossMoment_le (μ := μ) haL hcL
  have n2 := norm_crossMoment_le (μ := μ) hbL hcL
  have n3 := norm_crossMoment_le (μ := μ) hcL haL
  have n4 := norm_crossMoment_le (μ := μ) hcL hbL
  have n5 := norm_crossMoment_le (μ := μ) hcL hcL
  have sc0 := Real.sqrt_nonneg (∫ ω, ‖c ω‖ ^ 2 ∂μ)
  have hP0 := Real.sqrt_nonneg ‖P‖
  have hd0 := Real.sqrt_nonneg (d : ℝ)
  have hK0 := Real.sqrt_nonneg Kc
  have hM0 := Real.sqrt_nonneg CM
  have hbB := hB k
  have hac : √(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) ≤
      ((1 + B * Am) * √d * √‖P‖) * (β k ^ 2 * √Kc) :=
    mul_le_mul hsa hsc sc0 (by positivity)
  have hbc : √(∫ ω, ‖b ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) ≤ (β k * √CM) * (β k ^ 2 * √Kc) :=
    mul_le_mul hsb hsc sc0 (by positivity)
  have t1 := norm_add_le (crossMoment μ a c + crossMoment μ b c + crossMoment μ c a
    + crossMoment μ c b) (crossMoment μ c c)
  have t2 := norm_add_le (crossMoment μ a c + crossMoment μ b c + crossMoment μ c a)
    (crossMoment μ c b)
  have t3 := norm_add_le (crossMoment μ a c + crossMoment μ b c) (crossMoment μ c a)
  have t4 := norm_add_le (crossMoment μ a c) (crossMoment μ b c)
  have hsum : ‖crossMoment μ a c + crossMoment μ b c + crossMoment μ c a + crossMoment μ c b
      + crossMoment μ c c‖ ≤
      2 * (((1 + B * Am) * √d * √‖P‖) * (β k ^ 2 * √Kc))
      + 2 * ((β k * √CM) * (β k ^ 2 * √Kc)) + Kc * β k ^ 4 := by
    have e1 : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) * √(∫ ω, ‖a ω‖ ^ 2 ∂μ) =
        √(∫ ω, ‖a ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) := mul_comm _ _
    have e2 : √(∫ ω, ‖c ω‖ ^ 2 ∂μ) * √(∫ ω, ‖b ω‖ ^ 2 ∂μ) =
        √(∫ ω, ‖b ω‖ ^ 2 ∂μ) * √(∫ ω, ‖c ω‖ ^ 2 ∂μ) := mul_comm _ _
    linarith
  refine hsum.trans ?_
  have e3 : Kc * β k ^ 4 ≤ Kc * B * β k ^ 3 := by
    have : β k ^ 4 ≤ B * β k ^ 3 := by
      rw [show β k ^ 4 = β k * β k ^ 3 by ring]
      exact mul_le_mul_of_nonneg_right hbB (by positivity)
    calc Kc * β k ^ 4 ≤ Kc * (B * β k ^ 3) := mul_le_mul_of_nonneg_left this hKc
      _ = Kc * B * β k ^ 3 := by ring
  have e4 : 2 * ((β k * √CM) * (β k ^ 2 * √Kc)) = 2 * √CM * √Kc * β k ^ 3 := by ring
  have e5 : 2 * (((1 + B * Am) * √d * √‖P‖) * (β k ^ 2 * √Kc)) =
      2 * (1 + B * Am) * √d * √Kc * (β k ^ 2 * √‖P‖) := by ring
  have e6 : C * β k ^ 2 * (√‖P‖ + β k) =
      (2 * (1 + B * Am) * √d * √Kc) * (β k ^ 2 * √‖P‖)
        + (2 * √CM * √Kc) * β k ^ 3 + (Kc * B) * β k ^ 3
        + (2 * √CM * √Kc + Kc * B) * (β k ^ 2 * √‖P‖)
        + (2 * (1 + B * Am) * √d * √Kc) * β k ^ 3 := by
    rw [hC_def]; ring
  have p1 : 0 ≤ (2 * √CM * √Kc + Kc * B) * (β k ^ 2 * √‖P‖) := by positivity
  have p2 : 0 ≤ (2 * (1 + B * Am) * √d * √Kc) * β k ^ 3 := by positivity
  rw [e4, e5, e6]
  linarith

/-! ### The main theorem -/

/-- **Theorem 2.1 of the write-up.** Linear stochastic approximation
`θ (k+1) = θ k - β k A θ k + β k V k` with Markov noise decomposed as
`V k = M (k+1) + h k - h (k+1)` (martingale difference `M`, bounded-variance `h`) has
`β k⁻¹ E[θ k θ kᵀ] → Σ`, where `Σ` solves `(A - β̄/2) Σ + Σ (A - β̄/2)ᵀ = Γ` and
`Γ = lim E[M (k+1) M (k+1)ᵀ]`. -/
theorem tendsto_secondMoment_of_markov_noise [IsProbabilityMeasure μ] {β : ℕ → ℝ} {βbar : ℝ}
  (hβ : StepSizeRate β βbar) (A : Matrix (Fin d) (Fin d) ℝ) {η : ℝ} (hη : 0 < η)
  (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
  (ℱ : MeasureTheory.Filtration ℕ m0) {θ M h : ℕ → Ω → E d} {Γ : Mat d}
  (hθ : ∀ k ω, θ (k + 1) ω =
    θ k ω - β k • matCLM A (θ k ω) + β k • (M (k + 1) ω + h k ω - h (k + 1) ω))
  (hθ0 : StronglyMeasurable[ℱ 0] (θ 0)) (hθ0L : MemLp (θ 0) 2 μ)
  (hh : ∀ k, StronglyMeasurable[ℱ k] (h k)) (hhL : ∀ k, MemLp (h k) 2 μ)
  (hhB : ∃ Ch, ∀ k, ∫ ω, ‖h k ω‖ ^ 2 ∂μ ≤ Ch)
  (hM : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hML : ∀ k, MemLp (M (k + 1)) 2 μ)
  (hMB : ∃ CM, ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ ≤ CM)
  (hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
  (hΓ : Tendsto (fun k => secondMoment μ (M (k + 1))) atTop (𝓝 Γ)) :
  ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
    Tendsto (fun k => (β k)⁻¹ • secondMoment μ (θ k)) atTop (𝓝 Sig) := by
  obtain ⟨Sig, hSig⟩ := exists_solution_of_coercive _ (by positivity : (0 : ℝ) < 2 * η)
    (lyapOp_coercive _ hA) Γ
  refine ⟨Sig, hSig, ?_⟩
  have hadapt := iterates_adapted ℱ A hθ hθ0 hθ0L hh hhL hM hML
  obtain ⟨C, hC0, hCR⟩ :=
    secondMoment_recursion hβ A ℱ hθ hθ0 hθ0L hh hhL hhB hM hML hMB hmart
  obtain ⟨P, hP_def⟩ : ∃ P : ℕ → Mat d,
      P = fun k => secondMoment μ (fun ω => θ k ω + β k • h k ω) := ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ R : ℕ → Mat d, R = fun k => P (k + 1) - (P k - β k • lyapOp A (P k)
      + β k ^ 2 • sandwich A (P k) + β k ^ 2 • secondMoment μ (M (k + 1))) := ⟨_, rfl⟩
  have hrec : ∀ k, P (k + 1) = P k - β k • lyapOp A (P k) + β k ^ 2 • sandwich A (P k)
      + β k ^ 2 • secondMoment μ (M (k + 1)) + R k := by
    intro k
    simp only [hR_def]
    abel
  have hRb : ∃ C, 0 ≤ C ∧ ∀ k, ‖R k‖ ≤ C * β k ^ 2 * (√‖P k‖ + β k) :=
    ⟨C, hC0, fun k => by rw [hR_def, hP_def]; exact hCR k⟩
  have hPlim := tendsto_normalized_second_moment hβ A hη hA hSig hΓ hRb hrec
  -- the shifted second moments tend to zero
  have hP0 : Tendsto (fun k => ‖P k‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => β k • ((β k)⁻¹ • P k)) atTop (𝓝 ((0 : ℝ) • Sig)) :=
      hβ.tendsto_zero.smul hPlim
    rw [zero_smul] at h1
    have h2 : (fun k => β k • ((β k)⁻¹ • P k)) = P :=
      funext fun k => by rw [smul_smul, mul_inv_cancel₀ (hβ.pos k).ne', one_smul]
    rw [h2] at h1
    simpa using h1.norm
  -- the moments of `θ` and of the shifted iterates differ by `o(β)`
  obtain ⟨Ch, hCh⟩ := hhB
  have hCh0 : 0 ≤ Ch := (integral_norm_sq_nonneg (μ := μ) (h 0)).trans (hCh 0)
  have hdiff : ∀ k, ‖(β k)⁻¹ • secondMoment μ (θ k) - (β k)⁻¹ • P k‖ ≤
      2 * (√(d * ‖P k‖) * √Ch) + β k * Ch := by
    intro k
    have hb := hβ.pos k
    obtain ⟨θ', hθ'_def⟩ : ∃ θ' : Ω → E d, θ' = fun ω => θ k ω + β k • h k ω := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : Ω → E d, g = fun ω => (-β k) • h k ω := ⟨_, rfl⟩
    have hθ'L : MemLp θ' 2 μ := by
      rw [hθ'_def]; exact (hadapt k).2.add ((hhL k).const_smul (β k))
    have hgL : MemLp g 2 μ := by rw [hg_def]; exact (hhL k).const_smul (-β k)
    have hPk : P k = secondMoment μ θ' := by rw [hP_def, hθ'_def]
    have hθk : θ k = fun ω => θ' ω + g ω := by
      funext ω
      rw [hθ'_def, hg_def]
      simp only [neg_smul]
      abel
    have hexp : secondMoment μ (θ k) =
        secondMoment μ θ' + crossMoment μ θ' g + (crossMoment μ g θ' + crossMoment μ g g) := by
      rw [hθk, secondMoment, crossMoment_add_left hθ'L hgL
        (show MemLp (fun ω => θ' ω + g ω) 2 μ from hθ'L.add hgL),
        crossMoment_add_right hθ'L hθ'L hgL, crossMoment_add_right hgL hθ'L hgL]
      rfl
    have hEg : ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ β k ^ 2 * Ch := by
      have : (fun ω => ‖g ω‖ ^ 2) = fun ω => β k ^ 2 * ‖h k ω‖ ^ 2 := by
        funext ω
        rw [hg_def]
        simp only [norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
      rw [this, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hCh k) (sq_nonneg _)
    have hsg : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ β k * √Ch := by
      calc √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ √(β k ^ 2 * Ch) := Real.sqrt_le_sqrt hEg
        _ = β k * √Ch := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb.le]
    have hsθ : √(∫ ω, ‖θ' ω‖ ^ 2 ∂μ) ≤ √(d * ‖P k‖) := by
      rw [hPk]; exact Real.sqrt_le_sqrt (integral_norm_sq_le hθ'L)
    have hsg2 : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) * √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ β k ^ 2 * Ch := by
      rw [Real.mul_self_sqrt (integral_norm_sq_nonneg g)]; exact hEg
    have n1 := norm_crossMoment_le (μ := μ) hθ'L hgL
    have n2 := norm_crossMoment_le (μ := μ) hgL hθ'L
    have n3 := norm_crossMoment_le (μ := μ) hgL hgL
    have sg0 := Real.sqrt_nonneg (∫ ω, ‖g ω‖ ^ 2 ∂μ)
    have sθ0 := Real.sqrt_nonneg (∫ ω, ‖θ' ω‖ ^ 2 ∂μ)
    have m1 : √(∫ ω, ‖θ' ω‖ ^ 2 ∂μ) * √(∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ √(d * ‖P k‖) * (β k * √Ch) :=
      mul_le_mul hsθ hsg sg0 (Real.sqrt_nonneg _)
    have m2 : √(∫ ω, ‖g ω‖ ^ 2 ∂μ) * √(∫ ω, ‖θ' ω‖ ^ 2 ∂μ) ≤ √(d * ‖P k‖) * (β k * √Ch) := by
      rw [mul_comm]; exact m1
    have hnorm : ‖secondMoment μ (θ k) - P k‖ ≤ 2 * (√(d * ‖P k‖) * (β k * √Ch)) + β k ^ 2 * Ch := by
      have : secondMoment μ θ' + crossMoment μ θ' g + (crossMoment μ g θ' + crossMoment μ g g)
          - P k = crossMoment μ θ' g + crossMoment μ g θ' + crossMoment μ g g := by
        rw [hPk]; abel
      rw [hexp, this]
      have t1 := norm_add_le (crossMoment μ θ' g + crossMoment μ g θ') (crossMoment μ g g)
      have t2 := norm_add_le (crossMoment μ θ' g) (crossMoment μ g θ')
      linarith
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]
    calc (β k)⁻¹ * ‖secondMoment μ (θ k) - P k‖
        ≤ (β k)⁻¹ * (2 * (√(d * ‖P k‖) * (β k * √Ch)) + β k ^ 2 * Ch) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 2 * (√(d * ‖P k‖) * √Ch) + β k * Ch := by field_simp; ring
  have hdiff0 : Tendsto (fun k => 2 * (√(d * ‖P k‖) * √Ch) + β k * Ch) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => √(d * ‖P k‖)) atTop (𝓝 0) := by
      have h1 := hP0.const_mul (d : ℝ)
      rw [mul_zero] at h1
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this
      exact this
    have := ((hs.mul_const √Ch).const_mul 2).add (hβ.tendsto_zero.mul_const Ch)
    simpa using this
  have hsq := squeeze_zero_norm hdiff hdiff0
  have hsum := hPlim.add hsq
  rw [add_zero] at hsum
  exact hsum.congr fun k => by abel

end StochasticApproximation
