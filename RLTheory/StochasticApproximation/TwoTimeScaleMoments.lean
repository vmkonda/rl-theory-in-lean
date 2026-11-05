/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TwoTimeScaleNonlinear
import RLTheory.StochasticApproximation.Linearization

/-!
# Moment bounds for two time scales

The fourth-moment hypotheses of `tendsto_tts_taylor`, from dissipativity. In the coordinates
`x` (slow) and `z = y + D x` (fast), with drifts satisfying
`⟨x, F₁⟩ ≤ -η‖x‖² + K‖x‖‖z‖`, `⟨z, F₂⟩ ≤ -η‖z‖²` and linear growth, and bounded martingale noise,
`E‖x_k‖⁴` and `E‖z_k‖⁴` are `O(γ_k²)`.

* `bdd_of_coupled_box`: the scalar engine. If eventually `u' ≤ (1 - aβ) u + cβ v + Eβ` and
  `v' ≤ (1 - aγ) v + δ_k γ u + Cγ` with `δ_k → 0`, then `u` and `v` are bounded.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

/-- **Coupled boxes.** Let `u, v ≥ 0` satisfy eventually
`u_{k+1} ≤ (1 - a β_k) u_k + c β_k v_k + E β_k` and
`v_{k+1} ≤ (1 - a γ_k) v_k + δ_k γ_k u_k + C γ_k`, with `a > 0`, `a β_k ≤ 1`, `a γ_k ≤ 1` and
`δ_k → 0`. Then `u` and `v` are bounded: the box `[0, sU] × [0, sV]` is eventually invariant for
suitable `U, V` and every `s ≥ 1`. -/
lemma bdd_of_coupled_box {u v β γ δ : ℕ → ℝ} {a c E C : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hβ : ∀ k, 0 ≤ β k) (hγ : ∀ k, 0 ≤ γ k) (hδ : Tendsto δ atTop (𝓝 0))
    (hrec : ∀ᶠ k in atTop, u (k + 1) ≤ (1 - a * β k) * u k + c * β k * v k + E * β k ∧
      v (k + 1) ≤ (1 - a * γ k) * v k + δ k * γ k * u k + C * γ k ∧
      a * β k ≤ 1 ∧ a * γ k ≤ 1) :
    (∃ Mu, ∀ k, u k ≤ Mu) ∧ ∃ Mv, ∀ k, v k ≤ Mv := by
  -- the box
  set V := (C + 1) / a with hV
  set U := (c * V + E + 1) / a with hU
  have hV0 : 0 < V := by positivity
  have hU0 : 0 < U := by positivity
  have hδU : ∀ᶠ k in atTop, δ k * U ≤ 1 := by
    have h := hδ.mul_const U
    rw [zero_mul] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hrec.and hδU)
  set s := max 1 (max (u K / U) (v K / V)) with hs
  have hs1 : 1 ≤ s := le_max_left _ _
  have hinv : ∀ j, u (K + j) ≤ s * U ∧ v (K + j) ≤ s * V := by
    intro j
    induction j with
    | zero =>
      simp only [add_zero]
      refine ⟨?_, ?_⟩
      · have : u K / U ≤ s := (le_max_left _ _).trans (le_max_right _ _)
        rwa [div_le_iff₀ hU0] at this
      · have : v K / V ≤ s := (le_max_right _ _).trans (le_max_right _ _)
        rwa [div_le_iff₀ hV0] at this
    | succ j ih =>
      obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hK (K + j) (by omega)
      obtain ⟨iu, iv⟩ := ih
      have hb := hβ (K + j)
      have hg := hγ (K + j)
      have hd : δ (K + j) * U ≤ 1 := h5
      rw [show K + (j + 1) = K + j + 1 by ring]
      constructor
      · -- `c V + E + 1 = a U`
        have hUeq : a * U = c * V + E + 1 := by simp only [hU]; field_simp
        have t1 := mul_le_mul_of_nonneg_left iu (by linarith : 0 ≤ 1 - a * β (K + j))
        have t2 := mul_le_mul_of_nonneg_left iv (by positivity : 0 ≤ c * β (K + j))
        have t3 : E * β (K + j) ≤ s * (E * β (K + j)) :=
          le_mul_of_one_le_left (by positivity) hs1
        have t4 : 0 ≤ s * β (K + j) := by positivity
        nlinarith
      · have hVeq : a * V = C + 1 := by simp only [hV]; field_simp
        have t1 := mul_le_mul_of_nonneg_left iv (by linarith : 0 ≤ 1 - a * γ (K + j))
        -- `δ u ≤ δ s U ≤ s` when `δ ≥ 0`; when `δ < 0` the term is nonpositive
        have t2 : δ (K + j) * γ (K + j) * u (K + j) ≤ s * γ (K + j) := by
          rcases le_or_gt 0 (δ (K + j)) with hδ0 | hδ0
          · have q1 := mul_le_mul_of_nonneg_left iu (mul_nonneg hδ0 hg)
            have e : δ (K + j) * γ (K + j) * (s * U) = s * γ (K + j) * (δ (K + j) * U) := by ring
            have q2 := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ s * γ (K + j))
            linarith
          · have : δ (K + j) * γ (K + j) * u (K + j) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hδ0.le hg) (hu _)
            have : 0 ≤ s * γ (K + j) := by positivity
            linarith
        have t3 : C * γ (K + j) ≤ s * (C * γ (K + j)) := le_mul_of_one_le_left (by positivity) hs1
        have e2 : (1 - a * γ (K + j)) * (s * V) + s * γ (K + j) + s * (C * γ (K + j)) =
            s * V + s * γ (K + j) * (C + 1 - a * V) := by ring
        have e3 : s * γ (K + j) * (C + 1 - a * V) = 0 := by rw [hVeq]; ring
        linarith
  -- bounded overall
  refine ⟨⟨max (s * U) (∑ k ∈ range K, u k), fun k => ?_⟩,
    ⟨max (s * V) (∑ k ∈ range K, v k), fun k => ?_⟩⟩
  · by_cases hk : K ≤ k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact (hinv j).1.trans (le_max_left _ _)
    · push_neg at hk
      exact (single_le_sum (f := u) (fun i _ => hu i) (mem_range.mpr hk)).trans (le_max_right _ _)
  · by_cases hk : K ≤ k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact (hinv j).2.trans (le_max_left _ _)
    · push_neg at hk
      exact (single_le_sum (f := v) (fun i _ => hv i) (mem_range.mpr hk)).trans (le_max_right _ _)

section Steps

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **One step, second moments.** For `e' = u + s M` with `u` bounded and `ℱ_k`-measurable and `M`
a bounded martingale difference, `E‖e'‖² ≤ E‖u‖² + s² C_M²`. -/
lemma integral_sq_step (ℱ : MeasureTheory.Filtration ℕ m0) (k : ℕ) {e' u M : Ω → E d} {s CM : ℝ}
    (hu : StronglyMeasurable[ℱ k] u) (hub : ∃ C, ∀ ω, ‖u ω‖ ≤ C)
    (hM : StronglyMeasurable[ℱ (k + 1)] M) (hMb : ∀ ω, ‖M ω‖ ≤ CM)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ k] =ᵐ[μ] 0) (he : ∀ ω, e' ω = u ω + s • M ω) :
    ∫ ω, ‖e' ω‖ ^ 2 ∂μ ≤ ∫ ω, ‖u ω‖ ^ 2 ∂μ + s ^ 2 * CM ^ 2 := by
  obtain ⟨C, hC⟩ := hub
  have huL : MemLp u 2 μ :=
    MemLp.of_bound ((hu.mono (ℱ.le k)).aestronglyMeasurable) C (Eventually.of_forall hC)
  have hML : MemLp M 2 μ :=
    MemLp.of_bound ((hM.mono (ℱ.le (k + 1))).aestronglyMeasurable) CM (Eventually.of_forall hMb)
  have hexp : ∀ ω, ‖e' ω‖ ^ 2 = ‖u ω‖ ^ 2 + 2 * s * ⟪u ω, M ω⟫_ℝ + s ^ 2 * ‖M ω‖ ^ 2 := fun ω => by
    rw [he ω, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hzero : ∫ ω, ⟪u ω, M ω⟫_ℝ ∂μ = 0 := integral_inner_mart_eq_zero ℱ k hu huL hML hmart
  have hiu := memLp_sq_integrable huL
  have hiM := memLp_sq_integrable hML
  have hiX : Integrable (fun ω => ⟪u ω, M ω⟫_ℝ) μ := by
    refine (memLp_top_of_bound ((hu.mono (ℱ.le k)).aestronglyMeasurable.inner
      (hM.mono (ℱ.le (k + 1))).aestronglyMeasurable) (C * CM)
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (hC ω) (hMb ω) (norm_nonneg _)
      ((norm_nonneg _).trans (hC ω)))
  have iA : Integrable (fun ω => ‖u ω‖ ^ 2 + 2 * s * ⟪u ω, M ω⟫_ℝ) μ := hiu.add (hiX.const_mul _)
  rw [show (fun ω => ‖e' ω‖ ^ 2) = fun ω => ‖u ω‖ ^ 2 + 2 * s * ⟪u ω, M ω⟫_ℝ
    + s ^ 2 * ‖M ω‖ ^ 2 from funext hexp, integral_add iA (hiM.const_mul _),
    integral_add hiu (hiX.const_mul _), integral_const_mul, integral_const_mul, hzero, mul_zero,
    add_zero]
  have : ∫ ω, ‖M ω‖ ^ 2 ∂μ ≤ CM ^ 2 := by
    calc ∫ ω, ‖M ω‖ ^ 2 ∂μ ≤ ∫ _ω, CM ^ 2 ∂μ :=
          integral_mono hiM (integrable_const _) fun ω =>
            pow_le_pow_left₀ (norm_nonneg _) (hMb ω) 2
      _ = CM ^ 2 := by simp
  have := mul_le_mul_of_nonneg_left this (sq_nonneg s)
  linarith

/-- **One step, fourth moments.** For `e' = u + s M` as above,
`E‖e'‖⁴ ≤ E‖u‖⁴ + 8 s² C_M² E‖u‖² + 3 s⁴ C_M⁴`. -/
lemma integral_four_step (ℱ : MeasureTheory.Filtration ℕ m0) (k : ℕ) {e' u M : Ω → E d}
    {s CM : ℝ} (hu : StronglyMeasurable[ℱ k] u) (hub : ∃ C, ∀ ω, ‖u ω‖ ≤ C)
    (hM : StronglyMeasurable[ℱ (k + 1)] M) (hMb : ∀ ω, ‖M ω‖ ≤ CM)
    (hmart : ∀ j, μ[fun ω => M ω j | ℱ k] =ᵐ[μ] 0) (he : ∀ ω, e' ω = u ω + s • M ω) :
    ∫ ω, ‖e' ω‖ ^ 4 ∂μ ≤ ∫ ω, (‖u ω‖ ^ 2) ^ 2 ∂μ + 8 * s ^ 2 * CM ^ 2 * ∫ ω, ‖u ω‖ ^ 2 ∂μ
      + 3 * s ^ 4 * CM ^ 4 := by
  obtain ⟨C', hC'⟩ := hub
  set C := max C' 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ ω, ‖u ω‖ ≤ C := fun ω => (hC' ω).trans (le_max_left _ _)
  have huL : MemLp u 2 μ :=
    MemLp.of_bound ((hu.mono (ℱ.le k)).aestronglyMeasurable) C (Eventually.of_forall hC)
  have hML : MemLp M 2 μ :=
    MemLp.of_bound ((hM.mono (ℱ.le (k + 1))).aestronglyMeasurable) CM (Eventually.of_forall hMb)
  have hua : AEStronglyMeasurable u μ := (hu.mono (ℱ.le k)).aestronglyMeasurable
  have hMa : AEStronglyMeasurable M μ := (hM.mono (ℱ.le (k + 1))).aestronglyMeasurable
  have hbd : ∀ (g : Ω → ℝ), AEStronglyMeasurable g μ → (∃ B, ∀ ω, |g ω| ≤ B) → Integrable g μ :=
    fun g hg ⟨B, hB⟩ => (memLp_top_of_bound hg B (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hB ω)).integrable le_top
  have hiu2 := memLp_sq_integrable huL
  have hiu4 : Integrable (fun ω => (‖u ω‖ ^ 2) ^ 2) μ :=
    hbd _ ((hua.norm.pow 2).pow 2) ⟨(C ^ 2) ^ 2, fun ω => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2) 2⟩
  have hiaX : Integrable (fun ω => ‖u ω‖ ^ 2 * ⟪u ω, M ω⟫_ℝ) μ :=
    hbd _ ((hua.norm.pow 2).mul (hua.inner hMa)) ⟨C ^ 2 * (C * CM), fun ω => by
      rw [abs_mul, abs_of_nonneg (by positivity), ← Real.norm_eq_abs]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2) ((norm_inner_le_norm _ _).trans
        (mul_le_mul (hC ω) (hMb ω) (norm_nonneg _) hC0)) (norm_nonneg _) (by positivity)⟩
  have hie4 : Integrable (fun ω => ‖e' ω‖ ^ 4) μ := by
    have hea : AEStronglyMeasurable e' μ := by
      have : e' = fun ω => u ω + s • M ω := funext he
      rw [this]; exact hua.add (hMa.const_smul s)
    refine hbd _ (hea.norm.pow 4) ⟨(C + |s| * CM) ^ 4, fun ω => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
    rw [he ω]
    refine (norm_add_le _ _).trans (add_le_add (hC ω) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hMb ω) (abs_nonneg _)
  -- `E[‖u‖² ⟨u, M⟩] = 0`
  have hzero4 : ∫ ω, ‖u ω‖ ^ 2 * ⟪u ω, M ω⟫_ℝ ∂μ = 0 := by
    have hwm : StronglyMeasurable[ℱ k] fun ω => ‖u ω‖ ^ 2 • u ω := (hu.norm.pow 2).smul hu
    have hwL : MemLp (fun ω => ‖u ω‖ ^ 2 • u ω) 2 μ := by
      refine MemLp.of_bound (hwm.mono (ℱ.le k)).aestronglyMeasurable (C ^ 2 * C)
        (Eventually.of_forall fun ω => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2) (hC ω) (norm_nonneg _)
        (by positivity)
    have := integral_inner_mart_eq_zero ℱ k hwm hwL hML hmart
    simpa only [inner_smul_left, RCLike.conj_to_real] using this
  -- the pointwise bound
  have hpt : ∀ ω, ‖e' ω‖ ^ 4 ≤ (‖u ω‖ ^ 2) ^ 2 + 4 * s * (‖u ω‖ ^ 2 * ⟪u ω, M ω⟫_ℝ)
      + 8 * s ^ 2 * CM ^ 2 * ‖u ω‖ ^ 2 + 3 * s ^ 4 * CM ^ 4 := fun ω => by
    set a := ‖u ω‖ ^ 2
    set X := ⟪u ω, M ω⟫_ℝ
    set m := ‖M ω‖ ^ 2
    have hexp2 : ‖e' ω‖ ^ 2 = a + 2 * s * X + s ^ 2 * m := by
      rw [he ω, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have h4 : ‖e' ω‖ ^ 4 = (a + 2 * s * X + s ^ 2 * m) ^ 2 := by
      rw [show ‖e' ω‖ ^ 4 = (‖e' ω‖ ^ 2) ^ 2 by ring, hexp2]
    have ha : 0 ≤ a := by positivity
    have hm0 : 0 ≤ m := by positivity
    have hmC : m ≤ CM ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMb ω) 2
    have hX2 : X ^ 2 ≤ a * m := by
      have := abs_real_inner_le_norm (u ω) (M ω)
      calc X ^ 2 = |X| ^ 2 := (sq_abs X).symm
        _ ≤ (‖u ω‖ * ‖M ω‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = a * m := by simp only [a, m]; ring
    have hexp : (a + 2 * s * X + s ^ 2 * m) ^ 2 = a ^ 2 + 4 * s * (a * X)
        + 4 * s ^ 2 * X ^ 2 + 2 * s ^ 2 * (a * m) + 4 * s ^ 3 * (X * m) + s ^ 4 * m ^ 2 := by ring
    have i1 : 4 * s ^ 3 * (X * m) ≤ 2 * s ^ 2 * X ^ 2 + 2 * s ^ 4 * m ^ 2 := by
      nlinarith [sq_nonneg (X - s * m), sq_nonneg s]
    have i2 : s ^ 2 * X ^ 2 ≤ s ^ 2 * (a * m) := mul_le_mul_of_nonneg_left hX2 (sq_nonneg _)
    have i3 : s ^ 2 * (a * m) ≤ s ^ 2 * (a * CM ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmC ha) (sq_nonneg _)
    have i4 : s ^ 4 * m ^ 2 ≤ s ^ 4 * (CM ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmC 2) (by positivity)
    rw [h4, hexp]
    nlinarith [i1, i2, i3, i4]
  have iB : Integrable (fun ω => (‖u ω‖ ^ 2) ^ 2 + 4 * s * (‖u ω‖ ^ 2 * ⟪u ω, M ω⟫_ℝ)) μ :=
    hiu4.add (hiaX.const_mul _)
  have iC : Integrable (fun ω => (‖u ω‖ ^ 2) ^ 2 + 4 * s * (‖u ω‖ ^ 2 * ⟪u ω, M ω⟫_ℝ)
      + 8 * s ^ 2 * CM ^ 2 * ‖u ω‖ ^ 2) μ := iB.add (hiu2.const_mul _)
  have hint4 : Integrable (fun ω => (‖u ω‖ ^ 2) ^ 2 + 4 * s * (‖u ω‖ ^ 2 * ⟪u ω, M ω⟫_ℝ)
      + 8 * s ^ 2 * CM ^ 2 * ‖u ω‖ ^ 2 + 3 * s ^ 4 * CM ^ 4) μ := iC.add (integrable_const _)
  have step1 := integral_mono hie4 hint4 hpt
  rw [integral_add iC (integrable_const _), integral_add iB (hiu2.const_mul _),
    integral_add hiu4 (hiaX.const_mul _), integral_const_mul, integral_const_mul, hzero4,
    mul_zero, add_zero] at step1
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using step1

end Steps

section Pointwise

variable {d₁ d₂ : ℕ}

/-- **The slow step.** If `⟨x, f⟩ ≤ -η‖x‖² + K‖x‖‖z‖` and `‖f‖ ≤ K(‖x‖ + ‖z‖)`, then
`‖x + β f‖² ≤ (1 - ηβ + 2K²β²) ‖x‖² + (K²/η + 2K²β) β ‖z‖²`. -/
lemma slow_step_bound {x f : E d₁} {zn η K β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (hzn : 0 ≤ zn)
    (hin : ⟪x, f⟫_ℝ ≤ -η * ‖x‖ ^ 2 + K * ‖x‖ * zn) (hf : ‖f‖ ≤ K * (‖x‖ + zn)) (hK : 0 ≤ K) :
    ‖x + β • f‖ ^ 2 ≤ (1 - η * β + 2 * K ^ 2 * β ^ 2) * ‖x‖ ^ 2
      + (K ^ 2 / η + 2 * K ^ 2 * β) * β * zn ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
  set a := ‖x‖
  have ha : 0 ≤ a := norm_nonneg _
  have h1 : 2 * K * a * zn ≤ η * a ^ 2 + K ^ 2 / η * zn ^ 2 := by
    have : 0 ≤ (η * a - K * zn) ^ 2 / η := by positivity
    have e : (η * a - K * zn) ^ 2 / η = η * a ^ 2 - 2 * K * a * zn + K ^ 2 / η * zn ^ 2 := by
      field_simp; ring
    linarith
  have h2 : ‖f‖ ^ 2 ≤ 2 * K ^ 2 * (a ^ 2 + zn ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hf 2
    nlinarith [sq_nonneg (a - zn)]
  have t1 := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 2 * β)
  have t2 := mul_le_mul_of_nonneg_left h1 hβ
  have t3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg β)
  have e1 : (β * ‖f‖) ^ 2 = β ^ 2 * ‖f‖ ^ 2 := by ring
  rw [e1]
  nlinarith [t1, t2, t3]

/-- The scalar assembly of the fast step. -/
lemma fast_scalar {P Q Bz X η γ K K' β : ℝ} (hη : 0 < η) (hγ : 0 < γ) (hηγ : η * γ ≤ 1)
    (hBz : 0 ≤ Bz) (hX : 0 ≤ X) (hQ0 : 0 ≤ Q)
    (hP : P ≤ (1 - 2 * η * γ) * Bz + 2 * K ^ 2 * γ ^ 2 * (X + Bz))
    (hQ : Q ≤ 2 * K' ^ 2 * β ^ 2 * (X + Bz)) :
    (1 + η * γ) * P + (1 + 1 / (η * γ)) * Q ≤
      (1 - η * γ + (4 * K ^ 2 + 4 * K' ^ 2 / η) * (γ ^ 2 + β ^ 2 / γ)) * Bz
        + (4 * K ^ 2 + 4 * K' ^ 2 / η) * (γ ^ 2 + β ^ 2 / γ) * X := by
  have ht : 0 < η * γ := mul_pos hη hγ
  have hinv : 1 + 1 / (η * γ) ≤ 2 / (η * γ) := by
    have h1 : 1 ≤ 1 / (η * γ) := by rw [le_div_iff₀ ht]; linarith
    have h2 : (2 : ℝ) / (η * γ) = 1 / (η * γ) + 1 / (η * γ) := by ring
    linarith
  have s1 := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 1 + η * γ)
  have s2 := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 1 + 1 / (η * γ))
  have hXB : 0 ≤ 2 * K' ^ 2 * β ^ 2 * (X + Bz) := by positivity
  have s3 := mul_le_mul_of_nonneg_right hinv hXB
  have e2 : 2 / (η * γ) * (2 * K' ^ 2 * β ^ 2 * (X + Bz)) =
      4 * K' ^ 2 / η * (β ^ 2 / γ) * (X + Bz) := by field_simp; ring
  have e3 : (1 + η * γ) * ((1 - 2 * η * γ) * Bz + 2 * K ^ 2 * γ ^ 2 * (X + Bz)) =
      (1 - η * γ) * Bz - 2 * (η * γ) ^ 2 * Bz + (1 + η * γ) * (2 * K ^ 2 * γ ^ 2 * (X + Bz)) := by
    ring
  have hKX : 0 ≤ 2 * K ^ 2 * γ ^ 2 * (X + Bz) := by positivity
  have h5 : (1 + η * γ) * (2 * K ^ 2 * γ ^ 2 * (X + Bz)) ≤ 2 * (2 * K ^ 2 * γ ^ 2 * (X + Bz)) :=
    mul_le_mul_of_nonneg_right (by linarith) hKX
  have h6 : 0 ≤ 2 * (η * γ) ^ 2 * Bz := by positivity
  have e4 : (1 - η * γ + (4 * K ^ 2 + 4 * K' ^ 2 / η) * (γ ^ 2 + β ^ 2 / γ)) * Bz
      + (4 * K ^ 2 + 4 * K' ^ 2 / η) * (γ ^ 2 + β ^ 2 / γ) * X =
      (1 - η * γ) * Bz + 2 * (2 * K ^ 2 * γ ^ 2 * (X + Bz))
        + 4 * K' ^ 2 / η * (β ^ 2 / γ) * (X + Bz)
        + (4 * K ^ 2 * (β ^ 2 / γ) + 4 * K' ^ 2 / η * γ ^ 2) * (X + Bz) := by ring
  have h7 : 0 ≤ (4 * K ^ 2 * (β ^ 2 / γ) + 4 * K' ^ 2 / η * γ ^ 2) * (X + Bz) := by positivity
  linarith

/-- **The fast step.** If `⟨z, f₂⟩ ≤ -η‖z‖²`, `‖f₂‖ ≤ K(‖x‖ + ‖z‖)`, `‖w‖ ≤ K'(‖x‖ + ‖z‖)`,
`0 < γ` and `ηγ ≤ 1`, then
`‖z + γ f₂ + β w‖² ≤ (1 - ηγ + c τ) ‖z‖² + c τ ‖x‖²` with `τ = γ² + β²/γ` and
`c = 4K² + 4K'²/η`. -/
lemma fast_step_bound {z f₂ w : E d₂} {xn η K K' β γ : ℝ} (hη : 0 < η) (hγ : 0 < γ)
    (hηγ : η * γ ≤ 1) (hβ : 0 ≤ β) (hxn : 0 ≤ xn) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hin : ⟪z, f₂⟫_ℝ ≤ -η * ‖z‖ ^ 2) (hf : ‖f₂‖ ≤ K * (xn + ‖z‖)) (hw : ‖w‖ ≤ K' * (xn + ‖z‖)) :
    ‖z + γ • f₂ + β • w‖ ^ 2 ≤
      (1 - η * γ + (4 * K ^ 2 + 4 * K' ^ 2 / η) * (γ ^ 2 + β ^ 2 / γ)) * ‖z‖ ^ 2
        + (4 * K ^ 2 + 4 * K' ^ 2 / η) * (γ ^ 2 + β ^ 2 / γ) * xn ^ 2 := by
  have ht : 0 < η * γ := mul_pos hη hγ
  have hyoung : ‖z + γ • f₂ + β • w‖ ^ 2 ≤ (1 + η * γ) * ‖z + γ • f₂‖ ^ 2
      + (1 + 1 / (η * γ)) * ‖β • w‖ ^ 2 := by
    rw [norm_add_sq_real]
    have h1 : ⟪z + γ • f₂, β • w⟫_ℝ ≤ ‖z + γ • f₂‖ * ‖β • w‖ := real_inner_le_norm _ _
    have h2 : 2 * (‖z + γ • f₂‖ * ‖β • w‖) ≤ η * γ * ‖z + γ • f₂‖ ^ 2
        + 1 / (η * γ) * ‖β • w‖ ^ 2 := by
      have h0 : 0 ≤ (η * γ * ‖z + γ • f₂‖ - ‖β • w‖) ^ 2 / (η * γ) := by positivity
      have e : (η * γ * ‖z + γ • f₂‖ - ‖β • w‖) ^ 2 / (η * γ) =
          η * γ * ‖z + γ • f₂‖ ^ 2 - 2 * (‖z + γ • f₂‖ * ‖β • w‖)
            + 1 / (η * γ) * ‖β • w‖ ^ 2 := by
        field_simp; ring
      linarith
    linarith
  have hsum2 : (xn + ‖z‖) ^ 2 ≤ 2 * (xn ^ 2 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (xn - ‖z‖)]
  have hp : ‖z + γ • f₂‖ ^ 2 ≤ (1 - 2 * η * γ) * ‖z‖ ^ 2
      + 2 * K ^ 2 * γ ^ 2 * (xn ^ 2 + ‖z‖ ^ 2) := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    have t1 := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 2 * γ)
    have h2 : ‖f₂‖ ^ 2 ≤ 2 * K ^ 2 * (xn ^ 2 + ‖z‖ ^ 2) := by
      have h3 := pow_le_pow_left₀ (norm_nonneg _) hf 2
      have h4 := mul_le_mul_of_nonneg_left hsum2 (sq_nonneg K)
      have e : (K * (xn + ‖z‖)) ^ 2 = K ^ 2 * (xn + ‖z‖) ^ 2 := by ring
      linarith
    have t3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg γ)
    have e1 : (γ * ‖f₂‖) ^ 2 = γ ^ 2 * ‖f₂‖ ^ 2 := by ring
    rw [e1]
    have e5 : 2 * γ * (-η * ‖z‖ ^ 2) = -(2 * η * γ) * ‖z‖ ^ 2 := by ring
    linarith
  have hq : ‖β • w‖ ^ 2 ≤ 2 * K' ^ 2 * β ^ 2 * (xn ^ 2 + ‖z‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have h4 := mul_le_mul_of_nonneg_left hsum2 (sq_nonneg K')
    have e : (K' * (xn + ‖z‖)) ^ 2 = K' ^ 2 * (xn + ‖z‖) ^ 2 := by ring
    have h5 : ‖w‖ ^ 2 ≤ 2 * K' ^ 2 * (xn ^ 2 + ‖z‖ ^ 2) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg β)
    have e1 : (β * ‖w‖) ^ 2 = β ^ 2 * ‖w‖ ^ 2 := by ring
    rw [e1]
    linarith
  have hfs := fast_scalar (P := ‖z + γ • f₂‖ ^ 2) (Q := ‖β • w‖ ^ 2) (Bz := ‖z‖ ^ 2) (X := xn ^ 2)
    (K := K) (K' := K') (β := β) hη hγ hηγ (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
    (by linarith [hp]) (by linarith [hq])
  linarith

end Pointwise

end StochasticApproximation
