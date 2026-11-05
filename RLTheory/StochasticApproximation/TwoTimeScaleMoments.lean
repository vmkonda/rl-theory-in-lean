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

section Scalar

/-- `(1 - 2t)² (1 + t) ≤ 1 - t` for `0 ≤ t ≤ 1/2`. -/
lemma sq_contract_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : (1 - 2 * t) ^ 2 * (1 + t) ≤ 1 - t := by
  have e : (1 - 2 * t) ^ 2 * (1 + t) = 1 - 3 * t + 4 * t ^ 3 := by ring
  rw [e]
  have : t ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The scalar core of the two-time-scale moment bounds.** Second moments `a, b` and fourth
moments `A, B` of the slow and fast errors obeying the one-step recursions below are
`A, B = O(γ²)`. Here `q₁ = 1 - ηβ + κβ²`, `q₂ = 1 - ηγ + c₂τ`, `τ = γ² + β²/γ`, `ε = (η - c₀)/4`,
and the step sizes satisfy `β/γ → 0`, `γ²/β → 0` and `γ_k / γ_{k+1} ≤ 1 + c₀ β_k` with
`c₀ < η`. -/
lemma tts_moments_scalar {β γ a b A B : ℕ → ℝ} {η c₀ κ c₁ c₂ CM CN : ℝ}
    (hβp : ∀ k, 0 < β k) (hγp : ∀ k, 0 < γ k) (hβ0 : Tendsto β atTop (𝓝 0))
    (hγ0 : Tendsto γ atTop (𝓝 0)) (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0)) (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η)
    (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k) (hκ : 0 ≤ κ) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hCM : 0 ≤ CM) (hCN : 0 ≤ CN)
    (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k) (hA0 : ∀ k, 0 ≤ A k) (hB0 : ∀ k, 0 ≤ B k)
    (Ra : ∀ k, a (k + 1) ≤ (1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k + CM * β k ^ 2)
    (Rb : ∀ᶠ k in atTop, b (k + 1) ≤ (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
      + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k + CN * γ k ^ 2)
    (RA : ∀ k, A (k + 1) ≤ (1 + (η - c₀) / 4 * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2 * A k
      + (1 + 1 / ((η - c₀) / 4 * β k)) * (c₁ * β k) ^ 2 * B k
      + 8 * β k ^ 2 * CM * ((1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k)
      + 3 * β k ^ 4 * CM ^ 2)
    (RB : ∀ᶠ k in atTop, B (k + 1) ≤ (1 + (η - c₀) / 4 * γ k)
        * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * B k
      + (1 + 1 / ((η - c₀) / 4 * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * A k
      + 8 * γ k ^ 2 * CN * ((1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k) + 3 * γ k ^ 4 * CN ^ 2) :
    ∃ W, ∀ k, A k ≤ W * γ k ^ 2 ∧ B k ≤ W * γ k ^ 2 := by
  set a₀ := (η - c₀) / 4 with ha₀
  have ha₀0 : 0 < a₀ := by simp only [ha₀]; linarith
  have hη : 0 < η := by linarith
  set τ : ℕ → ℝ := fun k => γ k ^ 2 + β k ^ 2 / γ k with hτ
  set q₁ : ℕ → ℝ := fun k => 1 - η * β k + κ * β k ^ 2 with hq₁
  set q₂ : ℕ → ℝ := fun k => 1 - η * γ k + c₂ * τ k with hq₂
  set ρ : ℕ → ℝ := fun k => γ k / γ (k + 1) with hρ
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => div_nonneg (hγp k).le (hγp (k + 1)).le
  have hτ0 : ∀ k, 0 ≤ τ k := fun k => by
    have := hβp k; have := hγp k; simp only [hτ]; positivity
  -- bounds on the steps
  obtain ⟨Bβ, hBβ⟩ := hβ0.bddAbove_range
  obtain ⟨Bγ, hBγ⟩ := hγ0.bddAbove_range
  obtain ⟨Bq, hBq⟩ := hβγ.bddAbove_range
  have hβB : ∀ k, β k ≤ Bβ := fun k => hBβ ⟨k, rfl⟩
  have hγB : ∀ k, γ k ≤ Bγ := fun k => hBγ ⟨k, rfl⟩
  have hqB : ∀ k, β k / γ k ≤ Bq := fun k => hBq ⟨k, rfl⟩
  have hBβ0 : 0 ≤ Bβ := (hβp 0).le.trans (hβB 0)
  have hBγ0 : 0 ≤ Bγ := (hγp 0).le.trans (hγB 0)
  have hBq0 : 0 ≤ Bq := (div_nonneg (hβp 0).le (hγp 0).le).trans (hqB 0)
  -- `τ / γ → 0`
  have hτγ : Tendsto (fun k => τ k / γ k) atTop (𝓝 0) := by
    have h := hγ0.add (hβγ.pow 2)
    simp only [add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    refine h.congr fun k => ?_
    have := (hγp k).ne'
    simp only [hτ]; field_simp; ring
  obtain ⟨T, hT⟩ := (hτγ.mul hγ0).bddAbove_range
  have hτT : ∀ k, τ k ≤ T := fun k => by
    have := hT ⟨k, rfl⟩
    have e : τ k / γ k * γ k = τ k := div_mul_cancel₀ _ (hγp k).ne'
    have : τ k / γ k * γ k ≤ T := this
    rwa [e] at this
  have hT0 : 0 ≤ T := (hτ0 0).trans (hτT 0)
  -- the eventual facts
  have ev1 : ∀ᶠ k in atTop, 0 ≤ q₁ k ∧ (1 + c₀ * β k) * q₁ k ≤ 1 - 2 * a₀ * β k := by
    have hlim : Tendsto (fun k => β k * (κ - c₀ * η) + c₀ * κ * β k ^ 2) atTop (𝓝 0) := by
      simpa using (hβ0.mul_const (κ - c₀ * η)).add ((hβ0.pow 2).const_mul (c₀ * κ))
    have hq1 : Tendsto q₁ atTop (𝓝 1) := by
      simpa [hq₁] using ((hβ0.const_mul η).const_sub 1).add ((hβ0.pow 2).const_mul κ)
    filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (η - c₀) / 2)),
      hq1.eventually (le_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k h1 h2
    refine ⟨h2, ?_⟩
    have hb := hβp k
    have e : (1 + c₀ * β k) * q₁ k - (1 - 2 * a₀ * β k) =
        β k * (-((η - c₀) / 2) + (β k * (κ - c₀ * η) + c₀ * κ * β k ^ 2)) := by
      simp only [hq₁, ha₀]; ring
    have : β k * (-((η - c₀) / 2) + (β k * (κ - c₀ * η) + c₀ * κ * β k ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb.le (by linarith)
    linarith
  have ev2 : ∀ᶠ k in atTop, 0 ≤ q₂ k ∧ (1 + c₀ * β k) * q₂ k ≤ 1 - 2 * a₀ * γ k := by
    have hq2 : Tendsto q₂ atTop (𝓝 1) := by
      have h := ((hγ0.const_mul η).const_sub 1).add ((hτγ.mul hγ0).const_mul c₂)
      simp only [mul_zero, sub_zero, add_zero] at h
      refine h.congr fun k => ?_
      have := (hγp k).ne'
      simp only [hq₂]; field_simp
    have hlim : Tendsto (fun k => c₂ * (τ k / γ k) + c₀ * (β k / γ k) * q₂ k) atTop (𝓝 0) := by
      simpa using (hτγ.const_mul c₂).add ((hβγ.const_mul c₀).mul hq2)
    filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 2)),
      hq2.eventually (le_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k h1 h2
    refine ⟨h2, ?_⟩
    have hg := hγp k
    have e : (1 + c₀ * β k) * q₂ k - (1 - 2 * a₀ * γ k) =
        γ k * (-η + 2 * a₀ + (c₂ * (τ k / γ k) + c₀ * (β k / γ k) * q₂ k)) := by
      have := hg.ne'
      simp only [hq₂, ha₀]; field_simp; ring
    have h3 : -η + 2 * a₀ ≤ -(η / 2) := by simp only [ha₀]; linarith
    have : γ k * (-η + 2 * a₀ + (c₂ * (τ k / γ k) + c₀ * (β k / γ k) * q₂ k)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hg.le (by linarith)
    linarith
  have ev3 : ∀ᶠ k in atTop, a₀ * β k ≤ 1 / 2 ∧ a₀ * γ k ≤ 1 / 2 ∧ 1 + c₀ * β k ≤ 2 := by
    have h1 := (hβ0.const_mul a₀).eventually (ge_mem_nhds (by simp : a₀ * 0 < 1 / 2))
    have h2 := (hγ0.const_mul a₀).eventually (ge_mem_nhds (by simp : a₀ * 0 < 1 / 2))
    have h3 := ((hβ0.const_mul c₀).const_add 1).eventually
      (ge_mem_nhds (by simp : (1 : ℝ) + c₀ * 0 < 2))
    filter_upwards [h1, h2, h3] with k h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- stage 1: second moments
  set u : ℕ → ℝ := fun k => a k / γ k with hu
  set v : ℕ → ℝ := fun k => b k / γ k with hv
  have hu0 : ∀ k, 0 ≤ u k := fun k => div_nonneg (ha0 k) (hγp k).le
  have hv0 : ∀ k, 0 ≤ v k := fun k => div_nonneg (hb0 k) (hγp k).le
  have hua : ∀ k, a k = u k * γ k := fun k => by simp only [hu]; field_simp [(hγp k).ne']
  have hvb : ∀ k, b k = v k * γ k := fun k => by simp only [hv]; field_simp [(hγp k).ne']
  have hnext : ∀ (f : ℕ → ℝ) (k : ℕ), f (k + 1) / γ (k + 1) = ρ k * (f (k + 1) / γ k) :=
    fun f k => by simp only [hρ]; field_simp [(hγp k).ne', (hγp (k + 1)).ne']; ring
  have box1 := bdd_of_coupled_box (u := u) (v := v) (β := β) (γ := γ)
    (δ := fun k => 2 * c₂ * (τ k / γ k)) (a := a₀) (c := 2 * c₁) (E := 2 * Bq * CM)
    (C := 2 * CN) ha₀0 (by positivity) (by positivity) (by positivity) hu0 hv0
    (fun k => (hβp k).le) (fun k => (hγp k).le) (by simpa using hτγ.const_mul (2 * c₂))
    (by
      filter_upwards [hratio, ev1, ev2, ev3, Rb] with k hr e1 e2 e3 hbk
      obtain ⟨hq10, hq1⟩ := e1
      obtain ⟨hq20, hq2⟩ := e2
      obtain ⟨e3a, e3b, e3c⟩ := e3
      have hb := hβp k
      have hg := hγp k
      have hρ2 : ρ k ≤ 2 := hr.trans e3c
      refine ⟨?_, ?_, by linarith, by linarith⟩
      · -- the slow component
        have h1 : u (k + 1) = ρ k * (a (k + 1) / γ k) := hnext a k
        have h2 : a (k + 1) / γ k ≤ q₁ k * u k + c₁ * β k * v k + CM * β k * (β k / γ k) := by
          rw [div_le_iff₀ hg]
          have := Ra k
          rw [hua k, hvb k] at this
          have e : (q₁ k * u k + c₁ * β k * v k + CM * β k * (β k / γ k)) * γ k =
              q₁ k * (u k * γ k) + c₁ * β k * (v k * γ k) + CM * β k ^ 2 := by
            field_simp; ring
          rw [e]; exact this
        have h3 : ρ k * (q₁ k * u k) ≤ (1 - 2 * a₀ * β k) * u k := by
          have t1 : ρ k * q₁ k ≤ (1 + c₀ * β k) * q₁ k := mul_le_mul_of_nonneg_right hr hq10
          have t2 := mul_le_mul_of_nonneg_right (t1.trans hq1) (hu0 k)
          have e : ρ k * (q₁ k * u k) = ρ k * q₁ k * u k := by ring
          linarith
        have h4 : ρ k * (c₁ * β k * v k) ≤ 2 * c₁ * β k * v k := by
          have := mul_le_mul_of_nonneg_right hρ2 (mul_nonneg (mul_nonneg hc₁ hb.le) (hv0 k))
          linarith
        have h5 : ρ k * (CM * β k * (β k / γ k)) ≤ 2 * Bq * CM * β k := by
          have t1 : CM * β k * (β k / γ k) ≤ CM * β k * Bq :=
            mul_le_mul_of_nonneg_left (hqB k) (by positivity)
          have t2 := mul_le_mul hρ2 t1 (by positivity) (by norm_num)
          linarith
        have h6 : ρ k * (a (k + 1) / γ k) ≤ ρ k * (q₁ k * u k + c₁ * β k * v k
            + CM * β k * (β k / γ k)) := mul_le_mul_of_nonneg_left h2 (hρ0 k)
        have h7 : (1 - 2 * a₀ * β k) * u k ≤ (1 - a₀ * β k) * u k :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg ha₀0.le hb.le]) (hu0 k)
        have e : ρ k * (q₁ k * u k + c₁ * β k * v k + CM * β k * (β k / γ k)) =
            ρ k * (q₁ k * u k) + ρ k * (c₁ * β k * v k) + ρ k * (CM * β k * (β k / γ k)) := by ring
        rw [h1]
        linarith
      · -- the fast component
        have h1 : v (k + 1) = ρ k * (b (k + 1) / γ k) := hnext b k
        have h2 : b (k + 1) / γ k ≤ q₂ k * v k + c₂ * τ k / γ k * u k * γ k + CN * γ k := by
          rw [div_le_iff₀ hg]
          rw [hua k, hvb k] at hbk
          have e : (q₂ k * v k + c₂ * τ k / γ k * u k * γ k + CN * γ k) * γ k =
              q₂ k * (v k * γ k) + c₂ * τ k * (u k * γ k) + CN * γ k ^ 2 := by
            field_simp; ring
          rw [e]; exact hbk
        have h3 : ρ k * (q₂ k * v k) ≤ (1 - 2 * a₀ * γ k) * v k := by
          have t1 : ρ k * q₂ k ≤ (1 + c₀ * β k) * q₂ k := mul_le_mul_of_nonneg_right hr hq20
          have t2 := mul_le_mul_of_nonneg_right (t1.trans hq2) (hv0 k)
          have e : ρ k * (q₂ k * v k) = ρ k * q₂ k * v k := by ring
          linarith
        have h4 : ρ k * (c₂ * τ k / γ k * u k * γ k) ≤ 2 * c₂ * (τ k / γ k) * γ k * u k := by
          have h0 : 0 ≤ c₂ * τ k / γ k * u k * γ k :=
            mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hc₂ (hτ0 k)) hg.le) (hu0 k)) hg.le
          have := mul_le_mul_of_nonneg_right hρ2 h0
          have e : 2 * (c₂ * τ k / γ k * u k * γ k) = 2 * c₂ * (τ k / γ k) * γ k * u k := by ring
          linarith
        have h5 : ρ k * (CN * γ k) ≤ 2 * CN * γ k := by
          have := mul_le_mul_of_nonneg_right hρ2 (by positivity : 0 ≤ CN * γ k)
          linarith
        have h6 : ρ k * (b (k + 1) / γ k) ≤ ρ k * (q₂ k * v k + c₂ * τ k / γ k * u k * γ k
            + CN * γ k) := mul_le_mul_of_nonneg_left h2 (hρ0 k)
        have h7 : (1 - 2 * a₀ * γ k) * v k ≤ (1 - a₀ * γ k) * v k :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg ha₀0.le hg.le]) (hv0 k)
        have e : ρ k * (q₂ k * v k + c₂ * τ k / γ k * u k * γ k + CN * γ k) =
            ρ k * (q₂ k * v k) + ρ k * (c₂ * τ k / γ k * u k * γ k) + ρ k * (CN * γ k) := by ring
        rw [h1]
        have e2 : 2 * c₂ * (τ k / γ k) * γ k * u k = (fun k => 2 * c₂ * (τ k / γ k)) k * γ k * u k :=
          rfl
        linarith)
  obtain ⟨⟨Mu, hMu⟩, ⟨Mv, hMv⟩⟩ := box1
  set W₁ := max (max Mu Mv) 0 with hW₁
  have hW₁0 : 0 ≤ W₁ := le_max_right _ _
  have haW : ∀ k, a k ≤ W₁ * γ k := fun k => by
    rw [hua k]
    exact mul_le_mul_of_nonneg_right ((hMu k).trans ((le_max_left _ _).trans (le_max_left _ _)))
      (hγp k).le
  have hbW : ∀ k, b k ≤ W₁ * γ k := fun k => by
    rw [hvb k]
    exact mul_le_mul_of_nonneg_right ((hMv k).trans ((le_max_right _ _).trans (le_max_left _ _)))
      (hγp k).le
  -- stage 2: fourth moments
  set U : ℕ → ℝ := fun k => A k / γ k ^ 2 with hU
  set V : ℕ → ℝ := fun k => B k / γ k ^ 2 with hV
  have hU0 : ∀ k, 0 ≤ U k := fun k => div_nonneg (hA0 k) (sq_nonneg _)
  have hV0 : ∀ k, 0 ≤ V k := fun k => div_nonneg (hB0 k) (sq_nonneg _)
  have hUA : ∀ k, A k = U k * γ k ^ 2 := fun k => by
    simp only [hU]; field_simp [(hγp k).ne']
  have hVB : ∀ k, B k = V k * γ k ^ 2 := fun k => by
    simp only [hV]; field_simp [(hγp k).ne']
  have hnext2 : ∀ (f : ℕ → ℝ) (k : ℕ), f (k + 1) / γ (k + 1) ^ 2 =
      ρ k ^ 2 * (f (k + 1) / γ k ^ 2) := fun f k => by
    simp only [hρ]; field_simp [(hγp k).ne', (hγp (k + 1)).ne']; ring
  set c' := 4 * c₁ ^ 2 * (Bβ + 1 / a₀) with hc'
  set E' := 32 * CM * W₁ * (1 + c₁ * Bβ) * Bq + 12 * CM ^ 2 * Bβ * Bq ^ 2 with hE'
  set C' := 32 * CN * W₁ * (1 + c₂ * T) + 12 * CN ^ 2 * Bγ with hC'
  have hδ₂ : Tendsto (fun k => 4 * c₂ ^ 2 * (γ k * (τ k / γ k) ^ 2 + (τ k / γ k) ^ 2 / a₀)) atTop
      (𝓝 0) := by
    simpa using ((hγ0.mul (hτγ.pow 2)).add ((hτγ.pow 2).div_const a₀)).const_mul (4 * c₂ ^ 2)
  have box2 := bdd_of_coupled_box (u := U) (v := V) (β := β) (γ := γ)
    (δ := fun k => 4 * c₂ ^ 2 * (γ k * (τ k / γ k) ^ 2 + (τ k / γ k) ^ 2 / a₀)) (a := a₀) (c := c')
    (E := E') (C := C') ha₀0 (by positivity) (by positivity) (by positivity) hU0 hV0
    (fun k => (hβp k).le) (fun k => (hγp k).le) hδ₂
    (by
      filter_upwards [hratio, ev1, ev2, ev3, RB] with k hr e1 e2 e3 hBk
      obtain ⟨hq10, hq1⟩ := e1
      obtain ⟨hq20, hq2⟩ := e2
      obtain ⟨e3a, e3b, e3c⟩ := e3
      have hb := hβp k
      have hg := hγp k
      have hρ2 : ρ k ≤ 2 := hr.trans e3c
      have hρsq : ρ k ^ 2 ≤ 4 := by
        have := pow_le_pow_left₀ (hρ0 k) hρ2 2; norm_num at this; linarith
      have hρs0 : 0 ≤ ρ k ^ 2 := sq_nonneg _
      have hq1le : q₁ k ≤ 1 := by
        have : q₁ k ≤ (1 + c₀ * β k) * q₁ k := le_mul_of_one_le_left hq10 (by
          linarith [mul_nonneg hc₀ hb.le])
        linarith [mul_nonneg ha₀0.le hb.le]
      have hq2le : q₂ k ≤ 1 := by
        have : q₂ k ≤ (1 + c₀ * β k) * q₂ k := le_mul_of_one_le_left hq20 (by
          linarith [mul_nonneg hc₀ hb.le])
        linarith [mul_nonneg ha₀0.le hg.le]
      -- the squared contraction factors
      have hc1 : ρ k ^ 2 * ((1 + a₀ * β k) * q₁ k ^ 2) ≤ 1 - a₀ * β k := by
        have t0 : 0 ≤ ρ k * q₁ k := mul_nonneg (hρ0 k) hq10
        have t1 : ρ k * q₁ k ≤ 1 - 2 * a₀ * β k :=
          (mul_le_mul_of_nonneg_right hr hq10).trans hq1
        have t2 : (ρ k * q₁ k) ^ 2 ≤ (1 - 2 * (a₀ * β k)) ^ 2 := by
          have := pow_le_pow_left₀ t0 t1 2; ring_nf; ring_nf at this; linarith
        have t3 := sq_contract_le (mul_nonneg ha₀0.le hb.le) e3a
        have t4 := mul_le_mul_of_nonneg_right t2 (by positivity : (0 : ℝ) ≤ 1 + a₀ * β k)
        have e : ρ k ^ 2 * ((1 + a₀ * β k) * q₁ k ^ 2) = (ρ k * q₁ k) ^ 2 * (1 + a₀ * β k) := by
          ring
        linarith
      have hc2 : ρ k ^ 2 * ((1 + a₀ * γ k) * q₂ k ^ 2) ≤ 1 - a₀ * γ k := by
        have t0 : 0 ≤ ρ k * q₂ k := mul_nonneg (hρ0 k) hq20
        have t1 : ρ k * q₂ k ≤ 1 - 2 * a₀ * γ k :=
          (mul_le_mul_of_nonneg_right hr hq20).trans hq2
        have t2 : (ρ k * q₂ k) ^ 2 ≤ (1 - 2 * (a₀ * γ k)) ^ 2 := by
          have := pow_le_pow_left₀ t0 t1 2; ring_nf; ring_nf at this; linarith
        have t3 := sq_contract_le (mul_nonneg ha₀0.le hg.le) e3b
        have t4 := mul_le_mul_of_nonneg_right t2 (by positivity : (0 : ℝ) ≤ 1 + a₀ * γ k)
        have e : ρ k ^ 2 * ((1 + a₀ * γ k) * q₂ k ^ 2) = (ρ k * q₂ k) ^ 2 * (1 + a₀ * γ k) := by
          ring
        linarith
      refine ⟨?_, ?_, by linarith, by linarith⟩
      · -- the slow component
        have h1 : U (k + 1) = ρ k ^ 2 * (A (k + 1) / γ k ^ 2) := hnext2 A k
        have hγ2 : 0 < γ k ^ 2 := by positivity
        set X1 := (1 + a₀ * β k) * q₁ k ^ 2 * U k
        set X2 := (1 + 1 / (a₀ * β k)) * (c₁ * β k) ^ 2 * V k
        set X3 := 8 * β k ^ 2 * CM * (q₁ k * a k + c₁ * β k * b k) / γ k ^ 2
        set X4 := 3 * β k ^ 4 * CM ^ 2 / γ k ^ 2
        have h2 : A (k + 1) / γ k ^ 2 ≤ X1 + X2 + X3 + X4 := by
          rw [div_le_iff₀ hγ2]
          have := RA k
          rw [hUA k, hVB k] at this
          have e : (X1 + X2 + X3 + X4) * γ k ^ 2 =
              (1 + (η - c₀) / 4 * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2 * (U k * γ k ^ 2)
              + (1 + 1 / ((η - c₀) / 4 * β k)) * (c₁ * β k) ^ 2 * (V k * γ k ^ 2)
              + 8 * β k ^ 2 * CM * ((1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k)
              + 3 * β k ^ 4 * CM ^ 2 := by
            have hηc : η - c₀ ≠ 0 := (sub_pos.mpr hc₀η).ne'
            simp only [X1, X2, X3, X4, hq₁, ha₀]; field_simp [hb.ne', hg.ne', hηc]; ring
          rw [e]; exact this
        have s1 : ρ k ^ 2 * X1 ≤ (1 - a₀ * β k) * U k := by
          have := mul_le_mul_of_nonneg_right hc1 (hU0 k)
          have e : ρ k ^ 2 * X1 = ρ k ^ 2 * ((1 + a₀ * β k) * q₁ k ^ 2) * U k := by
            simp only [X1]; ring
          linarith
        have s2 : ρ k ^ 2 * X2 ≤ c' * β k * V k := by
          have e1 : (1 + 1 / (a₀ * β k)) * (c₁ * β k) ^ 2 = c₁ ^ 2 * (β k + 1 / a₀) * β k := by
            field_simp; ring
          have t1 : c₁ ^ 2 * (β k + 1 / a₀) * β k ≤ c₁ ^ 2 * (Bβ + 1 / a₀) * β k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hβB k])
              (sq_nonneg _)) hb.le
          have t2 : 0 ≤ c₁ ^ 2 * (β k + 1 / a₀) * β k := by positivity
          have t3 := mul_le_mul hρsq t1 t2 (by norm_num)
          have t4 := mul_le_mul_of_nonneg_right t3 (hV0 k)
          have e : ρ k ^ 2 * X2 = ρ k ^ 2 * (c₁ ^ 2 * (β k + 1 / a₀) * β k) * V k := by
            simp only [X2]; rw [e1]; ring
          have e' : 4 * (c₁ ^ 2 * (Bβ + 1 / a₀) * β k) * V k = c' * β k * V k := by
            simp only [hc']; ring
          linarith
        have s3 : ρ k ^ 2 * X3 ≤ (32 * CM * W₁ * (1 + c₁ * Bβ) * Bq) * β k := by
          have t1 : q₁ k * a k + c₁ * β k * b k ≤ W₁ * (1 + c₁ * Bβ) * γ k := by
            have u1 : q₁ k * a k ≤ a k := mul_le_of_le_one_left (ha0 k) hq1le
            have u2 : c₁ * β k * b k ≤ c₁ * Bβ * (W₁ * γ k) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hβB k) hc₁) (hbW k) (hb0 k) (by positivity)
            have := haW k
            nlinarith
          have t2 : X3 ≤ 8 * CM * W₁ * (1 + c₁ * Bβ) * Bq * β k := by
            simp only [X3]
            rw [div_le_iff₀ hγ2]
            have t3 : 8 * β k ^ 2 * CM * (q₁ k * a k + c₁ * β k * b k) ≤
                8 * β k ^ 2 * CM * (W₁ * (1 + c₁ * Bβ) * γ k) :=
              mul_le_mul_of_nonneg_left t1 (by positivity)
            have t4 : β k ≤ Bq * γ k := by
              have := hqB k; rwa [div_le_iff₀ hg] at this
            have t5 : 8 * β k ^ 2 * CM * (W₁ * (1 + c₁ * Bβ) * γ k) ≤
                8 * CM * W₁ * (1 + c₁ * Bβ) * Bq * β k * γ k ^ 2 := by
              have e : 8 * CM * W₁ * (1 + c₁ * Bβ) * Bq * β k * γ k ^ 2 =
                  8 * β k * CM * (W₁ * (1 + c₁ * Bβ) * γ k) * (Bq * γ k) := by ring
              rw [e]
              have e2 : 8 * β k ^ 2 * CM * (W₁ * (1 + c₁ * Bβ) * γ k) =
                  8 * β k * CM * (W₁ * (1 + c₁ * Bβ) * γ k) * β k := by ring
              rw [e2]
              exact mul_le_mul_of_nonneg_left t4 (by positivity)
            linarith
          have t6 : 0 ≤ X3 := by
            simp only [X3]
            have : 0 ≤ q₁ k * a k + c₁ * β k * b k :=
              add_nonneg (mul_nonneg hq10 (ha0 k)) (mul_nonneg (mul_nonneg hc₁ hb.le) (hb0 k))
            positivity
          have := mul_le_mul hρsq t2 t6 (by norm_num)
          linarith
        have s4 : ρ k ^ 2 * X4 ≤ (12 * CM ^ 2 * Bβ * Bq ^ 2) * β k := by
          have t1 : X4 ≤ 3 * CM ^ 2 * Bβ * Bq ^ 2 * β k := by
            simp only [X4]
            rw [div_le_iff₀ hγ2]
            have t4 : β k ≤ Bq * γ k := by
              have := hqB k; rwa [div_le_iff₀ hg] at this
            have t5 : β k ^ 2 ≤ (Bq * γ k) ^ 2 := pow_le_pow_left₀ hb.le t4 2
            have e : 3 * β k ^ 4 * CM ^ 2 = 3 * CM ^ 2 * β k * β k * β k ^ 2 := by ring
            have e2 : 3 * CM ^ 2 * Bβ * Bq ^ 2 * β k * γ k ^ 2 =
                3 * CM ^ 2 * β k * Bβ * (Bq * γ k) ^ 2 := by ring
            rw [e, e2]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hβB k) (by positivity)) t5
              (sq_nonneg _) (by positivity)
          have t6 : 0 ≤ X4 := by simp only [X4]; positivity
          have := mul_le_mul hρsq t1 t6 (by norm_num)
          linarith
        have h6 : ρ k ^ 2 * (A (k + 1) / γ k ^ 2) ≤ ρ k ^ 2 * (X1 + X2 + X3 + X4) :=
          mul_le_mul_of_nonneg_left h2 hρs0
        have e : ρ k ^ 2 * (X1 + X2 + X3 + X4) =
            ρ k ^ 2 * X1 + ρ k ^ 2 * X2 + ρ k ^ 2 * X3 + ρ k ^ 2 * X4 := by ring
        have e2 : E' * β k = (32 * CM * W₁ * (1 + c₁ * Bβ) * Bq) * β k
            + (12 * CM ^ 2 * Bβ * Bq ^ 2) * β k := by simp only [hE']; ring
        rw [h1]
        linarith
      · -- the fast component
        have h1 : V (k + 1) = ρ k ^ 2 * (B (k + 1) / γ k ^ 2) := hnext2 B k
        have hγ2 : 0 < γ k ^ 2 := by positivity
        set Y1 := (1 + a₀ * γ k) * q₂ k ^ 2 * V k
        set Y2 := (1 + 1 / (a₀ * γ k)) * (c₂ * τ k) ^ 2 * U k
        set Y3 := 8 * CN * (q₂ k * b k + c₂ * τ k * a k)
        set Y4 := 3 * γ k ^ 2 * CN ^ 2
        have h2 : B (k + 1) / γ k ^ 2 ≤ Y1 + Y2 + Y3 + Y4 := by
          rw [div_le_iff₀ hγ2]
          rw [hUA k, hVB k] at hBk
          have e : (Y1 + Y2 + Y3 + Y4) * γ k ^ 2 =
              (1 + (η - c₀) / 4 * γ k) * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2
                * (V k * γ k ^ 2)
              + (1 + 1 / ((η - c₀) / 4 * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2
                * (U k * γ k ^ 2)
              + 8 * γ k ^ 2 * CN * ((1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
                + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k) + 3 * γ k ^ 4 * CN ^ 2 := by
            have hηc : η - c₀ ≠ 0 := (sub_pos.mpr hc₀η).ne'
            simp only [Y1, Y2, Y3, Y4, hq₂, hτ, ha₀]; field_simp [hb.ne', hg.ne', hηc]; ring
          rw [e]; exact hBk
        have s1 : ρ k ^ 2 * Y1 ≤ (1 - a₀ * γ k) * V k := by
          have := mul_le_mul_of_nonneg_right hc2 (hV0 k)
          have e : ρ k ^ 2 * Y1 = ρ k ^ 2 * ((1 + a₀ * γ k) * q₂ k ^ 2) * V k := by
            simp only [Y1]; ring
          linarith
        have s2 : ρ k ^ 2 * Y2 ≤ 4 * c₂ ^ 2 * (γ k * (τ k / γ k) ^ 2 + (τ k / γ k) ^ 2 / a₀)
            * γ k * U k := by
          have e1 : (1 + 1 / (a₀ * γ k)) * (c₂ * τ k) ^ 2 =
              c₂ ^ 2 * (γ k * (τ k / γ k) ^ 2 + (τ k / γ k) ^ 2 / a₀) * γ k := by
            field_simp; ring
          have t2 : 0 ≤ c₂ ^ 2 * (γ k * (τ k / γ k) ^ 2 + (τ k / γ k) ^ 2 / a₀) * γ k := by
            positivity
          have t3 := mul_le_mul_of_nonneg_right hρsq t2
          have t4 := mul_le_mul_of_nonneg_right t3 (hU0 k)
          have e : ρ k ^ 2 * Y2 = ρ k ^ 2 * (c₂ ^ 2 * (γ k * (τ k / γ k) ^ 2
              + (τ k / γ k) ^ 2 / a₀) * γ k) * U k := by
            simp only [Y2]; rw [e1]; ring
          linarith
        have s3 : ρ k ^ 2 * Y3 ≤ (32 * CN * W₁ * (1 + c₂ * T)) * γ k := by
          have t1 : q₂ k * b k + c₂ * τ k * a k ≤ W₁ * (1 + c₂ * T) * γ k := by
            have u1 : q₂ k * b k ≤ b k := mul_le_of_le_one_left (hb0 k) hq2le
            have u2 : c₂ * τ k * a k ≤ c₂ * T * (W₁ * γ k) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hτT k) hc₂) (haW k) (ha0 k) (by positivity)
            have := hbW k
            nlinarith
          have t6 : 0 ≤ Y3 := by
            simp only [Y3]
            have : 0 ≤ q₂ k * b k + c₂ * τ k * a k :=
              add_nonneg (mul_nonneg hq20 (hb0 k)) (mul_nonneg (mul_nonneg hc₂ (hτ0 k)) (ha0 k))
            positivity
          have t2 : Y3 ≤ 8 * CN * (W₁ * (1 + c₂ * T) * γ k) := by
            simp only [Y3]; exact mul_le_mul_of_nonneg_left t1 (by positivity)
          have := mul_le_mul hρsq t2 t6 (by norm_num)
          linarith
        have s4 : ρ k ^ 2 * Y4 ≤ (12 * CN ^ 2 * Bγ) * γ k := by
          have t1 : Y4 ≤ 3 * CN ^ 2 * Bγ * γ k := by
            simp only [Y4]
            have e : 3 * γ k ^ 2 * CN ^ 2 = 3 * CN ^ 2 * γ k * γ k := by ring
            rw [e]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hγB k) (by positivity))
              hg.le |>.trans_eq (by ring)
          have t6 : 0 ≤ Y4 := by simp only [Y4]; positivity
          have := mul_le_mul hρsq t1 t6 (by norm_num)
          linarith
        have h6 : ρ k ^ 2 * (B (k + 1) / γ k ^ 2) ≤ ρ k ^ 2 * (Y1 + Y2 + Y3 + Y4) :=
          mul_le_mul_of_nonneg_left h2 hρs0
        have e : ρ k ^ 2 * (Y1 + Y2 + Y3 + Y4) =
            ρ k ^ 2 * Y1 + ρ k ^ 2 * Y2 + ρ k ^ 2 * Y3 + ρ k ^ 2 * Y4 := by ring
        have e2 : C' * γ k = (32 * CN * W₁ * (1 + c₂ * T)) * γ k + (12 * CN ^ 2 * Bγ) * γ k := by
          simp only [hC']; ring
        rw [h1]
        linarith)
  obtain ⟨⟨MU, hMU⟩, ⟨MV, hMV⟩⟩ := box2
  refine ⟨max MU MV, fun k => ⟨?_, ?_⟩⟩
  · rw [hUA k]
    exact mul_le_mul_of_nonneg_right ((hMU k).trans (le_max_left _ _)) (sq_nonneg _)
  · rw [hVB k]
    exact mul_le_mul_of_nonneg_right ((hMV k).trans (le_max_right _ _)) (sq_nonneg _)

end Scalar

end StochasticApproximation
