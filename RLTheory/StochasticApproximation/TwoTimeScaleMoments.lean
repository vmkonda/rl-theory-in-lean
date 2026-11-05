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
lemma slow_step_bound {x f : E d₁} {zn η K β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (_hzn : 0 ≤ zn)
    (hin : ⟪x, f⟫_ℝ ≤ -η * ‖x‖ ^ 2 + K * ‖x‖ * zn) (hf : ‖f‖ ≤ K * (‖x‖ + zn)) (_hK : 0 ≤ K) :
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
    (hBz : 0 ≤ Bz) (hX : 0 ≤ X) (_hQ0 : 0 ≤ Q)
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
    (hηγ : η * γ ≤ 1) (hβ : 0 ≤ β) (_hxn : 0 ≤ xn) (_hK : 0 ≤ K) (_hK' : 0 ≤ K')
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
and the step sizes satisfy `β/γ → 0` and `γ_k / γ_{k+1} ≤ 1 + c₀ β_k` with
`c₀ < η`. -/
lemma tts_moments_scalar {β γ a b A B : ℕ → ℝ} {η c₀ κ c₁ c₂ CM CN : ℝ}
    (hβp : ∀ k, 0 < β k) (hγp : ∀ k, 0 < γ k) (hβ0 : Tendsto β atTop (𝓝 0))
    (hγ0 : Tendsto γ atTop (𝓝 0)) (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η)
    (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k) (hc₁ : 0 ≤ c₁)
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

/-- Young's inequality for squares: `(p + q)² ≤ (1 + t) p² + (1 + 1/t) q²` for `t > 0`. -/
lemma young_sq {p q t : ℝ} (ht : 0 < t) : (p + q) ^ 2 ≤ (1 + t) * p ^ 2 + (1 + 1 / t) * q ^ 2 := by
  have h : 0 ≤ (t * p - q) ^ 2 / t := by positivity
  have e : (t * p - q) ^ 2 / t = t * p ^ 2 - 2 * p * q + 1 / t * q ^ 2 := by field_simp; ring
  nlinarith

end Scalar

section Main

variable {d₁ d₂ : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

set_option maxHeartbeats 8000000 in
/-- **The moment engine for two time scales.** Let `x_{k+1} = u_k + β_k M_{k+1}` and
`z_{k+1} = v_k + γ_k N_{k+1}`, with `u_k, v_k` known at time `k` and `M, N` bounded martingale
differences. If the known parts contract,
* `‖u_k‖² ≤ (1 - ηβ_k + κβ_k²) ‖x_k‖² + c₁ β_k ‖z_k‖² + G β_k²`,
* eventually `‖v_k‖² ≤ (1 - ηγ_k + c₂τ_k) ‖z_k‖² + c₂τ_k ‖x_k‖² + G γ_k²`, `τ = γ² + β²/γ`,

and `β/γ → 0`, `γ_k / γ_{k+1} ≤ 1 + c₀ β_k` with `0 ≤ c₀ < η`, then
`E‖x_k‖⁴, E‖z_k‖⁴ ≤ W γ_k²`. The additive `G` terms absorb small perturbations of the drift,
such as Poisson shifts and sampling remainders. -/
lemma tts_moments_of_steps {β γ : ℕ → ℝ} (hβp : ∀ k, 0 < β k) (hγp : ∀ k, 0 < γ k)
    (hβ0 : Tendsto β atTop (𝓝 0)) (hγ0 : Tendsto γ atTop (𝓝 0))
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0)) {η c₀ κ c₁ c₂ G CM CN : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η) (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hG : 0 ≤ G) (hq : ∀ k, 0 ≤ 1 - η * β k + κ * β k ^ 2)
    (ℱ : MeasureTheory.Filtration ℕ m0) {x u M : ℕ → Ω → E d₁} {z v N : ℕ → Ω → E d₂}
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hzm : ∀ k, StronglyMeasurable[ℱ k] (z k))
    (hum : ∀ k, StronglyMeasurable[ℱ k] (u k)) (hvm : ∀ k, StronglyMeasurable[ℱ k] (v k))
    (hbd : ∀ k, ∃ C, 0 ≤ C ∧ ∀ ω, ‖x k ω‖ ≤ C ∧ ‖z k ω‖ ≤ C)
    (hubd : ∀ k, ∃ C, ∀ ω, ‖u k ω‖ ≤ C) (hvbd : ∀ k, ∃ C, ∀ ω, ‖v k ω‖ ≤ C)
    (hMm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1))) (hMb : ∀ k ω, ‖M (k + 1) ω‖ ≤ CM)
    (hMmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hNm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (N (k + 1))) (hNb : ∀ k ω, ‖N (k + 1) ω‖ ≤ CN)
    (hNmart : ∀ k j, μ[fun ω => N (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hxs : ∀ k ω, x (k + 1) ω = u k ω + β k • M (k + 1) ω)
    (hzs : ∀ k ω, z (k + 1) ω = v k ω + γ k • N (k + 1) ω)
    (hu2 : ∀ k ω, ‖u k ω‖ ^ 2 ≤ (1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2
      + c₁ * β k * ‖z k ω‖ ^ 2 + G * β k ^ 2)
    (hv2 : ∀ᶠ k in atTop, ∀ ω, ‖v k ω‖ ^ 2 ≤
      (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2 + G * γ k ^ 2) :
    ∃ W, ∀ k, ∫ ω, ‖x k ω‖ ^ 4 ∂μ ≤ W * γ k ^ 2 ∧ ∫ ω, ‖z k ω‖ ^ 4 ∂μ ≤ W * γ k ^ 2 := by
  have hη : 0 < η := by linarith
  set a : ℕ → ℝ := fun k => ∫ ω, ‖x k ω‖ ^ 2 ∂μ with ha
  set b : ℕ → ℝ := fun k => ∫ ω, ‖z k ω‖ ^ 2 ∂μ with hb'
  set A : ℕ → ℝ := fun k => ∫ ω, ‖x k ω‖ ^ 4 ∂μ with hA
  set B : ℕ → ℝ := fun k => ∫ ω, ‖z k ω‖ ^ 4 ∂μ with hB
  have ha0 : ∀ k, 0 ≤ a k := fun k => integral_nonneg fun _ => by positivity
  have hb0 : ∀ k, 0 ≤ b k := fun k => integral_nonneg fun _ => by positivity
  have hbI : ∀ (g : Ω → ℝ), AEStronglyMeasurable g μ → (∃ C, ∀ ω, |g ω| ≤ C) →
      Integrable g μ := fun g hg ⟨C, hC⟩ => (memLp_top_of_bound hg C
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top
  have hxa : ∀ k, AEStronglyMeasurable (x k) μ := fun k =>
    ((hxm k).mono (ℱ.le k)).aestronglyMeasurable
  have hza : ∀ k, AEStronglyMeasurable (z k) μ := fun k =>
    ((hzm k).mono (ℱ.le k)).aestronglyMeasurable
  have ipow : ∀ {n : ℕ} (w : Ω → E n) (p : ℕ), AEStronglyMeasurable w μ →
      (∃ C, ∀ ω, ‖w ω‖ ≤ C) → Integrable (fun ω => ‖w ω‖ ^ p) μ := by
    intro n w p hw ⟨C, hC⟩
    refine hbI _ (hw.norm.pow p) ⟨max C 0 ^ p, fun ω => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hC ω).trans (le_max_left _ _)) p
  have ix : ∀ k p, Integrable (fun ω => ‖x k ω‖ ^ p) μ := fun k p => by
    obtain ⟨C, -, hC⟩ := hbd k; exact ipow _ p (hxa k) ⟨C, fun ω => (hC ω).1⟩
  have iz : ∀ k p, Integrable (fun ω => ‖z k ω‖ ^ p) μ := fun k p => by
    obtain ⟨C, -, hC⟩ := hbd k; exact ipow _ p (hza k) ⟨C, fun ω => (hC ω).2⟩
  have iu : ∀ k p, Integrable (fun ω => ‖u k ω‖ ^ p) μ := fun k p =>
    ipow _ p ((hum k).mono (ℱ.le k)).aestronglyMeasurable (hubd k)
  have iv : ∀ k p, Integrable (fun ω => ‖v k ω‖ ^ p) μ := fun k p =>
    ipow _ p ((hvm k).mono (ℱ.le k)).aestronglyMeasurable (hvbd k)
  -- integrals of the comparison functions
  have I2 : ∀ (f g : Ω → ℝ) (p q r : ℝ), Integrable f μ → Integrable g μ →
      ∫ ω, (p * f ω + q * g ω + r) ∂μ = p * ∫ ω, f ω ∂μ + q * ∫ ω, g ω ∂μ + r := by
    intro f g p q r hf hg
    have i1 : Integrable (fun ω => p * f ω + q * g ω) μ := (hf.const_mul p).add (hg.const_mul q)
    rw [integral_add i1 (integrable_const r), integral_add (hf.const_mul p) (hg.const_mul q),
      integral_const_mul, integral_const_mul]
    simp
  have I4 : ∀ (f g f' g' : Ω → ℝ) (p q p' q' r : ℝ), Integrable f μ → Integrable g μ →
      Integrable f' μ → Integrable g' μ →
      ∫ ω, (p * f ω + q * g ω + (p' * f' ω + q' * g' ω) + r) ∂μ =
        p * ∫ ω, f ω ∂μ + q * ∫ ω, g ω ∂μ + (p' * ∫ ω, f' ω ∂μ + q' * ∫ ω, g' ω ∂μ) + r := by
    intro f g f' g' p q p' q' r hf hg hf' hg'
    have i1 : Integrable (fun ω => p * f ω + q * g ω) μ := (hf.const_mul p).add (hg.const_mul q)
    have i2 : Integrable (fun ω => p' * f' ω + q' * g' ω) μ :=
      (hf'.const_mul p').add (hg'.const_mul q')
    have i3 : Integrable (fun ω => p * f ω + q * g ω + (p' * f' ω + q' * g' ω)) μ := i1.add i2
    rw [integral_add i3 (integrable_const r), integral_add i1 i2,
      integral_add (hf.const_mul p) (hg.const_mul q),
      integral_add (hf'.const_mul p') (hg'.const_mul q'), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul]
    simp
  have hηγ : ∀ᶠ k in atTop, η * γ k ≤ 1 := by
    have h := hγ0.const_mul η
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  set t₀ := (η - c₀) / 4 with ht₀
  have ht₀0 : 0 < t₀ := by simp only [ht₀]; linarith
  -- the slow component
  have hiu : ∀ k, ∫ ω, ‖u k ω‖ ^ 2 ∂μ ≤ (1 - η * β k + κ * β k ^ 2) * a k
      + c₁ * β k * b k + G * β k ^ 2 := fun k => by
    calc ∫ ω, ‖u k ω‖ ^ 2 ∂μ ≤ ∫ ω, ((1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2
          + c₁ * β k * ‖z k ω‖ ^ 2 + G * β k ^ 2) ∂μ :=
          integral_mono (iu k 2) ((((ix k 2).const_mul _).add ((iz k 2).const_mul _)).add
            (integrable_const _)) (hu2 k)
      _ = _ := I2 _ _ _ _ _ (ix k 2) (iz k 2)
  have hiu4 : ∀ k, ∫ ω, (‖u k ω‖ ^ 2) ^ 2 ∂μ ≤
      (1 + t₀ * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2 * A k
        + (1 + 1 / (t₀ * β k)) * (c₁ * β k) ^ 2 * B k
        + (2 * G * β k ^ 2 * (1 - η * β k + κ * β k ^ 2) * a k
          + 2 * G * β k ^ 2 * (c₁ * β k) * b k) + G ^ 2 * β k ^ 4 := fun k => by
    have hb := hβp k
    have iu4 : Integrable (fun ω => (‖u k ω‖ ^ 2) ^ 2) μ := by
      have := iu k 4
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only; ring
    have hpt : ∀ ω, (‖u k ω‖ ^ 2) ^ 2 ≤
        (1 + t₀ * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2 * ‖x k ω‖ ^ 4
        + (1 + 1 / (t₀ * β k)) * (c₁ * β k) ^ 2 * ‖z k ω‖ ^ 4
        + (2 * G * β k ^ 2 * (1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2
          + 2 * G * β k ^ 2 * (c₁ * β k) * ‖z k ω‖ ^ 2) + G ^ 2 * β k ^ 4 := fun ω => by
      set P := (1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2 + c₁ * β k * ‖z k ω‖ ^ 2 with hP
      have h1 := pow_le_pow_left₀ (sq_nonneg _) (hu2 k ω) 2
      have h2 := young_sq (p := (1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2)
        (q := c₁ * β k * ‖z k ω‖ ^ 2) (mul_pos ht₀0 hb)
      have e1 : (P + G * β k ^ 2) ^ 2 = P ^ 2 + 2 * G * β k ^ 2 * P + G ^ 2 * β k ^ 4 := by ring
      have e2 : (1 + t₀ * β k) * ((1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2) ^ 2
          + (1 + 1 / (t₀ * β k)) * (c₁ * β k * ‖z k ω‖ ^ 2) ^ 2 =
          (1 + t₀ * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2 * ‖x k ω‖ ^ 4
          + (1 + 1 / (t₀ * β k)) * (c₁ * β k) ^ 2 * ‖z k ω‖ ^ 4 := by ring
      have e3 : 2 * G * β k ^ 2 * P = 2 * G * β k ^ 2 * (1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2
          + 2 * G * β k ^ 2 * (c₁ * β k) * ‖z k ω‖ ^ 2 := by simp only [hP]; ring
      have h1' : (‖u k ω‖ ^ 2) ^ 2 ≤ (P + G * β k ^ 2) ^ 2 := h1
      rw [e1] at h1'
      linarith
    calc ∫ ω, (‖u k ω‖ ^ 2) ^ 2 ∂μ ≤ ∫ ω, ((1 + t₀ * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2
          * ‖x k ω‖ ^ 4 + (1 + 1 / (t₀ * β k)) * (c₁ * β k) ^ 2 * ‖z k ω‖ ^ 4
          + (2 * G * β k ^ 2 * (1 - η * β k + κ * β k ^ 2) * ‖x k ω‖ ^ 2
            + 2 * G * β k ^ 2 * (c₁ * β k) * ‖z k ω‖ ^ 2) + G ^ 2 * β k ^ 4) ∂μ :=
          integral_mono iu4 (((((ix k 4).const_mul _).add ((iz k 4).const_mul _)).add
            (((ix k 2).const_mul _).add ((iz k 2).const_mul _))).add (integrable_const _)) hpt
      _ = _ := I4 _ _ _ _ _ _ _ _ _ (ix k 4) (iz k 4) (ix k 2) (iz k 2)
  -- the fast component
  have hiv : ∀ᶠ k in atTop, ∫ ω, ‖v k ω‖ ^ 2 ∂μ ≤
      (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k + G * γ k ^ 2 := by
    filter_upwards [hv2] with k hk
    calc ∫ ω, ‖v k ω‖ ^ 2 ∂μ ≤ ∫ ω, ((1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k))
          * ‖z k ω‖ ^ 2 + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2 + G * γ k ^ 2) ∂μ :=
          integral_mono (iv k 2) ((((iz k 2).const_mul _).add ((ix k 2).const_mul _)).add
            (integrable_const _)) hk
      _ = _ := I2 _ _ _ _ _ (iz k 2) (ix k 2)
  have hiv4 : ∀ᶠ k in atTop, ∫ ω, (‖v k ω‖ ^ 2) ^ 2 ∂μ ≤
      (1 + t₀ * γ k) * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * B k
        + (1 + 1 / (t₀ * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * A k
        + (2 * G * γ k ^ 2 * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
          + 2 * G * γ k ^ 2 * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * a k) + G ^ 2 * γ k ^ 4 := by
    filter_upwards [hv2] with k hk
    have hg := hγp k
    have iv4 : Integrable (fun ω => (‖v k ω‖ ^ 2) ^ 2) μ := by
      have := iv k 4
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only; ring
    have hpt : ∀ ω, (‖v k ω‖ ^ 2) ^ 2 ≤
        (1 + t₀ * γ k) * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * ‖z k ω‖ ^ 4
        + (1 + 1 / (t₀ * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * ‖x k ω‖ ^ 4
        + (2 * G * γ k ^ 2 * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
          + 2 * G * γ k ^ 2 * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖x k ω‖ ^ 2)
        + G ^ 2 * γ k ^ 4 := fun ω => by
      set P := (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2 with hP
      have h1 := pow_le_pow_left₀ (sq_nonneg _) (hk ω) 2
      have h2 := young_sq (p := (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2)
        (q := c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2) (mul_pos ht₀0 hg)
      have e1 : (P + G * γ k ^ 2) ^ 2 = P ^ 2 + 2 * G * γ k ^ 2 * P + G ^ 2 * γ k ^ 4 := by ring
      have e2 : (1 + t₀ * γ k) * ((1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2) ^ 2
          + (1 + 1 / (t₀ * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2) ^ 2 =
          (1 + t₀ * γ k) * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * ‖z k ω‖ ^ 4
          + (1 + 1 / (t₀ * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * ‖x k ω‖ ^ 4 := by ring
      have e3 : 2 * G * γ k ^ 2 * P =
          2 * G * γ k ^ 2 * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
          + 2 * G * γ k ^ 2 * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖x k ω‖ ^ 2 := by
        simp only [hP]; ring
      have h1' : (‖v k ω‖ ^ 2) ^ 2 ≤ (P + G * γ k ^ 2) ^ 2 := h1
      rw [e1] at h1'
      linarith
    calc ∫ ω, (‖v k ω‖ ^ 2) ^ 2 ∂μ ≤ ∫ ω, ((1 + t₀ * γ k)
          * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * ‖z k ω‖ ^ 4
          + (1 + 1 / (t₀ * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * ‖x k ω‖ ^ 4
          + (2 * G * γ k ^ 2 * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
            + 2 * G * γ k ^ 2 * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖x k ω‖ ^ 2)
          + G ^ 2 * γ k ^ 4) ∂μ :=
          integral_mono iv4 (((((iz k 4).const_mul _).add ((ix k 4).const_mul _)).add
            (((iz k 2).const_mul _).add ((ix k 2).const_mul _))).add (integrable_const _)) hpt
      _ = _ := I4 _ _ _ _ _ _ _ _ _ (iz k 4) (ix k 4) (iz k 2) (ix k 2)
  -- the raw recursions
  have Ra : ∀ k, a (k + 1) ≤ (1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k
      + (CM ^ 2 + 2 * G) * β k ^ 2 := fun k => by
    have h1 := integral_sq_step (μ := μ) ℱ k (hum k) (hubd k) (hMm k) (hMb k) (hMmart k) (hxs k)
    have h2 := hiu k
    have h3 : 0 ≤ G * β k ^ 2 := by positivity
    simp only [ha]; linarith
  have Rb : ∀ᶠ k in atTop, b (k + 1) ≤ (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
      + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k + (CN ^ 2 + 2 * G) * γ k ^ 2 := by
    filter_upwards [hiv] with k hk
    have h1 := integral_sq_step (μ := μ) ℱ k (hvm k) (hvbd k) (hNm k) (hNb k) (hNmart k) (hzs k)
    have h3 : 0 ≤ G * γ k ^ 2 := by positivity
    simp only [hb']; linarith
  have RA : ∀ k, A (k + 1) ≤ (1 + (η - c₀) / 4 * β k) * (1 - η * β k + κ * β k ^ 2) ^ 2
        * A k + (1 + 1 / ((η - c₀) / 4 * β k)) * (c₁ * β k) ^ 2 * B k
      + 8 * β k ^ 2 * (CM ^ 2 + 2 * G) * ((1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k)
      + 3 * β k ^ 4 * (CM ^ 2 + 2 * G) ^ 2 := fun k => by
    have hb := hβp k
    have h1 := integral_four_step (μ := μ) ℱ k (hum k) (hubd k) (hMm k) (hMb k) (hMmart k)
      (hxs k)
    have h2 := hiu4 k
    have h3 := mul_le_mul_of_nonneg_left (hiu k) (by positivity : 0 ≤ 8 * β k ^ 2 * CM ^ 2)
    have hX : 0 ≤ (1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k :=
      add_nonneg (mul_nonneg (hq k) (ha0 k)) (by have := hb0 k; positivity)
    have h4 : 0 ≤ G * β k ^ 2 * ((1 - η * β k + κ * β k ^ 2) * a k + c₁ * β k * b k) := by
      positivity
    have h5 : 0 ≤ (4 * CM ^ 2 * G + 11 * G ^ 2) * β k ^ 4 := by positivity
    simp only [hA, ← ht₀] at h1 h2 ⊢
    linarith
  have RB : ∀ᶠ k in atTop, B (k + 1) ≤ (1 + (η - c₀) / 4 * γ k)
        * (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * B k
      + (1 + 1 / ((η - c₀) / 4 * γ k)) * (c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) ^ 2 * A k
      + 8 * γ k ^ 2 * (CN ^ 2 + 2 * G) * ((1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k) + 3 * γ k ^ 4 * (CN ^ 2 + 2 * G) ^ 2 := by
    filter_upwards [hiv, hiv4, hηγ] with k hk hk4 hkη
    have hg := hγp k
    have h1 := integral_four_step (μ := μ) ℱ k (hvm k) (hvbd k) (hNm k) (hNb k) (hNmart k)
      (hzs k)
    have h3 := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 8 * γ k ^ 2 * CN ^ 2)
    have hτ : 0 ≤ c₂ * (γ k ^ 2 + β k ^ 2 / γ k) := by have := hβp k; positivity
    have hX : 0 ≤ (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k :=
      add_nonneg (mul_nonneg (by linarith) (hb0 k)) (mul_nonneg hτ (ha0 k))
    have h4 : 0 ≤ G * γ k ^ 2 * ((1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * b k
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * a k) := by positivity
    have h5 : 0 ≤ (4 * CN ^ 2 * G + 11 * G ^ 2) * γ k ^ 4 := by positivity
    simp only [hB, ← ht₀] at h1 hk4 ⊢
    linarith
  exact tts_moments_scalar (β := β) (γ := γ) (a := a) (b := b) (A := A) (B := B)
    (κ := κ) (c₁ := c₁) (c₂ := c₂) (CM := CM ^ 2 + 2 * G) (CN := CN ^ 2 + 2 * G) hβp hγp
    hβ0 hγ0 hβγ hc₀ hc₀η hratio hc₁ hc₂ (by positivity) (by positivity) ha0 hb0
    (fun k => integral_nonneg fun _ => by positivity) (fun k => integral_nonneg fun _ => by positivity)
    Ra Rb RA RB

set_option maxHeartbeats 8000000 in
/-- **Fourth moments for two time scales.** Let
`x_{k+1} = x_k + β_k (F₁(x_k, y_k) + M₁_{k+1})` and `y_{k+1} = y_k + γ_k (F₂(x_k, y_k) + M₂_{k+1})`,
and write `z = y + D x`. Suppose:
* `⟨x, F₁⟩ ≤ -η‖x‖² + K‖x‖‖z‖`, `⟨z, F₂⟩ ≤ -η‖z‖²` and `‖F_i‖ ≤ K(‖x‖ + ‖z‖)`;
* `M₁, M₂` are bounded martingale differences and the start is bounded;
* `β/γ → 0` and eventually `γ_k / γ_{k+1} ≤ 1 + c₀ β_k` with `0 ≤ c₀ < η`.

Then each iterate is bounded and `E‖x_k‖⁴, E‖y_k‖⁴ ≤ W γ_k²`. -/
theorem moment_bounds_tts {β γ : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar)
    (hγ : StepSizeRate γ 0) (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0)) {η c₀ K CM : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η) (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k)
    (hK : 0 ≤ K) (ℱ : MeasureTheory.Filtration ℕ m0) {x M₁ : ℕ → Ω → E d₁}
    {y M₂ : ℕ → Ω → E d₂} (D : Matrix (Fin d₂) (Fin d₁) ℝ) {F₁ : E d₁ → E d₂ → E d₁}
    {F₂ : E d₁ → E d₂ → E d₂}
    (hF₁in : ∀ u w, ⟪u, F₁ u w⟫_ℝ ≤ -η * ‖u‖ ^ 2 + K * ‖u‖ * ‖w + matCLM D u‖)
    (hF₁g : ∀ u w, ‖F₁ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₂in : ∀ u w, ⟪w + matCLM D u, F₂ u w⟫_ℝ ≤ -η * ‖w + matCLM D u‖ ^ 2)
    (hF₂g : ∀ u w, ‖F₂ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₁c : Continuous fun p : E d₁ × E d₂ => F₁ p.1 p.2)
    (hF₂c : Continuous fun p : E d₁ × E d₂ => F₂ p.1 p.2)
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • (F₁ (x k ω) (y k ω) + M₁ (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • (F₂ (x k ω) (y k ω) + M₂ (k + 1) ω))
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hym : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hx0 : ∃ C, ∀ ω, ‖x 0 ω‖ ≤ C) (hy0 : ∃ C, ∀ ω, ‖y 0 ω‖ ≤ C)
    (hM₁ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₁ (k + 1))) (hM₁b : ∀ k ω, ‖M₁ (k + 1) ω‖ ≤ CM)
    (hmart₁ : ∀ k j, μ[fun ω => M₁ (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hM₂ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₂ (k + 1))) (hM₂b : ∀ k ω, ‖M₂ (k + 1) ω‖ ≤ CM)
    (hmart₂ : ∀ k j, μ[fun ω => M₂ (k + 1) ω j | ℱ k] =ᵐ[μ] 0) :
    (∀ k, ∃ C, ∀ ω, ‖x k ω‖ ≤ C ∧ ‖y k ω‖ ≤ C) ∧
      ∃ W, ∀ k, ∫ ω, ‖x k ω‖ ^ 4 ∂μ ≤ W * γ k ^ 2 ∧ ∫ ω, ‖y k ω‖ ^ 4 ∂μ ≤ W * γ k ^ 2 := by
  have hη : 0 < η := by linarith
  set CM₀ := max CM 0
  have hCM₀ : 0 ≤ CM₀ := le_max_right _ _
  have hM₁b' : ∀ k ω, ‖M₁ (k + 1) ω‖ ≤ CM₀ := fun k ω => (hM₁b k ω).trans (le_max_left _ _)
  have hM₂b' : ∀ k ω, ‖M₂ (k + 1) ω‖ ≤ CM₀ := fun k ω => (hM₂b k ω).trans (le_max_left _ _)
  obtain ⟨Bβ, hBβ⟩ := hβ.tendsto_zero.bddAbove_range
  obtain ⟨Bγ, hBγ⟩ := hγ.tendsto_zero.bddAbove_range
  obtain ⟨Bq, hBq⟩ := hβγ.bddAbove_range
  have hβB : ∀ k, β k ≤ Bβ := fun k => hBβ ⟨k, rfl⟩
  have hqB : ∀ k, β k / γ k ≤ Bq := fun k => hBq ⟨k, rfl⟩
  have hBβ0 : 0 ≤ Bβ := (hβ.pos 0).le.trans (hβB 0)
  have hBq0 : 0 ≤ Bq := (div_nonneg (hβ.pos 0).le (hγ.pos 0).le).trans (hqB 0)
  set nD := ‖matCLM D‖
  have hnD : 0 ≤ nD := norm_nonneg _
  -- the coordinates and the steps
  set z : ℕ → Ω → E d₂ := fun k ω => y k ω + matCLM D (x k ω) with hz
  set f₁ : ℕ → Ω → E d₁ := fun k ω => F₁ (x k ω) (y k ω) with hf₁
  set f₂ : ℕ → Ω → E d₂ := fun k ω => F₂ (x k ω) (y k ω) with hf₂
  set u : ℕ → Ω → E d₁ := fun k ω => x k ω + β k • f₁ k ω with hu
  set v : ℕ → Ω → E d₂ := fun k ω => z k ω + γ k • f₂ k ω + β k • matCLM D (f₁ k ω) with hv
  set Mt : ℕ → Ω → E d₂ := fun n ω => M₂ n ω + (β (n - 1) / γ (n - 1)) • matCLM D (M₁ n ω)
    with hMt
  have hxstep : ∀ k ω, x (k + 1) ω = u k ω + β k • M₁ (k + 1) ω := fun k ω => by
    simp only [hu, hf₁, hx k ω, smul_add]; abel
  have hzstep : ∀ k ω, z (k + 1) ω = v k ω + γ k • Mt (k + 1) ω := fun k ω => by
    have hg := (hγ.pos k).ne'
    simp only [hz, hv, hMt, hf₁, hf₂, hx k ω, hy k ω, Nat.add_sub_cancel, map_add, map_smul,
      smul_add, smul_smul]
    rw [mul_div_cancel₀ _ hg]
    abel
  -- measurability
  have hzm : ∀ k, StronglyMeasurable[ℱ k] (z k) := fun k =>
    (hym k).add ((matCLM D).continuous.comp_stronglyMeasurable (hxm k))
  have hf₁m : ∀ k, StronglyMeasurable[ℱ k] (f₁ k) := fun k =>
    hF₁c.comp_stronglyMeasurable ((hxm k).prodMk (hym k))
  have hf₂m : ∀ k, StronglyMeasurable[ℱ k] (f₂ k) := fun k =>
    hF₂c.comp_stronglyMeasurable ((hxm k).prodMk (hym k))
  have hum : ∀ k, StronglyMeasurable[ℱ k] (u k) := fun k => by
    have := (hxm k).add ((hf₁m k).const_smul (β k)); exact this
  have hvm : ∀ k, StronglyMeasurable[ℱ k] (v k) := fun k => by
    have := ((hzm k).add ((hf₂m k).const_smul (γ k))).add
      (((matCLM D).continuous.comp_stronglyMeasurable (hf₁m k)).const_smul (β k))
    exact this
  have hMtm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Mt (k + 1)) := fun k => by
    have := (hM₂ k).add (((matCLM D).continuous.comp_stronglyMeasurable (hM₁ k)).const_smul
      (β k / γ k))
    exact this
  set CMt := CM₀ + Bq * nD * CM₀ with hCMt
  have hMtb : ∀ k ω, ‖Mt (k + 1) ω‖ ≤ CMt := fun k ω => by
    simp only [hMt, Nat.add_sub_cancel]
    refine (norm_add_le _ _).trans (add_le_add (hM₂b' k ω) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hβ.pos k).le (hγ.pos k).le)]
    have h1 : ‖matCLM D (M₁ (k + 1) ω)‖ ≤ nD * CM₀ :=
      ((matCLM D).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM₁b' k ω) hnD)
    calc β k / γ k * ‖matCLM D (M₁ (k + 1) ω)‖ ≤ Bq * (nD * CM₀) :=
          mul_le_mul (hqB k) h1 (norm_nonneg _) hBq0
      _ = Bq * nD * CM₀ := by ring
  have hMtmart : ∀ k j, μ[fun ω => Mt (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j => by
    have hM₁L : MemLp (M₁ (k + 1)) 2 μ := MemLp.of_bound
      ((hM₁ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM₀ (Eventually.of_forall (hM₁b' k))
    have hM₂L : MemLp (M₂ (k + 1)) 2 μ := MemLp.of_bound
      ((hM₂ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM₀ (Eventually.of_forall (hM₂b' k))
    have h2 := condExp_matCLM_eq_zero (μ := μ) (ℱ := ℱ k) D hM₁L (hmart₁ k) j
    have i1 := (memLp_apply hM₂L j).integrable one_le_two
    have i2 : Integrable (fun ω => matCLM D (M₁ (k + 1) ω) j) μ :=
      (memLp_apply ((matCLM D).comp_memLp' hM₁L) j).integrable one_le_two
    have e : (fun ω => Mt (k + 1) ω j) = (fun ω => M₂ (k + 1) ω j)
        + (β k / γ k) • fun ω => matCLM D (M₁ (k + 1) ω) j := by
      funext ω; simp [hMt]
    rw [e]
    filter_upwards [condExp_add i1 (i2.smul (β k / γ k)) (ℱ k),
      condExp_smul (β k / γ k) (fun ω => matCLM D (M₁ (k + 1) ω) j) (ℱ k), hmart₂ k j, h2]
      with ω h1 h3 h4 h5
    rw [h1, Pi.add_apply, h3, Pi.smul_apply, h4, h5]
    simp
  -- the drifts are of linear size
  have hf₁b : ∀ k ω, ‖f₁ k ω‖ ≤ K * (‖x k ω‖ + ‖z k ω‖) := fun k ω => hF₁g _ _
  have hf₂b : ∀ k ω, ‖f₂ k ω‖ ≤ K * (‖x k ω‖ + ‖z k ω‖) := fun k ω => hF₂g _ _
  have hDf₁b : ∀ k ω, ‖matCLM D (f₁ k ω)‖ ≤ nD * K * (‖x k ω‖ + ‖z k ω‖) := fun k ω => by
    have := ((matCLM D).le_opNorm (f₁ k ω)).trans (mul_le_mul_of_nonneg_left (hf₁b k ω) hnD)
    linarith [show nD * (K * (‖x k ω‖ + ‖z k ω‖)) = nD * K * (‖x k ω‖ + ‖z k ω‖) by ring]
  -- each iterate is bounded
  have hbd : ∀ k, ∃ C, 0 ≤ C ∧ ∀ ω, ‖x k ω‖ ≤ C ∧ ‖z k ω‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      obtain ⟨Cx, hCx⟩ := hx0
      obtain ⟨Cy, hCy⟩ := hy0
      refine ⟨max (max Cx 0) (max Cy 0 + nD * max Cx 0), by positivity, fun ω => ⟨?_, ?_⟩⟩
      · exact (hCx ω).trans ((le_max_left _ _).trans (le_max_left _ _))
      · refine ((norm_add_le _ _).trans (add_le_add ((hCy ω).trans (le_max_left _ _)) ?_)).trans
          (le_max_right _ _)
        exact ((matCLM D).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((hCx ω).trans (le_max_left _ _)) hnD)
    | succ k ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      have hb := hβ.pos k
      have hg := hγ.pos k
      refine ⟨C + (β k + γ k + β k * nD) * (2 * K * C) + β k * CM₀ + γ k * CMt, by positivity,
        fun ω => ⟨?_, ?_⟩⟩
      · rw [hxstep k ω]
        have t1 : ‖u k ω‖ ≤ C + β k * (2 * K * C) := by
          simp only [hu]
          refine (norm_add_le _ _).trans (add_le_add (hC ω).1 ?_)
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
          refine mul_le_mul_of_nonneg_left ((hf₁b k ω).trans ?_) hb.le
          nlinarith [(hC ω).1, (hC ω).2, norm_nonneg (x k ω), norm_nonneg (z k ω)]
        have t2 : ‖β k • M₁ (k + 1) ω‖ ≤ β k * CM₀ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
          exact mul_le_mul_of_nonneg_left (hM₁b' k ω) hb.le
        have : 0 ≤ (γ k + β k * nD) * (2 * K * C) + γ k * CMt := by positivity
        have e : C + (β k + γ k + β k * nD) * (2 * K * C) + β k * CM₀ + γ k * CMt =
            (C + β k * (2 * K * C)) + β k * CM₀ + ((γ k + β k * nD) * (2 * K * C) + γ k * CMt) := by
          ring
        rw [e]
        linarith [norm_add_le (u k ω) (β k • M₁ (k + 1) ω)]
      · rw [hzstep k ω]
        have hxz : ‖x k ω‖ + ‖z k ω‖ ≤ 2 * C := by linarith [(hC ω).1, (hC ω).2]
        have t1 : ‖v k ω‖ ≤ C + γ k * (2 * K * C) + β k * nD * (2 * K * C) := by
          simp only [hv]
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (hC ω).2 ?_)) ?_)
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hg]
            refine mul_le_mul_of_nonneg_left ((hf₂b k ω).trans ?_) hg.le
            nlinarith
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
            have := (hDf₁b k ω).trans (mul_le_mul_of_nonneg_left hxz (by positivity))
            calc β k * ‖matCLM D (f₁ k ω)‖ ≤ β k * (nD * K * (2 * C)) :=
                  mul_le_mul_of_nonneg_left this hb.le
              _ = β k * nD * (2 * K * C) := by ring
        have t2 : ‖γ k • Mt (k + 1) ω‖ ≤ γ k * CMt := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hg]
          exact mul_le_mul_of_nonneg_left (hMtb k ω) hg.le
        have : 0 ≤ β k * (2 * K * C) + β k * CM₀ := by positivity
        have e : C + (β k + γ k + β k * nD) * (2 * K * C) + β k * CM₀ + γ k * CMt =
            (C + γ k * (2 * K * C) + β k * nD * (2 * K * C)) + γ k * CMt
              + (β k * (2 * K * C) + β k * CM₀) := by ring
        rw [e]
        linarith [norm_add_le (v k ω) (γ k • Mt (k + 1) ω)]
  have hubd : ∀ k, ∃ C, ∀ ω, ‖u k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd k
    refine ⟨C + β k * (K * (2 * C)), fun ω => ?_⟩
    simp only [hu]
    refine (norm_add_le _ _).trans (add_le_add (hC ω).1 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hβ.pos k)]
    refine mul_le_mul_of_nonneg_left ((hf₁b k ω).trans ?_) (hβ.pos k).le
    exact mul_le_mul_of_nonneg_left (by linarith [(hC ω).1, (hC ω).2]) hK
  have hvbd : ∀ k, ∃ C, ∀ ω, ‖v k ω‖ ≤ C := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd k
    refine ⟨C + γ k * (K * (2 * C)) + β k * (nD * K * (2 * C)), fun ω => ?_⟩
    have hxz : ‖x k ω‖ + ‖z k ω‖ ≤ 2 * C := by linarith [(hC ω).1, (hC ω).2]
    simp only [hv]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (hC ω).2 ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hγ.pos k)]
      exact mul_le_mul_of_nonneg_left ((hf₂b k ω).trans (mul_le_mul_of_nonneg_left hxz hK))
        (hγ.pos k).le
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hβ.pos k)]
      exact mul_le_mul_of_nonneg_left ((hDf₁b k ω).trans (mul_le_mul_of_nonneg_left hxz
        (by positivity))) (hβ.pos k).le
  -- the pointwise drift bounds
  set c₁ := K ^ 2 / η + 2 * K ^ 2 * Bβ with hc₁
  set c₂ := 4 * K ^ 2 + 4 * (nD * K) ^ 2 / η with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hu2 : ∀ k ω, ‖u k ω‖ ^ 2 ≤ (1 - η * β k + 2 * K ^ 2 * β k ^ 2) * ‖x k ω‖ ^ 2
      + c₁ * β k * ‖z k ω‖ ^ 2 := fun k ω => by
    have hb := hβ.pos k
    have h := slow_step_bound (x := x k ω) (f := f₁ k ω) (zn := ‖z k ω‖) hη hb.le (norm_nonneg _)
      (hF₁in _ _) (hf₁b k ω) hK
    have t : (K ^ 2 / η + 2 * K ^ 2 * β k) * β k * ‖z k ω‖ ^ 2 ≤ c₁ * β k * ‖z k ω‖ ^ 2 := by
      have : K ^ 2 / η + 2 * K ^ 2 * β k ≤ c₁ := by
        simp only [hc₁]; nlinarith [hβB k, sq_nonneg K]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hb.le) (sq_nonneg _)
    simp only [hu]; linarith
  have hηγ : ∀ᶠ k in atTop, η * γ k ≤ 1 := by
    have h := hγ.tendsto_zero.const_mul η
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have hv2 : ∀ k, η * γ k ≤ 1 → ∀ ω, ‖v k ω‖ ^ 2 ≤
      (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2 := fun k hk ω => by
    have h := fast_step_bound (z := z k ω) (f₂ := f₂ k ω) (w := matCLM D (f₁ k ω))
      (xn := ‖x k ω‖) (K := K) (K' := nD * K) (β := β k) hη (hγ.pos k) hk (hβ.pos k).le
      (norm_nonneg _) hK (by positivity) (hF₂in _ _) (by simpa [add_comm] using hf₂b k ω)
      (by simpa [add_comm] using hDf₁b k ω)
    simpa only [hv, hc₂] using h
  -- the moment engine
  have hq : ∀ k, 0 ≤ 1 - η * β k + (2 * K ^ 2 + η ^ 2 / 4) * β k ^ 2 := fun k => by
    nlinarith [sq_nonneg (1 - η * β k / 2), sq_nonneg (K * β k)]
  have hu2' : ∀ k ω, ‖u k ω‖ ^ 2 ≤ (1 - η * β k + (2 * K ^ 2 + η ^ 2 / 4) * β k ^ 2)
      * ‖x k ω‖ ^ 2 + c₁ * β k * ‖z k ω‖ ^ 2 + 0 * β k ^ 2 := fun k ω => by
    have := hu2 k ω
    nlinarith [sq_nonneg (η * β k * ‖x k ω‖)]
  have hv2' : ∀ᶠ k in atTop, ∀ ω, ‖v k ω‖ ^ 2 ≤
      (1 - η * γ k + c₂ * (γ k ^ 2 + β k ^ 2 / γ k)) * ‖z k ω‖ ^ 2
        + c₂ * (γ k ^ 2 + β k ^ 2 / γ k) * ‖x k ω‖ ^ 2 + 0 * γ k ^ 2 := by
    filter_upwards [hηγ] with k hk ω
    simpa using hv2 k hk ω
  obtain ⟨W, hW⟩ := tts_moments_of_steps (μ := μ) (κ := 2 * K ^ 2 + η ^ 2 / 4) (G := 0)
    hβ.pos hγ.pos hβ.tendsto_zero hγ.tendsto_zero hβγ hc₀ hc₀η hratio hc₁0 hc₂0 le_rfl hq ℱ
    hxm hzm hum hvm hbd hubd hvbd hM₁ hM₁b' hmart₁ hMtm hMtb hMtmart hxstep hzstep hu2' hv2'
  set A : ℕ → ℝ := fun k => ∫ ω, ‖x k ω‖ ^ 4 ∂μ with hA
  set B : ℕ → ℝ := fun k => ∫ ω, ‖z k ω‖ ^ 4 ∂μ with hB
  have hbI : ∀ (k : ℕ) (g : Ω → ℝ), AEStronglyMeasurable g μ → (∃ C, ∀ ω, |g ω| ≤ C) →
      Integrable g μ := fun _ g hg ⟨C, hC⟩ => (memLp_top_of_bound hg C
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top
  have hxa : ∀ k, AEStronglyMeasurable (x k) μ := fun k =>
    ((hxm k).mono (ℱ.le k)).aestronglyMeasurable
  have hza : ∀ k, AEStronglyMeasurable (z k) μ := fun k =>
    ((hzm k).mono (ℱ.le k)).aestronglyMeasurable
  have ix4 : ∀ k, Integrable (fun ω => ‖x k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd k
    exact hbI k _ ((hxa k).norm.pow 4) ⟨C ^ 4, fun ω => by
      rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (norm_nonneg _) (hC ω).1 4⟩
  have iz4 : ∀ k, Integrable (fun ω => ‖z k ω‖ ^ 4) μ := fun k => by
    obtain ⟨C, hC0, hC⟩ := hbd k
    exact hbI k _ ((hza k).norm.pow 4) ⟨C ^ 4, fun ω => by
      rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (norm_nonneg _) (hC ω).2 4⟩
  -- back to `y = z - D x`
  refine ⟨fun k => ?_, (8 + 8 * nD ^ 4) * max W 0, fun k => ⟨?_, ?_⟩⟩
  · obtain ⟨C, hC0, hC⟩ := hbd k
    refine ⟨C + nD * C, fun ω => ⟨(hC ω).1.trans (by nlinarith), ?_⟩⟩
    have e : y k ω = z k ω - matCLM D (x k ω) := by simp only [hz]; abel
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (hC ω).2 (((matCLM D).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hC ω).1 hnD)))
  · have h := (hW k).1
    have hW' : W * γ k ^ 2 ≤ max W 0 * γ k ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have : max W 0 * γ k ^ 2 ≤ (8 + 8 * nD ^ 4) * max W 0 * γ k ^ 2 := by
      have := mul_nonneg (le_max_right W 0) (sq_nonneg (γ k))
      nlinarith [pow_nonneg hnD 4]
    show A k ≤ _
    linarith
  · have hpt : ∀ ω, ‖y k ω‖ ^ 4 ≤ 8 * ‖z k ω‖ ^ 4 + 8 * nD ^ 4 * ‖x k ω‖ ^ 4 := fun ω => by
      have e : y k ω = z k ω - matCLM D (x k ω) := by simp only [hz]; abel
      have h1 : ‖y k ω‖ ≤ ‖z k ω‖ + nD * ‖x k ω‖ := by
        rw [e]; exact (norm_sub_le _ _).trans (add_le_add_left ((matCLM D).le_opNorm _) _)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      have p := norm_nonneg (z k ω)
      have q : 0 ≤ nD * ‖x k ω‖ := mul_nonneg hnD (norm_nonneg _)
      have h3 : (‖z k ω‖ + nD * ‖x k ω‖) ^ 4 ≤ 8 * ‖z k ω‖ ^ 4 + 8 * (nD * ‖x k ω‖) ^ 4 := by
        nlinarith [sq_nonneg (‖z k ω‖ - nD * ‖x k ω‖), sq_nonneg (‖z k ω‖ ^ 2 - (nD * ‖x k ω‖) ^ 2),
          mul_nonneg p q, sq_nonneg (‖z k ω‖ + nD * ‖x k ω‖)]
      have e2 : (nD * ‖x k ω‖) ^ 4 = nD ^ 4 * ‖x k ω‖ ^ 4 := by ring
      linarith
    have iy4 : Integrable (fun ω => ‖y k ω‖ ^ 4) μ := by
      obtain ⟨C, hC0, hC⟩ := hbd k
      have hya : AEStronglyMeasurable (y k) μ := ((hym k).mono (ℱ.le k)).aestronglyMeasurable
      refine hbI k _ (hya.norm.pow 4) ⟨(C + nD * C) ^ 4, fun ω => ?_⟩
      rw [abs_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
      have e : y k ω = z k ω - matCLM D (x k ω) := by simp only [hz]; abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add (hC ω).2 (((matCLM D).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hC ω).1 hnD)))
    have hint : ∫ ω, ‖y k ω‖ ^ 4 ∂μ ≤ 8 * B k + 8 * nD ^ 4 * A k := by
      calc ∫ ω, ‖y k ω‖ ^ 4 ∂μ ≤ ∫ ω, (8 * ‖z k ω‖ ^ 4 + 8 * nD ^ 4 * ‖x k ω‖ ^ 4) ∂μ :=
            integral_mono iy4 (((iz4 k).const_mul _).add ((ix4 k).const_mul _)) hpt
        _ = _ := by rw [integral_add ((iz4 k).const_mul _) ((ix4 k).const_mul _),
            integral_const_mul, integral_const_mul]
    have h1 := (hW k).1
    have h2 := (hW k).2
    have hW' : W ≤ max W 0 := le_max_left _ _
    have t1 := mul_le_mul_of_nonneg_right hW' (sq_nonneg (γ k))
    have t2 := mul_le_mul_of_nonneg_left (h1.trans t1) (by positivity : (0 : ℝ) ≤ 8 * nD ^ 4)
    have t3 := mul_le_mul_of_nonneg_left (h2.trans t1) (by norm_num : (0 : ℝ) ≤ 8)
    have e : (8 + 8 * nD ^ 4) * max W 0 * γ k ^ 2 =
        8 * (max W 0 * γ k ^ 2) + 8 * nD ^ 4 * (max W 0 * γ k ^ 2) := by ring
    linarith

set_option maxHeartbeats 8000000 in
/-- **Assumption 2.2 for two time scales, from dissipativity.** The two-time-scale iteration
`x_{k+1} = x_k + β_k (F₁(x_k, y_k) + M₁_{k+1})`, `y_{k+1} = y_k + γ_k (F₂(x_k, y_k) + M₂_{k+1})` with
* dissipative drifts in the coordinates `x` and `z = y + D x` (`moment_bounds_tts`),
* drifts linear to first order, `F(x, y) = -A(x, y) + O(‖x‖² + ‖y‖²)`, with `A₂₂ D = A₂₁`,
* bounded martingale noise whose covariances are within `δ_k + C(R + R²)` of `Γ`,
* `β/γ → 0`, `γ²/β → 0` and `γ_k / γ_{k+1} ≤ 1 + c₀ β_k` with `c₀ < η`,

has the asymptotic covariances of its linearization. -/
theorem tendsto_tts_dissipative {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (hγβ : Tendsto (fun k => γ k ^ 2 / β k) atTop (𝓝 0)) {η c₀ K L CM : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₀η : c₀ < η) (hratio : ∀ᶠ k in atTop, γ k / γ (k + 1) ≤ 1 + c₀ * β k)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (A₁₁ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₁ : Matrix (Fin d₂) (Fin d₁) ℝ) (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ)
    (D : Matrix (Fin d₂) (Fin d₁) ℝ) (hD : A₂₂ * D = A₂₁) {η' : ℝ} (hη' : 0 < η')
    (hΔ : ∀ x, η' * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A₁₁ - A₁₂ * D - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η' * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {x M₁ : ℕ → Ω → E d₁} {y M₂ : ℕ → Ω → E d₂}
    {F₁ : E d₁ → E d₂ → E d₁} {F₂ : E d₁ → E d₂ → E d₂}
    (hF₁in : ∀ u w, ⟪u, F₁ u w⟫_ℝ ≤ -η * ‖u‖ ^ 2 + K * ‖u‖ * ‖w + matCLM D u‖)
    (hF₁g : ∀ u w, ‖F₁ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₂in : ∀ u w, ⟪w + matCLM D u, F₂ u w⟫_ℝ ≤ -η * ‖w + matCLM D u‖ ^ 2)
    (hF₂g : ∀ u w, ‖F₂ u w‖ ≤ K * (‖u‖ + ‖w + matCLM D u‖))
    (hF₁ : ∀ u w, ‖F₁ u w + (matCLM A₁₁ u + matCLM A₁₂ w)‖ ≤ L * (‖u‖ ^ 2 + ‖w‖ ^ 2))
    (hF₂ : ∀ u w, ‖F₂ u w + (matCLM A₂₁ u + matCLM A₂₂ w)‖ ≤ L * (‖u‖ ^ 2 + ‖w‖ ^ 2))
    (hF₁c : Continuous fun p : E d₁ × E d₂ => F₁ p.1 p.2)
    (hF₂c : Continuous fun p : E d₁ × E d₂ => F₂ p.1 p.2)
    (hx : ∀ k ω, x (k + 1) ω = x k ω + β k • (F₁ (x k ω) (y k ω) + M₁ (k + 1) ω))
    (hy : ∀ k ω, y (k + 1) ω = y k ω + γ k • (F₂ (x k ω) (y k ω) + M₂ (k + 1) ω))
    (hxm : ∀ k, StronglyMeasurable[ℱ k] (x k)) (hym : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hx0 : ∃ C, ∀ ω, ‖x 0 ω‖ ≤ C) (hy0 : ∃ C, ∀ ω, ‖y 0 ω‖ ≤ C)
    (hM₁ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₁ (k + 1))) (hM₁b : ∀ k ω, ‖M₁ (k + 1) ω‖ ≤ CM)
    (hmart₁ : ∀ k j, μ[fun ω => M₁ (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    (hM₂ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M₂ (k + 1))) (hM₂b : ∀ k ω, ‖M₂ (k + 1) ω‖ ≤ CM)
    (hmart₂ : ∀ k j, μ[fun ω => M₂ (k + 1) ω j | ℱ k] =ᵐ[μ] 0)
    {C : ℝ} (hC : 0 ≤ C) {Γ₁₁ : Mat d₁} {Γ₁₂ : Rect d₁ d₂} {Γ₂₂ : Mat d₂} {δ₁ δ₂ δ₃ : ℕ → ℝ}
    (hδ₁0 : ∀ k, 0 ≤ δ₁ k) (hδ₂0 : ∀ k, 0 ≤ δ₂ k) (hδ₃0 : ∀ k, 0 ≤ δ₃ k)
    (hδ₁ : Tendsto δ₁ atTop (𝓝 0)) (hδ₂ : Tendsto δ₂ atTop (𝓝 0)) (hδ₃ : Tendsto δ₃ atTop (𝓝 0))
    (dev₁ : ∀ k, ‖secondMoment μ (M₁ (k + 1)) - Γ₁₁‖ ≤
      δ₁ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₂ : ∀ k, ‖crossMoment μ (M₁ (k + 1)) (M₂ (k + 1)) - Γ₁₂‖ ≤
      δ₂ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2))
    (dev₃ : ∀ k, ‖secondMoment μ (M₂ (k + 1)) - Γ₂₂‖ ≤
      δ₃ k + C * ((rms μ (x k) + rms μ (y k)) + (rms μ (x k) + rms μ (y k)) ^ 2)) :
    ∃ a c b, lyapOp A₂₂ b = Γ₂₂ ∧ rmul A₂₂ c + lmul A₁₂ b = Γ₁₂ ∧
      lyapOp (A₁₁ - A₁₂ * D - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁₁ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • crossMoment μ (x k) (fun ω => y k ω + matCLM D (x k ω)))
        atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • secondMoment μ (fun ω => y k ω + matCLM D (x k ω))) atTop
        (𝓝 b) := by
  obtain ⟨hbd, W, hW⟩ := moment_bounds_tts (μ := μ) hβ hγ hβγ hc₀ hc₀η hratio hK ℱ D hF₁in hF₁g
    hF₂in hF₂g hF₁c hF₂c hx hy hxm hym hx0 hy0 hM₁ hM₁b hmart₁ hM₂ hM₂b hmart₂
  set CM₀ := max CM 0
  have hCM₀ : 0 ≤ CM₀ := le_max_right _ _
  set C' := max C CM₀
  have hC' : 0 ≤ C' := le_trans hC (le_max_left _ _)
  have hxL : ∀ k, MemLp (x k) 2 μ := fun k => by
    obtain ⟨B, hB⟩ := hbd k
    exact MemLp.of_bound ((hxm k).mono (ℱ.le k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => (hB ω).1)
  have hyL : ∀ k, MemLp (y k) 2 μ := fun k => by
    obtain ⟨B, hB⟩ := hbd k
    exact MemLp.of_bound ((hym k).mono (ℱ.le k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => (hB ω).2)
  have hM₁L : ∀ k, MemLp (M₁ (k + 1)) 2 μ := fun k =>
    MemLp.of_bound ((hM₁ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM
      (Eventually.of_forall (hM₁b k))
  have hM₂L : ∀ k, MemLp (M₂ (k + 1)) 2 μ := fun k =>
    MemLp.of_bound ((hM₂ k).mono (ℱ.le (k + 1))).aestronglyMeasurable CM
      (Eventually.of_forall (hM₂b k))
  have hR0 : ∀ k, 0 ≤ rms μ (x k) + rms μ (y k) := fun k => add_nonneg (rms_nonneg _) (rms_nonneg _)
  have rM : ∀ {n : ℕ} (M : Ω → E n), (∀ ω, ‖M ω‖ ≤ CM) → ∀ k,
      rms μ M ≤ C' * (1 + (rms μ (x k) + rms μ (y k))) := by
    intro n M hb k
    have h1 : rms μ M ≤ CM₀ := by
      unfold rms
      refine Real.sqrt_le_iff.mpr ⟨hCM₀, ?_⟩
      calc ∫ ω, ‖M ω‖ ^ 2 ∂μ ≤ ∫ _ω, CM₀ ^ 2 ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
              (integrable_const _) (Eventually.of_forall fun ω =>
                pow_le_pow_left₀ (norm_nonneg _) ((hb ω).trans (le_max_left _ _)) 2)
        _ = CM₀ ^ 2 := by simp
    have h2 : CM₀ ≤ C' := le_max_right _ _
    have := hR0 k
    nlinarith
  have rzero : ∀ {n : ℕ}, rms μ (fun _ : Ω => (0 : E n)) = 0 := by
    intro n; simp [rms]
  have hup : ∀ t : ℝ, 0 ≤ t → C * t ≤ C' * t := fun t ht =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) ht
  refine tendsto_tts_taylor hβ hγ hβγ hγβ A₁₁ A₁₂ A₂₁ A₂₂ D hD hη' hΔ hA₂₂ ℱ
    (h := fun _ _ => 0) (g := fun _ _ => 0) (r₁ := fun _ _ => 0) (r₂ := fun _ _ => 0)
    (Cr := 0) (C₄ := W) hL hF₁ hF₂ hF₁c hF₂c
    (fun k ω => by rw [hx k ω]; simp) (fun k ω => by rw [hy k ω]; simp)
    hxm hym (hxL 0) (hyL 0)
    (fun _ => stronglyMeasurable_const) (fun _ => memLp_const _)
    (fun _ => stronglyMeasurable_const) (fun _ => memLp_const _)
    hM₁ hM₁L hM₂ hM₂L (fun _ => stronglyMeasurable_const) (fun _ _ => by simp)
    (fun _ => stronglyMeasurable_const) (fun _ _ => by simp) ?_ ?_
    (fun k => (hW k).1) (fun k => (hW k).2) hmart₁ hmart₂ hC'
    (fun k => by rw [rzero]; exact hC') (fun k => by rw [rzero]; exact hC')
    (fun k => rM _ (hM₁b k) k) (fun k => rM _ (hM₂b k) k)
    hδ₁0 hδ₂0 hδ₃0 hδ₁ hδ₂ hδ₃
    (fun k => (dev₁ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₂ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
    (fun k => (dev₃ k).trans (add_le_add_left (hup _ (by nlinarith [hR0 k])) _))
  · intro k
    obtain ⟨B, hB⟩ := hbd k
    refine (memLp_top_of_bound (((hxm k).mono (ℱ.le k)).aestronglyMeasurable.norm.pow 4) (B ^ 4)
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    show ‖‖x k ω‖ ^ 4‖ ≤ B ^ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB ω).1 4
  · intro k
    obtain ⟨B, hB⟩ := hbd k
    refine (memLp_top_of_bound (((hym k).mono (ℱ.le k)).aestronglyMeasurable.norm.pow 4) (B ^ 4)
      (Eventually.of_forall fun ω => ?_)).integrable le_top
    show ‖‖y k ω‖ ^ 4‖ ≤ B ^ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB ω).2 4

end Main

end StochasticApproximation
