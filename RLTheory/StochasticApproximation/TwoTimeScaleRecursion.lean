/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.CovarianceRecursion

/-!
# Coupled second-moment recursions on two time scales

The deterministic part of the two-time-scale covariance theorem
(`docs/two-time-scale-covariance.md`):

* `Rect m n`: `m × n` matrices with the Frobenius inner product, and the maps
  `lmul A : X ↦ A X`, `rmul B : X ↦ X Bᵀ`, `transCLM : X ↦ Xᵀ` between them.
* `rmul_coercive`: `X ↦ X Aᵀ` is coercive when `A` is positive definite.
* `tendsto_zero_of_coupled_recursion`: Lemma 3.3 for the errors, three coupled recursions
  driven by coercive maps, two of them on the fast time scale.
-/

open Filter Topology Finset Real Matrix
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

/-! ### Rectangular matrices -/

/-- `m × n` matrices with the Frobenius inner product. -/
abbrev Rect (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

variable {m n p : ℕ}

/-- Left multiplication `X ↦ A X`. -/
noncomputable def lmul (A : Matrix (Fin m) (Fin n) ℝ) : Rect n p →L[ℝ] Rect m p :=
  LinearMap.toContinuousLinearMap
  { toFun := fun X => fun ij => ∑ k, A ij.1 k * X (k, ij.2)
    map_add' := by
      intro X Y
      funext ij
      simp [mul_add, sum_add_distrib]
    map_smul' := by
      intro c X
      funext ij
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring }

/-- Right multiplication by a transpose, `X ↦ X Bᵀ`. -/
noncomputable def rmul (B : Matrix (Fin p) (Fin n) ℝ) : Rect m n →L[ℝ] Rect m p :=
  LinearMap.toContinuousLinearMap
  { toFun := fun X => fun ij => ∑ k, X (ij.1, k) * B ij.2 k
    map_add' := by
      intro X Y
      funext ij
      simp [add_mul, sum_add_distrib]
    map_smul' := by
      intro c X
      funext ij
      simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring }

/-- The transpose `X ↦ Xᵀ`. -/
noncomputable def transCLM : Rect m n →L[ℝ] Rect n m :=
  LinearMap.toContinuousLinearMap
  { toFun := fun X => fun ij => X (ij.2, ij.1)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

lemma lmul_apply (A : Matrix (Fin m) (Fin n) ℝ) (X : Rect n p) (ij : Fin m × Fin p) :
    lmul A X ij = ∑ k, A ij.1 k * X (k, ij.2) := rfl

lemma rmul_apply (B : Matrix (Fin p) (Fin n) ℝ) (X : Rect m n) (ij : Fin m × Fin p) :
    rmul B X ij = ∑ k, X (ij.1, k) * B ij.2 k := rfl

lemma transCLM_apply (X : Rect m n) (ij : Fin n × Fin m) : transCLM X ij = X (ij.2, ij.1) := rfl

/-- `lyapOp A = lmul A + rmul A`. -/
lemma lyapOp_eq (A : Matrix (Fin n) (Fin n) ℝ) (X : Mat n) :
    lyapOp A X = lmul A X + rmul A X := rfl

/-- If `x ⬝ A x ≥ η |x|²` for all `x`, then `X ↦ X Aᵀ` is coercive with constant `η`. -/
theorem rmul_coercive (A : Matrix (Fin n) (Fin n) ℝ) {η : ℝ}
    (hA : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (X : Rect m n) :
    η * ‖X‖ ^ 2 ≤ ⟪rmul A X, X⟫ := by
  simp only [rmul, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.inner_apply, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, RCLike.inner_apply,
    conj_trivial, Real.norm_eq_abs, sq_abs]
  have hr := sum_le_sum fun i (_ : i ∈ univ) => hA (fun j => X (i, j))
  simp only [dotProduct, mulVec] at hr
  have e1 : ∑ x, ∑ y, X (x, y) * ∑ k, X (x, k) * A y k =
      ∑ i, ∑ j, X (i, j) * ∑ k, A j k * X (i, k) :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
      congr 1; exact sum_congr rfl fun k _ => by ring
  have e2 : η * ∑ x, ∑ y, X (x, y) ^ 2 = ∑ i, η * ∑ j, X (i, j) * X (i, j) := by
    simp only [sq, ← mul_sum]
  rw [e1, e2]
  exact hr

/-! ### Coupled recursions -/

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [NormedAddCommGroup V₃]
  [InnerProductSpace ℝ V₃]

/-- Eventually a coercive step contracts. -/
lemma eventually_contracts {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V →L[ℝ] V) {η : ℝ} (hη : 0 < η) (hL : ∀ v, η * ‖v‖ ^ 2 ≤ ⟪L v, v⟫) {β : ℕ → ℝ}
    (hβ : ∀ k, 0 ≤ β k) (hβ0 : Tendsto β atTop (𝓝 0)) :
    ∀ᶠ k in atTop, η / 2 * β k ≤ 1 ∧ ∀ v, ‖v - β k • L v‖ ≤ (1 - η / 2 * β k) * ‖v‖ := by
  have hpos : (0 : ℝ) < min (η / (‖L‖ ^ 2 + 1)) (2 / η) := by positivity
  refine (hβ0.eventually (gt_mem_nhds hpos)).mono fun k hk => ?_
  have hk1 := hk.trans_le (min_le_left _ _)
  have hk2 := hk.trans_le (min_le_right _ _)
  have h1 : β k * ‖L‖ ^ 2 ≤ η := by
    have : β k * (‖L‖ ^ 2 + 1) ≤ η := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖L‖ ^ 2 + 1)).mp hk1
      linarith
    nlinarith [hβ k]
  have h2 : η / 2 * β k ≤ 1 := by
    have := (lt_div_iff₀ hη).mp hk2
    linarith
  exact ⟨h2, norm_sub_smul_le L hL (hβ k) h1 h2⟩

/-- Lemma 3.3 of the write-up, for the errors `e = (a - a*, c - c*, b - b*)`: three coupled
recursions, the last two on the fast time scale `γ`, with perturbations
`‖δ‖ ≤ ε (S + ‖eᵃ‖ + ‖eᶜ‖ + ‖eᵇ‖)` and `ε → 0`, converge to zero. -/
theorem tendsto_zero_of_coupled_recursion (L₁ : V₁ →L[ℝ] V₁) (L₂ : V₂ →L[ℝ] V₂)
    (L₃ : V₃ →L[ℝ] V₃) (K₁₂ : V₂ →L[ℝ] V₁) (K₂₃ : V₃ →L[ℝ] V₂) {η : ℝ} (hη : 0 < η)
    (hL₁ : ∀ v, η * ‖v‖ ^ 2 ≤ ⟪L₁ v, v⟫) (hL₂ : ∀ v, η * ‖v‖ ^ 2 ≤ ⟪L₂ v, v⟫)
    (hL₃ : ∀ v, η * ‖v‖ ^ 2 ≤ ⟪L₃ v, v⟫)
    {β γ ε : ℕ → ℝ} (hβ : ∀ k, 0 ≤ β k) (hγ : ∀ k, 0 ≤ γ k)
    (hβ0 : Tendsto β atTop (𝓝 0)) (hγ0 : Tendsto γ atTop (𝓝 0))
    (hβsum : Tendsto (fun n => ∑ k ∈ range n, β k) atTop atTop)
    (hγsum : Tendsto (fun n => ∑ k ∈ range n, γ k) atTop atTop)
    (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ k, 0 ≤ ε k) {S : ℝ} (hS : 0 ≤ S)
    {ea δ₁ : ℕ → V₁} {ec δ₂ : ℕ → V₂} {eb δ₃ : ℕ → V₃}
    (hδ₁ : ∀ k, ‖δ₁ k‖ ≤ ε k * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖))
    (hδ₂ : ∀ k, ‖δ₂ k‖ ≤ ε k * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖))
    (hδ₃ : ∀ k, ‖δ₃ k‖ ≤ ε k * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖))
    (hrec₁ : ∀ k, ea (k + 1) = ea k - β k • L₁ (ea k) + β k • (δ₁ k - K₁₂ (ec k)))
    (hrec₂ : ∀ k, ec (k + 1) = ec k - γ k • L₂ (ec k) + γ k • (δ₂ k - K₂₃ (eb k)))
    (hrec₃ : ∀ k, eb (k + 1) = eb k - γ k • L₃ (eb k) + γ k • δ₃ k) :
    Tendsto ea atTop (𝓝 0) ∧ Tendsto ec atTop (𝓝 0) ∧ Tendsto eb atTop (𝓝 0) := by
  -- the constants of the invariant region
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = η / 2 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨Kb, hKb⟩ : ∃ K, K = 1 / κ := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ K, K = (‖K₂₃‖ * Kb + 1) / κ := ⟨_, rfl⟩
  obtain ⟨Ka, hKa⟩ : ∃ K, K = (‖K₁₂‖ * Kc + 1) / κ := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hKa0 : 0 ≤ Ka := by rw [hKa]; positivity
  have hκKb : κ * Kb = 1 := by rw [hKb]; field_simp
  have hκKc : κ * Kc = ‖K₂₃‖ * Kb + 1 := by rw [hKc]; field_simp
  have hκKa : κ * Ka = ‖K₁₂‖ * Kc + 1 := by rw [hKa]; field_simp
  obtain ⟨s, hs⟩ : ∃ s, s = S + Ka + Kc + Kb := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  -- from some time on the steps contract and `ε s ≤ 1`
  have hev := ((eventually_contracts L₁ hη hL₁ hβ hβ0).and
    ((eventually_contracts L₂ hη hL₂ hγ hγ0).and (eventually_contracts L₃ hη hL₃ hγ hγ0))).and
    (hε.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (s + 1))))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
  have hKa1 : 0 < Ka := by rw [hKa]; positivity
  have hKc1 : 0 < Kc := by rw [hKc]; positivity
  have hKb1 : 0 < Kb := by rw [hKb]; positivity
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = max 1 (max (‖ea k₀‖ / Ka) (max (‖ec k₀‖ / Kc) (‖eb k₀‖ / Kb))) :=
    ⟨_, rfl⟩
  have hlam1 : 1 ≤ lam := hlam ▸ le_max_left _ _
  have hlam0 : 0 ≤ lam := zero_le_one.trans hlam1
  have hεs : ∀ k ≥ k₀, ε k * s ≤ 1 := by
    intro k hk
    have h := (hk₀ k hk).2
    have : ε k * (s + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at h
    nlinarith [hε0 k]
  -- the invariant region
  have hinv : ∀ k ≥ k₀, ‖ea k‖ ≤ lam * Ka ∧ ‖ec k‖ ≤ lam * Kc ∧ ‖eb k‖ ≤ lam * Kb := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      refine ⟨?_, ?_, ?_⟩
      · have : ‖ea k₀‖ / Ka ≤ lam := hlam ▸ (le_max_left _ _).trans (le_max_right _ _)
        rwa [div_le_iff₀ hKa1] at this
      · have : ‖ec k₀‖ / Kc ≤ lam := hlam ▸ ((le_max_left _ _).trans (le_max_right _ _)).trans
          (le_max_right _ _)
        rwa [div_le_iff₀ hKc1] at this
      · have : ‖eb k₀‖ / Kb ≤ lam := hlam ▸ ((le_max_right _ _).trans (le_max_right _ _)).trans
          (le_max_right _ _)
        rwa [div_le_iff₀ hKb1] at this
    | succ k hk ih =>
      obtain ⟨ha, hc, hb⟩ := ih
      obtain ⟨⟨⟨hβ1, hc₁⟩, ⟨hγ1, hc₂⟩, ⟨_, hc₃⟩⟩, _⟩ := hk₀ k hk
      rw [← hκ] at hβ1 hγ1 hc₁ hc₂ hc₃
      have hn : S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖ ≤ lam * s := by
        have : S ≤ lam * S := le_mul_of_one_le_left hS hlam1
        rw [hs]; nlinarith
      have hδ : ∀ x, x ≤ ε k * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖) → x ≤ lam := by
        intro x hx
        have := mul_le_mul_of_nonneg_left hn (hε0 k)
        have h2 := hεs k hk
        nlinarith
      have d₁ := hδ _ (hδ₁ k)
      have d₂ := hδ _ (hδ₂ k)
      have d₃ := hδ _ (hδ₃ k)
      have hb0 := hβ k
      have hg0 := hγ k
      refine ⟨?_, ?_, ?_⟩
      · rw [hrec₁ k]
        have t1 := norm_add_le (ea k - β k • L₁ (ea k)) (β k • (δ₁ k - K₁₂ (ec k)))
        have t2 : ‖β k • (δ₁ k - K₁₂ (ec k))‖ ≤ β k * (lam + ‖K₁₂‖ * (lam * Kc)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add d₁ ?_)) hb0
          exact (K₁₂.le_opNorm _).trans (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
        have t3 := (hc₁ (ea k)).trans (mul_le_mul_of_nonneg_left ha (by linarith))
        have e : (1 - κ * β k) * (lam * Ka) + β k * (lam + ‖K₁₂‖ * (lam * Kc)) = lam * Ka := by
          have : (1 - κ * β k) * (lam * Ka) + β k * (lam + ‖K₁₂‖ * (lam * Kc)) =
              lam * Ka - β k * lam * (κ * Ka - ‖K₁₂‖ * Kc - 1) := by ring
          rw [this, hκKa]; ring
        linarith
      · rw [hrec₂ k]
        have t1 := norm_add_le (ec k - γ k • L₂ (ec k)) (γ k • (δ₂ k - K₂₃ (eb k)))
        have t2 : ‖γ k • (δ₂ k - K₂₃ (eb k))‖ ≤ γ k * (lam + ‖K₂₃‖ * (lam * Kb)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hg0]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add d₂ ?_)) hg0
          exact (K₂₃.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        have t3 := (hc₂ (ec k)).trans (mul_le_mul_of_nonneg_left hc (by linarith))
        have e : (1 - κ * γ k) * (lam * Kc) + γ k * (lam + ‖K₂₃‖ * (lam * Kb)) = lam * Kc := by
          have : (1 - κ * γ k) * (lam * Kc) + γ k * (lam + ‖K₂₃‖ * (lam * Kb)) =
              lam * Kc - γ k * lam * (κ * Kc - ‖K₂₃‖ * Kb - 1) := by ring
          rw [this, hκKc]; ring
        linarith
      · rw [hrec₃ k]
        have t1 := norm_add_le (eb k - γ k • L₃ (eb k)) (γ k • δ₃ k)
        have t2 : ‖γ k • δ₃ k‖ ≤ γ k * lam := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hg0]
          exact mul_le_mul_of_nonneg_left d₃ hg0
        have t3 := (hc₃ (eb k)).trans (mul_le_mul_of_nonneg_left hb (by linarith))
        have e : (1 - κ * γ k) * (lam * Kb) + γ k * lam = lam * Kb := by
          have : (1 - κ * γ k) * (lam * Kb) + γ k * lam = lam * Kb - γ k * lam * (κ * Kb - 1) := by
            ring
          rw [this, hκKb]; ring
        linarith
  -- the perturbations vanish
  have hδ0 : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) →
      (∀ k, f k ≤ ε k * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖)) → Tendsto f atTop (𝓝 0) := by
    intro f hf0 hf
    refine squeeze_zero' (Eventually.of_forall hf0) ?_
      (by simpa using hε.mul_const (S + lam * Ka + lam * Kc + lam * Kb))
    filter_upwards [eventually_ge_atTop k₀] with k hk
    obtain ⟨ha, hc, hb⟩ := hinv k hk
    exact (hf k).trans (mul_le_mul_of_nonneg_left (by linarith) (hε0 k))
  have hd₁ := tendsto_zero_iff_norm_tendsto_zero.mpr (hδ0 _ (fun k => norm_nonneg _) hδ₁)
  have hd₂ := tendsto_zero_iff_norm_tendsto_zero.mpr (hδ0 _ (fun k => norm_nonneg _) hδ₂)
  have hd₃ := tendsto_zero_iff_norm_tendsto_zero.mpr (hδ0 _ (fun k => norm_nonneg _) hδ₃)
  have hb := tendsto_zero_of_coercive_recursion L₃ hη hL₃ hγ hγ0 hγsum hd₃ hrec₃
  have hc := tendsto_zero_of_coercive_recursion L₂ hη hL₂ hγ hγ0 hγsum
    (by simpa using hd₂.sub ((K₂₃.continuous.tendsto 0).comp hb)) hrec₂
  have ha := tendsto_zero_of_coercive_recursion L₁ hη hL₁ hβ hβ0 hβsum
    (by simpa using hd₁.sub ((K₁₂.continuous.tendsto 0).comp hc)) hrec₁
  exact ⟨ha, hc, hb⟩

/-! ### Normalization -/

/-- The coupling `c ↦ A₁₂ cᵀ + c A₁₂ᵀ` of the slow equation. -/
noncomputable def coupleCLM {d₁ d₂ : ℕ} (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Rect d₁ d₂ →L[ℝ] Mat d₁ :=
  (lmul A₁₂).comp transCLM + rmul A₁₂

lemma coupleCLM_apply {d₁ d₂ : ℕ} (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ) (Z : Rect d₁ d₂) :
    coupleCLM A₁₂ Z = lmul A₁₂ (transCLM Z) + rmul A₁₂ Z := rfl

/-- The normalized slow recursion (one step). -/
lemma slow_step_identity {d₁ d₂ : ℕ} (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (L₁ : Mat d₁ →L[ℝ] Mat d₁)
    (K : Rect d₁ d₂ →L[ℝ] Mat d₁) {βbar b b' : ℝ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hLeq : ∀ W, L₁ W = lyapOp Δ W - βbar • W) {X X' R Γ a : Mat d₁} {Z c : Rect d₁ d₂}
    (ha : L₁ a + K c = Γ)
    (hX : X' = X - b • (lyapOp Δ X + K Z) + b ^ 2 • Γ + R) :
    b'⁻¹ • X' - a = (b⁻¹ • X - a) - b • L₁ (b⁻¹ • X - a)
      + b • ((((b'⁻¹ - b⁻¹) - βbar) * b⁻¹) • X
        - (βbar + ((b'⁻¹ - b⁻¹) - βbar)) • (lyapOp Δ X + K Z)
        + (b * (βbar + ((b'⁻¹ - b⁻¹) - βbar))) • Γ + (b * b')⁻¹ • R - K (b⁻¹ • Z - c)) := by
  rw [hX, map_sub, map_sub, map_smul, map_smul, hLeq X, ← ha]
  funext ij
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The normalized cross recursion (one step). -/
lemma cross_step_identity {d₁ d₂ : ℕ} (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) {βbar b b' g : ℝ} (hb : b ≠ 0) (hb' : b' ≠ 0) (hg : g ≠ 0)
    {Z Z' R Γ c : Rect d₁ d₂} {Y bb : Mat d₂} (hc : rmul A₂₂ c + lmul A₁₂ bb = Γ)
    (hZ : Z' = Z - g • rmul A₂₂ Z - b • lmul A₁₂ Y + (b * g) • Γ + R) :
    b'⁻¹ • Z' - c = (b⁻¹ • Z - c) - g • rmul A₂₂ (b⁻¹ • Z - c)
      + g • ((((βbar + ((b'⁻¹ - b⁻¹) - βbar))) * g⁻¹) • Z
        - (βbar + ((b'⁻¹ - b⁻¹) - βbar)) • rmul A₂₂ Z
        - (b * (βbar + ((b'⁻¹ - b⁻¹) - βbar)) * g⁻¹) • lmul A₁₂ Y
        + (b * (βbar + ((b'⁻¹ - b⁻¹) - βbar))) • Γ + (g * b')⁻¹ • R
        - lmul A₁₂ (g⁻¹ • Y - bb)) := by
  rw [hZ, map_sub, map_sub, map_smul, map_smul, ← hc]
  funext ij
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The normalized fast recursion (one step). -/
lemma fast_step_identity {d₂ : ℕ} (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) {g g' : ℝ} (hg : g ≠ 0)
    (hg' : g' ≠ 0) {Y Y' R Γ bb : Mat d₂} (hbb : lyapOp A₂₂ bb = Γ)
    (hY : Y' = Y - g • lyapOp A₂₂ Y + g ^ 2 • Γ + R) :
    g'⁻¹ • Y' - bb = (g⁻¹ • Y - bb) - g • lyapOp A₂₂ (g⁻¹ • Y - bb)
      + g • (((g'⁻¹ - g⁻¹) * g⁻¹) • Y - (g'⁻¹ - g⁻¹) • lyapOp A₂₂ Y
        + (g * (g'⁻¹ - g⁻¹)) • Γ + (g * g')⁻¹ • R) := by
  rw [hY, map_sub, map_smul, ← hbb]
  funext ij
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

set_option maxHeartbeats 4000000 in
/-- The deterministic part of Theorem 2.1 of the write-up: if the second moments `X`, `Z`,
`Y` of the slow iterate, the cross term and the fast iterate follow the recursions of
Lemma 3.2 with remainders `o(β²) n`, `o(β γ) n`, `o(γ²) n`, where
`n = 1 + ‖X‖/β + ‖Z‖/β + ‖Y‖/γ`, then `X/β → a`, `Z/β → c`, `Y/γ → b`, the solutions of
`A₂₂ b + b A₂₂ᵀ = Γ₃`, `c A₂₂ᵀ + A₁₂ b = Γ₂` and
`(Δ - β̄/2) a + a (Δ - β̄/2)ᵀ + A₁₂ cᵀ + c A₁₂ᵀ = Γ₁`. -/
theorem tendsto_two_time_scale_moments {d₁ d₂ : ℕ} {β γ : ℕ → ℝ} {βbar : ℝ}
    (hβ : StepSizeRate β βbar) (hγ : StepSizeRate γ 0)
    (hβγ : Tendsto (fun k => β k / γ k) atTop (𝓝 0))
    (Δ : Matrix (Fin d₁) (Fin d₁) ℝ) (A₁₂ : Matrix (Fin d₁) (Fin d₂) ℝ)
    (A₂₂ : Matrix (Fin d₂) (Fin d₂) ℝ) {η : ℝ} (hη : 0 < η)
    (hΔ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((Δ - (βbar / 2) • 1) *ᵥ x))
    (hA₂₂ : ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A₂₂ *ᵥ x))
    {Γ₁ : Mat d₁} {Γ₂ : Rect d₁ d₂} {Γ₃ : Mat d₂}
    {X R₁ : ℕ → Mat d₁} {Z R₂ : ℕ → Rect d₁ d₂} {Y R₃ : ℕ → Mat d₂} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ k, 0 ≤ ε k)
    (hR₁ : ∀ k, ‖R₁ k‖ ≤ ε k * β k ^ 2 * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k))
    (hR₂ : ∀ k, ‖R₂ k‖ ≤ ε k * (β k * γ k) * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k))
    (hR₃ : ∀ k, ‖R₃ k‖ ≤ ε k * γ k ^ 2 * (1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k))
    (hX : ∀ k, X (k + 1) = X k - β k • (lyapOp Δ (X k) + coupleCLM A₁₂ (Z k))
      + β k ^ 2 • Γ₁ + R₁ k)
    (hZ : ∀ k, Z (k + 1) = Z k - γ k • rmul A₂₂ (Z k) - β k • lmul A₁₂ (Y k)
      + (β k * γ k) • Γ₂ + R₂ k)
    (hY : ∀ k, Y (k + 1) = Y k - γ k • lyapOp A₂₂ (Y k) + γ k ^ 2 • Γ₃ + R₃ k)
    {a : Mat d₁} {c : Rect d₁ d₂} {b : Mat d₂} (hb : lyapOp A₂₂ b = Γ₃)
    (hc : rmul A₂₂ c + lmul A₁₂ b = Γ₂)
    (ha : lyapOp (Δ - (βbar / 2) • 1) a + coupleCLM A₁₂ c = Γ₁) :
    Tendsto (fun k => (β k)⁻¹ • X k) atTop (𝓝 a) ∧
      Tendsto (fun k => (β k)⁻¹ • Z k) atTop (𝓝 c) ∧
      Tendsto (fun k => (γ k)⁻¹ • Y k) atTop (𝓝 b) := by
  have hβb := hβ.βbar_nonneg
  -- the operators
  obtain ⟨L₁, hL₁⟩ : ∃ L, L = lyapOp (Δ - (βbar / 2) • 1) := ⟨_, rfl⟩
  obtain ⟨K₁₂, hK₁₂⟩ : ∃ K, K = coupleCLM A₁₂ := ⟨_, rfl⟩
  have hLeq : ∀ W, L₁ W = lyapOp Δ W - βbar • W := by
    intro W
    rw [hL₁, lyapOp_sub_smul_one]
    congr 2
    ring
  have cL₁ : ∀ v, η * ‖v‖ ^ 2 ≤ ⟪L₁ v, v⟫ := fun v => by
    rw [hL₁]
    have := lyapOp_coercive _ hΔ v
    nlinarith [sq_nonneg ‖v‖]
  have cL₂ : ∀ v : Rect d₁ d₂, η * ‖v‖ ^ 2 ≤ ⟪rmul A₂₂ v, v⟫ := rmul_coercive A₂₂ hA₂₂
  have cL₃ : ∀ v, η * ‖v‖ ^ 2 ≤ ⟪lyapOp A₂₂ v, v⟫ := fun v => by
    have := lyapOp_coercive _ hA₂₂ v
    nlinarith [sq_nonneg ‖v‖]
  -- the normalized moments and their errors
  obtain ⟨ea, hea⟩ : ∃ e : ℕ → Mat d₁, e = fun k => (β k)⁻¹ • X k - a := ⟨_, rfl⟩
  obtain ⟨ec, hec⟩ : ∃ e : ℕ → Rect d₁ d₂, e = fun k => (β k)⁻¹ • Z k - c := ⟨_, rfl⟩
  obtain ⟨eb, heb⟩ : ∃ e : ℕ → Mat d₂, e = fun k => (γ k)⁻¹ • Y k - b := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = 1 + ‖a‖ + ‖c‖ + ‖b‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℝ, N = fun k => S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖ := ⟨_, rfl⟩
  have hXN : ∀ k, ‖X k‖ ≤ β k * N k := by
    intro k
    have hb := hβ.pos k
    have : ‖X k‖ = β k * ‖(β k)⁻¹ • X k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]; field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    have h1 : ‖(β k)⁻¹ • X k‖ ≤ ‖ea k‖ + ‖a‖ := by
      rw [hea]; simpa using norm_le_norm_sub_add ((β k)⁻¹ • X k) a
    rw [hN, hS]; dsimp only; linarith [norm_nonneg (ec k), norm_nonneg (eb k), norm_nonneg c,
      norm_nonneg b]
  have hZN : ∀ k, ‖Z k‖ ≤ β k * N k := by
    intro k
    have hb := hβ.pos k
    have : ‖Z k‖ = β k * ‖(β k)⁻¹ • Z k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]; field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    have h1 : ‖(β k)⁻¹ • Z k‖ ≤ ‖ec k‖ + ‖c‖ := by
      rw [hec]; simpa using norm_le_norm_sub_add ((β k)⁻¹ • Z k) c
    rw [hN, hS]; dsimp only; linarith [norm_nonneg (ea k), norm_nonneg (eb k), norm_nonneg a,
      norm_nonneg b]
  have hYN : ∀ k, ‖Y k‖ ≤ γ k * N k := by
    intro k
    have hb := hγ.pos k
    have : ‖Y k‖ = γ k * ‖(γ k)⁻¹ • Y k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]; field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    have h1 : ‖(γ k)⁻¹ • Y k‖ ≤ ‖eb k‖ + ‖b‖ := by
      rw [heb]; simpa using norm_le_norm_sub_add ((γ k)⁻¹ • Y k) b
    rw [hN, hS]; dsimp only; linarith [norm_nonneg (ea k), norm_nonneg (ec k), norm_nonneg a,
      norm_nonneg c]
  have hN1 : ∀ k, 1 ≤ N k := fun k => by
    rw [hN, hS]; dsimp only; linarith [norm_nonneg (ea k), norm_nonneg (ec k), norm_nonneg (eb k),
      norm_nonneg a, norm_nonneg b, norm_nonneg c]
  have hnN : ∀ k, 1 + ‖X k‖ / β k + ‖Z k‖ / β k + ‖Y k‖ / γ k ≤ 4 * N k := by
    intro k
    have h1 : ‖X k‖ / β k ≤ N k := by rw [div_le_iff₀ (hβ.pos k)]; linarith [hXN k]
    have h2 : ‖Z k‖ / β k ≤ N k := by rw [div_le_iff₀ (hβ.pos k)]; linarith [hZN k]
    have h3 : ‖Y k‖ / γ k ≤ N k := by rw [div_le_iff₀ (hγ.pos k)]; linarith [hYN k]
    linarith [hN1 k]
  -- the perturbations
  obtain ⟨εβ, hεβ⟩ : ∃ e : ℕ → ℝ, e = fun k => ((β (k + 1))⁻¹ - (β k)⁻¹) - βbar := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ e : ℕ → ℝ, e = fun k => (γ (k + 1))⁻¹ - (γ k)⁻¹ := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ : ℕ → Mat d₁, δ = fun k => (εβ k * (β k)⁻¹) • X k
      - (βbar + εβ k) • (lyapOp Δ (X k) + K₁₂ (Z k)) + (β k * (βbar + εβ k)) • Γ₁
      + (β k * β (k + 1))⁻¹ • R₁ k := ⟨_, rfl⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ : ℕ → Rect d₁ d₂, δ = fun k => ((βbar + εβ k) * (γ k)⁻¹) • Z k
      - (βbar + εβ k) • rmul A₂₂ (Z k) - (β k * (βbar + εβ k) * (γ k)⁻¹) • lmul A₁₂ (Y k)
      + (β k * (βbar + εβ k)) • Γ₂ + (γ k * β (k + 1))⁻¹ • R₂ k := ⟨_, rfl⟩
  obtain ⟨δ₃, hδ₃⟩ : ∃ δ : ℕ → Mat d₂, δ = fun k => (ζ k * (γ k)⁻¹) • Y k
      - ζ k • lyapOp A₂₂ (Y k) + (γ k * ζ k) • Γ₃ + (γ k * γ (k + 1))⁻¹ • R₃ k := ⟨_, rfl⟩
  rw [← hL₁, ← hK₁₂] at ha
  rw [← hK₁₂] at hX
  have hrec₁ : ∀ k, ea (k + 1) = ea k - β k • L₁ (ea k) + β k • (δ₁ k - K₁₂ (ec k)) := by
    intro k
    rw [hea, hec, hδ₁, hεβ]
    exact slow_step_identity Δ L₁ K₁₂ (hβ.pos k).ne' (hβ.pos (k + 1)).ne' hLeq ha (hX k)
  have hrec₂ : ∀ k, ec (k + 1) = ec k - γ k • rmul A₂₂ (ec k)
      + γ k • (δ₂ k - lmul A₁₂ (eb k)) := by
    intro k
    rw [hec, heb, hδ₂, hεβ]
    exact cross_step_identity A₁₂ A₂₂ (hβ.pos k).ne' (hβ.pos (k + 1)).ne' (hγ.pos k).ne' hc (hZ k)
  have hrec₃ : ∀ k, eb (k + 1) = eb k - γ k • lyapOp A₂₂ (eb k) + γ k • δ₃ k := by
    intro k
    rw [heb, hδ₃, hζ]
    exact fast_step_identity A₂₂ (hγ.pos k).ne' (hγ.pos (k + 1)).ne' hb (hY k)
  -- bounds on the perturbations
  have sm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (r : ℝ) (w : W) (B : ℝ),
      ‖w‖ ≤ B → ‖r • w‖ ≤ |r| * B := fun r w B h => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left h (abs_nonneg r)
  obtain ⟨e₁, he₁⟩ : ∃ e : ℕ → ℝ, e = fun k => |εβ k| + β k * |βbar + εβ k| *
      (‖lyapOp Δ‖ + ‖K₁₂‖ + ‖Γ₁‖) + β k / β (k + 1) * (4 * ε k) := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : ℕ → ℝ, e = fun k => |βbar + εβ k| * (β k / γ k + β k * ‖(rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖
      + β k * ‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖ + β k * ‖Γ₂‖) + β k / β (k + 1) * (4 * ε k) := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e : ℕ → ℝ, e = fun k => |ζ k| * (1 + γ k * ‖lyapOp A₂₂‖ + γ k * ‖Γ₃‖)
      + γ k / γ (k + 1) * (4 * ε k) := ⟨_, rfl⟩
  have hb₁ : ∀ k, ‖δ₁ k‖ ≤ e₁ k * N k := by
    intro k
    have hb := hβ.pos k
    have hb' := hβ.pos (k + 1)
    have hN0 : 0 ≤ N k := zero_le_one.trans (hN1 k)
    rw [hδ₁, he₁]
    simp only
    have n1 : ‖(εβ k * (β k)⁻¹) • X k‖ ≤ |εβ k| * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hb]
      calc |εβ k| * (β k)⁻¹ * ‖X k‖ ≤ |εβ k| * (β k)⁻¹ * (β k * N k) :=
            mul_le_mul_of_nonneg_left (hXN k) (by positivity)
        _ = |εβ k| * N k := by field_simp; ring
    have n2 : ‖(βbar + εβ k) • (lyapOp Δ (X k) + K₁₂ (Z k))‖ ≤
        |βbar + εβ k| * (β k * (‖lyapOp Δ‖ + ‖K₁₂‖) * N k) := by
      refine sm _ _ _ ((norm_add_le _ _).trans ?_)
      have t1 := (lyapOp Δ).le_opNorm (X k)
      have t2 := K₁₂.le_opNorm (Z k)
      have t3 := mul_le_mul_of_nonneg_left (hXN k) (norm_nonneg (lyapOp Δ))
      have t4 := mul_le_mul_of_nonneg_left (hZN k) (norm_nonneg K₁₂)
      have e : β k * (‖lyapOp Δ‖ + ‖K₁₂‖) * N k = ‖lyapOp Δ‖ * (β k * N k) + ‖K₁₂‖ * (β k * N k) := by
        ring
      linarith only [t1, t2, t3, t4, e]
    have n3 : ‖(β k * (βbar + εβ k)) • Γ₁‖ ≤ β k * |βbar + εβ k| * ‖Γ₁‖ * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hb]
      have := mul_le_mul_of_nonneg_left (hN1 k) (by positivity : 0 ≤ β k * |βbar + εβ k| * ‖Γ₁‖)
      linarith
    have n4 : ‖(β k * β (k + 1))⁻¹ • R₁ k‖ ≤ β k / β (k + 1) * (4 * ε k) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (β k * β (k + 1))⁻¹ * ‖R₁ k‖
          ≤ (β k * β (k + 1))⁻¹ * (ε k * β k ^ 2 * (4 * N k)) :=
            mul_le_mul_of_nonneg_left ((hR₁ k).trans
              (mul_le_mul_of_nonneg_left (hnN k) (by have := hε0 k; positivity))) (by positivity)
        _ = β k / β (k + 1) * (4 * ε k) * N k := by field_simp; ring
    have t1 := norm_add_le ((εβ k * (β k)⁻¹) • X k - (βbar + εβ k) • (lyapOp Δ (X k) + K₁₂ (Z k))
      + (β k * (βbar + εβ k)) • Γ₁) ((β k * β (k + 1))⁻¹ • R₁ k)
    have t2 := norm_add_le ((εβ k * (β k)⁻¹) • X k - (βbar + εβ k) • (lyapOp Δ (X k) + K₁₂ (Z k)))
      ((β k * (βbar + εβ k)) • Γ₁)
    have t3 := norm_sub_le ((εβ k * (β k)⁻¹) • X k) ((βbar + εβ k) • (lyapOp Δ (X k) + K₁₂ (Z k)))
    have e : (|εβ k| + β k * |βbar + εβ k| * (‖lyapOp Δ‖ + ‖K₁₂‖ + ‖Γ₁‖)
        + β k / β (k + 1) * (4 * ε k)) * N k = |εβ k| * N k
        + |βbar + εβ k| * (β k * (‖lyapOp Δ‖ + ‖K₁₂‖) * N k)
        + β k * |βbar + εβ k| * ‖Γ₁‖ * N k + β k / β (k + 1) * (4 * ε k) * N k := by ring
    rw [e]
    linarith
  have hb₂ : ∀ k, ‖δ₂ k‖ ≤ e₂ k * N k := by
    intro k
    have hb := hβ.pos k
    have hb' := hβ.pos (k + 1)
    have hg := hγ.pos k
    have hN0 : 0 ≤ N k := zero_le_one.trans (hN1 k)
    rw [hδ₂, he₂]
    simp only
    have n1 : ‖((βbar + εβ k) * (γ k)⁻¹) • Z k‖ ≤ |βbar + εβ k| * (β k / γ k) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hg]
      calc |βbar + εβ k| * (γ k)⁻¹ * ‖Z k‖ ≤ |βbar + εβ k| * (γ k)⁻¹ * (β k * N k) :=
            mul_le_mul_of_nonneg_left (hZN k) (by positivity)
        _ = |βbar + εβ k| * (β k / γ k) * N k := by field_simp; ring
    have n2 : ‖(βbar + εβ k) • rmul A₂₂ (Z k)‖ ≤ |βbar + εβ k| * (β k * ‖(rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * N k) := by
      refine sm _ _ _ ((rmul A₂₂).le_opNorm _ |>.trans ?_)
      have := mul_le_mul_of_nonneg_left (hZN k) (norm_nonneg (rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂))
      linarith
    have n3 : ‖(β k * (βbar + εβ k) * (γ k)⁻¹) • lmul A₁₂ (Y k)‖ ≤
        |βbar + εβ k| * (β k * ‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_inv, abs_of_pos hg, abs_of_pos hb]
      calc β k * |βbar + εβ k| * (γ k)⁻¹ * ‖lmul A₁₂ (Y k)‖
          ≤ β k * |βbar + εβ k| * (γ k)⁻¹ * (‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖ * (γ k * N k)) :=
            mul_le_mul_of_nonneg_left (((lmul A₁₂).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hYN k) (norm_nonneg _))) (by positivity)
        _ = |βbar + εβ k| * (β k * ‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖) * N k := by field_simp; ring
    have n4 : ‖(β k * (βbar + εβ k)) • Γ₂‖ ≤ |βbar + εβ k| * (β k * ‖Γ₂‖) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hb]
      have := mul_le_mul_of_nonneg_left (hN1 k) (by positivity : 0 ≤ β k * |βbar + εβ k| * ‖Γ₂‖)
      linarith
    have n5 : ‖(γ k * β (k + 1))⁻¹ • R₂ k‖ ≤ β k / β (k + 1) * (4 * ε k) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (γ k * β (k + 1))⁻¹ * ‖R₂ k‖
          ≤ (γ k * β (k + 1))⁻¹ * (ε k * (β k * γ k) * (4 * N k)) :=
            mul_le_mul_of_nonneg_left ((hR₂ k).trans
              (mul_le_mul_of_nonneg_left (hnN k) (by have := hε0 k; positivity))) (by positivity)
        _ = β k / β (k + 1) * (4 * ε k) * N k := by field_simp; ring
    have t1 := norm_add_le (((βbar + εβ k) * (γ k)⁻¹) • Z k - (βbar + εβ k) • rmul A₂₂ (Z k)
      - (β k * (βbar + εβ k) * (γ k)⁻¹) • lmul A₁₂ (Y k) + (β k * (βbar + εβ k)) • Γ₂)
      ((γ k * β (k + 1))⁻¹ • R₂ k)
    have t2 := norm_add_le (((βbar + εβ k) * (γ k)⁻¹) • Z k - (βbar + εβ k) • rmul A₂₂ (Z k)
      - (β k * (βbar + εβ k) * (γ k)⁻¹) • lmul A₁₂ (Y k)) ((β k * (βbar + εβ k)) • Γ₂)
    have t3 := norm_sub_le (((βbar + εβ k) * (γ k)⁻¹) • Z k - (βbar + εβ k) • rmul A₂₂ (Z k))
      ((β k * (βbar + εβ k) * (γ k)⁻¹) • lmul A₁₂ (Y k))
    have t4 := norm_sub_le (((βbar + εβ k) * (γ k)⁻¹) • Z k) ((βbar + εβ k) • rmul A₂₂ (Z k))
    have e : (|βbar + εβ k| * (β k / γ k + β k * ‖(rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ + β k * ‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖ + β k * ‖Γ₂‖)
        + β k / β (k + 1) * (4 * ε k)) * N k = |βbar + εβ k| * (β k / γ k) * N k
        + |βbar + εβ k| * (β k * ‖(rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖ * N k) + |βbar + εβ k| * (β k * ‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖) * N k
        + |βbar + εβ k| * (β k * ‖Γ₂‖) * N k + β k / β (k + 1) * (4 * ε k) * N k := by ring
    rw [e]
    linarith
  have hb₃ : ∀ k, ‖δ₃ k‖ ≤ e₃ k * N k := by
    intro k
    have hg := hγ.pos k
    have hg' := hγ.pos (k + 1)
    have hN0 : 0 ≤ N k := zero_le_one.trans (hN1 k)
    rw [hδ₃, he₃]
    simp only
    have n1 : ‖(ζ k * (γ k)⁻¹) • Y k‖ ≤ |ζ k| * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hg]
      calc |ζ k| * (γ k)⁻¹ * ‖Y k‖ ≤ |ζ k| * (γ k)⁻¹ * (γ k * N k) :=
            mul_le_mul_of_nonneg_left (hYN k) (by positivity)
        _ = |ζ k| * N k := by field_simp; ring
    have n2 : ‖ζ k • lyapOp A₂₂ (Y k)‖ ≤ |ζ k| * (γ k * ‖lyapOp A₂₂‖ * N k) := by
      refine sm _ _ _ ((lyapOp A₂₂).le_opNorm _ |>.trans ?_)
      have := mul_le_mul_of_nonneg_left (hYN k) (norm_nonneg (lyapOp A₂₂))
      linarith
    have n3 : ‖(γ k * ζ k) • Γ₃‖ ≤ |ζ k| * (γ k * ‖Γ₃‖) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hg]
      have := mul_le_mul_of_nonneg_left (hN1 k) (by positivity : 0 ≤ γ k * |ζ k| * ‖Γ₃‖)
      linarith
    have n4 : ‖(γ k * γ (k + 1))⁻¹ • R₃ k‖ ≤ γ k / γ (k + 1) * (4 * ε k) * N k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (γ k * γ (k + 1))⁻¹ * ‖R₃ k‖
          ≤ (γ k * γ (k + 1))⁻¹ * (ε k * γ k ^ 2 * (4 * N k)) :=
            mul_le_mul_of_nonneg_left ((hR₃ k).trans
              (mul_le_mul_of_nonneg_left (hnN k) (by have := hε0 k; positivity))) (by positivity)
        _ = γ k / γ (k + 1) * (4 * ε k) * N k := by field_simp; ring
    have t1 := norm_add_le ((ζ k * (γ k)⁻¹) • Y k - ζ k • lyapOp A₂₂ (Y k) + (γ k * ζ k) • Γ₃)
      ((γ k * γ (k + 1))⁻¹ • R₃ k)
    have t2 := norm_add_le ((ζ k * (γ k)⁻¹) • Y k - ζ k • lyapOp A₂₂ (Y k)) ((γ k * ζ k) • Γ₃)
    have t3 := norm_sub_le ((ζ k * (γ k)⁻¹) • Y k) (ζ k • lyapOp A₂₂ (Y k))
    have e : (|ζ k| * (1 + γ k * ‖lyapOp A₂₂‖ + γ k * ‖Γ₃‖) + γ k / γ (k + 1) * (4 * ε k)) * N k
        = |ζ k| * N k + |ζ k| * (γ k * ‖lyapOp A₂₂‖ * N k) + |ζ k| * (γ k * ‖Γ₃‖) * N k
          + γ k / γ (k + 1) * (4 * ε k) * N k := by ring
    rw [e]
    linarith
  -- the coefficients vanish
  have hratio : ∀ {s : ℕ → ℝ} {sb : ℝ}, StepSizeRate s sb →
      Tendsto (fun k => s k / s (k + 1)) atTop (𝓝 1) := by
    intro s sb hs
    have := hs.tendsto_ratio.inv₀ one_ne_zero
    simp only [inv_one] at this
    exact this.congr fun k => by rw [inv_div]
  have hεβ0 : Tendsto εβ atTop (𝓝 0) := by
    have := hβ.inv_diff.sub_const βbar
    simpa [hεβ] using this
  have hζ0 : Tendsto ζ atTop (𝓝 0) := by simpa [hζ] using hγ.inv_diff
  have hb0 := hβ.tendsto_zero
  have hg0 := hγ.tendsto_zero
  have he : Tendsto (fun k => e₁ k + e₂ k + e₃ k) atTop (𝓝 0) := by
    have l1 : Tendsto e₁ atTop (𝓝 0) := by
      rw [he₁]
      have := (hεβ0.abs.add ((hb0.mul (hεβ0.const_add βbar).abs).mul_const
        (‖lyapOp Δ‖ + ‖K₁₂‖ + ‖Γ₁‖))).add ((hratio hβ).mul (hε.const_mul 4))
      simpa using this
    have l2 : Tendsto e₂ atTop (𝓝 0) := by
      rw [he₂]
      have := (((hεβ0.const_add βbar).abs.mul ((((hβγ.add (hb0.mul_const ‖(rmul A₂₂ : Rect d₁ d₂ →L[ℝ] Rect d₁ d₂)‖)).add
        (hb0.mul_const ‖(lmul A₁₂ : Mat d₂ →L[ℝ] Rect d₁ d₂)‖)).add (hb0.mul_const ‖Γ₂‖)))).add
        ((hratio hβ).mul (hε.const_mul 4)))
      simpa using this
    have l3 : Tendsto e₃ atTop (𝓝 0) := by
      rw [he₃]
      have := (hζ0.abs.mul (((tendsto_const_nhds (x := (1 : ℝ))).add (hg0.mul_const ‖lyapOp A₂₂‖)).add
        (hg0.mul_const ‖Γ₃‖))).add ((hratio hγ).mul (hε.const_mul 4))
      simpa using this
    simpa using (l1.add l2).add l3
  have he0 : ∀ k, 0 ≤ e₁ k + e₂ k + e₃ k := by
    intro k
    have hb := hβ.pos k
    have hb' := hβ.pos (k + 1)
    have hg := hγ.pos k
    have hg' := hγ.pos (k + 1)
    have := hε0 k
    rw [he₁, he₂, he₃]
    positivity
  have hN' : ∀ k, N k = S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖ := fun k => by rw [hN]
  have hN0 : ∀ k, 0 ≤ N k := fun k => zero_le_one.trans (hN1 k)
  have he₁0 : ∀ k, 0 ≤ e₁ k := fun k => by
    have := hε0 k; have := hβ.pos k; have := hβ.pos (k + 1); rw [he₁]; positivity
  have he₂0 : ∀ k, 0 ≤ e₂ k := fun k => by
    have := hε0 k; have := hβ.pos k; have := hβ.pos (k + 1); have := hγ.pos k
    rw [he₂]; positivity
  have he₃0 : ∀ k, 0 ≤ e₃ k := fun k => by
    have := hε0 k; have := hγ.pos k; have := hγ.pos (k + 1); rw [he₃]; positivity
  have hd₁ : ∀ k, ‖δ₁ k‖ ≤ (e₁ k + e₂ k + e₃ k) * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖) := fun k => by
    rw [← hN' k]; nlinarith [hb₁ k, hN0 k, he₂0 k, he₃0 k]
  have hd₂ : ∀ k, ‖δ₂ k‖ ≤ (e₁ k + e₂ k + e₃ k) * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖) := fun k => by
    rw [← hN' k]; nlinarith [hb₂ k, hN0 k, he₁0 k, he₃0 k]
  have hd₃ : ∀ k, ‖δ₃ k‖ ≤ (e₁ k + e₂ k + e₃ k) * (S + ‖ea k‖ + ‖ec k‖ + ‖eb k‖) := fun k => by
    rw [← hN' k]; nlinarith [hb₃ k, hN0 k, he₁0 k, he₂0 k]
  obtain ⟨ha', hc', hb'⟩ := tendsto_zero_of_coupled_recursion L₁ (rmul A₂₂) (lyapOp A₂₂) K₁₂
    (lmul A₁₂) hη cL₁ cL₂ cL₃ (fun k => (hβ.pos k).le) (fun k => (hγ.pos k).le) hb0 hg0
    hβ.tendsto_sum hγ.tendsto_sum he he0 hS0 hd₁ hd₂ hd₃ hrec₁ hrec₂ hrec₃
  refine ⟨?_, ?_, ?_⟩
  · rw [hea] at ha'; exact tendsto_sub_nhds_zero_iff.mp ha'
  · rw [hec] at hc'; exact tendsto_sub_nhds_zero_iff.mp hc'
  · rw [heb] at hb'; exact tendsto_sub_nhds_zero_iff.mp hb'

end StochasticApproximation
