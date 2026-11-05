/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.TwoTimeScaleMarkov

/-!
# Markov noise with a parameter-dependent chain

The iteration `θ_{k+1} = θ_k + β_k H(θ_k, ξ_{k+1})`, where the finite chain `ξ` moves by
`ξ_{k+1} ~ P_{θ_k}(ξ_k, ·)`. Given a Poisson pair `(U, V)` with
`U_t - V_t = H_t - f(t)` and `V_t = P_t U_t`, the noise splits as
`H(θ_k, ξ_{k+1}) = f(θ_k) + M_{k+1} + h_k - h_{k+1} + r_k` with
* the martingale difference `M_{k+1} = U_{θ_k}(ξ_{k+1}) - V_{θ_k}(ξ_k)`;
* the Poisson shift `h_k = V_{θ_{k-1}}(ξ_k)`, known at time `k`;
* the remainder `r_k = V_{θ_k}(ξ_k) - V_{θ_{k-1}}(ξ_k)`, also known at time `k`, of size
  `L_V ‖θ_k - θ_{k-1}‖ = O(β_k)` when `V` is Lipschitz in the parameter.

Lagging the parameter in `h` is what keeps the remainder known at time `k`, as the moment bounds
of `moment_bounds_of_dissipative_markov` require.

* `param_noise_decomp`: the algebraic identity.
* `condExp_finite_mix`: the conditional expectation of `G(ξ_{k+1})` for a finite chain.
* `tendsto_secondMoment_of_param_chain`: Assumption 2.2 for θ-dependent sampling.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace StochasticApproximation

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **The Poisson decomposition.** If `U_t - V_t = H_t - f(t)`, then
`H(θ_k, ξ_{k+1}) = f(θ_k) + M_{k+1} + h_k - h_{k+1} + r_k` with `M, h, r` as in the module doc. -/
lemma param_noise_decomp {θ : ℕ → Ω → E d} {ξ : ℕ → Ω → S} {H U V : E d → S → E d}
    {f : E d → E d} (hP : ∀ t s, U t s - V t s = H t s - f t) (k : ℕ) (ω : Ω) :
    H (θ k ω) (ξ (k + 1) ω) = f (θ k ω) + (U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω))
      + V (θ (k - 1) ω) (ξ k ω) - V (θ (k + 1 - 1) ω) (ξ (k + 1) ω)
      + (V (θ k ω) (ξ k ω) - V (θ (k - 1) ω) (ξ k ω)) := by
  have h1 : H (θ k ω) (ξ (k + 1) ω) =
      f (θ k ω) + (U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ (k + 1) ω)) := by
    rw [hP]; abel
  simp only [Nat.add_sub_cancel]
  rw [h1]
  abel

omit [DecidableEq S] in
/-- A function of a continuous-in-the-parameter family at a finite random index is strongly
measurable. -/
lemma stronglyMeasurable_comp_finite {n : ℕ} {m : MeasurableSpace Ω} {t : Ω → E d} {X : Ω → S}
    (ht : StronglyMeasurable[m] t) (hX : Measurable[m] X) {G : E d → S → E n}
    (hG : ∀ s, Continuous fun u => G u s) : StronglyMeasurable[m] (fun ω => G (t ω) (X ω)) := by
  have e : (fun ω => G (t ω) (X ω)) =
      fun ω => ∑ s ∈ univ, (X ⁻¹' {s}).indicator (fun ω => G (t ω) s) ω := by
    funext ω
    rw [Finset.sum_eq_single (X ω)]
    · simp
    · intro s _ hs
      simp [Ne.symm hs]
    · simp
  rw [e]
  exact Finset.stronglyMeasurable_sum _ fun s _ =>
    ((hG s).comp_stronglyMeasurable ht).indicator (hX (measurableSet_singleton s))

/-- **Conditional expectations along a finite chain.** If the conditional law of `X` given `ℱ_k`
is `p`, then `E[G_X | ℱ_k] = Σ_s p_s G_s` for `ℱ_k`-measurable bounded `G_s`. -/
lemma condExp_finite_mix (ℱ : MeasureTheory.Filtration ℕ m0) (k : ℕ) {X : Ω → S}
    (hX : Measurable X) {p : S → Ω → ℝ}
    (hlaw : ∀ s, μ[{ω | X ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ] p s)
    {G : S → Ω → ℝ} (hG : ∀ s, StronglyMeasurable[ℱ k] (G s))
    (hGb : ∀ s, ∃ C, ∀ ω, |G s ω| ≤ C) :
    μ[fun ω => G (X ω) ω | ℱ k] =ᵐ[μ] fun ω => ∑ s, p s ω * G s ω := by
  set I : S → Ω → ℝ := fun s => {ω | X ω = s}.indicator fun _ => 1 with hI
  have hIa : ∀ s ω, I s ω = if X ω = s then 1 else 0 := fun s ω => by
    by_cases h : X ω = s
    · simp only [hI, h, if_true]; exact Set.indicator_of_mem (show ω ∈ {ω | X ω = s} from h) _
    · simp only [hI, h, if_false]
      exact Set.indicator_of_notMem (show ω ∉ {ω | X ω = s} from h) _
  have hIi : ∀ s, Integrable (I s) μ := fun s =>
    (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton s))
  have hGi : ∀ s, Integrable (G s) μ := fun s => by
    obtain ⟨C, hC⟩ := hGb s
    exact (memLp_top_of_bound ((hG s).mono (ℱ.le k)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top
  have hint : ∀ s, Integrable (G s * I s) μ := fun s =>
    (hIi s).bdd_mul ((hG s).mono (ℱ.le k)).aestronglyMeasurable (hGb s) |>.congr
      (Eventually.of_forall fun ω => by simp)
  have e : (fun ω => G (X ω) ω) = ∑ s, (G s * I s) := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, hIa]
    simp
  rw [e]
  have hsum := condExp_finset_sum (s := univ) (μ := μ) (fun s _ => hint s) (ℱ k)
  have hterm : ∀ s, μ[G s * I s | ℱ k] =ᵐ[μ] fun ω => p s ω * G s ω := fun s => by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hG s) (hint s) (hIi s), hlaw s]
      with ω h1 h2
    rw [h1, Pi.mul_apply, h2, mul_comm]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with ω h1 h2
  rw [h1, Finset.sum_apply, sum_congr rfl fun s _ => h2 s]

lemma continuous_of_lipschitz_bound {n : ℕ} {F : E d → E n} {L : ℝ}
    (hF : ∀ t t', ‖F t - F t'‖ ≤ L * ‖t - t'‖) : Continuous F := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (|L| + 1), by positivity, fun a ha => ?_⟩
  rw [dist_eq_norm] at ha ⊢
  have h1 := hF a b
  have h2 : L * ‖a - b‖ ≤ |L| * ‖a - b‖ := mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)
  have h3 : |L| * ‖a - b‖ ≤ |L| * (ε / (|L| + 1)) :=
    mul_le_mul_of_nonneg_left ha.le (abs_nonneg L)
  have h4 : |L| * (ε / (|L| + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg L]
  linarith

/-- The martingale part `M_{k+1} = U_{θ_k}(ξ_{k+1}) - V_{θ_k}(ξ_k)` (indexed by `n = k + 1`). -/
noncomputable def paramM {Ω : Type*} (U V : E d → S → E d) (θ : ℕ → Ω → E d) (ξ : ℕ → Ω → S)
    (n : ℕ) (ω : Ω) : E d :=
  U (θ (n - 1) ω) (ξ n ω) - V (θ (n - 1) ω) (ξ (n - 1) ω)

/-- The Poisson shift `h_k = V_{θ_{k-1}}(ξ_k)`. -/
def paramH {Ω : Type*} (V : E d → S → E d) (θ : ℕ → Ω → E d) (ξ : ℕ → Ω → S) (k : ℕ)
    (ω : Ω) : E d :=
  V (θ (k - 1) ω) (ξ k ω)

/-- The remainder `r_k = V_{θ_k}(ξ_k) - V_{θ_{k-1}}(ξ_k)`. -/
noncomputable def paramR {Ω : Type*} (V : E d → S → E d) (θ : ℕ → Ω → E d) (ξ : ℕ → Ω → S)
    (k : ℕ) (ω : Ω) : E d :=
  V (θ k ω) (ξ k ω) - V (θ (k - 1) ω) (ξ k ω)

set_option maxHeartbeats 4000000 in
/-- **The decomposition along the process.** Under the hypotheses of
`tendsto_secondMoment_of_param_chain`, the iteration is
`θ_{k+1} = θ_k + β_k (f(θ_k) + M_{k+1} + h_k - h_{k+1} + r_k)` with `M` a bounded martingale
difference, and `h`, `r` known at time `k`, `h` bounded and `r = O(β_k)`. -/
lemma param_chain_decomp {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar)
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d} {ξ : ℕ → Ω → S}
    {f : E d → E d} {H U V : E d → S → E d} {P : E d → S → S → ℝ} {CU CV LV CH : ℝ}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • H (θ k ω) (ξ (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (θ k ω) (ξ k ω) s)
    (hpois : ∀ t s, U t s - V t s = H t s - f t) (hV : ∀ t s, V t s = ∑ s', P t s s' • U t s')
    (hUc : ∀ s, Continuous fun t => U t s) (hUb : ∀ t s, ‖U t s‖ ≤ CU)
    (hVb : ∀ t s, ‖V t s‖ ≤ CV) (hVL : ∀ t t' s, ‖V t s - V t' s‖ ≤ LV * ‖t - t'‖)
    (hHb : ∀ t s, ‖H t s‖ ≤ CH) :
    (∀ k ω, θ (k + 1) ω = θ k ω + β k • (f (θ k ω) + paramM U V θ ξ (k + 1) ω
      + paramH V θ ξ k ω - paramH V θ ξ (k + 1) ω + paramR V θ ξ k ω)) ∧
    (∀ k, StronglyMeasurable[ℱ k] (paramH V θ ξ k)) ∧
    (∀ k, StronglyMeasurable[ℱ k] (paramR V θ ξ k)) ∧
    (∃ Cr, ∀ k ω, ‖paramR V θ ξ k ω‖ ≤ Cr * β k) ∧
    (∀ k, StronglyMeasurable[ℱ (k + 1)] (paramM U V θ ξ (k + 1))) ∧
    (∀ k ω, ‖paramM U V θ ξ (k + 1) ω‖ ≤ CU + CV) ∧
    (∀ k j, μ[fun ω => paramM U V θ ξ (k + 1) ω j | ℱ k] =ᵐ[μ] 0) := by
  obtain ⟨R, C₀, hR1, -, hR⟩ := hβ.prev_le
  have hVc : ∀ s, Continuous fun t => V t s := fun s =>
    continuous_of_lipschitz_bound (fun t t' => hVL t t' s)
  set M : ℕ → Ω → E d := fun n ω => U (θ (n - 1) ω) (ξ n ω) - V (θ (n - 1) ω) (ξ (n - 1) ω)
    with hMdef
  set h : ℕ → Ω → E d := fun k ω => V (θ (k - 1) ω) (ξ k ω) with hh
  set r : ℕ → Ω → E d := fun k ω => V (θ k ω) (ξ k ω) - V (θ (k - 1) ω) (ξ k ω) with hr
  have hθ' : ∀ k ω, θ (k + 1) ω = θ k ω + β k • (f (θ k ω) + M (k + 1) ω + h k ω
      - h (k + 1) ω + r k ω) := fun k ω => by
    rw [hθ k ω, param_noise_decomp (θ := θ) (ξ := ξ) hpois k ω]
    simp only [hMdef, hh, hr, Nat.add_sub_cancel]
  have hθprev : ∀ k, StronglyMeasurable[ℱ k] (θ (k - 1)) := fun k =>
    (hθm (k - 1)).mono (ℱ.mono (Nat.sub_le k 1))
  have hhm : ∀ k, StronglyMeasurable[ℱ k] (h k) := fun k =>
    stronglyMeasurable_comp_finite (hθprev k) (hξm k) hVc
  have hrm : ∀ k, StronglyMeasurable[ℱ k] (r k) := fun k =>
    (stronglyMeasurable_comp_finite (hθm k) (hξm k) hVc).sub (hhm k)
  set LV₀ := max LV 0
  set CH₀ := max CH 0
  have hLV : 0 ≤ LV₀ := le_max_right _ _
  have hCH : 0 ≤ CH₀ := le_max_right _ _
  have hR0 : 0 ≤ R := by linarith
  have hrb : ∀ k ω, ‖r k ω‖ ≤ (LV₀ * CH₀ * R) * β k := fun k ω => by
    cases k with
    | zero => simp [hr]; have := hβ.pos 0; positivity
    | succ j =>
      simp only [hr, Nat.add_sub_cancel]
      have h1 := (hVL (θ (j + 1) ω) (θ j ω) (ξ (j + 1) ω)).trans
        (mul_le_mul_of_nonneg_right (le_max_left LV 0) (norm_nonneg _))
      have h2 : ‖θ (j + 1) ω - θ j ω‖ ≤ β j * CH₀ := by
        rw [hθ j ω, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hβ.pos j)]
        exact mul_le_mul_of_nonneg_left ((hHb _ _).trans (le_max_left _ _)) (hβ.pos j).le
      have h3 : β j ≤ R * β (j + 1) := by simpa using (hR (j + 1)).1
      have h4 := mul_le_mul_of_nonneg_left h2 hLV
      have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hLV hCH)
      have e1 : LV₀ * (β j * CH₀) = LV₀ * CH₀ * β j := by ring
      have e2 : LV₀ * CH₀ * (R * β (j + 1)) = LV₀ * CH₀ * R * β (j + 1) := by ring
      linarith
  have hMm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (M (k + 1)) := fun k => by
    simp only [hMdef, Nat.add_sub_cancel]
    exact (stronglyMeasurable_comp_finite ((hθm k).mono (ℱ.mono k.le_succ)) (hξm (k + 1)) hUc).sub
      ((stronglyMeasurable_comp_finite (hθm k) (hξm k) hVc).mono (ℱ.mono k.le_succ))
  have hMb : ∀ k ω, ‖M (k + 1) ω‖ ≤ CU + CV := fun k ω => by
    simp only [hMdef, Nat.add_sub_cancel]
    exact (norm_sub_le _ _).trans (add_le_add (hUb _ _) (hVb _ _))
  have hmart : ∀ k j, μ[fun ω => M (k + 1) ω j | ℱ k] =ᵐ[μ] 0 := fun k j => by
    have habs : ∀ v : E d, |v j| ≤ ‖v‖ := fun v => by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have hcompsum : ∀ (c : S → ℝ) (u : S → E d), (∑ s, c s • u s) j = ∑ s, c s * u s j :=
      fun c u => by rw [Finset.sum_apply]; simp
    have hcomp : ∀ (F : E d → S → E d), (∀ s, Continuous fun t => F t s) → ∀ s,
        StronglyMeasurable[ℱ k] (fun ω => F (θ k ω) s j) := fun F hF s =>
      (((EuclideanSpace.proj j : E d →L[ℝ] ℝ).continuous.comp (hF s)).comp_stronglyMeasurable
        (hθm k))
    have hmix := condExp_finite_mix (μ := μ) ℱ k ((hξm (k + 1)).mono (ℱ.le (k + 1)) le_rfl)
      (hlaw k) (G := fun s ω => U (θ k ω) s j) (hcomp U hUc)
      (fun s => ⟨CU, fun ω => (habs _).trans (hUb _ _)⟩)
    have hVk : StronglyMeasurable[ℱ k] (fun ω => V (θ k ω) (ξ k ω) j) :=
      ((EuclideanSpace.proj j : E d →L[ℝ] ℝ).continuous).comp_stronglyMeasurable
        (stronglyMeasurable_comp_finite (hθm k) (hξm k) hVc)
    have iU : Integrable (fun ω => U (θ k ω) (ξ (k + 1) ω) j) μ := by
      refine (memLp_top_of_bound (((EuclideanSpace.proj j : E d →L[ℝ] ℝ).continuous.comp_stronglyMeasurable
        (stronglyMeasurable_comp_finite ((hθm k).mono (ℱ.mono
          k.le_succ)) (hξm (k + 1)) hUc)).mono (ℱ.le (k + 1))).aestronglyMeasurable CU
        (Eventually.of_forall fun ω => ?_)).integrable le_top
      rw [Real.norm_eq_abs]; exact (habs _).trans (hUb _ _)
    have iV : Integrable (fun ω => V (θ k ω) (ξ k ω) j) μ :=
      (memLp_top_of_bound (hVk.mono (ℱ.le k)).aestronglyMeasurable CV
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact (habs _).trans (hVb _ _))).integrable le_top
    have e : (fun ω => M (k + 1) ω j) =
        (fun ω => U (θ k ω) (ξ (k + 1) ω) j) - fun ω => V (θ k ω) (ξ k ω) j := by
      funext ω; simp [hMdef]
    rw [e]
    filter_upwards [condExp_sub iU iV (ℱ k), hmix] with ω h1 h2
    rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable (ℱ.le k) hVk iV]
    simp only [Pi.zero_apply]
    rw [hV, hcompsum]
    simp
  exact ⟨hθ', hhm, hrm, ⟨_, hrb⟩, hMm, hMb, hmart⟩

set_option maxHeartbeats 4000000 in
/-- **Assumption 2.2 for θ-dependent sampling.** Let `θ_{k+1} = θ_k + β_k H(θ_k, ξ_{k+1})`, where the
finite chain `ξ` has conditional law `P_{θ_k}(ξ_k, ·)` given `ℱ_k`. Suppose:
* the mean drift `f` is dissipative around `θ*`, of linear size, and linear to first order,
  `f(θ) = -A(θ - θ*) + O(‖θ - θ*‖²)`;
* `(U, V)` is a Poisson pair, `U_t - V_t = H_t - f(t)` and `V_t = P_t U_t`, with `U` bounded and
  continuous in `t`, and `V` bounded and Lipschitz in `t`;
* `H` is bounded and the start is bounded;
* the covariance of `M_{k+1} = U_{θ_k}(ξ_{k+1}) - V_{θ_k}(ξ_k)` converges to `Γ`.

Then `(θ_k - θ*)/√β_k` has the asymptotic covariance `Σ` with
`(A - (β̄/2) I) Σ + Σ (A - (β̄/2) I)ᵀ = Γ`. -/
theorem tendsto_secondMoment_of_param_chain {β : ℕ → ℝ} {βbar : ℝ} (hβ : StepSizeRate β βbar)
    (A : Matrix (Fin d) (Fin d) ℝ) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hA : ∀ x, η₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A - (βbar / 2) • 1) *ᵥ x))
    (ℱ : MeasureTheory.Filtration ℕ m0) {θ : ℕ → Ω → E d} {ξ : ℕ → Ω → S} {θh : E d}
    {f : E d → E d} {H U V : E d → S → E d} {P : E d → S → S → ℝ}
    {η K L CU CV LV CH : ℝ} (h2η : βbar < 2 * η) (hK0 : 0 ≤ K) (hL : 0 ≤ L)
    (hdis : ∀ x, ⟪x - θh, f x⟫_ℝ ≤ -η * ‖x - θh‖ ^ 2) (hlin : ∀ x, ‖f x‖ ≤ K * ‖x - θh‖)
    (hf : ∀ x, ‖f x + matCLM A (x - θh)‖ ≤ L * ‖x - θh‖ ^ 2) (hfc : Continuous f) {Γ : Mat d}
    (hθ : ∀ k ω, θ (k + 1) ω = θ k ω + β k • H (θ k ω) (ξ (k + 1) ω))
    (hθm : ∀ k, StronglyMeasurable[ℱ k] (θ k)) (hξm : ∀ k, Measurable[ℱ k] (ξ k))
    (hθ0 : ∃ C, ∀ ω, ‖θ 0 ω - θh‖ ≤ C)
    (hlaw : ∀ k s, μ[{ω | ξ (k + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => P (θ k ω) (ξ k ω) s)
    (hpois : ∀ t s, U t s - V t s = H t s - f t) (hV : ∀ t s, V t s = ∑ s', P t s s' • U t s')
    (hUc : ∀ s, Continuous fun t => U t s) (hUb : ∀ t s, ‖U t s‖ ≤ CU)
    (hVb : ∀ t s, ‖V t s‖ ≤ CV) (hVL : ∀ t t' s, ‖V t s - V t' s‖ ≤ LV * ‖t - t'‖)
    (hHb : ∀ t s, ‖H t s‖ ≤ CH)
    (hΓ : Tendsto (fun k => secondMoment μ
      (fun ω => U (θ k ω) (ξ (k + 1) ω) - V (θ k ω) (ξ k ω))) atTop (𝓝 Γ)) :
    ∃ Sig, lyapOp (A - (βbar / 2) • 1) Sig = Γ ∧
      Tendsto (fun k => (β k)⁻¹ • secondMoment μ (fun ω => θ k ω - θh)) atTop (𝓝 Sig) := by
  obtain ⟨hθ', hhm, hrm, ⟨Cr, hrb⟩, hMm, hMb, hmart⟩ := param_chain_decomp (μ := μ) hβ ℱ hθ hθm
    hξm hlaw hpois hV hUc hUb hVb hVL hHb
  exact tendsto_secondMoment_of_dissipative_markov hβ A hη₀ hA ℱ h2η hK0 hL hdis hlin hf hfc hθ'
    hθm hθ0 hhm (fun k ω => hVb _ _) hrm hrb hMm hMb hmart (by simpa [paramM] using hΓ)

end StochasticApproximation
