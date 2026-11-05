/-
SPDX-License-Identifier: MIT
-/
import RLTheory.StochasticApproximation.OrthogonalNoise

/-!
# The restart chain as a two-stage process

The martingale step of Theorems 4.5 and 4.7 of `docs/actor-critic-rates.md` uses the filtration
`𝒢_k` of the history up to `Y_{k-1}` together with the current flag and state `(f_k, s_k)`,
before the action `a_k` is drawn. This file shows that the sampling chain is `StateDriven` for
that filtration, with state `s_k` and next observation `ξ_{k+1} = (a_k, f_{k+1}, s_{k+1})`.

The chain is described by its two stages:
* the policy stage: given `𝒢_k`, the action is `a_k ~ π(· | s_k)`;
* the transition stage: given `ℋ_k = 𝒢_k ∨ σ(a_k)`, the next flag and state are drawn from
  `kap(Y_k, ·)`.

* `condExp_pair_of_law`: a conditional law for a variable `X` given `𝒢` extends to functions of
  `X` and of a `𝒢`-measurable finite variable `Z`.
* `TwoStageChain.stateDriven`: if the step law does not depend on the flag, the chain is
  `StateDriven` with `P(s, (a, f', s')) = π(a | s) kap((f, s, a), f', s')`.
-/

open Filter Topology Finset Real MeasureTheory RLTheory

namespace StochasticApproximation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

section Pair

variable {A B : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [DiscreteMeasurableSpace B]

/-- **Conditional laws extend to functions of a known variable.** If
`E[F(X) | 𝒢] = Σ_b p(Z, b) F(b)` for every `F`, with `Z` finite and `𝒢`-measurable, then
`E[H(Z, X) | 𝒢] = Σ_b p(Z, b) H(Z, b)` for every `H`. -/
lemma condExp_pair_of_law (𝒢 : MeasureTheory.Filtration ℕ m0) (k : ℕ) {Z : Ω → A} {X : Ω → B}
    (hZ : Measurable[𝒢 k] Z) (hX : Measurable X) {p : A → B → ℝ}
    (hlaw : ∀ F : B → ℝ, μ[fun ω => F (X ω) | 𝒢 k] =ᵐ[μ] fun ω => ∑ b, p (Z ω) b * F b)
    (H : A → B → ℝ) :
    μ[fun ω => H (Z ω) (X ω) | 𝒢 k] =ᵐ[μ] fun ω => ∑ b, p (Z ω) b * H (Z ω) b := by
  have h𝒢 := 𝒢.le k
  have hset : ∀ a, MeasurableSet[𝒢 k] {ω | Z ω = a} := fun a => hZ (measurableSet_singleton a)
  set I : A → Ω → ℝ := fun a => {ω | Z ω = a}.indicator fun _ => 1 with hI
  have hIm : ∀ a, StronglyMeasurable[𝒢 k] (I a) := fun a =>
    stronglyMeasurable_const.indicator (hset a)
  have hIa : ∀ a ω, I a ω = if Z ω = a then 1 else 0 := fun a ω => by
    by_cases h : Z ω = a
    · simp only [hI, h, if_true]; exact Set.indicator_of_mem (show ω ∈ {ω | Z ω = a} from h) _
    · simp only [hI, h, if_false]
      exact Set.indicator_of_notMem (show ω ∉ {ω | Z ω = a} from h) _
  have hXi : ∀ F : B → ℝ, Integrable (fun ω => F (X ω)) μ := fun F => by
    refine (memLp_top_of_bound ((StronglyMeasurable.of_discrete (f := F)).comp_measurable
      hX).aestronglyMeasurable (∑ b, |F b|) (Eventually.of_forall fun ω => ?_)).integrable le_top
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun b => |F b|) (fun _ _ => abs_nonneg _) (mem_univ _)
  have e : (fun ω => H (Z ω) (X ω)) = ∑ a, (I a * fun ω => H a (X ω)) := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, hIa]
    simp
  have hint : ∀ a, Integrable (I a * fun ω => H a (X ω)) μ := fun a =>
    (hXi (H a)).bdd_mul ((hIm a).mono h𝒢).aestronglyMeasurable
      ⟨1, fun ω => by rw [hIa]; split_ifs <;> simp⟩
  rw [e]
  have hsum := condExp_finset_sum (s := univ) (μ := μ) (fun a _ => hint a) (𝒢 k)
  have hterm : ∀ a, μ[I a * fun ω => H a (X ω) | 𝒢 k] =ᵐ[μ]
      fun ω => I a ω * ∑ b, p (Z ω) b * H a b := fun a => by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hIm a) (hint a) (hXi (H a)),
      hlaw (H a)] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with ω h1 h2
  rw [h1, Finset.sum_apply, sum_congr rfl fun a _ => h2 a]
  simp [hIa]

end Pair

section TwoStage

variable {S Ac : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [Fintype Ac] [DecidableEq Ac] [MeasurableSpace Ac] [DiscreteMeasurableSpace Ac]

/-- The sampling chain as a two-stage process. `fs k = (f_k, s_k)` is the flag and state, known
at `𝒢_k`; the action `a_k` is drawn from the policy given `𝒢_k`; and the next flag and state are
drawn from `kap(Y_k, ·)` given `ℋ_k = 𝒢_k ∨ σ(a_k)`. -/
structure TwoStageChain (μ : Measure Ω) (𝒢 ℋ : MeasureTheory.Filtration ℕ m0)
    (fs : ℕ → Ω → Bool × S) (a : ℕ → Ω → Ac) (pol : S → Ac → ℝ)
    (kap : Bool × S × Ac → Bool → S → ℝ) : Prop where
  le₁ : ∀ k, 𝒢 k ≤ ℋ k
  le₂ : ∀ k, ℋ k ≤ 𝒢 (k + 1)
  meas_fs : ∀ k, Measurable[𝒢 k] (fs k)
  meas_a : ∀ k, Measurable[ℋ k] (a k)
  policy : ∀ k (F : Ac → ℝ), μ[fun ω => F (a k ω) | 𝒢 k] =ᵐ[μ]
    fun ω => ∑ b, pol (fs k ω).2 b * F b
  step : ∀ k (F : Bool × S → ℝ), μ[fun ω => F (fs (k + 1) ω) | ℋ k] =ᵐ[μ]
    fun ω => ∑ x, kap ((fs k ω).1, (fs k ω).2, a k ω) x.1 x.2 * F x

/-- **The sampling chain is state-driven before the action.** If the step law does not depend
on the flag, the chain is `StateDriven` for the pre-action filtration `𝒢`, with state `s_k` and
next observation `ξ_{k+1} = (s_k, a_k, f_{k+1}, s_{k+1})`, whose law given `𝒢_k` is
`P(s, (s₀, a, f', s')) = 1{s₀ = s} π(a | s) kap((f, s, a), f', s')`. The current state is
included so that the TD error `δ_k`, a function of `(s_k, a_k, f_{k+1}, s_{k+1})`, is a function
of `ξ_{k+1}`. This is the hypothesis of `StateDriven.tendsto_secondMoment_of_centered_split`
used for Theorems 4.5 and 4.7. -/
theorem TwoStageChain.stateDriven {𝒢 ℋ : MeasureTheory.Filtration ℕ m0} {fs : ℕ → Ω → Bool × S}
    {a : ℕ → Ω → Ac} {pol : S → Ac → ℝ} {kap : Bool × S × Ac → Bool → S → ℝ}
    (hc : TwoStageChain μ 𝒢 ℋ fs a pol kap)
    (hkap : ∀ f₁ f₂ s b, kap (f₁, s, b) = kap (f₂, s, b)) :
    StateDriven μ 𝒢 (fun k ω => (fs k ω).2) (fun n ω => ((fs (n - 1) ω).2, a (n - 1) ω, fs n ω))
      (fun s x => (if x.1 = s then 1 else 0) * (pol s x.2.1 * kap (false, s, x.2.1) x.2.2.1 x.2.2.2))
    where
  state k := measurable_snd.comp (hc.meas_fs k)
  obs k := (((measurable_snd.comp (hc.meas_fs k)).mono ((hc.le₁ k).trans (hc.le₂ k)) le_rfl).prodMk
    (((hc.meas_a k).mono (hc.le₂ k) le_rfl).prodMk (hc.meas_fs (k + 1))))
  law k F := by
    show μ[fun ω => F ((fs k ω).2, a k ω, fs (k + 1) ω) | 𝒢 k] =ᵐ[μ] _
    set G : (Bool × S) × Ac → ℝ :=
      fun z => ∑ x, kap (z.1.1, z.1.2, z.2) x.1 x.2 * F (z.1.2, z.2, x) with hG
    -- the transition stage
    have inner : μ[fun ω => F ((fs k ω).2, a k ω, fs (k + 1) ω) | ℋ k] =ᵐ[μ]
        fun ω => G (fs k ω, a k ω) :=
      condExp_pair_of_law ℋ k (Z := fun ω => (fs k ω, a k ω)) (X := fs (k + 1))
        (((hc.meas_fs k).mono (hc.le₁ k) le_rfl).prodMk (hc.meas_a k))
        ((hc.meas_fs (k + 1)).mono (𝒢.le (k + 1)) le_rfl)
        (p := fun z x => kap (z.1.1, z.1.2, z.2) x.1 x.2) (hc.step k)
        (fun z x => F (z.1.2, z.2, x))
    -- the policy stage
    have outer : μ[fun ω => G (fs k ω, a k ω) | 𝒢 k] =ᵐ[μ]
        fun ω => ∑ b, pol (fs k ω).2 b * G (fs k ω, b) :=
      condExp_pair_of_law 𝒢 k (Z := fs k) (X := a k) (hc.meas_fs k)
        ((hc.meas_a k).mono (ℋ.le k) le_rfl) (p := fun z b => pol z.2 b) (hc.policy k)
        (fun z b => G (z, b))
    have tower := (condExp_condExp_of_le (μ := μ)
      (f := fun ω => F ((fs k ω).2, a k ω, fs (k + 1) ω)) (hc.le₁ k) (ℋ.le k)).symm
    filter_upwards [tower, condExp_congr_ae (m := 𝒢 k) inner, outer] with ω h1 h2 h3
    rw [h1, h2, h3, Fintype.sum_prod_type, sum_eq_single (fs k ω).2]
    · simp only [hG, if_true, one_mul, Fintype.sum_prod_type, mul_sum]
      refine sum_congr rfl fun b _ => sum_congr rfl fun f' _ => sum_congr rfl fun s' _ => ?_
      rw [hkap (fs k ω).1 false]
      ring
    · intro s0 _ hs0
      simp [hs0]
    · simp

end TwoStage

end StochasticApproximation
