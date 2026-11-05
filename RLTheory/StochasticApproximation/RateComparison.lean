/-
SPDX-License-Identifier: MIT
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import RLTheory.StochasticApproximation.MarkovNoiseCovariance

/-!
# The loss in expected reward and the comparison of rates

Section 3 of `docs/actor-critic-rates.md`.

* `quadPair H P = Σ_ij H_ij P_ij`, so that `E[xᵀ H x] = quadPair H E[x xᵀ]`.
* `tendsto_quadLoss`: Proposition 3.3, `β⁻¹ E[½ xᵀ H_J x] → ½ tr(H_J Σ)`.
* `loss_duality`: Proposition 3.4, `tr(H_J Σ) = tr(K Γ)` when `B Σ + Σ Bᵀ = Γ` and
  `Bᵀ K + K B = H_J`.
* `optLoss`, `optLoss_eq_trace`, `optLoss_mono`: Proposition 3.5, the optimal-gain loss
  `½ tr(H_J H⁻¹ Γ H⁻ᵀ)` is monotone in the noise covariance `Γ` in the Loewner order.
-/

open Filter Topology Finset Real Matrix MeasureTheory RLTheory

namespace StochasticApproximation

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### The quadratic loss -/

/-- The pairing `Σ_ij H_ij P_ij = tr(Hᵀ P)`. -/
def quadPair (H : Matrix (Fin d) (Fin d) ℝ) (P : Mat d) : ℝ := ∑ i, ∑ j, H i j * P (i, j)

lemma quadPair_smul (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (P : Mat d) :
    quadPair H (c • P) = c * quadPair H P := by
  simp only [quadPair, PiLp.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma continuous_quadPair (H : Matrix (Fin d) (Fin d) ℝ) : Continuous (quadPair H) := by
  unfold quadPair
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) (i, j)).continuous)

/-- `E[xᵀ H x] = Σ_ij H_ij E[x_i x_j]`. -/
lemma integral_quadForm (H : Matrix (Fin d) (Fin d) ℝ) {x : Ω → E d} (hx : MemLp x 2 μ) :
    ∫ ω, ∑ i, ∑ j, H i j * (x ω i * x ω j) ∂μ = quadPair H (secondMoment μ x) := by
  have hint : ∀ i j, Integrable (fun ω => H i j * (x ω i * x ω j)) μ := fun i j =>
    ((memLp_apply hx i).integrable_mul (memLp_apply hx j)).const_mul _
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, secondMoment, crossMoment_apply hx hx]

/-- **Proposition 3.3.** If `β⁻¹ E[x xᵀ] → Σ`, the normalized expected quadratic loss
`β⁻¹ E[½ xᵀ H x]` tends to `½ tr(Hᵀ Σ)` (`= ½ tr(H Σ)` for symmetric `H`). -/
theorem tendsto_quadLoss (H : Matrix (Fin d) (Fin d) ℝ) {β : ℕ → ℝ} {x : ℕ → Ω → E d}
    {Sig : Mat d} (hxL : ∀ k, MemLp (x k) 2 μ)
    (hlim : Tendsto (fun k => (β k)⁻¹ • secondMoment μ (x k)) atTop (𝓝 Sig)) :
    Tendsto (fun k => (β k)⁻¹ * ∫ ω, (1 / 2) * ∑ i, ∑ j, H i j * (x k ω i * x k ω j) ∂μ) atTop
      (𝓝 ((1 / 2) * quadPair H Sig)) := by
  have h := ((continuous_quadPair H).tendsto Sig).comp hlim
  have h2 := h.const_mul (1 / 2)
  refine h2.congr fun k => ?_
  simp only [Function.comp, quadPair_smul, integral_const_mul, integral_quadForm H (hxL k)]
  ring

/-! ### Duality -/

/-- **Proposition 3.4.** If `B Σ + Σ Bᵀ = Γ` and `Bᵀ K + K B = H`, then
`Σ_ij H_ij Σ_ij = Σ_ij K_ij Γ_ij`: the loss is a linear functional of the noise covariance. -/
theorem loss_duality (B K H : Matrix (Fin d) (Fin d) ℝ) (Sig : Mat d)
    (hK : ∀ i j, H i j = ∑ k, B k i * K k j + ∑ k, K i k * B k j) :
    quadPair H Sig = ∑ i, ∑ j, K i j * lyapOp B Sig (i, j) := by
  simp only [quadPair, hK, lyapOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, add_mul, mul_add, sum_add_distrib, sum_mul, mul_sum]
  congr 1
  · -- `Σ_ijk B_ki K_kj Σ_ij = Σ_ijk K_ij B_ik Σ_kj`
    calc ∑ i, ∑ j, ∑ k, B k i * K k j * Sig (i, j)
        = ∑ i, ∑ k, ∑ j, B k i * K k j * Sig (i, j) := sum_congr rfl fun i _ => sum_comm
      _ = ∑ k, ∑ i, ∑ j, B k i * K k j * Sig (i, j) := sum_comm
      _ = ∑ k, ∑ j, ∑ i, B k i * K k j * Sig (i, j) := sum_congr rfl fun k _ => sum_comm
      _ = _ := sum_congr rfl fun k _ => sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
  · -- `Σ_ijk K_ik B_kj Σ_ij = Σ_ijk K_ij Σ_ik B_jk`
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring

/-! ### The optimal-gain loss -/

/-- The optimal-gain loss `½ tr(H⁻ᵀ H_J H⁻¹ Γ)`. -/
noncomputable def optLoss (HJ Hinv Γ : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (1 / 2) * trace (Hinvᵀ * HJ * Hinv * Γ)

/-- `½ tr(H_J Σ*)` with `Σ* = H⁻¹ Γ H⁻ᵀ`. -/
lemma optLoss_eq_trace (HJ Hinv Γ : Matrix (Fin d) (Fin d) ℝ) :
    (1 / 2) * trace (HJ * (Hinv * Γ * Hinvᵀ)) = optLoss HJ Hinv Γ := by
  unfold optLoss
  congr 1
  rw [show HJ * (Hinv * Γ * Hinvᵀ) = (HJ * Hinv * Γ) * Hinvᵀ by simp only [Matrix.mul_assoc],
    trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- The trace of a positive semidefinite matrix is nonnegative. -/
lemma trace_nonneg_of_posSemidef {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef) :
    0 ≤ trace M := by
  unfold trace
  refine sum_nonneg fun i _ => ?_
  have := hM.2 (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using this

/-- `tr(K D) ≥ 0` for positive semidefinite `K` and `D`. -/
lemma trace_mul_nonneg_of_posSemidef {K D : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosSemidef)
    (hD : D.PosSemidef) : 0 ≤ trace (K * D) := by
  obtain ⟨B, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hK
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have := hD.mul_mul_conjTranspose_same B
  rw [Matrix.mul_assoc] at this
  exact trace_nonneg_of_posSemidef this

/-- **Proposition 3.5.** The optimal-gain loss is monotone in the noise covariance: if
`H_J ⪰ 0` and `Γ_A ⪯ Γ_B`, then `ℓ*(Γ_A) ≤ ℓ*(Γ_B)`. -/
theorem optLoss_mono {HJ Hinv ΓA ΓB : Matrix (Fin d) (Fin d) ℝ} (hHJ : HJ.PosSemidef)
    (hΓ : (ΓB - ΓA).PosSemidef) : optLoss HJ Hinv ΓA ≤ optLoss HJ Hinv ΓB := by
  have hK : (Hinvᵀ * HJ * Hinv).PosSemidef := by
    have := hHJ.conjTranspose_mul_mul_same Hinv
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have h := trace_mul_nonneg_of_posSemidef hK hΓ
  unfold optLoss
  rw [Matrix.mul_sub, trace_sub] at h
  linarith

end StochasticApproximation
