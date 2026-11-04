/-
SPDX-License-Identifier: MIT
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Calculus rules for `HasGradientAt`

Mathlib states most calculus rules for `HasFDerivAt` only. These are the corresponding
rules for real-valued functions on a real Hilbert space, phrased with gradients.
-/

open InnerProductSpace
open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f g : F → ℝ} {f' g' x : F}

namespace HasGradientAt

lemma add' (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
  HasGradientAt (fun y => f y + g y) (f' + g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.add hg using 1
  ext v
  simp

lemma sub' (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
  HasGradientAt (fun y => f y - g y) (f' - g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.sub hg using 1
  ext v
  simp

lemma mul' (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
  HasGradientAt (fun y => f y * g y) (f x • g' + g x • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.mul hg using 1
  ext v
  simp

lemma const_mul' (c : ℝ) (hf : HasGradientAt f f' x) :
  HasGradientAt (fun y => c * f y) (c • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.const_mul c using 1
  ext v
  simp

lemma mul_const' (c : ℝ) (hf : HasGradientAt f f' x) :
  HasGradientAt (fun y => f y * c) (c • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.mul_const c using 1
  ext v
  simp

lemma sum' {ι : Type*} {u : Finset ι} {A : ι → F → ℝ} {A' : ι → F}
  (h : ∀ i ∈ u, HasGradientAt (A i) (A' i) x) :
  HasGradientAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert HasFDerivAt.fun_sum (fun i hi => (h i hi).hasFDerivAt) using 1
  ext v
  simp

lemma log' (hf : HasGradientAt f f' x) (hx : f x ≠ 0) :
  HasGradientAt (fun y => Real.log (f y)) ((f x)⁻¹ • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.log hx using 1
  ext v
  simp

lemma exp' (hf : HasGradientAt f f' x) :
  HasGradientAt (fun y => Real.exp (f y)) (Real.exp (f x) • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert hf.exp using 1
  ext v
  simp

end HasGradientAt

lemma hasGradientAt_inner_const (v x : F) :
  HasGradientAt (fun y => ⟪y, v⟫) v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have : (fun y => ⟪y, v⟫) = innerSL ℝ v := by
    ext y
    simp [real_inner_comm]
  rw [this]
  convert (innerSL ℝ v).hasFDerivAt using 1
