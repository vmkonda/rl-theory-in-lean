/-
SPDX-License-Identifier: MIT
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Bounded and Lipschitz functions

Real-constant versions of boundedness and Lipschitz continuity, with closure under the
algebraic operations used to show that policy gradients are Lipschitz. The Lipschitz
predicate `IsLip` matches the `∃ C, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖` form used
throughout the project.
-/

open Finset
open scoped RealInnerProductSpace

namespace RLTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- `f` is Lipschitz with some real constant. -/
def IsLip (f : E → F) : Prop := ∃ C, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖

/-- `f` is bounded in norm. -/
def IsBdd (f : E → F) : Prop := ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C

namespace IsLip

lemma const (c : F) : IsLip fun _ : E => c := ⟨0, le_rfl, fun x y => by simp⟩

lemma add {f g : E → F} (hf : IsLip f) (hg : IsLip g) : IsLip fun x => f x + g x := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, by positivity, fun x y => ?_⟩
  calc ‖f x + g x - (f y + g y)‖ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; abel
    _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ (A + B) * ‖x - y‖ := by linarith [hf x y, hg x y]

lemma neg {f : E → F} (hf : IsLip f) : IsLip fun x => -f x := by
  obtain ⟨A, hA, hf⟩ := hf
  exact ⟨A, hA, fun x y => by rw [← norm_neg]; simpa [add_comm, sub_eq_add_neg] using hf x y⟩

lemma sub {f g : E → F} (hf : IsLip f) (hg : IsLip g) : IsLip fun x => f x - g x := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma sum {ι : Type*} (u : Finset ι) {f : ι → E → F} (hf : ∀ i ∈ u, IsLip (f i)) :
  IsLip fun x => ∑ i ∈ u, f i x := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using const (E := E) (0 : F)
  | insert i u hi ih =>
    simp only [sum_insert hi]
    exact (hf i (mem_insert_self i u)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

lemma comp_of_eq {f g : E → F} (hf : IsLip f) (h : f = g) : IsLip g := h ▸ hf

variable [NormedSpace ℝ F]

lemma const_smul (c : ℝ) {f : E → F} (hf : IsLip f) : IsLip fun x => c • f x := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨|c| * A, by positivity, fun x y => ?_⟩
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)

/-- Product of a bounded Lipschitz scalar function and a bounded Lipschitz function. -/
lemma smul {f : E → ℝ} {g : E → F} (hf : IsLip f) (hfb : IsBdd f) (hg : IsLip g)
  (hgb : IsBdd g) : IsLip fun x => f x • g x := by
  obtain ⟨Kf, hKf, hf⟩ := hf
  obtain ⟨A, hA, hfb⟩ := hfb
  obtain ⟨Kg, hKg, hg⟩ := hg
  obtain ⟨B, hB, hgb⟩ := hgb
  refine ⟨A * Kg + B * Kf, by positivity, fun x y => ?_⟩
  have : f x • g x - f y • g y = f x • (g x - g y) + (f x - f y) • g y := by
    rw [smul_sub, sub_smul]; abel
  rw [this]
  calc ‖f x • (g x - g y) + (f x - f y) • g y‖
      ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ A * (Kg * ‖x - y‖) + (Kf * ‖x - y‖) * B := by
        gcongr
        · exact hfb x
        · exact hg x y
        · exact hf x y
        · exact hgb y
    _ = (A * Kg + B * Kf) * ‖x - y‖ := by ring

lemma mul {f g : E → ℝ} (hf : IsLip f) (hfb : IsBdd f) (hg : IsLip g) (hgb : IsBdd g) :
  IsLip fun x => f x * g x := by
  simpa [smul_eq_mul] using hf.smul hfb hg hgb

/-- A function whose gradient is bounded by `C` is `C`-Lipschitz. -/
lemma of_hasGradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {f : E → ℝ} {f' : E → E} (hf : ∀ x, HasGradientAt f (f' x) x)
  {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f' x‖ ≤ C) : IsLip f := by
  refine ⟨C, hC, fun x y => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := f) (f' := fun x => InnerProductSpace.toDual ℝ E (f' x))
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt)
    (fun z _ => by simpa using hb z) (Set.mem_univ y) (Set.mem_univ x)
  exact this

end IsLip

lemma IsLip.lipschitzWith {f : E → F} (hf : IsLip f) : ∃ K : NNReal, LipschitzWith K f := by
  obtain ⟨C, hC, hf⟩ := hf
  exact ⟨⟨C, hC⟩, LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm] using hf x y⟩

namespace IsBdd

omit [NormedAddCommGroup E] in
lemma const (c : F) : IsBdd fun _ : E => c := ⟨‖c‖, norm_nonneg _, fun _ => le_rfl⟩

omit [NormedAddCommGroup E] in
lemma add {f g : E → F} (hf : IsBdd f) (hg : IsBdd g) : IsBdd fun x => f x + g x := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  exact ⟨A + B, by positivity, fun x => (norm_add_le _ _).trans (add_le_add (hf x) (hg x))⟩

omit [NormedAddCommGroup E] in
lemma sub {f g : E → F} (hf : IsBdd f) (hg : IsBdd g) : IsBdd fun x => f x - g x := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  exact ⟨A + B, by positivity, fun x => (norm_sub_le _ _).trans (add_le_add (hf x) (hg x))⟩

omit [NormedAddCommGroup E] in
lemma sum {ι : Type*} (u : Finset ι) {f : ι → E → F} (hf : ∀ i ∈ u, IsBdd (f i)) :
  IsBdd fun x => ∑ i ∈ u, f i x := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using const (E := E) (0 : F)
  | insert i u hi ih =>
    simp only [sum_insert hi]
    exact (hf i (mem_insert_self i u)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

variable [NormedSpace ℝ F]

omit [NormedAddCommGroup E] in
lemma smul {f : E → ℝ} {g : E → F} (hf : IsBdd f) (hg : IsBdd g) :
  IsBdd fun x => f x • g x := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A * B, by positivity, fun x => ?_⟩
  rw [norm_smul]
  exact mul_le_mul (hf x) (hg x) (norm_nonneg _) hA

omit [NormedAddCommGroup E] in
lemma const_smul (c : ℝ) {f : E → F} (hf : IsBdd f) : IsBdd fun x => c • f x :=
  (const (E := E) c).smul hf

omit [NormedAddCommGroup E] in
lemma mul {f g : E → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd fun x => f x * g x := by
  simpa [smul_eq_mul] using hf.smul hg

end IsBdd

end RLTheory
