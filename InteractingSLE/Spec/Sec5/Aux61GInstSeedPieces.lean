/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstBoundaryMeas

/-! # Measurable seed collars from the recorded inverse and old boundary -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory

namespace InteractingSLE.Sec5.Aux61GInst

open scoped Classical in
def seedDistance {X : Type*} (E : Set X) (F : X → ℝ → ℂ) (C : X → Set ℂ) (x : X) (a : ℝ) : ℝ :=
  if x ∈ E then infDist (F x a) (C x) else 0

/-- A countable family of measurable pieces with a fixed free real collar.
The boundary set and inverse coordinate are read only from the history. -/
theorem exists_measurable_seedPieces {X : Type*} [MeasurableSpace X]
    {E : Set X} (hE : MeasurableSet E) {F : X → ℝ → ℂ} {C : X → Set ℂ}
    (hFm : ∀ a, Measurable (E.indicator fun x => F x a))
    (hFc : ∀ x ∈ E, Continuous (F x))
    (hCm : ∀ z, Measurable (E.indicator fun x => infDist z (C x)))
    (hCc : ∀ x ∈ E, IsClosed (C x)) (hCne : ∀ x ∈ E, (C x).Nonempty)
    (hgap : ∀ x ∈ E, ∃ δ > 0, ∀ a : ℝ, |a| < δ → F x a ∉ C x) :
    ∃ S : ℕ × ℕ → Set X, (∀ p, MeasurableSet (S p)) ∧ E = ⋃ p, S p ∧
      (∀ p, S p ⊆ E) ∧
      ∀ p x, x ∈ S p → ∀ a : ℝ, |a| ≤ collarRadius p.1 → F x a ∉ C x := by
  classical
  let g := seedDistance E F C
  have hDm : Measurable (Function.uncurry fun (z : ℂ) (x : X) =>
      E.indicator (fun x => infDist z (C x)) x) :=
    measurable_uncurry_of_continuous_of_measurable (fun x => by
      by_cases hx : x ∈ E
      · simpa only [indicator_of_mem hx] using continuous_infDist_pt (C x)
      · simpa only [indicator_of_notMem hx] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))) hCm
  have hgm : ∀ a, Measurable (fun x => g x a) := by
    intro a
    have hm := hDm.comp ((hFm a).prodMk measurable_id)
    convert hm using 1
    funext x
    by_cases hx : x ∈ E <;> simp [g, seedDistance, hx]
  have hgc : ∀ x ∈ E, Continuous (g x) := by
    intro x hx
    have he : g x = fun a => infDist (F x a) (C x) := funext fun a => by simp [g, seedDistance, hx]
    rw [he]
    exact (continuous_infDist_pt (C x)).comp (hFc x hx)
  have hg0 : ∀ x ∈ E, ∃ δ > 0, ∀ a : ℝ, |a| < δ → 0 < g x a := by
    intro x hx
    obtain ⟨δ, hδ, hfree⟩ := hgap x hx
    refine ⟨δ, hδ, fun a ha => ?_⟩
    change (if x ∈ E then infDist (F x a) (C x) else 0) > 0
    rw [if_pos hx]
    exact ((hCc x hx).notMem_iff_infDist_pos (hCne x hx)).1 (hfree a ha)
  refine ⟨fun p => collarPiece E g p.1 p.2,
    fun p => measurableSet_collarPiece hE hgm hgc p.1 p.2,
    collarPieces_cover hgc hg0, fun _ _ hx => hx.1, ?_⟩
  intro p x hx a ha hm
  have hp := positive_on_collarPiece hx ha
  have he : g x a = 0 := by simp [g, seedDistance, hx.1, infDist_zero_of_mem hm]
  exact hp.ne' he

end InteractingSLE.Sec5.Aux61GInst
