/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoLocallyFinite
import InteractingSLE.Spec.Supplement.GB9Cap

/-!
# Bounded chart images when the counterflow tip misses the flow line

The inverse chart sends infinity to the counterflow tip. GB9's general closure
lemma therefore bounds the chart image of any set whose closure misses that
tip. In particular the image of the entire proper flow arc outside the hull is
bounded whenever the tip is on its strict left side.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

variable {w : ℝ → ℝ} {β η : ℝ → ℂ} {s : ℝ}

/-- A set separated from the counterflow tip has bounded chart image. -/
theorem isBounded_revChart_image_of_notMem_closure (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) (hβs : β s ≠ 0)
    {A : Set ℂ} (hA : A ⊆ H \ cfHullQ w s)
    (htip : negInv (β s) ∉ closure A) : IsBounded (revChart w s '' A) := by
  by_contra hunb
  have hlim : Tendsto (revChartInv w s) (cobounded ℂ ⊓ 𝓟 H)
      (𝓝 (negInv (β s))) :=
    tendsto_revChartInv_tip hβ hw hw0 hs hβs
      (mem_inf_of_right (mem_principal_self H))
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
  have hAH : revChart w s '' A ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact revChart_mem_H hw hs (hA hz)
  have himg : revChartInv w s '' (revChart w s '' A) = A := by
    rw [image_image]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Function.comp_apply, revChartInv_revChart hw hw0 hs (hA hx)] using hx
    · intro hz
      exact ⟨z, hz, revChartInv_revChart hw hw0 hs (hA hz)⟩
  have h := Supp8.GB9Cap.mem_closure_image_of_tendsto_cobounded hlim hAH hunb
  rw [himg] at h
  exact htip h

/-- In a putative left-tip configuration all the flow excursions together have
bounded image in the counterflow chart, despite any number of hull contacts. -/
theorem isBounded_revChart_arcRange_of_mem_leftSideOf (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hL : negInv (β s) ∈ leftSideOf (arcRange η)) :
    IsBounded (revChart w s '' (arcRange η ∩ (H \ cfHullQ w s))) := by
  have hβs : β s ≠ 0 := by
    intro he
    have hz := ne_zero_of_mem_H hL.1.1
    exact hz (by rw [he]; simp only [negInv, inv_zero, neg_zero])
  refine isBounded_revChart_image_of_notMem_closure hβ hw hw0 hs hβs
    inter_subset_right ?_
  intro hcl
  exact hL.1.2 (hη.isClosed_arcRange.closure_eq ▸ closure_mono inter_subset_left hcl)

end InteractingSLE.Sec5.Prop51HTopo
