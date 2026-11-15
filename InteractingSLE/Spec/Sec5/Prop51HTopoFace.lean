/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopo
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# The outer face of the chart-Q excursion set

The outer face is constructed as the unbounded component outside the closed
chart image of the proper flow arc. Its inverse image is preconnected, avoids
the whole flow arc, and has the counterflow tip in its closure. Consequently a
single point of this face on the physical right side suffices for no-wrap.
These facts include all filled hull contacts; the right-side witness still
requires the excursion orientation argument.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- The flow arc visible in the counterflow chart. -/
def chartFlowSet (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Set ℂ :=
  revChart w s '' (arcRange η ∩ (H \ cfHullQ w s))

/-- The face incident to infinity in the counterflow chart. -/
def outerChartFace (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Set ℂ :=
  H \ fillH (chartFlowSet η w s)

/-- Its physical realization under the inverse counterflow chart. -/
def physicalOuterFace (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Set ℂ :=
  revChartInv w s '' outerChartFace η w s

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-- The outer face is the actual selected component outside the closed
excursion image, with an explicit far-away base point. -/
theorem exists_outerChartFace_eq_component
    (hb : IsBounded (chartFlowSet η w s)) :
    ∃ R : ℝ, 0 < R ∧ closure (chartFlowSet η w s) ⊆ ball 0 R ∧
      outerChartFace η w s = connectedComponentIn
        (H \ closure (chartFlowSet η w s)) (((R + 1 : ℝ) : ℂ) * I) := by
  obtain ⟨R, hR, hsub⟩ := exists_closure_subset_ball hb
  exact ⟨R, hR, hsub, H_diff_fillH hR hsub⟩

theorem isPreconnected_outerChartFace (hb : IsBounded (chartFlowSet η w s)) :
    IsPreconnected (outerChartFace η w s) := by
  obtain ⟨R, _, _, heq⟩ := exists_outerChartFace_eq_component hb
  rw [heq]
  exact isPreconnected_connectedComponentIn

theorem isOpen_outerChartFace (hb : IsBounded (chartFlowSet η w s)) :
    IsOpen (outerChartFace η w s) := isOpen_H_diff_fillH hb

/-- The inverse face avoids the entire physical arc, even its portions inside
the filled counterflow hull. -/
theorem physicalOuterFace_subset (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) : physicalOuterFace η w s ⊆ H \ arcRange η := by
  rintro _ ⟨z, hz, rfl⟩
  have hmem := revChartInv_mem hw hw0 hs hz.1
  refine ⟨hmem.1, fun hA => hz.2 ?_⟩
  exact ⟨hz.1, Or.inl (subset_closure
    ⟨revChartInv w s z, ⟨hA, hmem⟩, revChart_revChartInv hw hw0 hs hz.1⟩)⟩

theorem isPreconnected_physicalOuterFace (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hb : IsBounded (chartFlowSet η w s)) :
    IsPreconnected (physicalOuterFace η w s) :=
  (isPreconnected_outerChartFace hb).image _
    ((continuousOn_revChartInv hw hw0 hs).mono sdiff_subset)

/-- The physical outer face approaches the actual counterflow tip. -/
theorem tip_mem_closure_physicalOuterFace (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) (hβs : β s ≠ 0)
    (hb : IsBounded (chartFlowSet η w s)) :
    negInv (β s) ∈ closure (physicalOuterFace η w s) := by
  obtain ⟨R, hR, hsub⟩ := exists_closure_subset_ball hb
  let z : ℕ → ℂ := fun n => (((R + (n : ℝ) + 1) : ℝ) : ℂ) * I
  have hzH : ∀ n, z n ∈ H := by
    intro n
    show 0 < (z n).im
    simpa only [z, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
      mul_zero, add_zero] using (by positivity : 0 < R + (n : ℝ) + 1)
  have hznorm : ∀ n, ‖z n‖ = R + (n : ℝ) + 1 := by
    intro n
    simp only [z, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hzF : ∀ n, z n ∈ outerChartFace η w s := by
    intro n
    refine ⟨hzH n, fun hfill => ?_⟩
    have hlt := mem_ball_zero_iff.1 (fillH_subset_ball hR hsub hfill)
    rw [hznorm] at hlt
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hlt, hn]
  have hzlim : Tendsto (fun n => ‖z n‖) atTop atTop := by
    simp only [hznorm]
    exact tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ R tendsto_natCast_atTop_atTop)
  exact mem_closure_of_tendsto
    (tendsto_revChartInv_tip hβ hw hw0 hs hβs (Eventually.of_forall hzH) hzlim)
    (Eventually.of_forall fun n => ⟨z n, hzF n, rfl⟩)

end InteractingSLE.Sec5.Prop51HTopo
