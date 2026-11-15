/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceComponents
import InteractingSLE.Spec.Sec7.PocketReverseFieldsInf

/-!
# Local connectivity of an unbounded change pocket at finite points

PROVE-R7-GAPEQ. The bounded disc pocket is Jordan even when its physical image has
an infinite end. Transfer its local connectivity through the existing inverse charts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- The disc picture supplies local connectivity at every closed-pocket point,
including the flow seed. -/
theorem isLocConnWithin_discPocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) {w : ℂ}
    (hw : w ∈ closure (cayley '' changePocket R L r)) :
    IsLocConnWithin (cayley '' changePocket R L r) w := by
  obtain ⟨hJ, hball, hfr⟩ := h.cayleyChange_props
  exact R7LocalFace.isLocConnWithin_pocket
    (Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H)
    (Lemma71F.isConnected_cayley_image h.isConnected_changePocket h.changePocket_subset_H)
    (isBounded_ball.subset hball) (hfr ▸ hJ) hw

/-- An actual physical change pocket is locally connected from within at every
finite point of its closure. No exclusion of the flow seed from the closed pocket is
needed. -/
theorem isLocConnWithin_cfPocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) {z : ℂ} (hz : z ∈ closure (cfPocket R L r)) :
    IsLocConnWithin (cfPocket R L r) z := by
  have hzH : z ∈ Hbar := closure_image_negInv_subset_Hbar h.changePocket_subset_H hz
  have hdisc : ∀ w ∈ cayley '' changePocket R L r, w ≠ -1 := by
    intro w hw he
    have := h.cayleyChange_props.2.1 hw
    rw [he, mem_ball_zero_iff, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  apply R7GapEqFin.isLocConnWithin_of_inverse (f := cfPt) (g := fun w => -cayley w)
    (E := cayley '' changePocket R L r)
    (continuousOn_cfPt.mono hdisc) (continuousAt_cfPt (neg_cayley_ne_neg_one hzH))
    (continuousAt_neg_cayley hzH)
  · intro w hw
    rw [cfPocket, image_negInv_eq h.changePocket_subset_H]
    exact mem_image_of_mem cfPt hw
  · intro w hw
    rw [← image_neg_cayley_image_negInv h.changePocket_subset_H]
    exact mem_image_of_mem _ hw
  · intro w hw
    exact cfPt_neg_cayley (H_subset_Hbar' (PocketJordan.image_negInv_subset_H h.changePocket_subset_H hw))
  · exact cfPt_neg_cayley hzH
  · exact isLocConnWithin_discPocket h (neg_cayley_mem_closure h.changePocket_subset_H hz)

end InteractingSLE.Sec7.R7EndFace
