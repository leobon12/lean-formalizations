/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRealContact

/-!
# G8: real boundary separation and the deterministic frame

The remaining real-boundary assertion is proved from the source premises.
The continuous shifted trace and the upper-frontier inverse exclude its
real contacts; the committed interior separation completes the argument.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.RLC

/-- The last boundary case of the late-cut hull separation, with no additional
geometric hypothesis. Both endpoint prime ends are included. -/
theorem realCutBoundaryNHStatement : RealCutBoundaryNHStatement := by
  intro α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH a₀ ha₀
  obtain ⟨t₀, ht₀, hfuture⟩ := G8Det.exists_final_restart_domain hcop hα0 hβ0 hw hw0 hgen
    hsw hq hασ hsmall hβH hβoff hNH
  obtain ⟨b, hb, hd⟩ := G8Det.Closed.exists_final_disjoint_images hcop hα0 hβ0 hw hw0 hgen
    (max_lt ha₀ ht₀) hsw hq hασ hβH hβoff hsmall hNH
  obtain ⟨c, hc, hno⟩ := G8Det.Late.exists_late_no_new_contact hcop.1 hb.2 hq hασ hsmall
  obtain ⟨a, hca, haσ⟩ := exists_between hc.2
  have hba : b < a := hc.1.trans hca
  have hta : t₀ < a := (le_max_right a₀ t₀).trans_lt (hb.1.trans hba)
  refine ⟨a, ⟨(le_max_left a₀ t₀).trans_lt (hb.1.trans hba), haσ⟩, ?_⟩
  exact G8Det.RealBoundary.real_boundary_of_late_domain hcop.1 hcop.2.2.2.2.1 hcop.2.1 hβ0
    hw hw0 hgen haσ (hfuture a hta haσ).2.2.2.2
    (fun u hu => hno u ⟨hca.trans_le hu.1, hu.2⟩) (hd a ⟨hba, haσ⟩)

/-- Full separation of the two closed late-cut image hulls. -/
theorem lateSeparationNHStatement : LateSeparationNHStatement :=
  lateSeparationNHStatement_of_realBoundary realCutBoundaryNHStatement

/-- All late-cut geometry, including the strict boundary order. -/
theorem lateCutGeometryNHStatement : LateCutGeometryNHStatement :=
  lateCutGeometryNHStatement_of_realBoundary realCutBoundaryNHStatement

/-- Aux. 8's relative chain, clock and boundary-flow identifications. -/
theorem g8RelativeChartNHStatement : G8RelativeChartNHStatement :=
  g8RelativeChartNHStatement_of_realBoundary realCutBoundaryNHStatement

/-- R63's deterministic G8 frame, from the source hypotheses alone. -/
theorem g8DetFrameNHStatement : G8DetFrameNHStatement :=
  g8DetFrameNHStatement_of_realBoundary realCutBoundaryNHStatement

/-- Positivity now needs only the existing W0b input; no deterministic or
real-boundary input remains. -/
theorem g8PositivityStatement_of_w0b (hW0b : Supp9.W0bStatement.{u}) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_realBoundary hW0b realCutBoundaryNHStatement

/-- Lemma 7.5 supplies the existing probabilistic noncoincidence input. -/
theorem g8PositivityStatement_of_lemma75 (h75 : Theorem15.Lemma75Statement.{u}) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_w0b (Supp9.w0bStatement_of_lemma75 h75)

/-- The original G8 assembly inputs now require no deterministic frame input. -/
theorem g8FrameStatement_of_proved_det_inputs (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetHistStatement.{0}) : G8FrameStatement.{0} :=
  g8FrameStatement_of_nh_inputs h75 href h12p h13 hD g8DetFrameNHStatement

end InteractingSLE.RLC
