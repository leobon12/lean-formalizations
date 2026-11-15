/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSepSides

/-!
# G8: reduction to closed image-hull separation alone

Packet PROVE-G8-DET. The two strict boundary inequalities are discharged
by the inverse-chart order theorem and real-flow monotonicity. Only closed
image-hull separation remains as an explicitly named, unproved planar input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.RLC

/-- The precise remaining planar assertion: arbitrarily late cuts separate
the two closed restriction hulls. No boundary order is included or assumed.
This assertion is not proved by the present module. -/
def LateSeparationNHStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q : ℝ),
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    (∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) → ∀ a₀ < σ, ∃ a ∈ Ioo a₀ σ,
      Disjoint (closure (G8Det.cutObstacle α β a r))
        (closure (fwdHull (G8Det.cutDrive w a) ((σ : ℝ) - a)))

/-- Separation alone gives both boundary inequalities; no order hypothesis
is retained from the previous continuation. -/
theorem lateSeparationOrderNHStatement_of_separation (hSep : LateSeparationNHStatement) :
    LateSeparationOrderNHStatement := by
  intro α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH a₀ ha₀
  obtain ⟨t₀, ht₀, hact⟩ := G8Det.exists_final_activity_of_nonneg_real hcop hα0 hβ0 hw hw0 hgen
    hsw hq hασ hsmall hβH hβoff (G8Det.nonneg_real_le_of_before hNH hq hασ)
  obtain ⟨a, ha, hd⟩ := hSep α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ
    hβH hβoff hsmall hNH (max a₀ t₀) (max_lt ha₀ ht₀)
  have hat : t₀ < a := (le_max_right _ _).trans_lt ha.1
  obtain ⟨haH, _, haD, hβD, hreal, h1D⟩ := hact a hat ha.2
  exact ⟨a, ⟨(le_max_left _ _).trans_lt ha.1, ha.2⟩, hd,
    G8Det.Late.boundary_order_of_clearance hcop hα0 hβ0 hw hw0 hgen ha.2 hsw hq hασ hβH hβoff hNH
      haH haD hβD hreal h1D hd⟩

theorem lateCutGeometryNHStatement_of_separation (hSep : LateSeparationNHStatement) :
    LateCutGeometryNHStatement :=
  lateCutGeometryNHStatement_of_separation_order (lateSeparationOrderNHStatement_of_separation hSep)

theorem g8RelativeChartNHStatement_of_separation (hSep : LateSeparationNHStatement) :
    G8RelativeChartNHStatement :=
  g8RelativeChartNHStatement_of_lateCutGeometry (lateCutGeometryNHStatement_of_separation hSep)

theorem g8DetFrameNHStatement_of_separation (hSep : LateSeparationNHStatement) :
    G8DetFrameNHStatement :=
  g8DetFrameNHStatement_of_lateCutGeometry (lateCutGeometryNHStatement_of_separation hSep)

theorem g8PositivityStatement_of_separation (hW0b : Supp9.W0bStatement.{u})
    (hSep : LateSeparationNHStatement) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_lateCutGeometry hW0b (lateCutGeometryNHStatement_of_separation hSep)

end InteractingSLE.RLC
