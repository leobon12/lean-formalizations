/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetClosedLate

/-!
# G8: closed separation reduced to real boundary contacts

Packet PROVE-G8-DET. The complete interior intersection and compactness
arguments are proved. The remaining assertion concerns only common real
boundary points of the two cut-chart closures and is explicitly unproved.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.RLC

/-- Exact remaining boundary assertion: arbitrarily late cuts have no
common real point in the two image-hull closures. No interior disjointness,
positive distance or boundary-mark order is assumed. This remains unproved. -/
def RealCutBoundaryNHStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q : ℝ),
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    (∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) → ∀ a₀ < σ, ∃ a ∈ Ioo a₀ σ,
      ∀ x : ℝ, (x : ℂ) ∈ closure (G8Det.cutObstacle α β a r) →
        (x : ℂ) ∉ closure (fwdHull (G8Det.cutDrive w a) ((σ : ℝ) - a))

/-- The only missing case of closed separation is the real boundary case.
All common closure points in `H` have already been excluded unconditionally. -/
theorem lateSeparationNHStatement_of_realBoundary (hR : RealCutBoundaryNHStatement) :
    LateSeparationNHStatement := by
  intro α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH a₀ ha₀
  obtain ⟨b, hb, hd⟩ := G8Det.Closed.exists_final_disjoint_images hcop hα0 hβ0 hw hw0 hgen ha₀
    hsw hq hασ hβH hβoff hsmall hNH
  obtain ⟨a, ha, hr⟩ := hR α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH b hb.2
  have hV : Continuous (G8Det.cutDrive w a) :=
    hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
  exact ⟨a, ⟨hb.1.trans ha.1, ha.2⟩,
    G8Det.Closed.disjoint_closures_of_real
      (G8Det.isHPHull_cutObstacle hcop.1 hcop.2.2.2.2.1 hα0 hβ0 a r)
      (isHPHull_fwdHull hV (sub_nonneg.2 (by exact_mod_cast ha.2.le))) (hd a ha) hr⟩

/-- Compactness gives an actual positive Euclidean gap at arbitrarily late
cuts once the remaining real-boundary case has been excluded. -/
theorem exists_late_positive_gap_of_realBoundary (hR : RealCutBoundaryNHStatement)
    {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r a₀ : ℝ≥0} {q : ℝ} (ha₀ : a₀ < σ)
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (hq : 1 < q) (hασ : α σ = q)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) :
    ∃ a ∈ Ioo a₀ σ, ∃ δ > 0, ∀ z ∈ closure (G8Det.cutObstacle α β a r),
      ∀ v ∈ closure (fwdHull (G8Det.cutDrive w a) ((σ : ℝ) - a)), δ ≤ dist z v := by
  obtain ⟨a, ha, hd⟩ := lateSeparationNHStatement_of_realBoundary hR α β w σ r q hcop hα0 hβ0
    hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH a₀ ha₀
  have hV : Continuous (G8Det.cutDrive w a) :=
    hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
  exact ⟨a, ha, G8Det.Closed.exists_positive_gap
    (G8Det.isHPHull_cutObstacle hcop.1 hcop.2.2.2.2.1 hα0 hβ0 a r)
    (isHPHull_fwdHull hV (sub_nonneg.2 (by exact_mod_cast ha.2.le))) hd⟩

theorem lateCutGeometryNHStatement_of_realBoundary (hR : RealCutBoundaryNHStatement) :
    LateCutGeometryNHStatement :=
  lateCutGeometryNHStatement_of_separation (lateSeparationNHStatement_of_realBoundary hR)

theorem g8RelativeChartNHStatement_of_realBoundary (hR : RealCutBoundaryNHStatement) :
    G8RelativeChartNHStatement :=
  g8RelativeChartNHStatement_of_separation (lateSeparationNHStatement_of_realBoundary hR)

theorem g8DetFrameNHStatement_of_realBoundary (hR : RealCutBoundaryNHStatement) :
    G8DetFrameNHStatement :=
  g8DetFrameNHStatement_of_separation (lateSeparationNHStatement_of_realBoundary hR)

theorem g8PositivityStatement_of_realBoundary (hW0b : Supp9.W0bStatement.{u})
    (hR : RealCutBoundaryNHStatement) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_separation hW0b (lateSeparationNHStatement_of_realBoundary hR)

end InteractingSLE.RLC
