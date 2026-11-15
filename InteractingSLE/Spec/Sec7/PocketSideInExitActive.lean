/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitLanding

/-!
# The actual outgoing corner is active before a bounded pocket exits

PROVE-POCKET-SIDEIN. Reuse Aux. 40's already proved active earlier wall
prefix. Its initial point is the outgoing junction. The actual original
visit lies strictly before the junction's first visit.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketCoord PocketJordan PocketWordAssembly PocketMarks

/-- The outgoing junction belongs to the active ambient domain at every
interior pocket visit; Aux. 40 supplies the full unfilled-wall argument. -/
theorem outgoing_mem_active_of_reverse_pocket {W : ℝ → ℝ} {η : ℝ → ℂ}
    {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ t : ℝ}
    (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (ht : 0 ≤ t) (hvisit : η t ∈ C) :
    α₁ 0 ∈ H \ QuantumZipper.fwdHull W t := by
  have hp := hP.β_mem_domain ht (hP.mem_Ioo_of_mem ht hvisit).2
    (by simp : (0 : ℝ) ∈ Ici 0)
  rwa [hP.β_zero] at hp

/-- The bounded change-pocket outgoing physical corner is unfilled at an
actual visit, not merely unvisited by the trace. -/
theorem outgoing_mem_active_of_cfPocketConfig {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hc : IsCfPocketConfig R L r W η)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : η t ∈ cfPocket R L r) :
    cfPt (openPt R L r) ∈ H \ QuantumZipper.fwdHull W t := by
  have hP := hc.conf.isReversePocket_of_counterflow
    (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
    hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
  have hp := outgoing_mem_active_of_reverse_pocket hP ht hvisit
  rwa [PocketCoord.IsChangeConfigInc.cfArcR_zero] at hp

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketStopSide

variable {Ω : Type} [MeasurableSpace Ω]

/-- The physical outgoing corner of the bounded initial pocket. The
seed-opening case uses infinity instead, so this value is only used with
`j.infinite = false`. -/
def outgoingSeed (j : SideTest Ω) (d : WordObjects Ω) : Ω → ℂ :=
  fun ω => cfPt (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))

/-- Ready and an actual original visit prove that the bounded pocket's
outgoing corner is still active in the original ambient chart. -/
theorem outgoingSeed_mem_active_at_original_visit {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hBounded : j.infinite = false) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    j.outgoingSeed d ω ∈ H \ QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t := by
  rw [target_event] at hω
  rw [target_domain] at hvisit
  rcases hj with ⟨-, -, -, -, -, hcfg, -, -, hAG, -⟩
  simp only [hBounded, Bool.false_eq_true, ↓reduceIte] at hAG
  exact outgoing_mem_active_of_cfPocketConfig
    (hcfg ω (hAG hω).1 (hAG hω).2) ht hvisit

end InteractingSLE.Wire.Current.SideTest
