/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Source

/-!
# The original zero-time reference is the selected pocket exterior

PROVE-SIDE-COLLAR2. The equality holds on the whole sample space. It
therefore transports the actual local-set law, including its germ
record, rather than just comparing representatives on the test event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Wire.Current.SideTest

open WangWu Sec7 Sec7.SideC14 Sec7.PocketStopSide Sec7.PocketJordan

variable {Ω : Type} [MeasurableSpace Ω]

/-- The inverted original reference at time zero is literally the filled
exterior of the original selected change pocket, including off-event samples. -/
theorem original_initial_exterior_eq_selected (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) :
    (fun ω => negInv '' j.capacityReference i d 0 ω) =
      (fun ω => H \ selectedChangePocket j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) ω) := by
  classical
  rw [capacityReference, original_filling_zero, target_domain]
  funext ω
  by_cases hω : ω ∈ j.event
  · simp only [eventFilled, selectedChangePocket, hω, ↓reduceIte, Sec7.PocketUnionPt.extHullSet, union_empty]
    have he : H ∩ (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))ᶜ =
        H \ cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) := rfl
    rw [he, ← H_diff_image_negInv, cfPocket, image_negInv_image_negInv]
  · simp only [eventFilled, selectedChangePocket, hω, ↓reduceIte, sdiff_empty]
    exact isDomainChart_infinitySourceChart.image_eq

end InteractingSLE.Wire.Current.SideTest
