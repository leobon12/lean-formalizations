/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Frame

/-!
# R90's normalized initial side offset

PROVE-SIDE-COLLAR2. The internal side data take their offset from the
initial source frame. Keep the source branch and the global inversion
constant explicitly. No arbitrary caller offset is retained.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Wire

open Current

/-- The common offset obtained by transporting the original flow frame. -/
def sourceFrameOffset (κ b : ℝ) (n : ℤ) : ℝ :=
  b + 2 * π * chiC κ * (1 - (n : ℝ))

/-- R90: overwrite the side's internal offset with the initial frame's. -/
def normalizeInitialOffset {Ω : Type} (side : SideTest Ω → Late.SideData Ω)
    (a : SideTest Ω → ℝ) : SideTest Ω → Late.SideData Ω :=
  fun j => {side j with offset := a j}

@[simp] theorem normalizeInitialOffset_offset {Ω : Type}
    (side : SideTest Ω → Late.SideData Ω) (a : SideTest Ω → ℝ) (j : SideTest Ω) :
    (normalizeInitialOffset side a j).offset = a j := rfl

/-- Installing the source-frame offset proves the branch-compatibility
identity literally. This is the normalized version authorized by R90. -/
theorem normalizeInitialOffset_branch {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (b : SideTest Ω → ℝ) (n : SideTest Ω → ℤ) :
    ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure,
      ω ∈ (j.target i d).event →
        (normalizeInitialOffset side (fun j => sourceFrameOffset (16 / i.kappa) (b j) (n j)) j).offset =
          b j + 2 * π * chiC (16 / i.kappa) * (1 - (n j : ℝ)) :=
  fun _ _ => ae_of_all _ fun _ _ => rfl

/-- A proved frame transfers to side data normalized to its own offset.
The analytic side fields do not enter the initial frame predicate. -/
theorem InitialPocketFlowFrame.normalize_offset {Ω : Type} [MeasurableSpace Ω]
    {i : BothLow} {d : WordObjects Ω} {frameSide : SideTest Ω → Late.SideData Ω}
    {G : SideTest Ω → Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ}
    (h : InitialPocketFlowFrame i d frameSide G M)
    (side : SideTest Ω → Late.SideData Ω) :
    InitialPocketFlowFrame i d (normalizeInitialOffset side (fun j => (frameSide j).offset)) G M := h

end InteractingSLE.Wire
