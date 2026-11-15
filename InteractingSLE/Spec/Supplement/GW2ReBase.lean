/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T14GdBase

/-!
# Alive histories are guarded (D75, option (G))

PROVE-GW2-ROOTX round 15. ASSEMBLE7's guard `Wire.T14Gd.Guard c r l` (strictly ordered history, root `0` or in
`lowerArcRoots`) holds at every history alive in J32 (NOTHR's strict order
`RootJ32.pairwise_lt_historyProgram_of_alive`;
the root cases from the seed condition of the cover event, `GW2Omx.rootPt_cases_of_seedOK`). The guarded copies of
ROOTX's package chains (`GW2Re*`) take the record-event identity `E₀ = (launchBadRec)ᶜ` only on guarded histories and
supply the guard by **`guard_of_alive32`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.GW2Re

open GW2TipSystem GW2TipSystem.RootC24

/-- **A history alive in J32 is guarded.** -/
theorem guard_of_alive32 {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) {ω : Ω}
    (h : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l) : Wire.T14Gd.Guard c r l :=
  ⟨RootJ32.pairwise_lt_historyProgram_of_alive c r l ω h,
    GW2Omx.rootPt_cases_of_seedOK c r (RootJ32.alive_spec c r l ω h).1.1⟩

end InteractingSLE.Theorem14.GW2Re
