/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WndNull
import InteractingSLE.Spec.Sec5.Aux61WndCapExit

/-!
# The normalized-capture fibre cover with `OwnTipForwardLimit` and `PhysicalExit` discharged (ruling R102)

Packet PROVE-AUX61-WINDOW. `Aux61Wnd.dyCover_of_normalized_capture` (R102's route for Theorems 1.2–1.3's fibre covers)
takes the restart data, `ReaderFacts`, `OwnTipForwardLimit`, `WindowData`, `PhysicalExit`, the component comparisons
and the existential capture. For the finite-buffer restriction `finiteRestrict` of arbitrary restart choices `C S`
(SLITW's `restrictChoices`, which keeps the normalized chart):

* the restart data and `HasChart` are R1CHART's `RestartChoices.toR1Restart` / `.hasChart`;
* `ReaderFacts` is SLITW's `Aux61SlitWZ.readers` (selection stays Borel, `selected_measurable_finiteRestrict`);
* `OwnTipForwardLimit` is SLITW's `Aux61SlitWY.ownTipForwardLimit`;
* `PhysicalExit` is `physicalExit_finiteRestrict`.

`dyCover_of_finiteRestrict_capture` therefore leaves exactly GLUEINST's `WindowData` and existential capture and
COMPARE's component comparisons, all for the restricted family. `ae_mem_finiteRestrict` states when an actual capturing
record survives the restriction (its normalized chart keeps the index's closed buffer off the pole).

R48: no Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61WndCap

open Aux61SlitW Aux61R1C Aux61Asm2 Aux61SlitWX

universe u

/-- The restart data of the finite-buffer restriction. -/
abbrev finiteRestart {S : SourceSetting.{u}} (C : RestartChoices S) : R1Restart S :=
  (Aux61SlitWAC.restrictChoices C (finiteRestrict C)).toR1Restart

/-- **The normalized-capture fibre cover on the finite-buffer restrictions**: `ReaderFacts`, `OwnTipForwardLimit` and
`PhysicalExit` are discharged; the remaining inputs are the window data, the component comparisons and the existential
capture of the restricted families. -/
theorem dyCover_of_finiteRestrict_capture (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S))
      (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)
    (Cm : ∀ S : SourceSetting.{u}, ∀ i, Aux61GPrime.ZeroComparisons
      (S.marksData (cutSource S (source (finiteRestart (C S))
        (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart))) i)
    (hcaptured_cover : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (cutSource S (source (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart))) i p) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  Aux61Wnd.dyCover_of_normalized_capture (fun S => finiteRestart (C S))
    (fun S => (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)
    (fun S => Aux61SlitWZ.readers _ (selected_measurable_finiteRestrict (C S) (hsel S)))
    (fun S => Aux61SlitWY.ownTipForwardLimit S) V
    (fun S => physicalExit_finiteRestrict (C S) (hsel S)) Cm hcaptured_cover

end InteractingSLE.Sec5.Aux61WndCap
