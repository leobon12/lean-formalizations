/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextNormalized
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceOn

/-! # The original window-null and E1 targets from pointwise capture

This fresh route uses the normalized source and component comparisons,
then excludes its countably many completed-capture subevents. It does not
require the stronger all-selected-index capture premise of the old cover
assembly, and it does not assert a new dyadic fibre-cover provider.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61Asm2 Aux61SlitWX Aux61Kernel Aux61ULoc LawUnique
universe u

/-- Translate actual source-window exclusion back to the original source
binders, preserving the small-gap and original-law quantifiers exactly. -/
theorem restartWindowNullQOn_of_source_exclusion
    (hnull : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, ¬ S.windowEvent p) :
    RestartWindowNullQOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP hf η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact hnull (sourceSetting t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha
    P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

variable (D : ∀ S : SourceSetting.{u}, R1Restart S)
  (h : ∀ S : SourceSetting.{u}, (D S).HasChart)
  (R : ∀ S : SourceSetting.{u}, ReaderFacts (D S))
  (hTip : ∀ S : SourceSetting.{u}, OwnTipForwardLimit S)
  (V : ∀ S : SourceSetting.{u}, WindowData (D S) (h S))
  (hExit : ∀ S : SourceSetting.{u}, PhysicalExit (D S) (h S))
  (C : ∀ S : SourceSetting.{u}, ∀ i, Aux61GPrime.ZeroComparisons
    (S.marksData (cutSource S (source (D S) (h S)))) i)
  (hneg : Aux61Cov.R5NegStatement.{u})
  (hcaptured_cover : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∃ i, Aux61GRec.completedCapture
      (S.marksData (cutSource S (source (D S) (h S)))) i p)
include D h R hTip V hExit C hneg hcaptured_cover

/-- The exact original window-null input from normalized source data and
pointwise completed capture. All remaining mathematics is explicit. -/
theorem restartWindowNullQOn_of_normalized_capture :
    RestartWindowNullQOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) :=
  restartWindowNullQOn_of_source_exclusion fun S =>
    ae_not_normalized_of_pointwise_capture (D S) (h S) (R S) (hTip S)
      (V S) (hExit S) (C S) hneg (hcaptured_cover S)

/-- E1 in target-component form, for every angle pair, using the source's
pointwise capture quantifiers. This conditional helper changes no source
declaration and requires neither old full-ball comparisons nor every-index
future completion. -/
theorem fwdNoEastCrosscutTgtQOn_of_normalized_capture
    (hreg : Prop51Q.CfLineRegularQStatement.{u}) :
    FwdNoEastCrosscutTgtQOn.{u} (fun _ _ _ => True) :=
  fwdNoEastCrosscutTgtQOn_of_window_smallGap hreg
    (restartWindowNullQOn_of_normalized_capture D h R hTip V hExit C hneg hcaptured_cover)

end InteractingSLE.Sec5.Aux61GCaptureNext
