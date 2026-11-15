/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXBoundary

/-!
# The precise deterministic theorem sufficient for the remaining tip input

The unresolved step is the full forward limit at the endpoint of a simple
slit. This file names that exact theorem and proves its source-law adapter.
It does not assert the theorem or replace it by an inverse-access limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW
universe u

/-- The remaining deterministic simple-slit endpoint theorem. -/
def SimpleTipForwardLimit : Prop :=
  ∀ {W : ℝ → ℝ} {η : ℝ → ℂ}, Continuous W → W 0 = 0 → IsLoewnerTrace W η →
    WangWu.IsProperArc η → ∀ r : ℝ≥0, 0 < r →
      Tendsto (fwdMap W r) (𝓝[H \ fwdHull W r] (η r)) (𝓝[H] 0)

/-- All probabilistic hypotheses of the forward-tip input are discharged
by the actual source flow; only the deterministic theorem remains. -/
theorem ownTipForwardLimit_of_simpleTip (hTip : SimpleTipForwardLimit)
    (S : SourceSetting.{u}) : OwnTipForwardLimit S := by
  filter_upwards [S.physical_path] with p hp r hr
  have ht := hTip (W := fun t : ℝ => S.own.W t.toNNReal p.1)
    (η := fun t : ℝ => S.path p.1 t.toNNReal) hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2 r hr
  simpa only [Real.toNNReal_coe] using ht

end InteractingSLE.Sec5.Aux61SlitWX
