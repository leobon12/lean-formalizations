/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstCharts
import InteractingSLE.Spec.Sec6.DrivingArgLift

/-!
# Exact inherited incoming heights under an own Loewner stage

PROVE-POCKET-SIDEIN. The hydrodynamic derivative argument has zero limit at a
surviving original real point. Consequently R.5 germ preservation transports
the initial exact height through the actual frozen `Chart.loewner` lift.
No independent integer normalization of the new chart is made.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H chiC fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The initial inherited height remains exact after an own hydrodynamic
stage. The named inverse landing locates the surviving original side;
R.5 supplies the physical-mean difference limit. -/
theorem tendsto_exact_height_of_own_loewner {κ : ℝ} {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) {T x ξ : ℝ} (hT : 0 ≤ T) {a : ℝ → ℂ}
    (hSurvives : QuantumZipper.IsForwardSol W x T a)
    (hInverseLanding : Tendsto (fwdMapInv W T) (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)))
    {u vOld vNow : ℂ → ℝ} {b : ℝ}
    (hInitialHeight : Tendsto (sideMean κ c u vOld) (𝓝[H] (x : ℂ)) (𝓝 b))
    (hPhysicalGerm : Tendsto (fun z => vNow ((c.loewner W T).2.1 z) -
      vOld ((c.loewner W T).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0)) :
    Tendsto (sideMean κ (c.loewner W T) u vNow) (𝓝[H] (ξ : ℂ)) (𝓝 b) := by
  have harg := (Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hW hT hSurvives).comp
    hInverseLanding
  have hsum := (hPhysicalGerm.add (hInitialHeight.comp hInverseLanding)).add
    (harg.const_mul (chiC κ))
  simp only [zero_add, mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hInverseLanding.eventually self_mem_nhdsWithin] with z hz
  dsimp only [sideMean, Chart.loewner, Function.comp_def]
  rw [hc.2.2 _ hz]
  ring

end InteractingSLE.Sec7.PocketStopSide
