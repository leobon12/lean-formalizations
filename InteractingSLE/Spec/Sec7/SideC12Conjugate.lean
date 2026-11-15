/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Physical
import InteractingSLE.Spec.Sec7.SideC11Normalize

/-!
# The flow chart conjugate to the initial counterflow chart

PROVE-SIDE-COLLAR2. Retain the sum of the three derivative lifts and the
source branch integer. The centering and the two inversion lifts cancel
with the exact residual common offset. No branch integer is set to zero.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open scoped Real

namespace InteractingSLE.Sec7.SideC12

open WangWu (negInv)
open PocketStopSide

/-- The original flow coordinate obtained by conjugating the given
counterflow coordinate through the global inversion on both sides. -/
def conjugateFlowMap (c : Chart) (y : ℂ) : ℂ :=
  negInv (c.1 (negInv y))

/-- The chain-rule sum of the two inversion lifts and the given pocket
lift. Its common source branch remains a separate integer. -/
def conjugateFlowLift (c : Chart) (y : ℂ) : ℝ :=
  infinitySourceChart.2.2 (c.1 (negInv y)) + c.2.2 (negInv y) + infinitySourceChart.2.2 y

/-- Transport of the original flow identity gives the actual frame
identity with the exact offset `b + 2πχ(1 - n)`. -/
theorem frame_identity_of_conjugate_flow {κ : ℝ} (hκ : 0 < κ)
    (c : Chart) (M V : ℂ → ℝ) (n : ℤ) (b : ℝ) (z : ℂ)
    (hFlow : V (negInv z) = M (conjugateFlowMap c (negInv z)) -
      chiC κ * (conjugateFlowLift c (negInv z) + 2 * π * (n : ℝ)) + b) :
    (-V (negInv z) + sourceShift (-(π * chiC κ)) (chiC (16 / κ)) 0 z) +
        chiC (16 / κ) * c.2.2 z =
      centeredReversedMean κ M (c.1 z) - (b + 2 * π * chiC κ * (1 - (n : ℝ))) := by
  simp only [conjugateFlowMap, conjugateFlowLift, WangWu.negInv_negInv] at hFlow
  rw [hFlow, sourceShift, Sec4.chiC_sixteen_div hκ]
  simp only [centeredReversedMean, coordChange, StripSysField.infinitySourceChart_lift,
    sub_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat, log_im]
  change _ = - (M (negInv (c.1 z)) - chiC κ * _) - π * chiC κ - _
  ring

end InteractingSLE.Sec7.SideC12
