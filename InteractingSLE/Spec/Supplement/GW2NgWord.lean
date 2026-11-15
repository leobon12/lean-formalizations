/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2WmFar
import InteractingSLE.Spec.Supplement.GW2SdpHeight

/-!
# The stage word's premises of the far swallowing (D78)

Packet PROVE-GW2-NEARIMG2, decision D78. RELDET's `FlowSwallowStatement` (`GW2UbFlow`) asks, for the flow line of a
GFF with the data `b` of the stage word, a point `y > 0` and **total right weight `Σ flowLineRhoR κ b 0 0 < κ/2 − 2`**.
For the root-`x` stage word of the top's instances, `schedWordMapX κ c′ x s L N hN θa y` (the base stage word raised
by `θa χ`), this file proves:

* **`farR_schedWordMapX`**: its far-right height is `λ′ − πχ + θa χ` (the counterflow side, raised), as soon as the
  counterflow record of the past has positive extent on the left (`markPosL < 0` at the seed; part of `gb6TS`). This
  chains PROVE-GW2-GEOM2's `farR_jointWordOfRec`, `farR_shiftW`, `farR_stageWord`, `farR_upW`.
* **`sum_flowLineRhoR_schedWordMapX_lt`**: hence its total right weight is
  `cumWeightRight κ (λ′ − πχ + θa χ) = 3κ/4 − 3 + θa χ/λ`, which is `< κ/2 − 2` exactly when `θa < π/2`
  (`λ′ = λ − (π/2)χ`, `πχ = (2 − κ/2)λ`).
* `sum_flowLineRhoR_schedWordMapX_lt_of_mem`: the same for `θa ∈ (−π/2, π/2)` (the source's angle set).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Ni

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 GW2Wm

/-- **The far-right height of the instance's stage word**: `λ′ − πχ + θa χ` (the counterflow side, raised by the
current angle), when the past's counterflow record has positive extent on the left. -/
theorem farR_schedWordMapX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (N : ℕ) (hN : L.length = N) (θa : ℝ) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    FarR (schedWordMapX κ c' x s L N hN θa y) (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ) := by
  unfold schedWordMapX baseWordX
  refine farR_upW _ (farR_stageWord hκ (progAngle L)
    (A₀ := {r : RecData | markPosL (rdrv r) (rtime r) 0 < 0}) (fun r hr => ?_) N (stageDec x s L N hN y) ?_)
  · exact farR_shiftW _ (farR_jointWordOfRec hκ c' r hr)
  · rw [pastRoot_stageDec]
    exact hneg

/-- The right total weight at the counterflow side's raised height is `< κ/2 − 2` iff the angle is below `π/2`. -/
theorem cumWeightRight_far_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θa : ℝ} (hθ : θa < Real.pi / 2) :
    Sec4.cumWeightRight κ (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ + 0 * chiC κ) < κ / 2 - 2 := by
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have h2 := Sec4.pi_mul_chiC hκ
  unfold Sec4.cumWeightRight
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hl]
  have h3 : θa * chiC κ < Real.pi / 2 * chiC κ := mul_lt_mul_of_pos_right hθ hχ
  nlinarith

/-- **The stage word's total right weight is `< κ/2 − 2`** (the premise of `FlowSwallowStatement`), for an angle
`θa < π/2` and a past whose counterflow record has positive extent on the left. -/
theorem sum_flowLineRhoR_schedWordMapX_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c' : BoundaryWord) (x : ℝ)
    (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {θa : ℝ} (hθ : θa < Real.pi / 2) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    ∑ j, flowLineRhoR κ (schedWordMapX κ c' x s L N hN θa y).fn (schedWordMapX κ c' x s L N hN θa y).jumps 0 0 j <
      κ / 2 - 2 := by
  rw [sum_flowLineRhoR_of_farR hκ (farR_schedWordMapX hκ c' x s L N hN θa y hneg) 0]
  exact cumWeightRight_far_lt hκ hκ4 hθ

/-- The total-weight premise for an angle of the source's open angle range `(−π/2, π/2)`. -/
theorem sum_flowLineRhoR_schedWordMapX_lt_of_mem {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c' : BoundaryWord) (x : ℝ)
    (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {θa : ℝ}
    (hθ : θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    ∑ j, flowLineRhoR κ (schedWordMapX κ c' x s L N hN θa y).fn (schedWordMapX κ c' x s L N hN θa y).jumps 0 0 j <
      κ / 2 - 2 :=
  sum_flowLineRhoR_schedWordMapX_lt hκ hκ4 c' x s L N hN hθ.2 y hneg

end InteractingSLE.Theorem14.GW2Ni
