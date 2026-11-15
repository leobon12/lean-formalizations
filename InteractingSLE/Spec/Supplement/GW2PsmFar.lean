/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.SB2OmWord
import InteractingSLE.Spec.Supplement.Q3StopType

/-!
# GW2's open lines: the far-right height of the instance's typed data

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic):

* **`far_typed`**: on a type cell, the typed force data has the word's far-right height
  (`Q3Stop.isFlowType_typed`, `SB.Om.forceBoundaryData_eq_of_isFlowType`);
* **`farR_schedWordMapX`**: GEOM2's root-`x` word map has far-right height `λ'(16/κ) − πχ + θa χ` when the decoded
  root record's left mark is negative (`GW2Wm.farR_baseWordX`, `GW2Wm.farR_upW`).

With the kernel word's far-right height `λ'(16/κ) − πχ` (`GW2Wm.farR_jointWordOfRec`) this is the relation
`hK + θχ = hβ` of `GW2Psm.stage_step` when the current piece's angle is `θa`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist.StagedLaw Supp8.Q3Stop

/-- **The typed data has the word's far-right height.** -/
theorem far_typed {κ : ℝ} (hκ : 0 < κ) {w : WordType} {c : BoundaryWord} (hw : wordType κ c = w) {h : ℝ}
    (hfar : GW2Wm.FarR c h) :
    ∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet (typedXL κ w c) (typedXR κ w c) →
      forceBoundaryData κ (typedRhoL w) (typedRhoR w) (typedXL κ w c) (typedXR κ w c) y = h := by
  obtain ⟨B₀, hB₀⟩ := hfar
  have hft := isFlowType_typed hw
  refine ⟨max B₀ (∑ z ∈ c.jumps, |z|), fun y hy _ => ?_⟩
  have hy1 : B₀ < y := lt_of_le_of_lt (le_max_left _ _) hy
  have hy2 : ∑ z ∈ c.jumps, |z| < y := lt_of_le_of_lt (le_max_right _ _) hy
  have hyJ : y ∉ c.jumps := fun hyJ => by
    have := Finset.single_le_sum (f := fun z => |z|) (fun i _ => abs_nonneg i) hyJ
    have := le_abs_self y
    linarith
  have hy0 : y ≠ 0 := by
    have : 0 ≤ ∑ z ∈ c.jumps, |z| := Finset.sum_nonneg fun i _ => abs_nonneg i
    intro h0
    rw [h0] at hy2
    linarith
  rw [SB.Om.forceBoundaryData_eq_of_isFlowType hκ hft hy0 hyJ, hB₀ y hy1 hyJ, zero_mul, add_zero]

/-- **The far-right height of GEOM2's root-`x` word map.** -/
theorem farR_schedWordMapX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (N : ℕ) (hN : L.length = N) (θa : ℝ) (y : RecData)
    (hneg : markPosL (rdrv (GW2Wm.decHist N y).1) (rtime (GW2Wm.decHist N y).1) 0 < 0) :
    GW2Wm.FarR (GW2Wm.schedWordMapX κ c' x s L N hN θa y)
      (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ) :=
  GW2Wm.farR_upW _ (GW2Wm.farR_baseWordX hκ c' x s L N hN y hneg)

end InteractingSLE.Theorem14.GW2Psm
