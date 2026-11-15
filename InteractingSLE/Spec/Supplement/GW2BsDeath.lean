/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsContact
import InteractingSLE.Spec.Supplement.GW2BnBridge

/-!
# The cell exit fires before the death; the outermost near labels are controlled

Packet PROVE-GW2-BUF (round 16; step C). At a death of the candidate, its stage word `β` has a continuation threshold
along the stage path, in the form of `GW2Rz.NoThresholdX`. That is the death input: the maximality `ζ = T_*` of the
candidate's lifetime (`IsIntegratedSLEPath`, Theorem 1.3) read in the stage chart. Through the presentation, the
threshold is one of the near family's word along the comparison path (`cmp_threshold_of_stage`). So the cell exit
fires strictly before it (`cellStop_lt_of_threshold`):

* **`cellStop_lt_of_stage_threshold`**.

SDE's pinned shape puts the far-block cut below the outermost index on both sides. In the upper structure the
outermost left label is `≤ −3` (`NearStructTop.xm`). In the lower one the outermost right label is `≥ 3`
(`NearStructBot.xp`):

* `cutL_le`, `cutR_le`, **`outer_ctrl_of_nearShape`**: `f.mL ≤ f.nL − 1` and `f.mR ≤ f.nR − 1`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist.StagedLaw MartChar.RealFlow Sec5.CrossCond.StagedRepLater GW2TipSystem
  GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach GW2Sdo GW2Sdy

section Cell

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ)
  {y : RecData}

/-- **The cell exit fires strictly before a threshold of the stage word along the stage path.** -/
theorem cellStop_lt_of_stage_threshold (hsh : famShapeB f = (cell y).1)
    (hL : ∀ i : Fin f.nL, f.xL i = posL y i) (hR : ∀ j : Fin f.nR, f.xR j = posR y j)
    {β : BoundaryWord} {scale c : ℝ≥0} (hc : 0 < c) (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) (m : ℕ)
    (hP : GW2Sdf.PresentsO κ β scale flip f.xL (f.ρLs m) f.xR (f.ρRs m)) {cap : ℝ≥0} (hcap : 0 < cap)
    {D : ℝ≥0 → ℝ} (hD : Continuous D)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) D) 0 ∈
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    (u : ℝ≥0)
    (hthr : ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
      (fun i => -rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) u)
      (fun j => rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) u)) :
    cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, D) < u :=
  cellStop_lt_of_threshold f cell posL posR hsh hL hR (pow_pos hc 2) _ hcap hD h0 m
    (cmp_threshold_of_stage hc hsc flip hP hD u hthr)

end Cell

/-! ### The outermost near labels are controlled -/

theorem cutL_le (β : BoundaryWord)
    (hxm : flowLineXL β.fn β.jumps 0 (GW2TipStage.lastL β.fn β.jumps) ≤ -3) :
    cutL β ≤ flowLineNL β.fn β.jumps 0 - 1 := by
  unfold cutL
  have hsub : (univ.filter fun i : Fin (flowLineNL β.fn β.jumps 0) => -3 < flowLineXL β.fn β.jumps 0 i) ⊆
      univ.erase (GW2TipStage.lastL β.fn β.jumps) := by
    intro i hi
    rw [Finset.mem_erase]
    refine ⟨fun h => ?_, Finset.mem_univ _⟩
    rw [h] at hi
    exact absurd (Finset.mem_filter.1 hi).2 (not_lt.2 hxm)
  calc _ ≤ (univ.erase (GW2TipStage.lastL β.fn β.jumps)).card := Finset.card_le_card hsub
    _ = flowLineNL β.fn β.jumps 0 - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ,
        Fintype.card_fin]

theorem cutR_le (β : BoundaryWord)
    (hxp : 3 ≤ flowLineXR β.fn β.jumps 0 (GW2TipStage.lastR β.fn β.jumps)) :
    cutR β ≤ flowLineNR β.fn β.jumps 0 - 1 := by
  unfold cutR
  have hsub : (univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) => flowLineXR β.fn β.jumps 0 j < 3) ⊆
      univ.erase (GW2TipStage.lastR β.fn β.jumps) := by
    intro j hj
    rw [Finset.mem_erase]
    refine ⟨fun h => ?_, Finset.mem_univ _⟩
    rw [h] at hj
    exact absurd (Finset.mem_filter.1 hj).2 (not_lt.2 hxp)
  calc _ ≤ (univ.erase (GW2TipStage.lastR β.fn β.jumps)).card := Finset.card_le_card hsub
    _ = flowLineNR β.fn β.jumps 0 - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ,
        Fintype.card_fin]

/-- **The outermost near labels are controlled** for a family with SDE's pinned shape. -/
theorem outer_ctrl_of_nearShape {κ : ℝ} {f : NearCrossingFamily.{u} κ} {s : ℝ≥0} {flip : Bool} {c : BoundaryWord}
    (hsh : famShapeB f = nearShape κ s flip c) (hst : NearStruct κ s flip c) :
    f.mL ≤ f.nL - 1 ∧ f.mR ≤ f.nR - 1 := by
  unfold nearShape at hsh
  split_ifs at hsh with htop
  · simp only [famShapeB, Prod.mk.injEq] at hsh
    obtain ⟨h1, h2, h3, h4, -⟩ := hsh
    refine ⟨?_, ?_⟩
    · rw [h1, h3]; exact cutL_le _ htop.xm
    · rw [h2, h4]
  · simp only [famShapeB, Prod.mk.injEq] at hsh
    obtain ⟨h1, h2, h3, h4, -⟩ := hsh
    have hbot : NearStructBot κ s flip c := hst.resolve_left htop
    refine ⟨?_, ?_⟩
    · rw [h1, h3]
    · rw [h2, h4]; exact cutR_le _ hbot.xp

end InteractingSLE.Theorem14.GW2Bh
