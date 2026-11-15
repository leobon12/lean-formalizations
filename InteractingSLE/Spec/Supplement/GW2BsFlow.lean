/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsCmp
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Restart.RetAux79Zone
import InteractingSLE.Spec.Supplement.GW2BlLink

/-!
# The labels of the stage word are bounded by the flowed root junctions

Packet PROVE-GW2-BUF (round 16; step A of the label identification). GEOM2's base word is the root word flowed
through the restarts of the relative driver `R` at the stage boundaries `b` (`GW2Wm.baseWordX_augRecX`):
`stageWord W₀ θ N (pastOf cf R b N)`. A stop word moves the right marks of the old flow-line word by `markPos` and
its left marks by `markPosL` (`mem_jumps_stopWord`). The new seed mark is `0`. `markPos = rightImg − driver` is
monotone in the mark, and the images flow (`rightImg_shiftDrv`). By induction:

* **`stageWord_jump_le`**: every positive jump of the stage word after `n` restarts is at most
  `rightImg R xR (b n) − R (b n)`, where `xR ≥ 0` bounds the positive jumps of the root word;
* **`stageWord_jump_ge`**: every negative jump is at least `−rightImg (−R) (−xL) (b n) − R (b n)`, where `xL ≤ 0`
  bounds the negative jumps of the root word from below;
* `rdrv_stage_eq`, `rtime_stage` (the restarted records), `markPos_stage_eq`, `markPosL_stage_eq`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist.StagedLaw MartChar.RealFlow Sec5.Prop59NodeTree Sec5.CrossCond.Gen Sec5.CrossCond.StagedFinal
  GW2TipSystem

/-! ### The restarted stage records -/

theorem rtime_stage (f : ℝ≥0 → ℝ) (T : ℝ≥0) : rtime (recOf (T : ℝ≥0∞) (f, ⊤)) = T := by
  rw [rtime_recOf_coe]
  simp

/-- The recorded driver of a restart is the restarted real path, up to the record's time. -/
theorem rdrv_stage_eq {R : ℝ≥0 → ℝ} (hR : Continuous R) (S T : ℝ≥0) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) T) :
    rdrv (recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R S u, ⊤)) v = shiftDrv (rp R) S v := by
  have hv0 : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal _ hv.1
  have hvT : v.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hv.2
  rw [← hv0, Gm.rdrv_recOf_eq (Gm.isRegularDriver_top (GW2Rd.continuous_stgDrv hR S) (GW2Rd.stgDrv_zero R S))
    (by simp) (by simpa using (GW2Rd.continuous_stgDrv hR S).continuousOn)]
  have hmin : min v.toNNReal (min (T : ℝ≥0∞) (⊤ : ℝ≥0∞)).toNNReal = v.toNNReal := by
    rw [min_eq_left le_top, ENNReal.toNNReal_coe, min_eq_left hvT]
  show GW2Rd.stgDrv R S (min v.toNNReal (min (T : ℝ≥0∞) (⊤ : ℝ≥0∞)).toNNReal) = _
  rw [hmin]
  simp only [GW2Rd.stgDrv, shiftDrv, rp, Real.toNNReal_coe]
  congr 2
  apply NNReal.eq
  rw [NNReal.coe_add, hv0]
  exact (Real.coe_toNNReal _ (add_nonneg S.coe_nonneg hv.1)).symm

/-- **The right mark of a restart**: the flowed image, relative to the driver, at the end of the restart. -/
theorem markPos_stage_eq {R : ℝ≥0 → ℝ} (hR : Continuous R) (S T : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    markPos (rdrv (recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R S u, ⊤)))
        (rtime (recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R S u, ⊤))) x =
      rightImg (shiftDrv (rp R) S) x T - shiftDrv (rp R) S T := by
  rw [rtime_stage, markPos_eq_rightImg_of_nonneg (continuous_rdrv _) (rdrv_zero _) T.coe_nonneg hx]
  have hc := continuous_shiftDrv (continuous_rp hR) (S : ℝ)
  rw [Supp8.GB6.rightImg_congr hc T.coe_nonneg fun v hv => rdrv_stage_eq hR S T hv,
    rdrv_stage_eq hR S T ⟨T.coe_nonneg, le_rfl⟩]

/-- **The left mark of a restart.** -/
theorem markPosL_stage_eq {R : ℝ≥0 → ℝ} (hR : Continuous R) (S T : ℝ≥0) {x : ℝ} (hx : x ≤ 0) :
    markPosL (rdrv (recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R S u, ⊤)))
        (rtime (recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R S u, ⊤))) x =
      -rightImg (fun v => -shiftDrv (rp R) S v) (-x) T - shiftDrv (rp R) S T := by
  rw [rtime_stage, markPosL_eq_rightImg_of_nonpos (continuous_rdrv _) (rdrv_zero _) T.coe_nonneg hx]
  have hc := (continuous_shiftDrv (continuous_rp hR) (S : ℝ)).neg
  rw [Supp8.GB6.rightImg_congr (w' := fun v => -shiftDrv (rp R) S v) hc T.coe_nonneg
      fun v hv => by simp only [rdrv_stage_eq hR S T hv],
    rdrv_stage_eq hR S T ⟨T.coe_nonneg, le_rfl⟩]

theorem markPosL_nonpos {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t x : ℝ} (ht : 0 ≤ t) (hx : x ≤ 0) :
    markPosL w t x ≤ 0 := by
  rw [markPosL_eq_rightImg_of_nonpos hw hw0 ht hx]
  have := le_rightImg (w := fun s => -w s) hw.neg (-x) ht
  linarith

theorem markPos_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ markPos w t x := by
  rw [markPos_eq_rightImg_of_nonneg hw hw0 ht hx]
  have := le_rightImg hw x ht
  linarith

/-! ### The label bounds through the restarts -/

section Flow

variable {κ : ℝ} (W₀ : RecData → BoundaryWord) (θ : ℕ → ℝ) (cf : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R)
  (hR0 : R 0 = 0) {b : ℕ → ℝ≥0} (hb : Monotone b) (hb0 : b 0 = 0)

include hR hR0 hb hb0 in
/-- **Every positive jump of the stage word is at most the flowed right root bound.** -/
theorem stageWord_jump_le {xR : ℝ} (hxR : 0 ≤ xR) (h₀ : ∀ y ∈ (W₀ cf).jumps, 0 < y → y ≤ xR) :
    ∀ n : ℕ, ∀ y ∈ (GW2JDetR5.stageWord (κ := κ) W₀ θ n (GW2Wm.pastOf cf R b n)).jumps, 0 < y →
      y ≤ rightImg (rp R) xR (b n) - rp R (b n) := by
  have hU := continuous_rp hR
  intro n
  induction n with
  | zero =>
    intro y hy hy0
    have hz : rightImg (rp R) xR ((b 0 : ℝ≥0) : ℝ) - rp R ((b 0 : ℝ≥0) : ℝ) = xR := by
      rw [hb0, NNReal.coe_zero, rightImg_zero hU (by simp [rp, hR0]) hxR]
      simp [rp, hR0]
    rw [hz]
    exact h₀ y hy hy0
  | succ n ih =>
    intro y hy hy0
    set T : ℝ≥0 := b (n + 1) - b n with hT
    have hbT : (b n : ℝ) + T = b (n + 1) := by
      rw [hT, NNReal.coe_sub (hb (Nat.le_succ n))]
      ring
    have hzn : 0 ≤ rightImg (rp R) xR (b n) - rp R (b n) := by
      have := le_rightImg hU xR (b n).coe_nonneg
      linarith
    change y ∈ (stopWord κ (GW2JDetR5.stageWord (κ := κ) W₀ θ n (GW2Wm.pastOf cf R b n), θ n,
      recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))).jumps at hy
    rcases mem_jumps_stopWord hy with ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
    · exact absurd hy0 (not_lt.2 (markPosL_nonpos (continuous_rdrv _) (rdrv_zero _)
        (by rw [rtime_stage]; exact T.coe_nonneg) (GW3Word.flowLineXL_nonpos _ _ i)))
    · exact absurd hy0 (lt_irrefl 0)
    · have hx0 := GW3Word.flowLineXR_nonneg _ _ j
      have hxz : flowLineXR _ _ 0 j ≤ rightImg (rp R) xR (b n) - rp R (b n) := by
        rcases RetAux79.flowLineXR_eq_zero_or_mem _ j with h | ⟨hpos, hmem⟩
        · rw [h]; exact hzn
        · exact ih _ hmem hpos
      rw [markPos_stage_eq hR (b n) T hx0]
      have hmono := rightImg_mono_index (continuous_shiftDrv hU (b n : ℝ)) T.coe_nonneg hxz
      rw [rightImg_shiftDrv hU (b n).coe_nonneg T.coe_nonneg xR, hbT] at hmono
      have hsh : shiftDrv (rp R) (b n) T = rp R (b (n + 1)) - rp R (b n) := by
        simp only [shiftDrv, hbT]
      rw [hsh]
      linarith

include hR hR0 hb hb0 in
/-- **Every negative jump of the stage word is at least the flowed left root bound.** -/
theorem stageWord_jump_ge {xL : ℝ} (hxL : xL ≤ 0) (h₀ : ∀ y ∈ (W₀ cf).jumps, y < 0 → xL ≤ y) :
    ∀ n : ℕ, ∀ y ∈ (GW2JDetR5.stageWord (κ := κ) W₀ θ n (GW2Wm.pastOf cf R b n)).jumps, y < 0 →
      -rightImg (fun v => -rp R v) (-xL) (b n) - rp R (b n) ≤ y := by
  have hU := continuous_rp hR
  have hU' : Continuous fun v => -rp R v := hU.neg
  intro n
  induction n with
  | zero =>
    intro y hy hy0
    have hz : -rightImg (fun v => -rp R v) (-xL) ((b 0 : ℝ≥0) : ℝ) - rp R ((b 0 : ℝ≥0) : ℝ) = xL := by
      rw [hb0, NNReal.coe_zero, rightImg_zero hU' (by simp [rp, hR0]) (neg_nonneg.2 hxL)]
      simp [rp, hR0]
    rw [hz]
    exact h₀ y hy hy0
  | succ n ih =>
    intro y hy hy0
    set T : ℝ≥0 := b (n + 1) - b n with hT
    have hbT : (b n : ℝ) + T = b (n + 1) := by
      rw [hT, NNReal.coe_sub (hb (Nat.le_succ n))]
      ring
    have hzn : -rightImg (fun v => -rp R v) (-xL) (b n) - rp R (b n) ≤ 0 := by
      have : -rp R (b n) ≤ rightImg (fun v => -rp R v) (-xL) (b n) := le_rightImg hU' (-xL) (b n).coe_nonneg
      linarith
    change y ∈ (stopWord κ (GW2JDetR5.stageWord (κ := κ) W₀ θ n (GW2Wm.pastOf cf R b n), θ n,
      recOf (T : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))).jumps at hy
    rcases mem_jumps_stopWord hy with ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
    · have hx0 := GW3Word.flowLineXL_nonpos _ _ i
      have hxz : -rightImg (fun v => -rp R v) (-xL) (b n) - rp R (b n) ≤ flowLineXL _ _ 0 i := by
        rcases RetAux79.flowLineXL_eq_zero_or_mem _ i with h | ⟨hneg, hmem⟩
        · rw [h]; exact hzn
        · exact ih _ hmem hneg
      rw [markPosL_stage_eq hR (b n) T hx0]
      -- the left images flow along the negated driver
      have hneg : (fun v => -shiftDrv (rp R) (b n) v) = shiftDrv (fun v => -rp R v) (b n) := by
        funext v
        simp only [shiftDrv]
        ring
      have hxz' : -flowLineXL _ _ 0 i ≤ rightImg (fun v => -rp R v) (-xL) (b n) - (-rp R (b n)) := by
        linarith
      have hmono := rightImg_mono_index (continuous_shiftDrv hU' (b n : ℝ)) T.coe_nonneg hxz'
      rw [rightImg_shiftDrv hU' (b n).coe_nonneg T.coe_nonneg (-xL), hbT] at hmono
      rw [hneg]
      have hsh : shiftDrv (rp R) (b n) T = rp R (b (n + 1)) - rp R (b n) := by
        simp only [shiftDrv, hbT]
      rw [hsh]
      linarith
    · exact absurd hy0 (lt_irrefl 0)
    · exact absurd hy0 (not_lt.2 (markPos_nonneg (continuous_rdrv _) (rdrv_zero _)
        (by rw [rtime_stage]; exact T.coe_nonneg) (GW3Word.flowLineXR_nonneg _ _ j)))

end Flow

end InteractingSLE.Theorem14.GW2Bh
