/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BlContact
import InteractingSLE.Spec.Supplement.GW2BkCol
import InteractingSLE.Spec.Supplement.GW2RdStgChain
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# The near exit fires before a relative collision, and before contact under the contact clause

Packet PROVE-GW2-BUF (round 9). The near comparison path is the stage path `stgDrv R S` (the relative driver `R`
restarted at the stage start `S`), scaled to `s ↦ b · stgDrv R S (s / b²)` (`scaledPath (b²) b`). Its image state at
comparison time `b² u` reads the real-time driver `scD b (shiftDrv R S)`:

* **`rightImg_frozen_cmp`**: the right images of the comparison path are those of `scD b (shiftDrv R S)`;
* **`imgState_right_gap_eq`**: the gap of a comparison right label `b (rightImg R x S − R S)` at comparison time
  `b² u` is `b` times the relative gap of `x` at `S + u`;
* **`exitRule_lt_of_relCollision`**: if that label is gap-controlled by the buffer, the near exit rule fires strictly
  before a relative collision of `x` at `S + u` (with `GW2BlCol.rightImg_eq_of_real_tip`, the before-contact chain);
* **`exitRule_lt_of_gapVanishes`**: under the contact clause `GapVanishes` (decision D17), the near exit rule fires
  strictly before the relative life `L`, in stage time below `L − S`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw MartChar.RealFlow Sec5.Prop59NodeTree Sec5.CrossCond.StagedRepLater Supp12 Supp12.DSReach
  GW2Rd

variable {nL nR : ℕ}

/-- The real-time driver of a path on `ℝ≥0`. -/
abbrev rp (R : ℝ≥0 → ℝ) : ℝ → ℝ := fun r => R r.toNNReal

theorem continuous_rp {R : ℝ≥0 → ℝ} (hR : Continuous R) : Continuous (rp R) := hR.comp continuous_real_toNNReal

theorem continuous_scD_shiftDrv {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ) (b : ℝ) :
    Continuous (scD b (shiftDrv (rp R) S)) :=
  continuous_const.mul ((continuous_shiftDrv (continuous_rp hR) S).comp (continuous_id.div_const _))

/-- **The comparison path's frozen driver agrees with the scaled restarted relative driver up to `v`.** -/
theorem frozenDrive_cmp_eq {R : ℝ≥0 → ℝ} (S : ℝ≥0) {b : ℝ≥0} (hb : 0 < b) (v : ℝ≥0) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) v) :
    frozenDrive (scaledPath (b ^ 2) b (stgDrv R S)) v r = scD b (shiftDrv (rp R) S) r := by
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  unfold frozenDrive scaledPath stgDrv scD shiftDrv rp
  rw [min_eq_left hr.2]
  congr 2
  · congr 1
    apply NNReal.eq
    rw [NNReal.coe_add, NNReal.coe_div, Real.coe_toNNReal _ (add_nonneg S.coe_nonneg (div_nonneg hr.1 hb2.le)),
      Real.coe_toNNReal _ hr.1, NNReal.coe_pow]
  · rw [Real.toNNReal_coe]

/-- **The right images of the comparison path** are those of the scaled restarted relative driver. -/
theorem rightImg_frozen_cmp {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ≥0) {b : ℝ≥0} (hb : 0 < b) (v : ℝ≥0)
    (x' : ℝ) : rightImg (frozenDrive (scaledPath (b ^ 2) b (stgDrv R S)) v) x' v =
      rightImg (scD b (shiftDrv (rp R) S)) x' v :=
  Supp8.GB6.rightImg_congr (continuous_scD_shiftDrv hR S b) v.coe_nonneg fun _ hr =>
    frozenDrive_cmp_eq S hb v hr

/-- **The comparison right gap is the scaled relative gap.** -/
theorem imgState_right_gap_eq (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ≥0)
    {b : ℝ≥0} (hb : 0 < b) (u : ℝ≥0) {j : Fin nR} {x : ℝ}
    (hxj : xR j = (b : ℝ) * (rightImg (rp R) x S - rp R S)) :
    (GW2Sdg.imgState xL xR (scaledPath (b ^ 2) b (stgDrv R S)) (b ^ 2 * u)).2.2 j -
        (GW2Sdg.imgState xL xR (scaledPath (b ^ 2) b (stgDrv R S)) (b ^ 2 * u)).1 =
      (b : ℝ) * (rightImg (rp R) x (S + u) - rp R (S + u)) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  change rightImg (frozenDrive (scaledPath (b ^ 2) b (stgDrv R S)) ((b ^ 2 * u : ℝ≥0) : ℝ)) (xR j)
      ((b ^ 2 * u : ℝ≥0) : ℝ) - scaledPath (b ^ 2) b (stgDrv R S) (b ^ 2 * u) = _
  rw [rightImg_frozen_cmp hR S hb, hxj]
  have hfr : scaledPath (b ^ 2) b (stgDrv R S) (b ^ 2 * u) = scD b (shiftDrv (rp R) S) ((b : ℝ) ^ 2 * u) := by
    have h := frozenDrive_cmp_eq (R := R) S hb (b ^ 2 * u) (r := ((b ^ 2 * u : ℝ≥0) : ℝ))
      ⟨by positivity, le_rfl⟩
    unfold frozenDrive at h
    rw [min_self, Real.toNNReal_coe] at h
    rw [h]
    push_cast
    rfl
  rw [hfr]
  push_cast
  have h := gap_cmp_eq (continuous_rp hR) S.coe_nonneg hb' x u.coe_nonneg
  have hrp : rp R ((S : ℝ) + u) = rp R (S + u : ℝ≥0) := by simp only [rp, NNReal.coe_add]
  rw [h, hrp]

/-- **The near exit fires strictly before a relative collision** of a label whose comparison image is
gap-controlled by the buffer. -/
theorem exitRule_lt_of_relCollision (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {mL mR : ℕ} {Rb g : ℝ} (hg : 0 < g)
    (hB : IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p})
    (hBc : ({p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p}ᶜ).Nonempty)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ≥0) {b : ℝ≥0} (hb : 0 < b) {c : ℝ≥0} (hc : 0 < c) (y : RecData)
    (h0 : InBuffer mL mR Rb g (GW2Sdg.imgState xL xR (scaledPath (b ^ 2) b (stgDrv R S)) 0)) {u : ℝ≥0}
    (huc : u ≤ c) {j : Fin nR} (hj : mR ≤ (j : ℕ)) {x : ℝ} (hxj : xR j = (b : ℝ) * (rightImg (rp R) x S - rp R S))
    (hcol : rightImg (rp R) x (S + u) = rp R (S + u)) :
    exitRule xL xR {p | InBuffer mL mR Rb g p} (b ^ 2) b c (y, stgDrv R S) < u := by
  have hwc : Continuous (stgDrv R S) := (hR.comp (continuous_const.add continuous_id)).sub continuous_const
  refine exitRule_lt_of_rightCollision xL xR hg hB hBc (by positivity) (b : ℝ) hc y hwc h0 huc hj ?_
  have h := imgState_right_gap_eq xL xR hR S hb u hxj
  rw [hcol, sub_self, mul_zero] at h
  linarith

/-- **Under the contact clause, the near exit fires strictly before the relative life**, in stage time `< L − S`. -/
theorem exitRule_lt_of_gapVanishes (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {mL mR : ℕ} {Rb g : ℝ} (hg : 0 < g)
    (hB : IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p})
    (hBc : ({p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p}ᶜ).Nonempty)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ≥0) {b : ℝ≥0} (hb : 0 < b) {c : ℝ≥0} (hc : 0 < c) (y : RecData)
    (h0 : InBuffer mL mR Rb g (GW2Sdg.imgState xL xR (scaledPath (b ^ 2) b (stgDrv R S)) 0))
    {j : Fin nR} (hj : mR ≤ (j : ℕ)) {x : ℝ} (hxj : xR j = (b : ℝ) * (rightImg (rp R) x S - rp R S)) {L : ℝ}
    (hSL : (S : ℝ) < L) (hvan : GapVanishes (rp R) x L) :
    exitRule xL xR {p | InBuffer mL mR Rb g p} (b ^ 2) b c (y, stgDrv R S) < ENNReal.ofReal (L - S) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hwc : Continuous (stgDrv R S) := (hR.comp (continuous_const.add continuous_id)).sub continuous_const
  -- the initial comparison gap is above the level
  have hgap0 := imgState_right_gap_eq xL xR hR S hb 0 hxj
  simp only [mul_zero, NNReal.coe_zero, add_zero] at hgap0
  have hinit : g < rightImg (scD b (shiftDrv (rp R) S)) (b * (rightImg (rp R) x S - rp R S)) (b ^ 2 * 0) -
      scD b (shiftDrv (rp R) S) (b ^ 2 * 0) := by
    rw [gap_cmp_eq (continuous_rp hR) S.coe_nonneg hb' x le_rfl, add_zero, ← hgap0]
    exact h0.2.1 j hj
  obtain ⟨u, hu0, huL, hug⟩ :=
    exists_cmp_gap_eq_before (continuous_rp hR) hvan S.coe_nonneg hSL hb' hg hinit
  -- the comparison state is outside the buffer at stage time `u`
  set u' : ℝ≥0 := u.toNNReal with hu'def
  have hu'r : (u' : ℝ) = u := Real.coe_toNNReal _ hu0.le
  have hout : ¬ InBuffer mL mR Rb g (GW2Sdg.imgState xL xR (scaledPath (b ^ 2) b (stgDrv R S)) (b ^ 2 * u')) := by
    intro hin
    have h1 := hin.2.1 j hj
    rw [imgState_right_gap_eq xL xR hR S hb u' hxj] at h1
    have h2 := gap_cmp_eq (continuous_rp hR) S.coe_nonneg hb' x u'.coe_nonneg
    rw [hu'r] at h2
    have h3 : (b : ℝ) * (rightImg (rp R) x (S + u') - rp R (S + u')) =
        (b : ℝ) * (rightImg (rp R) x (S + u) - rp R (S + u)) := by
      simp only [rp, hu'r]
    rw [h3, ← h2, hug] at h1
    exact lt_irrefl _ h1
  obtain ⟨τ, hτe, -, hτc, -⟩ := exitRule_spec xL xR hB hBc (b ^ 2) b hc y hwc h0
  have hLS : (u' : ℝ≥0∞) < ENNReal.ofReal (L - S) := by
    rw [← ENNReal.ofReal_coe_nnreal, hu'r]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  by_cases huc : u' ≤ c
  · exact (exitRule_le_of_notMem xL xR hB hBc (b ^ 2) b hc y hwc h0 huc hout).trans_lt hLS
  · rw [hτe]
    exact (ENNReal.coe_le_coe.2 (hτc.trans (le_of_lt (not_le.1 huc)))).trans_lt hLS

end InteractingSLE.Theorem14.GW2Bh
