/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsFlow

/-!
# The comparison gaps are the scaled stage gaps; small stage gaps before `L'` force the exit before `L'`

Packet PROVE-GW2-BUF (round 16). On the comparison path `scaledPath (c²) (ε c) D` (`ε = ±1` the orientation), the
gap of a family label `x` at comparison time `c² u` is `c` times the gap of the stage label `x / c` along the
oriented real-time stage path `ε D` at stage time `u` (`rightImg_scale`):

* **`cmpGapR_eq`**, **`cmpGapL_eq`**;
* **`cellStop_lt_of_stageGap`**: if, for every `δ > 0`, some controlled label's stage gap is below `δ` at a stage
  time before `L'`, the cell exit fires strictly before `L'`;
* **`stageGapR_le`**, **`stageGapL_le`**: along the stage path `D = stgDrv R S`, the gap of a stage label below the
  flowed right root bound `rightImg R xR S − R S` is at most the relative gap of `xR` at `S + u`. On the left it is
  at most the mirrored relative gap. The contact clause (`GapVanishes`) makes these small before the relative life.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist.StagedLaw MartChar.RealFlow Sec5.Prop59NodeTree Sec5.CrossCond.StagedRepLater GW2TipSystem
  GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

variable {nL nR : ℕ}

/-- **The comparison right gap is the scaled stage right gap.** -/
theorem cmpGapR_eq (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {c : ℝ≥0} (hc : 0 < c) (ε : ℝ) {D : ℝ≥0 → ℝ}
    (hD : Continuous D) (u : ℝ≥0) (j : Fin nR) :
    (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (ε * c) D) (c ^ 2 * u)).2.2 j -
        (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (ε * c) D) (c ^ 2 * u)).1 =
      c * (rightImg (fun q => ε * D q.toNNReal) (xR j / c) u - ε * D u) := by
  rw [imgState_scaledPath_eq xL xR hc ε hD u]
  have hc' : (0 : ℝ) < c := hc
  have hG : Continuous fun q : ℝ => ε * D q.toNNReal := continuous_const.mul (hD.comp continuous_real_toNNReal)
  have h1 : rightImg (scD c (fun q => ε * D q.toNNReal)) (xR j) ((c : ℝ) ^ 2 * u) =
      c * rightImg (fun q => ε * D q.toNNReal) (xR j / c) u := by
    have := rightImg_scale hG hc' (xR j / c) u.coe_nonneg
    rwa [mul_div_cancel₀ _ hc'.ne'] at this
  have h2 : scD c (fun q => ε * D q.toNNReal) ((c : ℝ) ^ 2 * u) = c * (ε * D u) := by
    simp only [scD]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hc'.ne'), Real.toNNReal_coe]
  show rightImg (scD c (fun q => ε * D q.toNNReal)) (xR j) ((c : ℝ) ^ 2 * u) -
    scD c (fun q => ε * D q.toNNReal) ((c : ℝ) ^ 2 * u) = _
  rw [h1, h2]
  ring

/-- **The comparison left gap is the scaled stage left gap.** -/
theorem cmpGapL_eq (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {c : ℝ≥0} (hc : 0 < c) (ε : ℝ) {D : ℝ≥0 → ℝ}
    (hD : Continuous D) (u : ℝ≥0) (i : Fin nL) :
    (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (ε * c) D) (c ^ 2 * u)).1 -
        (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (ε * c) D) (c ^ 2 * u)).2.1 i =
      c * (ε * D u + rightImg (fun q => -(ε * D q.toNNReal)) (-(xL i / c)) u) := by
  rw [imgState_scaledPath_eq xL xR hc ε hD u]
  have hc' : (0 : ℝ) < c := hc
  have hG : Continuous fun q : ℝ => -(ε * D q.toNNReal) :=
    (continuous_const.mul (hD.comp continuous_real_toNNReal)).neg
  have hneg : (fun v => -scD c (fun q => ε * D q.toNNReal) v) = scD c (fun q => -(ε * D q.toNNReal)) := by
    funext v
    simp only [scD]
    ring
  have h1 : rightImg (fun v => -scD c (fun q => ε * D q.toNNReal) v) (-xL i) ((c : ℝ) ^ 2 * u) =
      c * rightImg (fun q => -(ε * D q.toNNReal)) (-(xL i / c)) u := by
    rw [hneg]
    have := rightImg_scale hG hc' (-(xL i / c)) u.coe_nonneg
    rwa [show (c : ℝ) * -(xL i / c) = -xL i by field_simp] at this
  have h2 : scD c (fun q => ε * D q.toNNReal) ((c : ℝ) ^ 2 * u) = c * (ε * D u) := by
    simp only [scD]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hc'.ne'), Real.toNNReal_coe]
  show scD c (fun q => ε * D q.toNNReal) ((c : ℝ) ^ 2 * u) -
    -rightImg (fun v => -scD c (fun q => ε * D q.toNNReal) v) (-xL i) ((c : ℝ) ^ 2 * u) = _
  rw [h1, h2]
  ring

section Cell

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ)
  {y : RecData}

/-- **Small controlled stage gaps before `L'` force the cell exit before `L'`.** -/
theorem cellStop_lt_of_stageGap (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) {c : ℝ≥0} (hc : 0 < c) (ε : ℝ) {cap : ℝ≥0} (hcap : 0 < cap)
    {D : ℝ≥0 → ℝ} (hD : Continuous D)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c ^ 2) (ε * c) D) 0 ∈
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {L' : ℝ≥0∞}
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ u : ℝ≥0, (u : ℝ≥0∞) < L' ∧
      ((∃ j : Fin f.nR, f.mR ≤ (j : ℕ) ∧ rightImg (fun q => ε * D q.toNNReal) (f.xR j / c) u - ε * D u < δ) ∨
        ∃ i : Fin f.nL, f.mL ≤ (i : ℕ) ∧
          ε * D u + rightImg (fun q => -(ε * D q.toNNReal)) (-(f.xL i / c)) u < δ)) :
    cellStop cell posL posR (c ^ 2) (ε * c) cap (y, D) < L' := by
  have hc' : (0 : ℝ) < c := hc
  obtain ⟨u, hu, hgap⟩ := hsmall (((1 / 2 : ℝ) ^ (cell y).2.2) / c) (by positivity)
  refine cellStop_lt_of_gap_le f cell posL posR hsh hL hR (c ^ 2) (ε * c) hcap hD h0 hu ?_
  rcases hgap with ⟨j, hj, hlt⟩ | ⟨i, hi, hlt⟩
  · refine Or.inl ⟨j, hj, ?_⟩
    rw [cmpGapR_eq f.xL f.xR hc ε hD u j]
    rw [lt_div_iff₀ hc'] at hlt
    linarith
  · refine Or.inr ⟨i, hi, ?_⟩
    rw [cmpGapL_eq f.xL f.xR hc ε hD u i]
    rw [lt_div_iff₀ hc'] at hlt
    linarith

end Cell

/-! ### Stage gaps under the flowed root bounds -/

/-- The real-time stage path is the restarted relative path. -/
theorem rp_stgDrv_eq (R : ℝ≥0 → ℝ) (S : ℝ≥0) {v : ℝ} (hv : 0 ≤ v) :
    (fun q : ℝ => GW2Rd.stgDrv R S q.toNNReal) v = shiftDrv (rp R) S v := by
  simp only [GW2Rd.stgDrv, shiftDrv, rp, Real.toNNReal_coe]
  congr 2
  apply NNReal.eq
  rw [NNReal.coe_add, Real.coe_toNNReal _ hv]
  exact (Real.coe_toNNReal _ (add_nonneg S.coe_nonneg hv)).symm

/-- **A stage right label below the flowed right root bound has its gap below the relative gap of the bound.** -/
theorem stageGapR_le {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ≥0) {xR yS : ℝ}
    (hy : yS ≤ rightImg (rp R) xR S - rp R S) (u : ℝ≥0) :
    rightImg (fun q => (1 : ℝ) * GW2Rd.stgDrv R S q.toNNReal) yS u - 1 * GW2Rd.stgDrv R S u ≤
      rightImg (rp R) xR ((S : ℝ) + u) - rp R ((S : ℝ) + u) := by
  have hU := continuous_rp hR
  have hsh := continuous_shiftDrv hU (S : ℝ)
  have hcg : rightImg (fun q => (1 : ℝ) * GW2Rd.stgDrv R S q.toNNReal) yS u =
      rightImg (shiftDrv (rp R) S) yS u :=
    Supp8.GB6.rightImg_congr hsh u.coe_nonneg fun v hv => by
      rw [one_mul]
      exact rp_stgDrv_eq R S hv.1
  have hD : (1 : ℝ) * GW2Rd.stgDrv R S u = shiftDrv (rp R) S u := by
    rw [one_mul]
    have := rp_stgDrv_eq R S u.coe_nonneg
    simp only [Real.toNNReal_coe] at this
    exact this
  rw [hcg, hD]
  have hmono := rightImg_mono_index hsh u.coe_nonneg hy
  rw [rightImg_shiftDrv hU S.coe_nonneg u.coe_nonneg xR] at hmono
  simp only [shiftDrv]
  linarith

/-- **A stage left label above the flowed left root bound has its gap below the mirrored relative gap.** -/
theorem stageGapL_le {R : ℝ≥0 → ℝ} (hR : Continuous R) (S : ℝ≥0) {xL yS : ℝ}
    (hy : -rightImg (fun v => -rp R v) (-xL) S - rp R S ≤ yS) (u : ℝ≥0) :
    1 * GW2Rd.stgDrv R S u + rightImg (fun q => -((1 : ℝ) * GW2Rd.stgDrv R S q.toNNReal)) (-yS) u ≤
      rightImg (fun v => -rp R v) (-xL) ((S : ℝ) + u) - -rp R ((S : ℝ) + u) := by
  have hU' : Continuous fun v => -rp R v := (continuous_rp hR).neg
  have hsh := continuous_shiftDrv hU' (S : ℝ)
  have hneg : ∀ v : ℝ, 0 ≤ v → -((1 : ℝ) * GW2Rd.stgDrv R S v.toNNReal) = shiftDrv (fun v => -rp R v) S v := by
    intro v hv
    have := rp_stgDrv_eq R S hv
    simp only at this
    rw [one_mul, this]
    simp only [shiftDrv]
    ring
  have hcg : rightImg (fun q => -((1 : ℝ) * GW2Rd.stgDrv R S q.toNNReal)) (-yS) u =
      rightImg (shiftDrv (fun v => -rp R v) S) (-yS) u :=
    Supp8.GB6.rightImg_congr hsh u.coe_nonneg fun v hv => hneg v hv.1
  have hD : (1 : ℝ) * GW2Rd.stgDrv R S u = -shiftDrv (fun v => -rp R v) S u := by
    have := hneg u u.coe_nonneg
    simp only [Real.toNNReal_coe] at this
    linarith
  rw [hcg, hD]
  have hy' : -yS ≤ rightImg (fun v => -rp R v) (-xL) S - (fun v => -rp R v) S := by
    simp only
    linarith
  have hmono := rightImg_mono_index hsh u.coe_nonneg hy'
  rw [rightImg_shiftDrv hU' S.coe_nonneg u.coe_nonneg (-xL)] at hmono
  simp only [shiftDrv] at hmono ⊢
  linarith

end InteractingSLE.Theorem14.GW2Bh
