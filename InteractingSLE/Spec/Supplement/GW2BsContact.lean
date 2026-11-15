/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsGap

/-!
# The cell exit fires before the contact

Packet PROVE-GW2-BUF (round 16; step B). The near family at index `m` presents the stage word `β` (`PresentsO`).
The family's labels divided by `c` are the stage word's labels (sides swapped on odd histories). The outermost
family labels are controlled (`f.mL ≤ f.nL − 1`, `f.mR ≤ f.nR − 1`). Their stage labels are an outermost right and
left mark of the stage word. By step A, these lie under the flowed root bounds `rightImg Wc xR S − Wc S` and
`−rightImg (−Wc) (−xL) S − Wc S`. The contact clause makes the relative gap of `xR` (or the mirrored gap of `xL`)
small before the relative life `L`. Then the controlled stage gap is small before `L − S` (`stageGapR_le`,
`stageGapL_le`), and the cell exit fires before `L − S` (`cellStop_lt_of_stageGap`).

* `stage_labels_of_presents` (the family's labels as stage labels, both orientations);
* **`cellStop_lt_of_contact`**.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist.StagedLaw MartChar.RealFlow Sec5.Prop59NodeTree Sec5.CrossCond.StagedRepLater GW2TipSystem
  GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

/-- **The family's labels, divided by `c`, are stage labels**: positive jumps or `0` on the stage word's right,
negative jumps or `0` on its left (sides swapped on odd histories). -/
theorem stage_labels_of_presents {κ : ℝ} {β : BoundaryWord} {scale c : ℝ≥0}
    (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hP : GW2Sdf.PresentsO κ β scale flip xL ρL xR ρR) :
    (flip = false → (∀ j, xR j / c = 0 ∨ (0 < xR j / c ∧ xR j / c ∈ β.jumps)) ∧
      ∀ i, xL i / c = 0 ∨ (xL i / c < 0 ∧ xL i / c ∈ β.jumps)) ∧
    (flip = true → (∀ i, -(xL i / c) = 0 ∨ (0 < -(xL i / c) ∧ -(xL i / c) ∈ β.jumps)) ∧
      ∀ j, -(xR j / c) = 0 ∨ (-(xR j / c) < 0 ∧ -(xR j / c) ∈ β.jumps)) := by
  have hdiv : ∀ x : ℝ, x / c = Real.sqrt scale * x := fun x => by rw [hsc, div_eq_inv_mul]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · subst hf
    obtain ⟨eL, eR, hxL, hxR, -, -⟩ := hP
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h1 := congrFun hxR (Fin.cast eR.symm j)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h1
      rw [hdiv, h1]
      exact RetAux79.flowLineXR_eq_zero_or_mem β _
    · have h1 := congrFun hxL (Fin.cast eL.symm i)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h1
      rw [hdiv, h1]
      exact RetAux79.flowLineXL_eq_zero_or_mem β _
  · subst hf
    obtain ⟨eL, eR, hxL, hxR, -, -⟩ := hP
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have h1 := congrFun hxR (Fin.cast eR.symm i)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h1
      rw [hdiv, h1]
      exact RetAux79.flowLineXR_eq_zero_or_mem β _
    · have h1 := congrFun hxL (Fin.cast eL.symm j)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at h1
      rw [hdiv, h1]
      exact RetAux79.flowLineXL_eq_zero_or_mem β _

section Cell

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ)
  {y : RecData}

/-- **The cell exit fires before the contact.** -/
theorem cellStop_lt_of_contact (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) {β : BoundaryWord} {scale c : ℝ≥0} (hc : 0 < c)
    (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) (m : ℕ)
    (hP : GW2Sdf.PresentsO κ β scale flip f.xL (f.ρLs m) f.xR (f.ρRs m))
    (hmL : f.mL ≤ f.nL - 1) (hmR : f.mR ≤ f.nR - 1) {cap : ℝ≥0} (hcap : 0 < cap)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (S : ℝ≥0)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) (GW2Rd.stgDrv Wc S)) 0 ∈
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {xR xL : ℝ} (hjR : ∀ z ∈ β.jumps, 0 < z → z ≤ rightImg (rp Wc) xR S - rp Wc S)
    (hjL : ∀ z ∈ β.jumps, z < 0 → -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ z) {L : ℝ}
    (hcon : (∀ δ : ℝ, 0 < δ → ∃ t : ℝ, (S : ℝ) < t ∧ t < L ∧ rightImg (rp Wc) xR t - rp Wc t < δ) ∨
      ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, (S : ℝ) < t ∧ t < L ∧
        rightImg (fun v => -rp Wc v) (-xL) t - -rp Wc t < δ) :
    cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, GW2Rd.stgDrv Wc S) <
      ENNReal.ofReal (L - S) := by
  have hU := continuous_rp hWc
  have hzR : 0 ≤ rightImg (rp Wc) xR S - rp Wc S := by
    have := le_rightImg hU xR S.coe_nonneg
    linarith
  have hzL : -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ 0 := by
    have : -rp Wc S ≤ rightImg (fun v => -rp Wc v) (-xL) S := le_rightImg hU.neg (-xL) S.coe_nonneg
    linarith
  -- the outermost labels are controlled
  have hiR : f.mR ≤ ((⟨f.nR - 1, Nat.sub_lt f.hnR one_pos⟩ : Fin f.nR) : ℕ) := hmR
  have hiL : f.mL ≤ ((⟨f.nL - 1, Nat.sub_lt f.hnL one_pos⟩ : Fin f.nL) : ℕ) := hmL
  set jR : Fin f.nR := ⟨f.nR - 1, Nat.sub_lt f.hnR one_pos⟩ with hjRdef
  set iL : Fin f.nL := ⟨f.nL - 1, Nat.sub_lt f.hnL one_pos⟩ with hiLdef
  obtain ⟨hfalse, htrue⟩ := stage_labels_of_presents hsc flip hP
  have hDc := GW2Rd.continuous_stgDrv hWc S
  -- the time before `L − S` from a contact time `t`
  have hut : ∀ t : ℝ, (S : ℝ) < t → t < L → ((t - S).toNNReal : ℝ≥0∞) < ENNReal.ofReal (L - S) ∧
      (S : ℝ) + ((t - S).toNNReal : ℝ) = t := by
    intro t hSt htL
    refine ⟨?_, ?_⟩
    · show ENNReal.ofReal (t - S) < ENNReal.ofReal (L - S)
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    · rw [Real.coe_toNNReal _ (by linarith)]
      ring
  refine cellStop_lt_of_stageGap f cell posL posR hsh hL hR hc _ hcap hDc h0 fun δ hδ => ?_
  cases flip with
  | false =>
    have hε : GW2Sdy.nearSign false = 1 := rfl
    obtain ⟨hRl, hLl⟩ := hfalse rfl
    rcases hcon with hr | hl
    · obtain ⟨t, hSt, htL, hgap⟩ := hr δ hδ
      obtain ⟨hlt, hSu⟩ := hut t hSt htL
      refine ⟨(t - S).toNNReal, hlt, Or.inl ⟨jR, hiR, ?_⟩⟩
      have hy : f.xR jR / c ≤ rightImg (rp Wc) xR S - rp Wc S := by
        rcases hRl jR with h | ⟨hpos, hmem⟩
        · rw [h]; exact hzR
        · exact hjR _ hmem hpos
      have := stageGapR_le hWc S hy (t - S).toNNReal
      rw [hSu] at this
      rw [hε]
      linarith
    · obtain ⟨t, hSt, htL, hgap⟩ := hl δ hδ
      obtain ⟨hlt, hSu⟩ := hut t hSt htL
      refine ⟨(t - S).toNNReal, hlt, Or.inr ⟨iL, hiL, ?_⟩⟩
      have hy : -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ f.xL iL / c := by
        rcases hLl iL with h | ⟨hneg, hmem⟩
        · rw [h]; exact hzL
        · exact hjL _ hmem hneg
      have := stageGapL_le hWc S hy (t - S).toNNReal
      rw [hSu] at this
      rw [hε]
      linarith
  | true =>
    have hε : GW2Sdy.nearSign true = -1 := rfl
    obtain ⟨hRl, hLl⟩ := htrue rfl
    have hneg1 : (fun q : ℝ => -(-1 * GW2Rd.stgDrv Wc S q.toNNReal)) =
        fun q : ℝ => (1 : ℝ) * GW2Rd.stgDrv Wc S q.toNNReal := by
      funext q
      ring
    have hneg2 : (fun q : ℝ => -1 * GW2Rd.stgDrv Wc S q.toNNReal) =
        fun q : ℝ => -((1 : ℝ) * GW2Rd.stgDrv Wc S q.toNNReal) := by
      funext q
      ring
    rcases hcon with hr | hl
    · -- a right contact is read by the family's left labels
      obtain ⟨t, hSt, htL, hgap⟩ := hr δ hδ
      obtain ⟨hlt, hSu⟩ := hut t hSt htL
      refine ⟨(t - S).toNNReal, hlt, Or.inr ⟨iL, hiL, ?_⟩⟩
      have hy : -(f.xL iL / c) ≤ rightImg (rp Wc) xR S - rp Wc S := by
        rcases hRl iL with h | ⟨hpos, hmem⟩
        · rw [h]; exact hzR
        · exact hjR _ hmem hpos
      have := stageGapR_le hWc S hy (t - S).toNNReal
      rw [hSu] at this
      rw [hε, hneg1]
      linarith
    · -- a left contact is read by the family's right labels
      obtain ⟨t, hSt, htL, hgap⟩ := hl δ hδ
      obtain ⟨hlt, hSu⟩ := hut t hSt htL
      refine ⟨(t - S).toNNReal, hlt, Or.inl ⟨jR, hiR, ?_⟩⟩
      have hy : -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ -(f.xR jR / c) := by
        rcases hLl jR with h | ⟨hneg, hmem⟩
        · rw [h]; exact hzL
        · exact hjL _ hmem hneg
      have := stageGapL_le hWc S hy (t - S).toNNReal
      rw [hSu, neg_neg] at this
      rw [hε, hneg2]
      linarith

end Cell

end InteractingSLE.Theorem14.GW2Bh
