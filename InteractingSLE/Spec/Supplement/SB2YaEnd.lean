/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XzTail
import InteractingSLE.Spec.Supplement.SB2McPart
import InteractingSLE.Spec.Supplement.SB2JyTip
import InteractingSLE.Spec.Supplement.SB2JwOrder
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.SB2XbTime

/-!
# The end of a launched piece with a right end-hit

Packet PROVE-T14-SB2LIFT (round 31; item 4, the relative root fields). For a launched piece of a right walk run with
finite positive lifetime and a right end-hit at `x` (beyond the record):
* **`actual_end`**: every real point of the piece before its end is `< x`, its end point is a real `z ≥ x`, and every
  real point of the prefix after the launch is `≤ z`;
* **`lRecR_eq_end`**: the new right record is `z`.
Deterministic: `lHit_run_iff` (the hit through closed fills of the partial prefixes), `mem_closure_partPrefix_of_mem`
(trace points are in the closed fill), the beyond-ray criterion `mem_closure_fillH_image_iff` and the compact-set
bound `exists_real_ge_of_mem_closure_fillH`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}

/-- Real points of a live walk prefix are at most its record. -/
theorem re_le_rec_of_mem_prefix (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D)
    (hrec : ∀ k, k ≤ n → RecInv κ b J θ D k) (hlm : ∀ k, NoLeftMove κ b J θ D k)
    (hst : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) ≠ stDone) {w : ℂ}
    (hw : w ∈ SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D n) (hw0 : w.im = 0) :
    w.re ≤ stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) := by
  by_contra h
  push Not at h
  have e : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hw0])
  exact notMem_prefix_of_beyond hP hrec hlm hst h (by rw [e]; exact hw)

/-- **The end of a piece with a right end-hit**: real points before the end are `< x`, the end point is a real
`z ≥ x`, and the real points of the prefix after the launch are `≤ z`. -/
theorem actual_end (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) (hW : WalkChainFacts κ b J θ D)
    (hrec : ∀ k, k ≤ n → RecInv κ b J θ D k) (hlm : ∀ k, NoLeftMove κ b J θ D k)
    (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hfin : (D n).2 ≠ ⊤) (hpos : (D n).2 ≠ 0)
    (hpt : stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) ≤
      stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n))
    (hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → pcPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) (D n) t ∈ Hbar)
    (hPH : SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1) ⊆ Hbar)
    {x : ℝ} (hx : stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) < x)
    (hhit : lHit (stChart (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n)) ⊤ (D n) x) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 → ∀ y : ℝ,
      pcPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) (D n) t = y → y < x) ∧
    ∃ z : ℝ, pcPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) (D n) (D n).2.toNNReal = z ∧ x ≤ z ∧
      ∀ w ∈ SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1), w.im = 0 → w.re ≤ z := by
  set s := ExplState.run κ b J (boundaryWalkSpec b J θ true) D n with hs
  obtain ⟨⟨c₁, θ₁⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ stDone := Lx.stStatus_ne_done_of_launches _ D hl'
  have hiff := lHit_run_iff hP hl' hfin (hrec n le_rfl x hx)
  obtain ⟨hA, hB⟩ := hiff.1 hhit
  set L := (D n).2.toNNReal with hLdef
  have hL : (D n).2 = L := (ENNReal.coe_toNNReal hfin).symm
  have hst : stopTime ⊤ (D n) = L := by simp [stopTime, hL]
  have hbe := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := J) _ D hP n).1
  have hr := LuM.pieceRegular_of_launch hP hl
  have hPc := continuousOn_pcPt hbe hr
  have h0 : pcPt s (D n) 0 = ((stPt s : ℝ) : ℂ) := pcPt_zero_launch hP hW hl hpos
  -- (i) real points before the end are left of `x`
  have hi : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 → ∀ y : ℝ, pcPt s (D n) t = y → y < x := by
    intro t ht y hy
    by_contra hge
    push Not at hge
    have htL : t < L := by rw [hL] at ht; exact_mod_cast ht
    have hrT : (t : ℝ) < stopTime ⊤ (D n) := by rw [hst]; exact_mod_cast htL
    apply hA (t : ℝ) t.2 hrT
    have hsub : pcPt s (D n) '' Icc 0 t ⊆ partPrefix κ b J θ D n (t : ℝ) := by
      rintro _ ⟨t', ht', rfl⟩
      refine Or.inr ⟨LuM.trOf (D n) t', ⟨t', ?_, rfl⟩, rfl⟩
      rw [Real.toNNReal_coe]
      exact ht'
    by_cases hxP : (x : ℂ) ∈ pcPt s (D n) '' Icc 0 t
    · exact mem_closure_partPrefix_of_mem hP hl' hfin hrec hlm hnd hx t.2 hrT.le (hsub hxP)
    · rcases eq_or_lt_of_le hge with hxy | hxy
      · exact absurd ⟨t, ⟨zero_le, le_rfl⟩, by rw [hy, hxy]⟩ hxP
      · -- the curve `pcPt` on `[0, t]`, extended constantly
        set β : ℝ≥0 → ℂ := fun u => pcPt s (D n) (min u t) with hβ
        have hβc : Continuous β := hPc.comp_continuous (continuous_id.min continuous_const) fun u =>
          (ENNReal.coe_le_coe.2 (min_le_right u t)).trans ht.le
        have hβH : ∀ u, β u ∈ Hbar := fun u =>
          hH _ ((ENNReal.coe_le_coe.2 (min_le_right u t)).trans ht.le)
        have himg : β '' Icc 0 t = pcPt s (D n) '' Icc 0 t := by
          refine image_congr fun u hu => ?_
          simp only [hβ, min_eq_left hu.2]
        have hβ0 : β 0 = ((stPt s : ℝ) : ℂ) := by simp only [hβ, min_eq_left zero_le, h0]
        have hmem : (x : ℂ) ∈ closure (fillH (β '' Icc 0 t)) := by
          refine (mem_closure_fillH_image_iff hβc hβH (zero_le : (0 : ℝ≥0) ≤ t) hβ0 (hpt.trans_lt hx)
            (by rw [himg]; exact hxP)).2 ⟨t, ⟨zero_le, le_rfl⟩, ?_, ?_⟩
          · simp only [hβ, min_self, hy, Complex.ofReal_im]
          · simp only [hβ, min_self, hy, Complex.ofReal_re]
            exact hxy
        rw [himg] at hmem
        exact closure_mono (fillH_mono hsub) hmem
  refine ⟨hi, ?_⟩
  -- (ii) the end point
  have hsucc := prefixPhysSet_succ_of_launch hl'
  have hcpt : IsCompact (SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1)) := by
    rw [hsucc]
    exact (Lx.isCompact_prefixPhysSet_run _ D hP n hnd).union (isCompact_tipSet_launch hP hl hfin)
  obtain ⟨_, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  -- every real point of the prefix after the launch: old ones `≤ record`, piece ones before the end `< x`
  have hclass : ∀ w ∈ SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1), w.im = 0 → x ≤ w.re →
      w = pcPt s (D n) L := by
    intro w hw hw0 hxw
    rw [hsucc] at hw
    rcases hw with hw | hw
    · have := re_le_rec_of_mem_prefix hP hrec hlm hnd hw hw0
      linarith
    · rw [htip] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      rcases (show (t : ℝ≥0∞) ≤ (D n).2 from ht).lt_or_eq with htl | hte
      · have e : pcPt s (D n) t = (((pcPt s (D n) t).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simp only [Complex.ofReal_im]; exact hw0)
        have := hi t htl _ e
        linarith
      · have : t = L := by rw [hL] at hte; exact_mod_cast hte
        rw [this]
  obtain ⟨w, hw, hw0, hxw⟩ := Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH hcpt hPH hB
  have hwL := hclass w hw hw0 hxw
  refine ⟨w.re, ?_, hxw, fun w' hw' hw'0 => ?_⟩
  · rw [← hwL]
    exact Complex.ext (by simp) (by simp [hw0])
  · by_contra hlt
    push Not at hlt
    have := hclass w' hw' hw'0 (hxw.trans hlt.le)
    rw [← hwL] at this
    rw [this] at hlt
    exact lt_irrefl _ hlt

/-- **The new right record of a piece with a right end-hit is its end point.** -/
theorem lRecR_eq_end (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D)
    (hrec : ∀ k, k ≤ n → RecInv κ b J θ D k)
    (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hfin : (D n).2 ≠ ⊤)
    (hPH : SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1) ⊆ Hbar) {z : ℝ}
    (hz : stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) < z)
    (hzmem : (z : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1))))
    (hmax : ∀ w ∈ SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1), w.im = 0 → w.re ≤ z) :
    lRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) ⊤ (D n) = z := by
  obtain ⟨⟨c₁, θ₁⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := Lx.stStatus_ne_done_of_launches _ D hl'
  have hsucc := prefixPhysSet_succ_of_launch hl'
  have hcpt : IsCompact (SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1)) := by
    rw [hsucc]
    exact (Lx.isCompact_prefixPhysSet_run _ D hP n hnd).union (isCompact_tipSet_launch hP hl hfin)
  rw [lRecR_run_eq hP hl' hfin (hrec n le_rfl)]
  have hS : IsGreatest (insert (stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n))
      {x : ℝ | stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) < x ∧
        (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1)))}) z := by
    refine ⟨Or.inr ⟨hz, hzmem⟩, ?_⟩
    rintro y (rfl | ⟨-, hy⟩)
    · exact hz.le
    · obtain ⟨w, hw, hw0, hyw⟩ := Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH hcpt hPH hy
      exact hyw.trans (hmax w hw hw0)
  exact hS.csSup_eq

end InteractingSLE.Theorem14.SB.Lk
