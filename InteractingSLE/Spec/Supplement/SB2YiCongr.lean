/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YiSample
import InteractingSLE.Spec.Supplement.SB2YiTail0
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# The root S2 record at every root sample

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3).

* `isStageS2_congr`: `Om.IsStageS2` reads its chart only through the inverse on `ℍ` and the lift;
* **`isStageS2_root_all`**: at the root `n = relOff` (not a zero root), at a B-time `t` of positive relative clock
  with clock `0` at `τE` (B's first visit of `R`), the S2 record in the post-head chart. If `R` is explored at the
  stage start (a mark entry or the root point), `τE = 0`: the post-head chart is the stage chart on `ℍ`, the shifted
  driver is the stopped driver, and the record is the tail one (`isStageS2_tail0`). Otherwise the root is a pure piece
  entry (`isStageS2_root`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.SB.Sx

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **`Om.IsStageS2` only reads the chart's inverse on `ℍ` and its lift.** -/
theorem isStageS2_congr {c c' Φ : Chart} {A₁ : Set ℂ} {wB : ℝ → ℝ} {sB : ℝ} {W : ℝ → ℝ} {u : ℝ}
    (h : Om.IsStageS2 c Φ A₁ wB sB W u) (h1 : ∀ z ∈ H, c'.2.1 z = c.2.1 z) (h2 : ∀ z, c'.2.2 z = c.2.2 z) :
    Om.IsStageS2 c' Φ A₁ wB sB W u := by
  obtain ⟨q, x₁, R, cr, g, β', γ, S₀, Sm, ηr, η, hq, hq0, hx₁, hqH, hqR, hR, hc, hgc, hgi, hgf, hL, hβ', hβ'0, hA,
    hγ, hγ0, hlift, hch, hS₀S, hnR, hs, hwc, hw0, hη, hwt, hηβ, hηH, hcap, hAeq, hinv, hlifteq⟩ := h
  have hcrH : ∀ y ∈ H, LP.reflectC (cr.2.1 (LP.reflectC y)) ∈ H := fun y hy =>
    LP.reflectC_mem_H_iff.2 (hc.1.inv_mem (LP.reflectC_mem_H_iff.2 hy)).1
  exact ⟨q, x₁, R, cr, g, β', γ, S₀, Sm, ηr, η, hq, hq0, hx₁, hqH, hqR, hR, hc, hgc, hgi, hgf, hL, hβ', hβ'0, hA,
    hγ, hγ0, hlift, hch, hS₀S, hnR, hs, hwc, hw0, hη, hwt, hηβ, hηH, hcap,
    fun z hz => by rw [h1 z hz]; exact hAeq z hz,
    fun y hy => by rw [h1 _ (hcrH y hy)]; exact hinv y hy,
    fun y hy => by rw [h2]; exact hlifteq y hy⟩

/-- **The root S2 record at every root sample** (in the post-head chart). -/
theorem isStageS2_root_all {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hoffn : relOff κ θ b jumps (realMax (pA '' Icc 0 1)) D = n)
    (hzr : ¬ ZeroRoot κ θ b jumps (realMax (pA '' Icc 0 1)) D)
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H)
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < (D n).2) (htip : LP.traceAt t (D n).1 ∈ H) {x₀ : ℝ}
    (hent : IsRightEntryChart (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
      (realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ((Mo.hullChart
      (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) 0).recenter x₀))
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0) {a : ℝ≥0 → ℝ≥0∞} (hac : Continuous a)
    (ham : Monotone a) (hazero : a (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1))) = 0) (hat : 0 < a t) (hatop : a t ≠ ⊤) {ηV : ℝ → ℂ}
    (hηV : IsLoewnerTrace (fun s : ℝ => W s.toNNReal) ηV)
    (hlink : ∀ s : ℝ≥0, s ≤ t → (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1))) ≤ s → pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s ∈
      ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
      x₀).dom : Set ℂ) →
      ηV (a s).toReal = (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ
        true) D n)) x₀).1 (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s)) :
    Om.IsStageS2 ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner (headDrv (D n)
      (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA '' Icc 0 1))))
      (headTime (D n) (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA
      '' Icc 0 1)))))
      (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) x₀)
        (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) (shiftDrive
        (headDrv (D n) t) (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax
        (pA '' Icc 0 1))))
      (headTime (D n) t - (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax
        (pA '' Icc 0 1)))) (fun s : ℝ => W s.toNNReal) ((a t).toNNReal : ℝ) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set R := realMax (pA '' Icc 0 1) with hRdef
  set τE := visitTime s (D n) R with hτEdef
  obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hτt : τE < t := by
    by_contra h
    push Not at h
    have := ham h
    rw [hazero] at this
    exact absurd (lt_of_lt_of_le hat this) (lt_irrefl 0)
  -- the entry of `R`
  obtain ⟨-, tR, htR, -⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by rw [← hβr, ← htR]; exact mem_range_self tR
  have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
  obtain ⟨hent', -⟩ := entryStage_spec κ θ b jumps hex
  have hoff := startOff_eq κ θ b jumps R D
  by_cases hold : (R : ℂ) ∈ statePhysicalSet 0 s
  · -- `R` is explored at the stage start: the tail record
    have hpos : (D n).2 ≠ 0 := ne_bot_of_gt htζ
    have hτ0 : τE = 0 := Dv.visitTime_eq_zero_of_old hP hW hl hpos hold
    have ht0 : 0 < t := lt_of_le_of_lt zero_le hτt
    have ha0 : a 0 = 0 := by rw [← hτ0]; exact hazero
    have h := isStageS2_tail0 hP hW hlm hlh hl hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hold hS3 ht0 htζ htip hent hWc
      hW0 hac ham ha0 hat hatop hηV (fun s' hs' hd => hlink s' hs' (by rw [hτ0]; exact zero_le) hd)
    rw [hτ0]
    have hT0 : headTime (D n) 0 = 0 := by simp [headTime]
    have hH0 : ∀ x : ℝ, headDrv (D n) 0 x = 0 := fun x => by
      have hPR : GW1P.PieceRegular (D n).1 (D n).2 := by
        have h' := hP n c' θ' hl'
        rwa [Lx.instrTime_boundaryWalk_of_launch hl', min_eq_right le_top] at h'
      simp [headDrv, hPR.1]
    have hHc : Continuous (headDrv (D n) 0) := by
      have e : headDrv (D n) 0 = fun _ => 0 := funext hH0
      rw [e]; exact continuous_const
    have hsh : shiftDrive (headDrv (D n) t) ((0 : ℝ≥0) : ℝ) = headDrv (D n) t := by
      funext x
      have h0 : headDrv (D n) t 0 = 0 := by
        have hPR : GW1P.PieceRegular (D n).1 (D n).2 := by
          have h' := hP n c' θ' hl'
          rwa [Lx.instrTime_boundaryWalk_of_launch hl', min_eq_right le_top] at h'
        simp [headDrv, hPR.1]
      simp only [shiftDrive, NNReal.coe_zero, zero_add, h0, sub_zero]
    have hTt : headTime (D n) t - ((0 : ℝ≥0) : ℝ) = t := by
      simp only [headTime, NNReal.coe_zero, sub_zero, min_eq_left htζ.le, ENNReal.toNNReal_coe]
    rw [hT0, hsh, hTt]
    exact isStageS2_congr h (fun z hz => GW2aCont.loewner_zero_inv hHc (hH0 0) hz)
      (fun z => by rw [GW2aCont.loewner_zero_lift])
  · -- a pure piece entry: the post-head record
    have hnm : ¬ MarkEntry κ θ b jumps R D := fun hm => hold (by
      have he1 := hoff.1 hm.1
      have : n = entryStage κ θ b jumps R D + 1 := by rw [← hoffn, relOff_of_mark κ θ b jumps hm]; omega
      show (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D n)
      rw [this]; exact hent')
    have hna : ¬ ArcEntry κ θ b jumps R D := fun ha => hzr ⟨ha, hnm⟩
    have hoe : n = entryStage κ θ b jumps R D := by rw [← hoffn, relOff_of_not_mark κ θ b jumps hnm]; exact hoff.2 hna
    have hnew : (R : ℂ) ∈ SB.prefixPhysSet κ b jumps w D (n + 1) := by rw [hoe]; exact hent'
    rw [prefixPhysSet_succ_of_launch hl'] at hnew
    obtain ⟨-, -, -, -, htip'⟩ := tipSet_newPc_launch hP hl
    have hRtip : ∃ t' : ℝ≥0, (t' : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s (D n) t' = (R : ℂ) := by
      rcases hnew with h | h
      · exact absurd h hold
      · rw [htip'] at h; obtain ⟨t', ht', he⟩ := h; exact ⟨t', ht', he⟩
    exact isStageS2_root hP hW hlm hlh hl hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hold hRtip hS3 hτt htζ htip hent hWc
      hW0 hac ham hazero hat hatop hηV hlink

end InteractingSLE.Theorem14.SB.Sx
