/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1TermRestart
import InteractingSLE.Spec.Supplement.GW1WalkExitFinite
import InteractingSLE.Spec.Supplement.GW1WalkFinishTip
import InteractingSLE.Spec.Supplement.CounterflowRange

/-!
# Proposition BW1: the terminal geometric correspondence at a threshold

Packet PROVE-BW1-PROP. Supplement p. 613 (proof of Proposition BW1, first paragraph): "Let `g_A : U → ℍ` be the own
hydrodynamic map and let `[a, b]` be its filled real base. The terminal geometric correspondence gives
`W = b = g_A(q)`." For the first piece of a staged history, launched from the root at angle `θ` with instruction
time `t`, on the event that it ends at a continuation threshold on the side `r` (`BW1.EndsAtThresholdSide`):

* `le_of_endsAtThresholdSide`, `launch_eq_top_of_le`: the lifetime `ζ` is at most `t`, so the launch is the launch
  through the lifetime (instruction time `⊤`, the form of the walk lemmas); `ne_top_of_endsAtThresholdSide`: `ζ < ∞`;
* **`tendsto_stateChart_statePoint`**: the inverse of the state's chart `g_A − W` tends to the state's point `q` (the
  new extreme real record) at `0` — the terminal geometric correspondence, from the walk lemmas
  (`GW1W.rProf_launch`/`lProf_launch`, `GW1WalkExit.exteriorInverse_launch`,
  `GW1WalkFinish.boundary_limit_of_exteriorRecord`), with the root state's profiles (`BW1Term.rProf_init`,
  `lProf_init`);
* **`trace_stop_eq_statePoint`**: the piece's trace ends at `q`: `α(ζ) = q` (trace closure at the horizon,
  `GW1WalkExit.tendsto_inverse_trace_le`, and uniqueness of the limit at `0`);
* `statePoint_pos`, `statePoint_neg`: `q > 0` on a right threshold and `q < 0` on a left one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.BW1Prop

open Exist Exist.Staged Exist.StagedLaw GW1WalkExit GW1WalkFinish

section Launch

variable {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞}

/-- **A launch whose lifetime is at most its instruction time is the launch through the lifetime.** -/
theorem launch_eq_top_of_le (h : D.2 ≤ t) : ExplState.launch s k D θ t = ExplState.launch s k D θ ⊤ := by
  have hm : min t D.2 = min ⊤ D.2 := (min_eq_right h).trans (min_eq_right le_top).symm
  have h3 : ¬ t < D.2 := not_lt.2 h
  have h4 : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  rw [hm]
  simp only [h3, h4, ↓reduceIte, decide_eq_true h, decide_eq_true (le_top : D.2 ≤ ⊤)]

/-- **A launch ending at a threshold has its lifetime at most its instruction time** (otherwise it stops at an
interior tip). -/
theorem le_of_endsAtThresholdSide {r : Bool} (h : BW1.EndsAtThresholdSide (ExplState.launch s k D θ t) r) :
    D.2 ≤ t := by
  by_contra hlt
  push Not at hlt
  have hne : min t D.2 ≠ ⊤ := by
    rw [min_eq_left hlt.le]
    exact ne_top_of_lt hlt
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k D θ t hne
  have h' : stStatus (ExplState.launch s k D θ t) = stThr (some r) := h
  rw [hst] at h'
  unfold lStatus at h'
  simp [hlt, stTip, stThr] at h'

/-- **A launch ending at a threshold has a finite lifetime.** -/
theorem ne_top_of_endsAtThresholdSide {r : Bool} (h : BW1.EndsAtThresholdSide (ExplState.launch s k D θ t) r) :
    D.2 ≠ ⊤ := by
  intro htop
  have hle := le_of_endsAtThresholdSide h
  rw [launch_eq_top_of_le hle] at h
  have hmin : min (⊤ : ℝ≥0∞) D.2 = ⊤ := by rw [htop, min_self]
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_top s k D θ ⊤ hmin
  have h' : stStatus (ExplState.launch s k D θ ⊤) = stThr (some r) := h
  rw [hst] at h'
  simp [stDone, stThr] at h'


end Launch

/-! ### The terminal geometric correspondence -/

section Corr

variable {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ}

/-- The chart of the root state is the identity. -/
theorem stChart_init_inv (z : ℂ) : (stChart (ExplState.init 0)).2.1 z = z := by
  simp [stChart, ExplState.init, Chart.recenter, Chart.id]

/-- **The inverse chart after a finite launch from the root** is the inverse Loewner map of the stopped driver at the
lifetime. -/
theorem stChart_launch_init_inv (hfin : D.2 ≠ ⊤) (z : ℂ) :
    (stChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 z =
      fwdMapInv (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) ((D.2.toNNReal : ℝ≥0) : ℝ) z := by
  rw [(launch_eq_of_ne_top (ExplState.init 0) 0 D θ ⊤ (GW1W.min_top_ne_top hfin)).1]
  simp only [Chart.loewner, stChart_init_inv, stopDrv_def, stopTime, min_eq_right (le_top : D.2 ≤ ⊤)]

/-- The inverse chart after a regular finite launch from the root has boundary limits on `ℍ̄`. -/
theorem hasBdryLimits_stChart_launch_init (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤) :
    HasBdryLimits (stChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 := by
  have he : (stChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 =
      fwdMapInv (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) ((D.2.toNNReal : ℝ≥0) : ℝ) :=
    funext (stChart_launch_init_inv hfin)
  rw [he]
  exact hP.hasBdryLimits hfin

/-- The record of a regular piece continuous up to its finite lifetime is good. -/
theorem isDrvGood_of_pieceRegular (hreg : IsRegularDriver D) (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤) :
    LocalExt.IsDrvGood (recHist (recOf ⊤ D)) :=
  isDrvGood_of_continuousOn_le hreg (GW1W.min_top_ne_top hfin)
    (by rw [min_eq_right (le_top : D.2 ≤ ⊤)]; exact hP.2.1)

/-- **The terminal correspondence at a right threshold**: the inverse of the chart after the piece tends to the new
right record at `0`. -/
theorem tendsto_stChart_launch_right (hreg : IsRegularDriver D) (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) (h : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some true)) :
    Tendsto (stChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 (𝓝[H] 0)
      (𝓝 (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) : ℂ)) := by
  have hs : OwnProfile true (ExplState.init 0) := by simpa [OwnProfile] using BW1Term.rProf_init
  have hgood := isDrvGood_of_pieceRegular hreg hP hfin
  obtain ⟨-, hhit, hpt, -⟩ := GW1W.launch_thr_true hfin h
  have hprof := (GW1W.rProf_launch BW1Term.rProf_init 0 θ hreg hgood hfin hhit).1
  have hInv : ExteriorInverse true (ExplState.launch (ExplState.init 0) 0 D θ ⊤) :=
    exteriorInverse_launch (exteriorInverse_init true 0) hs.isRealChart 0 θ hP hfin
      (fun x hx => alive_of_lt_outwardRecord hs 0 θ hreg hgood hfin hx)
  have hB := hasBdryLimits_stChart_launch_init (θ := θ) hP hfin
  have hE : ExteriorRecord true (ExplState.launch (ExplState.init 0) 0 D θ ⊤) :=
    exteriorRecord_of_profile_inverse hB (by simpa [OwnProfile] using hprof)
      (by simpa [sideCoord, outwardRecord] using hpt) hInv
  exact boundary_limit_of_exteriorRecord hB hE

/-- **The terminal correspondence at a left threshold.** -/
theorem tendsto_stChart_launch_left (hreg : IsRegularDriver D) (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) (h : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some false)) :
    Tendsto (stChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 (𝓝[H] 0)
      (𝓝 (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) : ℂ)) := by
  have hs : OwnProfile false (ExplState.init 0) := by simpa [OwnProfile] using BW1Term.lProf_init
  have hgood := isDrvGood_of_pieceRegular hreg hP hfin
  obtain ⟨-, hhit, hpt, -⟩ := GW1W.launch_thr_false hfin h
  have hprof := (GW1W.lProf_launch BW1Term.lProf_init 0 θ hreg hgood hfin hhit).1
  have hInv : ExteriorInverse false (ExplState.launch (ExplState.init 0) 0 D θ ⊤) :=
    exteriorInverse_launch (exteriorInverse_init false 0) hs.isRealChart 0 θ hP hfin
      (fun x hx => alive_of_lt_outwardRecord hs 0 θ hreg hgood hfin hx)
  have hB := hasBdryLimits_stChart_launch_init (θ := θ) hP hfin
  have hE : ExteriorRecord false (ExplState.launch (ExplState.init 0) 0 D θ ⊤) :=
    exteriorRecord_of_profile_inverse hB (by simpa [OwnProfile] using hprof)
      (by simp [sideCoord, outwardRecord, hpt]) hInv
  exact boundary_limit_of_exteriorRecord hB hE

/-- **Proposition BW1's terminal geometric correspondence** ("`W = b = g_A(q)`"): on the event that the first piece
(regular, launched from the root with instruction time `t`) ends at a threshold, the inverse of the state's chart
`g_A − W` tends to the state's point `q` at `0`. -/
theorem tendsto_stateChart_statePoint {t : ℝ≥0∞} {r : Bool} (hreg : IsRegularDriver D)
    (hP : GW1P.PieceRegular D.1 (min t D.2))
    (h : BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 D θ t) r) :
    Tendsto (BW1.stateChart (ExplState.launch (ExplState.init 0) 0 D θ t)).2.1 (𝓝[H] 0)
      (𝓝 (BW1.statePoint (ExplState.launch (ExplState.init 0) 0 D θ t) : ℂ)) := by
  have hle := le_of_endsAtThresholdSide h
  have hfin := ne_top_of_endsAtThresholdSide h
  rw [min_eq_right hle] at hP
  rw [launch_eq_top_of_le hle] at h ⊢
  have h' : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some r) := h
  cases r
  · exact tendsto_stChart_launch_left hreg hP hfin h'
  · exact tendsto_stChart_launch_right hreg hP hfin h'

/-- **The piece ends at the new record**: on the threshold event, the generating trace of the first piece takes the
value `q` (the state's point) at the lifetime. -/
theorem trace_stop_eq_statePoint {t : ℝ≥0∞} {r : Bool} (hreg : IsRegularDriver D)
    (hP : GW1P.PieceRegular D.1 (min t D.2)) {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 (min t D.2) α)
    (h : BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 D θ t) r) :
    α D.2.toNNReal = (BW1.statePoint (ExplState.launch (ExplState.init 0) 0 D θ t) : ℂ) := by
  have hle := le_of_endsAtThresholdSide h
  have hfin := ne_top_of_endsAtThresholdSide h
  have hlim := tendsto_stateChart_statePoint hreg hP h
  rw [min_eq_right hle] at hP hα
  rw [launch_eq_top_of_le hle] at hlim ⊢
  have hWs : Continuous fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) D.2).toNNReal :=
    CounterflowRange.continuous_stopped hP.2.1
  have hWs0 : (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) 0 = 0 := by
    show D.1 (min ((0 : ℝ≥0) : ℝ≥0∞) D.2).toNNReal = 0
    rw [CounterflowRange.stopped_eq_of_lt (W := D.1) (t := 0) (by simp)]
    exact hP.1
  have htr := GW1WalkExit.tendsto_inverse_trace_le (CounterflowRange.isGeneratingTrace_stopped hα) hWs hWs0
    (t := D.2.toNNReal) (by rw [ENNReal.coe_toNNReal hfin])
  have he : (BW1.stateChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 =
      fwdMapInv (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) ((D.2.toNNReal : ℝ≥0) : ℝ) :=
    funext (stChart_launch_init_inv hfin)
  rw [he] at hlim
  have := GW1P.neBot_nhdsWithin_H (p := 0) zero_mem_Hbar
  exact tendsto_nhds_unique htr hlim

/-- **The new record is positive at a right threshold.** -/
theorem statePoint_pos_of_right (hreg : IsRegularDriver D) (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤)
    (h : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some true)) :
    0 < stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
  have hs : OwnProfile true (ExplState.init 0) := by simpa [OwnProfile] using BW1Term.rProf_init
  have hgood := isDrvGood_of_pieceRegular hreg hP hfin
  obtain ⟨-, ⟨x, hx0, hhit⟩, hpt, -⟩ := GW1W.launch_thr_true hfin h
  have hx0' : 0 < x := hx0
  have hxle : x ≤ stRecR (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
    by_contra hlt
    push Not at hlt
    exact hhit.2 (alive_of_lt_outwardRecord hs 0 θ hreg hgood hfin (x := x)
      (by simpa [outwardRecord, sideCoord] using hlt)).2
  rw [hpt]
  exact hx0'.trans_le hxle

/-- **The new record is negative at a left threshold.** -/
theorem statePoint_neg_of_left (hreg : IsRegularDriver D) (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤)
    (h : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some false)) :
    stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) < 0 := by
  have hs : OwnProfile false (ExplState.init 0) := by simpa [OwnProfile] using BW1Term.lProf_init
  have hgood := isDrvGood_of_pieceRegular hreg hP hfin
  obtain ⟨-, ⟨x, hx0, hhit⟩, hpt, -⟩ := GW1W.launch_thr_false hfin h
  have hx0' : x < 0 := hx0
  have hxle : stRecL (ExplState.launch (ExplState.init 0) 0 D θ ⊤) ≤ x := by
    by_contra hlt
    push Not at hlt
    exact hhit.2 (alive_of_lt_outwardRecord hs 0 θ hreg hgood hfin (x := x)
      (by simpa [outwardRecord, sideCoord] using hlt)).2
  rw [hpt]
  exact hxle.trans_lt hx0'

/-- **The state's point is not the root** on the threshold event. -/
theorem statePoint_ne_zero {t : ℝ≥0∞} {r : Bool} (hreg : IsRegularDriver D)
    (hP : GW1P.PieceRegular D.1 (min t D.2))
    (h : BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 D θ t) r) :
    BW1.statePoint (ExplState.launch (ExplState.init 0) 0 D θ t) ≠ 0 := by
  have hle := le_of_endsAtThresholdSide h
  have hfin := ne_top_of_endsAtThresholdSide h
  rw [min_eq_right hle] at hP
  rw [launch_eq_top_of_le hle] at h ⊢
  have h' : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some r) := h
  cases r
  · exact (statePoint_neg_of_left hreg hP hfin h').ne
  · exact (statePoint_pos_of_right hreg hP hfin h').ne'

end Corr

end InteractingSLE.Theorem14.BW1Prop
