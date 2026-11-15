/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkSeedMove

/-! # The last connector transports an admissible original seed to the active word -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkMarkSeed

open Exist.Staged Exist.StagedLaw Restart WalkLaterSeed
open PiecewiseConstantBoundaryData (leftLim rightLim)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- At any later actual launch, the last connector moved to a mark beyond
the records just after the last launch. A zero first launch is allowed;
a zero later launch could not have been followed by another launch. -/
theorem restart_move_of_last_launch (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {ℓ k : ℕ} (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j = none)
    {β : BoundaryWord}
    (hI : GW2aConn.GInv b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D ℓ))
    (hreg : IsRegularDriver (D ℓ)) (hfin : (D ℓ).2 ≠ ⊤) :
    let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    ∃ (r : Bool) (w : ℝ), R k = ExplState.moveAlong (R (ℓ + 1)) r w true ∧
      (stRecR (R (ℓ + 1)) < w ∨ w < stRecL (R (ℓ + 1))) := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  obtain ⟨hle, hcont, hArc⟩ := GW1W.run_eq_of_last_launch hℓk hk hl hn
  change R k = ExplState.contStep κ b jumps (R (ℓ + 1)) none right at hcont
  have hLive : ¬ IsTerminal (R k) := fun ht => hk (isTerminal_run_of_le spec D ht k le_rfl).2
  have he := GW1W.launch_walk hl
  change R (ℓ + 1) = ExplState.launch (R ℓ) ℓ (D ℓ) θ ⊤ at he
  have hOld : ∀ r, stStatus (R (ℓ + 1)) ≠ GW1W.stArcM r := by
    intro r
    rw [he]
    exact WalkSeedFinite.launch_top_ne_arcM _ _ _ _ r
  have close
      (hR : GW2aConn.RStart κ b (R (ℓ + 1)) → stPt (R (ℓ + 1)) = stRecR (R (ℓ + 1)))
      (hL : GW2aConn.LStart κ b (R (ℓ + 1)) → stPt (R (ℓ + 1)) = stRecL (R (ℓ + 1))) :
      ∃ r w, R k = ExplState.moveAlong (R (ℓ + 1)) r w true ∧
        (stRecR (R (ℓ + 1)) < w ∨ w < stRecL (R (ℓ + 1))) := by
    obtain ⟨r, w, hm, hw⟩ := completed_connector_move (R (ℓ + 1)) right hOld
      (by rwa [← hcont]) (by rwa [← hcont]) hR hL
    exact ⟨r, w, hcont.trans hm, hw⟩
  by_cases hz : (D ℓ).2 = 0
  · have hℓ0 : ℓ = 0 := by
      by_contra hne
      have ht := WalkFreshRecord.terminal_after_later_zero D (Nat.pos_of_ne_zero hne) hl
        (by have hklen := (GW1W.even_of_launches_walk hk).2; omega) hz
      exact hLive (isTerminal_run_of_le spec D ht k hle).1
    subst ℓ
    obtain ⟨-, hR, hL⟩ := GW2aConn.launch_zero_eq hI 0 θ ⊤ hreg hz
    have hp := (GW1W.launch_zero (s := ExplState.init 0) (k := 0) (θ := θ) hz
      (by intro h; cases h)).2.1
    have hPt : stPt (R 1) = 0 := by rw [he]; exact hp
    have hRecR : stRecR (R 1) = 0 := by rw [he]; exact hR
    have hRecL : stRecL (R 1) = 0 := by rw [he]; exact hL
    exact close (fun _ => hPt.trans hRecR.symm) (fun _ => hPt.trans hRecL.symm)
  · rcases GW1W.launch_status_of_pos (s := R ℓ) (k := ℓ) (θ := θ) hfin hz with hs | hs | hs
    · have hp := (GW1W.launch_thr_true hfin hs).2.2.1
      rw [← he] at hs hp
      exact close (fun _ => hp) (fun h => by simp [GW2aConn.LStart, hs, stThr] at h)
    · have hp := (GW1W.launch_thr_false hfin hs).2.2.1
      rw [← he] at hs hp
      exact close (fun h => by simp [GW2aConn.RStart, hs, stThr] at h) (fun _ => hp)
    · have ht : IsTerminal (R (ℓ + 1)) := Or.inr (by rw [he]; exact hs)
      exact (hLive (isTerminal_run_of_le spec D ht k (by omega)).1).elim

/-- The actual last-launch formula has an admissible active seed at the
next launch. Both sides are read from untouched original boundary near the
selected new mark, so no global side-height bound is needed. -/
theorem admissible_next_word (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {ℓ k : ℕ} (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j = none)
    {β : BoundaryWord}
    (hI : GW2aConn.GInv b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D ℓ))
    (hreg : IsRegularDriver (D ℓ)) (hfin : (D ℓ).2 ≠ ⊤)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ (D ℓ)))) :
    let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    let γ := BoundaryWord.shiftW (((stChart (R (ℓ + 1))).1 0 - (stChart (R k)).1 0).re)
      (stopWord κ (β, θ, recOf ⊤ (D ℓ)))
    ExplState.IsAdmissibleSeed κ (leftLim γ.fn 0) (rightLim γ.fn 0) θ := by
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  let γ := stopWord κ (β, θ, recOf ⊤ (D ℓ))
  obtain ⟨r, w, hm, hw⟩ := restart_move_of_last_launch D hℓk hk hl hn hI hreg hfin
  change R k = ExplState.moveAlong (R (ℓ + 1)) r w true at hm
  have hG : GW2aConn.GInv b jumps γ (R (ℓ + 1)) := by
    have he := GW1W.launch_walk hl
    change R (ℓ + 1) = ExplState.launch (R ℓ) ℓ (D ℓ) θ ⊤ at he
    rw [he]
    exact GW2aConn.gInv_launch hκ hb hI ℓ θ ⊤ hreg hgood (GW1W.min_top_ne_top hfin)
  have ha := (WalkLaterSeed.laterLaunch_mark_seed D (by omega : 0 < k) hk).2
  change ExplState.IsAdmissibleSeed κ (leftLim b (stPt (R k))) (rightLim b (stPt (R k))) θ at ha
  rw [hm, GW1W.stPt_moveAlong] at ha
  change ExplState.IsAdmissibleSeed κ
    (leftLim (BoundaryWord.shiftW (((stChart (R (ℓ + 1))).1 0 - (stChart (R k)).1 0).re) γ).fn 0)
    (rightLim (BoundaryWord.shiftW (((stChart (R (ℓ + 1))).1 0 - (stChart (R k)).1 0).re) γ).fn 0) θ
  rw [hm, GW2aConn.shift_moveAlong]
  exact admissible_shift_of_gInv hb hG hw ha

end InteractingSLE.Theorem14.WalkMarkSeed
