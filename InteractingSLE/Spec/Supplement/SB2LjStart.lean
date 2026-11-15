/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LjRule

/-!
# SB2(2): the concrete offset is the start configuration

Packet PROVE-SB2-LIFTSET (round 12). The concrete rule (`SB2LjRule`) pairs relative stage `j` with actual stage
`j + relOff`. This file shows `relOff` is the start configuration of the data clause, and fills the start data there:

* `entry_arc`, `entry_piece`: at the entry stage `R` is added (and not before), read at `startOff`;
* `arc_len`, **`piece_launch`**: an arc entry is within the program; a non-arc entry is a launch at `startOff` whose
  piece contains `R` (`first_stage_cases`);
* **`arcStartData_of_zeroRoot`**: at a zero root, `ArcStartData` holds at offset `relOff` for any relative family with
  a regular zero root at stage `0` (the concrete `EL`, `zeroDrv` on `cZ`), from GW1's stage data, `AllowedSt`, `PtRec`
  and the actual positivity `nz₁` (`arcStart_actual`; the gap since `R` is not a mark);
* **`markStart_concrete`**: at a mark entry, the actual piece-start fields at offset `relOff = startOff + 2`
  (`markStart`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv} {R : ℝ}

/-- At an arc entry, `R` is not in the physical part at stage `startOff + 1` and is at stage `startOff + 2`. -/
theorem entry_arc
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hA : ArcEntry κ θ b jumps R D) :
    (R : ℂ) ∉ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)) ∧
      (R : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1 + 1)) := by
  obtain ⟨hin, hmin⟩ := entryStage_spec κ θ b jumps hex
  have he := (startOff_eq κ θ b jumps R D).1 hA
  have hpos : 1 ≤ entryStage κ θ b jumps R D := by unfold ArcEntry at hA; omega
  refine ⟨?_, by rw [he]; exact hin⟩
  have h := hmin (entryStage κ θ b jumps R D - 1) (by omega)
  rwa [show entryStage κ θ b jumps R D - 1 + 1 = startOff κ θ b jumps R D + 1 by omega] at h

/-- At a non-arc entry, `R` is not in the physical part at stage `startOff` (given it is not at stage `0`) and is at
stage `startOff + 1`. -/
theorem entry_piece
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hA : ¬ ArcEntry κ θ b jumps R D)
    (h0 : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0)) :
    (R : ℂ) ∉ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D)) ∧
      (R : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)) := by
  obtain ⟨hin, hmin⟩ := entryStage_spec κ θ b jumps hex
  have he := (startOff_eq κ θ b jumps R D).2 hA
  rw [he]
  refine ⟨?_, hin⟩
  rcases Nat.eq_zero_or_pos (entryStage κ θ b jumps R D) with h | h
  · rw [h]; exact h0
  · have h' := hmin (entryStage κ θ b jumps R D - 1) (by omega)
    rwa [show entryStage κ θ b jumps R D - 1 + 1 = entryStage κ θ b jumps R D by omega] at h'

/-- An arc entry is within the program: `startOff + 1 < length`. -/
theorem arc_len
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hA : ArcEntry κ θ b jumps R D) :
    startOff κ θ b jumps R D + 1 < (boundaryWalkSpec b jumps θ true).2.2.length := by
  obtain ⟨hn, hn1⟩ := entry_arc hex hA
  have hev := startOff_even κ θ b jumps R D
  rcases first_stage_cases hn hn1 with ⟨-, h, -⟩ | ⟨hlen, -⟩ | ⟨hlen, -⟩
  · omega
  · exact hlen
  · exact hlen

/-- **A non-arc entry is a launch at `startOff`** whose piece contains `R`. -/
theorem piece_launch
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hA : ¬ ArcEntry κ θ b jumps R D)
    (h0 : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0)) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)).2.2.2.1
        (startOff κ θ b jumps R D) ≠ none ∧
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1) =
        ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D))
          (startOff κ θ b jumps R D) (D (startOff κ θ b jumps R D)) θ ⊤ ∧
      (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D))
          (D (startOff κ θ b jumps R D))).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D))
          (D (startOff κ θ b jumps R D))).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D))
          (D (startOff κ θ b jumps R D))).2.2 := by
  obtain ⟨hn, hn1⟩ := entry_piece hex hA h0
  have hev := startOff_even κ θ b jumps R D
  rcases first_stage_cases hn hn1 with ⟨hl, -, hlaunch, hmem⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact ⟨hl, hlaunch, hmem⟩
  · omega
  · omega

/-- **The arc start at a zero root, at offset `relOff`**: from GW1's stage data, `AllowedSt` and `PtRec` at the
connector stage and the actual positivity `nz₁`, every relative family with a regular zero root at stage `0` has
`ArcStartData` at `relOff` (the gap: `R` is not a mark). -/
theorem arcStartData_of_zeroRoot (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hS : GW1WalkExit.WalkStageData κ b jumps θ true D)
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hZ : ZeroRoot κ θ b jumps R D)
    (hA : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)))
    {D₂ : ℕ → Drv} (hreg : IsRegularDriver (D₂ 0)) (hz : D₂ 0 = zeroDrv)
    (hnz : ∀ k, 2 + relOff κ θ b jumps R D ≤ k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none → (D k).2 ≠ 0) :
    ArcStartData κ θ b jumps R D D₂ (relOff κ θ b jumps R D) := by
  have ho := relOff_of_not_mark κ θ b jumps hZ.2
  obtain ⟨hn, hn1⟩ := entry_arc hex hZ.1
  have hlen := arc_len hex hZ.1
  obtain ⟨hmove, hθ, hptR, hrec, hgap, hlow⟩ :=
    arcStart_actual hb hS (startOff_even κ θ b jumps R D) hlen hA hpt hn hn1
  have hgap' : ∀ y ∈ restartSet κ b jumps
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)), R < y := by
    rcases hgap with h | h
    · exact h
    · exact absurd ⟨hZ.1, h⟩ hZ.2
  rw [ho] at hnz ⊢
  exact { even := startOff_even κ θ b jumps R D, len := hlen, move := hmove, angle := hθ, pt := hptR,
          recLe := hrec, gap := hgap', low := hlow hgap', reg₀ := hreg, zero₀ := by rw [hz]; exact zeroDrv_snd,
          nz₁ := hnz }

/-- **The piece start at a mark entry, at offset `relOff = startOff + 2`**: the actual fields of `markStart` (launch,
not a tip, `pt = R`, `recR ≤ R`, `R` on the launched piece). -/
theorem markStart_concrete (hW : WalkChainFacts κ b jumps θ D) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hS : GW1WalkExit.WalkStageData κ b jumps θ true D)
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hM : MarkEntry κ θ b jumps R D)
    (hA : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)))
    (hlen : relOff κ θ b jumps R D < (boundaryWalkSpec b jumps θ true).2.2.length) {N : ℕ}
    (hd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) = stDone)
    (hoN : relOff κ θ b jumps R D ≤ N) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 1) =
        ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
          (relOff κ θ b jumps R D) (D (relOff κ θ b jumps R D)) θ ⊤ ∧
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) ≠
        .inr (.inl ()) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) = R ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) ≤ R ∧
      (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
          (D (relOff κ θ b jumps R D))).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
          (D (relOff κ θ b jumps R D))).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
          (D (relOff κ θ b jumps R D))).2.2 := by
  rw [relOff_of_mark κ θ b jumps hM] at hlen hoN ⊢
  obtain ⟨hn, hn1⟩ := entry_arc hex hM.1
  have hlen1 := arc_len hex hM.1
  obtain ⟨hmove, -, -, hrec, -, -⟩ := arcStart_actual hb hS (startOff_even κ θ b jumps R D) hlen1 hA hpt hn hn1
  exact markStart hW (startOff_even κ θ b jumps R D) hlen hd hoN hmove hM.2 hrec hn hn1

end InteractingSLE.Theorem14.SB.Lk
