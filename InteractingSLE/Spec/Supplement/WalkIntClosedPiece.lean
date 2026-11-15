/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedRun

/-!
# A completed finite recorded piece has its exact prefix hull model

At the full finite lifetime, the prefix chart is exactly the chart just
after the original launch. Run regularity therefore supplies its model,
normalization and proper boundary extension without a live-time premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry WalkIntCanon Exist.StagedLaw

/-- A completed final piece contains the entire recorded ordinary set. -/
theorem prefixSet_at_stop_eq_wsetOf {s : ExplState} {pre : List Piece} {pc : Piece}
    (hs : s.1 = pre ++ [pc]) (hfin : pc.2.2 ≠ ⊤) :
    prefixSet pre pc pc.2.2.toNNReal = wsetOf s := by
  ext z
  simp only [prefixSet, wsetOf, ordOf, hs, ENNReal.coe_toNNReal hfin,
    mem_inter_iff, mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hz | hz, hzH⟩
    · obtain ⟨q, hq, hz⟩ := hz
      exact ⟨⟨q, Or.inl hq, hz⟩, hzH⟩
    · exact ⟨⟨pc, Or.inr rfl, hz⟩, hzH⟩
  · rintro ⟨⟨q, hq | hq, hz⟩, hzH⟩
    · exact ⟨Or.inl ⟨q, hq, hz⟩, hzH⟩
    · subst q
      exact ⟨Or.inr hz, hzH⟩

/-- Completing a recorded finite piece gives a normalized physical model
in its actual prefix chart. Its raw filling identity is a conclusion. -/
theorem exists_completed_prefix_model {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (w : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime w k) (D k).2))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps w D w.2.2.length).1 = pre ++ pc :: post)
    (hfin : pc.2.2 ≠ ⊤) :
    ∃ M : HullModel (prefixChart pc pc.2.2.toNNReal),
      IsNormalized (prefixChart pc pc.2.2.toNNReal) ∧
      GW1P.HasProperBdryExt (prefixChart pc pc.2.2.toNNReal) ∧
      M.hull = fillH (prefixSet pre pc pc.2.2.toNNReal) := by
  obtain ⟨k, _, θ', hl, hpre, hpc⟩ := WalkSide.exists_launch_of_pieces_eq
    w D w.2.2.length hs
  obtain ⟨_, he, _⟩ := eq_launch_of_launches w D hl
  have hS : min (instrTime w k) (D k).2 ≠ ⊤ := by
    simpa only [hpc, WalkSide.recPiece] using hfin
  have hchart : prefixChart pc pc.2.2.toNNReal =
      stChart (ExplState.run κ b jumps w D (k + 1)) := by
    change prefixChart pc pc.2.2.toNNReal =
      (ExplState.run κ b jumps w D (k + 1)).2.2.2.2.1
    rw [he, chart_launch _ _ _ _ _ hS, hpc]
    rfl
  have hpieces : (ExplState.run κ b jumps w D (k + 1)).1 = pre ++ [pc] := by
    rw [he, CounterflowRange.pieces_launch, hpre]
    change pre ++ [WalkSide.recPiece _ _ _] = pre ++ [pc]
    rw [← hpc]
  have hset := prefixSet_at_stop_eq_wsetOf hpieces hfin
  have hnot : stStatus (ExplState.run κ b jumps w D (k + 1)) ≠ stDone := by
    rw [he]
    exact status_launch_ne_done _ _ _ _ _ hS
  rw [hchart, hset]
  obtain ⟨M⟩ := exists_hullModel_runChart w D (k + 1) (fun j _ => hreg j)
  exact ⟨M, isNormalized_runChart w D (k + 1) (fun j _ => hreg j),
    (GW1P.isClosed_pieces_run w D hreg (k + 1)).1,
    hull_eq_fillH_wsetOf_run w D hreg (k + 1) hnot M⟩

end InteractingSLE.Theorem14.WalkIntClosed
