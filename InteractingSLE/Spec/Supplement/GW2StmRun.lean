/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwcCarrier
import InteractingSLE.Spec.Supplement.GW2TipSystemGB6
import InteractingSLE.Spec.Supplement.GW2LaterMeas

/-!
# GW2's stage step, part 10: the retained prefix of a GW2 schedule run

Packet PROVE-GW2-STAGEMEAN, step round. Bookkeeping for the launch datum `GW2TipSystem.HasLaunchPairEq` along a GW2
flow program whose first pieces were successful (`GW2Schedule.AllSucc`), from the explicit run
`GW2TipSystem.Swc.run_pieces_arcs` (the pieces are `livePiece`, no real connectors):

* **`contactSet_eq_prefixPhysSet`**: the retained prefix of the datum is GW1's old union `SB.prefixPhysSet`;
* **`contactSet_succ`**: the retained prefix grows by the physical tips of the new piece, read in its launch chart;
* **`contactSet_eq_of_recOf_eq`**: equal records of the successful (continuous) pieces give the same retained prefix.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Stm

open GW2Schedule Exist Staged StagedLaw GW2TipSystem GW2TipSystem.Swc

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}

/-- **The retained prefix is GW1's old union** along a successful GW2 run (there are no connectors). -/
theorem contactSet_eq_prefixPhysSet (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hk : k ≤ spec.2.2.length) (hs : AllSucc Δ D k) :
    contactSet κ b jumps spec D k = SB.prefixPhysSet κ b jumps spec D k := by
  obtain ⟨-, harcs⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) (D := D) hgw hprog hΔ k hk hs
  unfold contactSet SB.prefixPhysSet
  simp only [harcs, List.not_mem_nil, iUnion_of_empty, iUnion_empty, union_empty]

/-- **The retained prefix grows by the new piece.** -/
theorem contactSet_succ (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {j : ℕ} (hk : j + 1 ≤ spec.2.2.length) (hs : AllSucc Δ D (j + 1)) :
    contactSet κ b jumps spec D (j + 1) = contactSet κ b jumps spec D j ∪
      (succChart spec.1 Δ D j).tipSet (fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min (Δ j) (D j).2)).toNNReal)
        (min (Δ j) (D j).2) := by
  obtain ⟨hp1, -⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) (D := D) hgw hprog hΔ (j + 1) hk hs
  obtain ⟨hp0, -⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) (D := D) hgw hprog hΔ j
    (Nat.le_of_succ_le hk) (allSucc_succ.1 hs).1
  unfold contactSet
  rw [hp1, hp0, List.range_succ, List.map_append, List.map_singleton]
  ext z
  simp only [mem_union, mem_singleton_iff, mem_iUnion, exists_prop, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (hz | ⟨p, hp | rfl, hz⟩)
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr ⟨p, hp, hz⟩)
    · exact Or.inr hz
  · rintro ((hz | ⟨p, hp, hz⟩) | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨p, Or.inl hp, hz⟩
    · exact Or.inr ⟨_, Or.inr rfl, hz⟩

/-- **Equal records of the successful pieces give the same retained prefix.** -/
theorem contactSet_eq_of_recOf_eq (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hk : k ≤ spec.2.2.length) (hs : AllSucc Δ D k) (hs' : AllSucc Δ D' k)
    (hc : ∀ j < k, ContinuousOn (D j).1 {t | (t : ℝ≥0∞) ≤ Δ j})
    (hc' : ∀ j < k, ContinuousOn (D' j).1 {t | (t : ℝ≥0∞) ≤ Δ j})
    (h : ∀ j < k, recOf (Δ j) (D j) = recOf (Δ j) (D' j)) :
    contactSet κ b jumps spec D k = contactSet κ b jumps spec D' k := by
  obtain ⟨hp, -⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) (D := D) hgw hprog hΔ k hk hs
  obtain ⟨hp', -⟩ := run_pieces_arcs (κ := κ) (b := b) (jumps := jumps) (D := D') hgw hprog hΔ k hk hs'
  have hlive : ∀ i ∈ List.range k, livePiece spec.1 Δ D i = livePiece spec.1 Δ D' i := by
    intro i hi
    have hik := List.mem_range.1 hi
    have hsi := hs i hik
    have hsi' := hs' i hik
    have hchart := GW2Later.succChart_eq_of_recOf_eq spec.1 hΔ i (hs.mono hik.le) (hs'.mono hik.le)
      (fun j hj => hc j (hj.trans hik)) (fun j hj => hc' j (hj.trans hik)) (fun j hj => h j (hj.trans hik))
    have hf : (fun t : ℝ≥0 => (D i).1 (min (t : ℝ≥0∞) (Δ i)).toNNReal) =
        fun t : ℝ≥0 => (D' i).1 (min (t : ℝ≥0∞) (Δ i)).toNNReal := by
      refine Continuous.ext_on Exist.StagedLaw.denseRange_rat_toNNReal
        (GW2Later.continuous_stopAt (hΔ i) (hc i hik)) (GW2Later.continuous_stopAt (hΔ i) (hc' i hik)) ?_
      rintro _ ⟨q, rfl⟩
      have h1 := congrFun (congrArg Prod.fst (h i hik)) q
      simp only [recOf, readRec, retOf, min_eq_left hsi.le, min_eq_left hsi'.le] at h1
      exact h1
    simp only [livePiece, min_eq_left hsi.le, min_eq_left hsi'.le, hchart, hf]
  unfold contactSet
  rw [hp, hp', List.map_congr_left hlive]
end InteractingSLE.Theorem14.GW2Stm
