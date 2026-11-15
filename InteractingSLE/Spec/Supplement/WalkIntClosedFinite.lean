/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedOrder
import InteractingSLE.Spec.Supplement.WalkIntActualPrefix

/-!
# Physical prefix families for finite and infinite last pieces

A finite final ordinary piece can be retained completely. Its raw set is
the whole ordinary walk, so no endpoint collar is lost. An infinite final
piece is exhausted at integer own times. Both constructions use actual
recorded prefixes and dominate every closed-time prefix of the run.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry WalkIntCanon Exist.StagedLaw

/-- Completing a finite last piece gives exactly the entire ordinary
support, even when the run later ends by a zero-capacity real connector. -/
theorem exists_full_closedPrefix_of_last_finite {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} (w : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime w k) (D k).2))
    {pre : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps w D w.2.2.length).1 = pre ++ [pc])
    (hfin : pc.2.2 ≠ ⊤) :
    ∃ R : ClosedPrefix (ExplState.run κ b jumps w D w.2.2.length),
      R.raw = wsetOf (ExplState.run κ b jumps w D w.2.2.length) := by
  obtain ⟨M, hn, hp, hf⟩ := exists_completed_prefix_model w D hreg hs hfin
  refine ⟨⟨pre, [], pc, pc.2.2.toNNReal, hs, ENNReal.coe_toNNReal_le_self,
    M, hn, hp, hf⟩, ?_⟩
  exact prefixSet_at_stop_eq_wsetOf hs hfin

/-- A regular boundary run with a last recorded piece has a nested,
cofinal closed-prefix family covering the ordinary walk near every point.
The final lifetime is allowed to be finite, zero, or infinite. -/
theorem exists_closedPrefix_family_of_last_piece {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') → GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k)) {pre : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ [pc]) :
    let s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length
    ∃ R : ℕ → ClosedPrefix s, Monotone (fun n => (R n).raw) ∧
      (∀ Q : ClosedPrefix s, ∃ n, Q.raw ⊆ (R n).raw) ∧
      ∀ p : ℂ, ∃ n, wsetOf s ∩ ball p 1 ⊆ (R n).raw := by
  let s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    (boundaryWalkSpec b jumps θ right).2.2.length
  change ∃ R : ℕ → ClosedPrefix s, Monotone (fun n => (R n).raw) ∧
    (∀ Q : ClosedPrefix s, ∃ n, Q.raw ⊆ (R n).raw) ∧
    ∀ p : ℂ, ∃ n, wsetOf s ∩ ball p 1 ⊆ (R n).raw
  by_cases htop : pc.2.2 = ⊤
  · have hx (n : ℕ) : ∃ Q : ClosedPrefix s, Q.raw = prefixSet pre pc (n : ℝ≥0) := by
      have hn : ((n : ℝ≥0) : ℝ≥0∞) ≤ pc.2.2 := by rw [htop]; exact le_top
      obtain ⟨Q, hpre, _, hpc, htime⟩ := exists_closedPrefix θ right D hreg hD hs hn
      refine ⟨Q, ?_⟩
      rw [ClosedPrefix.raw, hpre, hpc, htime]
    choose R hR using hx
    refine ⟨R, ?_, ?_, ?_⟩
    · intro m n hmn
      change (R m).raw ⊆ (R n).raw
      rw [hR m, hR n]
      exact prefixSet_mono_time pre pc (by exact_mod_cast hmn)
    · intro Q
      obtain ⟨n, hn⟩ := exists_nat_ge Q.time
      refine ⟨n, Q.raw_subset_last_prefix hs |>.trans ?_⟩
      rw [hR n]
      exact prefixSet_mono_time pre pc hn
    · intro p
      obtain ⟨hc, hp⟩ := WalkIntActual.recorded_infinite_piece_facts _ D hreg hs htop
      obtain ⟨τ, hτ⟩ := WalkIntActual.exists_prefixSet_collar_of_last_infinite hs htop hc hp p
      obtain ⟨n, hn⟩ := exists_nat_ge τ
      refine ⟨n, hτ.trans ?_⟩
      rw [hR n]
      exact prefixSet_mono_time pre pc hn
  · obtain ⟨Q, hQ⟩ := exists_full_closedPrefix_of_last_finite _ D hreg hs htop
    refine ⟨fun _ => Q, monotone_const, ?_, ?_⟩
    · intro P
      refine ⟨0, ?_⟩
      rw [hQ]
      exact P.raw_subset
    · intro p
      refine ⟨0, ?_⟩
      rw [hQ]
      exact inter_subset_left

end InteractingSLE.Theorem14.WalkIntClosed
