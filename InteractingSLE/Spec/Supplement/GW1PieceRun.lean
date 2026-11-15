/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceChart
import InteractingSLE.Spec.Exist.StagedLawStruct

/-!
# GW1's properness, deterministic part: every piece of a run with regular launched pieces is closed

Packet PROVE-T14-GW1P. Along a staged history (any program; in particular the boundary walks of GW1) the chart of
the current domain is built from the recentred identity chart by real recentrings (boundary continuations,
`ExplState.moveAlong`) and Loewner steps after pieces stopped at a finite time (`ExplState.launch`). If every launched
piece has regular data (`PieceRegular`: continuous driver up to its stop, continuous generating trace, transient at
an infinite stop), then every chart along the run is good (`HasProperBdryExt`) and every recorded piece has a closed
tip set (`GW1P.isClosed_tipSet`).

## Main results

* `pieces_run_succ_of_noLaunch`, `chart_launch_of_top`: bookkeeping;
* **`isClosed_pieces_run`**: if each launch `k` recorded in the run (the launch record of the frozen
  `IsStagedHistory`, `(run (k + 1)).launches k = some (c, θ)`) has regular data `PieceRegular (D k).1 (min t_k ζ_k)`,
  then all charts along the run are good and all recorded pieces have closed tip sets;
* **`closure_tipSet_inter_H_subset_run`**: the conclusion in the form of `SB.GW1PieceProperStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GW1P

open Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A step without launch leaves the recorded pieces unchanged. -/
theorem pieces_run_succ_of_noLaunch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) :
    (ExplState.run κ b jumps spec D (k + 1)).1 = (ExplState.run κ b jumps spec D k).1 := by
  rw [run_succ] at h ⊢
  cases hk : spec.2.2[k]? with
  | none => rfl
  | some a =>
    rw [hk] at h
    simp only at h ⊢
    rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.2.1 k = none at h
      change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).1 = _
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t
        with e | e | e
      · rw [e]
      · rw [e]; rfl
      · rw [e, launches_launch, Function.update_self] at h; exact absurd h (by simp)
    all_goals
      change (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) _ pref).1 = _
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) _ pref
        with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e] <;> rfl

/-- A launch whose stop is `⊤` keeps the chart. -/
theorem chart_launch_of_top (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : min t D.2 = ⊤) : (ExplState.launch s k D θ t).2.2.2.2.1 = s.2.2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]

/-- **Along a run whose launched pieces are regular, every chart is good and every recorded piece is closed.** -/
theorem isClosed_pieces_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    HasProperBdryExt (ExplState.run κ b jumps spec D n).2.2.2.2.1 ∧
      ∀ p ∈ (ExplState.run κ b jumps spec D n).1, IsClosed (p.1.tipSet p.2.1 p.2.2) := by
  induction n with
  | zero =>
    refine ⟨hasProperBdryExt_recenter_id spec.1, fun p hp => ?_⟩
    simp [ExplState.run, ExplState.init] at hp
  | succ n ih =>
    obtain ⟨hc, hp⟩ := ih
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha, pieces_run_succ_of_noLaunch spec D hl]
      exact ⟨hc.recenter a, hp⟩
    · have hr := hreg n c θ hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he, CounterflowRange.pieces_launch]
      refine ⟨?_, fun p hp' => ?_⟩
      · rcases eq_or_ne (min (instrTime spec n) (D n).2) ⊤ with htop | htop
        · rw [chart_launch_of_top _ _ _ _ _ htop]
          exact hc
        · rw [chart_launch _ _ _ _ _ htop]
          exact hc.loewner_stopped hr htop
      · rcases List.mem_append.1 hp' with hq | hq
        · exact hp p hq
        · rw [List.mem_singleton] at hq
          subst hq
          exact isClosed_tipSet hc hr

/-- **GW1's piece properness for one run** (the form of `SB.GW1PieceProperStatement`): if every launched piece is
regular, every recorded piece of the completed run is relatively closed in `ℍ`. -/
theorem closure_tipSet_inter_H_subset_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    ∀ p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1,
      closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2 := fun p hp =>
  closure_inter_H_subset_of_isClosed ((isClosed_pieces_run spec D hreg _).2 p hp)

end GW1P

end Theorem14

end InteractingSLE
