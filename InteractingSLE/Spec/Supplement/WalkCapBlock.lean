/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideResume
import InteractingSLE.Spec.Supplement.GW1Later
import InteractingSLE.Spec.Supplement.GW1WalkFinishRun

/-!
# Non-launch of artificial walk caps from original seed data

Packet PROVE-T14-WALKSIDE2, seed continuation. At a skipped ordinary instruction,
the next artificial flow is also skipped. At an actual exit or at the program's
end it suffices that the original state is terminal or its seed is inadmissible.
These deterministic facts remove capped programs from the remaining input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkCapBlock

open Exist.Staged Exist.StagedLaw WalkSide

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A terminal state or an inadmissible non-root, non-tip seed cannot launch. -/
theorem flowStep_eq_self_of_seed (s : ExplState)
    (hroot : stStatus s ≠ .inl ()) (htip : stStatus s ≠ stTip)
    (hseed : IsTerminal s ∨
      ¬ ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ)
    (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) :
    ExplState.flowStep κ b false s k D θ t = s := by
  rcases hseed with ht | hna
  · exact isTerminal_flowStep ht k D θ t
  · obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, rR, rL⟩ := s
    rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · exact (hroot rfl).elim
    · exact (htip rfl).elim
    all_goals simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte, hna]

/-- A full-lifetime launch cannot end at the root or at an interior switch tip. -/
theorem launch_top_ne_root_tip (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) :
    stStatus (ExplState.launch s k D θ ⊤) ≠ .inl () ∧
      stStatus (ExplState.launch s k D θ ⊤) ≠ stTip := by
  by_cases htop : D.2 = ⊤
  · obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_top s k D θ ⊤ (by rw [htop]; rfl)
    rw [hst]
    constructor <;> intro h <;> cases h
  · obtain ⟨-, -, -, -, hst, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (by simpa only [min_top_left] using htop)
    rw [hst]
    simp only [lStatus, not_lt.2 (le_top : D.2 ≤ ⊤), ↓reduceIte]
    split_ifs
    · split <;> (constructor <;> intro h <;> cases h)
    all_goals constructor <;> intro h <;> cases h

/-- A complete boundary continuation cannot leave a root or an interior tip. -/
theorem contStep_ne_root_tip (s : ExplState) (right : Bool) :
    stStatus (ExplState.contStep κ b jumps s none right) ≠ .inl () ∧
      stStatus (ExplState.contStep κ b jumps s none right) ≠ stTip := by
  rcases GW1W.status_contStep (κ := κ) (b := b) (jumps := jumps) s right with
    ⟨r, hst⟩ | hst | hst <;> rw [hst] <;>
      constructor <;> intro h <;> cases h

/-- The decision not to launch is independent of the unused index, driver and own
time, provided the initial launch records at both tested indices are empty. -/
theorem noLaunch_flowStep_of_noLaunch (s : ExplState) {k j : ℕ}
    (hk : s.2.2.2.1 k = none) (hj : s.2.2.2.1 j = none)
    (D D' : (ℝ≥0 → ℝ) × ℝ≥0∞) (t t' : ℝ≥0∞)
    (hN : (ExplState.flowStep κ b false s k D θ t).2.2.2.1 k = none) :
    (ExplState.flowStep κ b false s j D' θ t').2.2.2.1 j = none := by
  have hK := launches_flowByStatus_ne_none_iff (κ := κ) (b := b)
    false (stStatus s) s hk D θ t
  have hJ := launches_flowByStatus_ne_none_iff (κ := κ) (b := b)
    false (stStatus s) s hj D' θ t'
  by_contra hnew
  rw [flowStep_eq_byStatus] at hnew
  have hold := hK.2 (hJ.1 hnew)
  rw [← flowStep_eq_byStatus] at hold
  exact hold hN

/-- Original-state seed data, without any artificial cap: every launched piece
ends at a terminal state or an inadmissible seed; so does the final program. -/
def WalkSeedData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  (∀ k, (R (k + 1)).2.2.2.1 k ≠ none →
    IsTerminal (R (k + 1)) ∨
      ¬ ExplState.IsAdmissibleSeed κ (ExplState.heights κ b (R (k + 1))).1
        (ExplState.heights κ b (R (k + 1))).2 θ) ∧
  (IsTerminal (R (boundaryWalkSpec b jumps θ right).2.2.length) ∨
    ¬ ExplState.IsAdmissibleSeed κ
      (ExplState.heights κ b (R (boundaryWalkSpec b jumps θ right).2.2.length)).1
      (ExplState.heights κ b (R (boundaryWalkSpec b jumps θ right).2.2.length)).2 θ)

/-- Original seed data imply non-launch at every artificial non-flow cap,
including the extra instruction appended at the end. -/
theorem noLaunch_capSpec_of_seedData {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hS : WalkSeedData κ b jumps θ right D)
    (ℓ : ℕ) (hℓ : ℓ ≤ (boundaryWalkSpec b jumps θ right).2.2.length)
    (hnon : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? ≠ some (Sum.inl (θ, ⊤))) :
    (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ 0)
      D (ℓ + 1)).2.2.2.1 ℓ = none := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  by_cases hend : ℓ = w.2.2.length
  · have hlen : 0 < w.2.2.length ∧ w.2.2.length % 2 = 0 := by
      dsimp only [w]
      rw [GW1WalkFinish.boundaryWalk_length]
      omega
    let j := w.2.2.length - 1
    have hjeq : j + 1 = w.2.2.length := by dsimp only [j]; omega
    have hcont : R w.2.2.length = ExplState.contStep κ b jumps (R j) none right := by
      rw [← hjeq]
      exact GW1W.run_succ_walk_cont (by omega : j < w.2.2.length) (by dsimp only [j]; omega)
    have hrt := contStep_ne_root_tip (κ := κ) (b := b) (jumps := jumps) (R j) right
    rw [← hcont] at hrt
    have hself := flowStep_eq_self_of_seed (R w.2.2.length) hrt.1 hrt.2 hS.2
      w.2.2.length (D w.2.2.length) 0
    rw [hend, run_capSpec_succ le_rfl D]
    change (ExplState.flowStep κ b false (R w.2.2.length) w.2.2.length
      (D w.2.2.length) θ 0).2.2.2.1 w.2.2.length = none
    rw [hself]
    exact launches_run_of_le w D le_rfl
  · have hlt : ℓ < w.2.2.length := lt_of_le_of_ne hℓ hend
    have hodd : ℓ % 2 = 1 := by
      rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left hlt] at hnon
      by_cases hev : ℓ % 2 = 0
      · exact (hnon (by rw [ite_eq_left hev])).elim
      · omega
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    have heven : k % 2 = 0 := by omega
    have hrun : R (k + 1) = ExplState.flowStep κ b false (R k) k (D k) θ ⊤ :=
      GW1W.run_succ_walk_flow (by omega) heven
    by_cases hl : (R (k + 1)).2.2.2.1 k = none
    · have hN : (ExplState.flowStep κ b false (R k) k (D k) θ ⊤).2.2.2.1 k = none := by
        rw [← hrun]
        exact hl
      have hsame : R (k + 1) = R k := hrun.trans
        (GW1W.flowStep_eq_self_of_noLaunch (R k) k (D k) θ ⊤ hN)
      rw [run_capSpec_succ hℓ D]
      change (ExplState.flowStep κ b false (R (k + 1)) (k + 1) (D (k + 1)) θ 0).2.2.2.1
        (k + 1) = none
      rw [hsame]
      exact noLaunch_flowStep_of_noLaunch (R k)
        (launches_run_of_le w D le_rfl) (launches_run_of_le w D (by omega))
        (D k) (D (k + 1)) ⊤ 0 hN
    · have hp : R (k + 1) = ExplState.launch (R k) k (D k) θ ⊤ := GW1W.launch_walk hl
      have hrt : stStatus (R (k + 1)) ≠ .inl () ∧ stStatus (R (k + 1)) ≠ stTip := by
        rw [hp]
        exact launch_top_ne_root_tip (R k) k (D k) θ
      have hself := flowStep_eq_self_of_seed (R (k + 1)) hrt.1 hrt.2 (hS.1 k hl)
        (k + 1) (D (k + 1)) 0
      rw [run_capSpec_succ hℓ D]
      change (ExplState.flowStep κ b false (R (k + 1)) (k + 1) (D (k + 1)) θ 0).2.2.2.1
        (k + 1) = none
      rw [hself]
      exact launches_run_of_le w D le_rfl

end InteractingSLE.Theorem14.WalkCapBlock
