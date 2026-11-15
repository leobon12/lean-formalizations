/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSeedFinite

/-!
# Finite completion from fresh admissible restart marks

Packet PROVE-T14-WALKSIDE2. The counting argument allows directions to change.
Its geometric input is that an admissible restart never repeats an earlier
mark. Finite-exit seed data are a separate input; infinite exits are terminal
by the existing deterministic launch semantics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkSeedFinite

open Exist.Staged Exist.StagedLaw GW1WalkFinish WalkCapBlock
open PiecewiseConstantBoundaryData (jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A state at which no further ordinary piece is needed or admissible. -/
def SeedBlocked (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) (s : ExplState) : Prop :=
  IsTerminal s ∨
    ¬ ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ

/-- At a positive round, a blocked seed stays blocked through the next round. -/
theorem seedBlocked_round_succ {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hn : n ≤ (jumpSet b jumps).card) (hn0 : 0 < n)
    (hS : SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n))) :
    SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * (n + 1))) := by
  let w := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps w D
  have hterminal (ht : IsTerminal (R (2 * n))) : SeedBlocked κ b θ (R (2 * (n + 1))) :=
    Or.inl ((isTerminal_run_of_le w D ht (2 * (n + 1)) (by omega)).1)
  rcases hS with ht | hbad
  · exact hterminal ht
  · rcases terminal_or_mark_at_round D (by omega : n ≤ (jumpSet b jumps).card + 1) hn0 with
      ht | ⟨r, hs, -⟩
    · exact hterminal ht
    · have hrt : stStatus (R (2 * n)) ≠ .inl () ∧ stStatus (R (2 * n)) ≠ stTip := by
        rw [hs]
        constructor <;> intro h <;> cases h
      have hself := flowStep_eq_self_of_seed (R (2 * n)) hrt.1 hrt.2 (Or.inr hbad)
        (2 * n) (D (2 * n)) ⊤
      have hf : R (2 * n + 1) = ExplState.flowStep κ b false (R (2 * n))
          (2 * n) (D (2 * n)) θ ⊤ :=
        GW1W.run_succ_walk_flow (by rw [boundaryWalk_length]; omega) (by omega)
      have hc : R (2 * (n + 1)) = ExplState.contStep κ b jumps (R (2 * n + 1)) none right := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
        exact GW1W.run_succ_walk_cont (by rw [boundaryWalk_length]; omega) (by omega)
      change SeedBlocked κ b θ (R (2 * (n + 1)))
      rw [hc, hf, hself, GW1W.contStep_eq_self _ right (Or.inl ⟨r, hs⟩)]
      exact Or.inr hbad

/-- A blocked positive round remains blocked at all later rounds of the walk. -/
theorem seedBlocked_round_mono {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n m : ℕ}
    (hn0 : 0 < n) (hnm : n ≤ m) (hm : m ≤ (jumpSet b jumps).card + 1)
    (hS : SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n))) :
    SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * m)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => simpa only [add_zero] using hS
  | succ d ih =>
    exact seedBlocked_round_succ D (by omega : n + d ≤ (jumpSet b jumps).card)
      (lt_of_lt_of_le hn0 (Nat.le_add_right n d)) (ih (by omega) (by omega))

/-- Only finite actual exits require a seed theorem. This predicate has no
condition on the final program state or on unused drivers. -/
def FiniteExitSeedData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  ∀ k, (R (k + 1)).2.2.2.1 k ≠ none → (D k).2 ≠ ⊤ → SeedBlocked κ b θ (R (k + 1))

/-- An admissible nonterminal original restart mark differs from every earlier
positive-round mark. This allows the continuation direction to change. -/
def FreshRestartData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  ∀ m n : ℕ, 0 < m → m < n → n ≤ (jumpSet b jumps).card + 1 →
    ¬ SeedBlocked κ b θ (R (2 * n)) → stPt (R (2 * m)) ≠ stPt (R (2 * n))

/-- There are too few original marks for all positive rounds to remain
admissible and fresh. This proves the final seed assertion without any fixed
orientation or additional termination hypothesis. -/
theorem seedBlocked_final_of_freshRestarts {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hF : FreshRestartData κ b jumps θ right D) :
    SeedBlocked κ b θ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (boundaryWalkSpec b jumps θ right).2.2.length) := by
  classical
  rw [boundaryWalk_length]
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  by_contra hlast
  have hnot (n : ℕ) (hn0 : 0 < n) (hn : n ≤ (jumpSet b jumps).card + 1) :
      ¬ SeedBlocked κ b θ (R (2 * n)) := by
    intro hs
    exact hlast (seedBlocked_round_mono D hn0 hn le_rfl hs)
  have hmark (i : Fin ((jumpSet b jumps).card + 1)) :
      stPt (R (2 * (i.val + 1))) ∈ jumpSet b jumps := by
    rcases terminal_or_mark_at_round D (by omega : i.val + 1 ≤ (jumpSet b jumps).card + 1)
      (by omega : 0 < i.val + 1) with ht | ⟨-, -, hm⟩
    · exact (hnot (i.val + 1) (by omega) (by omega) (Or.inl ht)).elim
    · exact hm
  let f : Fin ((jumpSet b jumps).card + 1) → jumpSet b jumps :=
    fun i => ⟨stPt (R (2 * (i.val + 1))), hmark i⟩
  have hfi : Function.Injective f := by
    intro i j hij
    have heq : stPt (R (2 * (i.val + 1))) = stPt (R (2 * (j.val + 1))) :=
      congrArg Subtype.val hij
    rcases lt_trichotomy i.val j.val with hlt | he | hgt
    · exact (hF (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)
        (hnot (j.val + 1) (by omega) (by omega)) heq).elim
    · exact Fin.ext he
    · exact (hF (j.val + 1) (i.val + 1) (by omega) (by omega) (by omega)
        (hnot (i.val + 1) (by omega) (by omega)) heq.symm).elim
  have hcard := Fintype.card_le_of_injective f hfi
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- Finite exits and fresh admissible restart marks suffice for the full
original seed data. Infinite lifetimes need no additional mathematical input. -/
theorem seedData_of_finiteExits_freshRestarts {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : FiniteExitSeedData κ b jumps θ right D)
    (hF : FreshRestartData κ b jumps θ right D) : WalkSeedData κ b jumps θ right D := by
  constructor
  · intro k hk
    by_cases ht : (D k).2 = ⊤
    · left
      rw [GW1W.launch_walk hk]
      exact isTerminal_launch_of_top _ k (D k) θ ⊤ (by rw [ht]; rfl)
    · exact hE k hk ht
  · exact seedBlocked_final_of_freshRestarts D hF

end InteractingSLE.Theorem14.WalkSeedFinite
