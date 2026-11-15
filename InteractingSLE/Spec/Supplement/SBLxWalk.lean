/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxKernel

/-!
# The lower walk's live stages

Packet PROVE-T14-SBLEAVES3. Deterministic facts about the lower walk's machine used by SB3's stage induction:

* a finished state stays put (`run_eq_of_done`), so no instruction launches after it (`launches_eq_none_of_done`);
* a walk piece with infinite lifetime finishes the walk (`stStatus_run_succ_of_launch_top`);
* hence a launch at `k` means every earlier launched piece had finite lifetime (`lowerLive_of_launch`), i.e. the
  retained prefix `A` is a finite prefix, as SB2(1) assumes ("Let `A` be a finite lower-walk prefix").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Exist.Staged Exist.StagedLaw

section Machine

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A finished state stays put.** -/
theorem run_eq_of_done (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (h : stStatus (ExplState.run κ b jumps spec D n) = GW1Conn.stDone) :
    ∀ m, n ≤ m → ExplState.run κ b jumps spec D m = ExplState.run κ b jumps spec D n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    rw [run_succ]
    cases hk : spec.2.2[m]? with
    | none => exact ih
    | some a =>
      have hd : stStatus (ExplState.run κ b jumps spec D m) = GW1Conn.stDone := by rw [ih]; exact h
      change ExplState.step κ b jumps spec.2.1 D (ExplState.run κ b jumps spec D m) (a, m) =
        ExplState.run κ b jumps spec D n
      rw [← ih]
      rcases a with ⟨θ, t⟩ | r | ⟨v, r⟩
      · exact isTerminal_flowStep (Or.inl hd) m (D m) θ t
      · exact GW1WalkChain.contStep_of_done hd none r
      · exact GW1WalkChain.contStep_of_done hd (some v) r

/-- **No launch after a finished state.** -/
theorem launches_eq_none_of_done (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (h : stStatus (ExplState.run κ b jumps spec D n) = GW1Conn.stDone) {k : ℕ} (hk : n ≤ k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none := by
  rw [run_eq_of_done spec D h (k + 1) (by omega)]
  exact launches_run_of_le spec D hk

/-- **A launched piece with infinite lifetime finishes the walk** (for instructions with infinite instruction time,
e.g. every flow instruction of a boundary walk). -/
theorem stStatus_run_succ_of_launch_top (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) (ht : instrTime spec k = ⊤)
    (hD : (D k).2 = ⊤) : stStatus (ExplState.run κ b jumps spec D (k + 1)) = GW1Conn.stDone := by
  obtain ⟨-, hrun, -⟩ := eq_launch_of_launches spec D hl
  rw [hrun]
  exact (launch_eq_of_top _ k (D k) θ _ (by rw [ht, hD, min_self])).2.2.2.2.1

/-- Flow instructions of a boundary walk have infinite instruction time. -/
theorem instrTime_boundaryWalk_of_launch {θ₀ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ₀ right) D (k + 1)).2.2.2.1 k = some (c, θ)) :
    instrTime (boundaryWalkSpec b jumps θ₀ right) k = ⊤ := by
  obtain ⟨hi, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
  rcases Lv.mem_boundaryWalkSpec_prog (List.mem_of_getElem? hi) with h1 | h1
  · simp only [Sum.inl.injEq, Prod.mk.injEq] at h1
    exact h1.2
  · simp at h1

end Machine

/-! ### Live stages of the lower walk -/

section Live

variable {Ω : Type u}

/-- Instruction `k` of the lower walk launches at `ω`. -/
def LowerLaunch (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) : Prop :=
  (lowerWalkState κ b jumps E (k + 1) ω).2.2.2.1 k ≠ none

/-- **A live stage**: every piece launched before instruction `k` has finite lifetime (the retained prefix through
`k` instructions is a finite prefix of the walk). -/
def LowerLive (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) : Prop :=
  ∀ j < k, LowerLaunch κ b jumps E j ω → (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2 ≠ ⊤

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem LowerLive.of_succ {k : ℕ} {ω : Ω} (h : LowerLive κ b jumps E (k + 1) ω) : LowerLive κ b jumps E k ω :=
  fun j hj => h j (Nat.lt_succ_of_lt hj)

theorem LowerLive.zero (ω : Ω) : LowerLive κ b jumps E 0 ω := fun j hj => absurd hj (Nat.not_lt_zero j)

/-- **A launch happens only at a live stage**: a piece of infinite lifetime finishes the walk. -/
theorem lowerLive_of_launch {k : ℕ} {ω : Ω} (hl : LowerLaunch κ b jumps E k ω) : LowerLive κ b jumps E k ω := by
  intro j hj hlj htop
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlj
  have hdone := stStatus_run_succ_of_launch_top _ _ hcθ (instrTime_boundaryWalk_of_launch hcθ) htop
  exact hl (launches_eq_none_of_done _ _ hdone (by omega))

/-- At a live next stage, a piece launched at `k` has finite lifetime. -/
theorem LowerLive.ne_top_of_launch {k : ℕ} {ω : Ω} (h : LowerLive κ b jumps E (k + 1) ω)
    (hl : LowerLaunch κ b jumps E k ω) : (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2 ≠ ⊤ :=
  h k (Nat.lt_succ_self k) hl

end Live

end InteractingSLE.Theorem14.SB.Lx
