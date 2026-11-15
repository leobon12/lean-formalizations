/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.ExplState_run
import InteractingSLE.Frozen.Spec.pastSigma

/-!
# Staged histories: deterministic facts about the run of a program

Packet PROVE-STAGED. Facts about the frozen semantics `ExplState.run` used to build a staged history one instruction at
a time:

* `run_succ`: one more instruction is one more `ExplState.step` (or nothing past the end of the program);
* `run_congr`: the state after `k` instructions only depends on the drivers of the instructions `j < k`;
  `pastSigma_congr`: so does the retained σ-algebra before instruction `k`;
* `launches_step_indep`: the launch record of a step does not depend on the drivers; `launches_run_succ_congr`;
* `launches_run_of_le`: no launch is recorded at an index not yet run;
* `angle_of_launch`: if instruction `k` launches a piece at angle `θ`, then `θ` is the angle of the instruction
  (`instrAngle`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Staged

/-- The angle of instruction `k` of a program (`0` if it is not an ordinary-piece instruction). -/
def instrAngle (spec : ExplSpec) (k : ℕ) : ℝ :=
  match spec.2.2[k]? with
  | some (Sum.inl (θ, _)) => θ
  | _ => 0

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- One more instruction is one more step. -/
theorem run_succ (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    ExplState.run κ b jumps spec D (k + 1) =
      match spec.2.2[k]? with
      | none => ExplState.run κ b jumps spec D k
      | some a => ExplState.step κ b jumps spec.2.1 D (ExplState.run κ b jumps spec D k) (a, k) := by
  unfold ExplState.run
  rw [List.take_add_one, List.foldl_append, List.getElem?_zipIdx]
  cases spec.2.2[k]? <;> simp

/-- A step only reads the driver of its own instruction. -/
theorem step_congr (gw2 : Bool) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (s : ExplState) (ik : Instr × ℕ)
    (h : D ik.2 = D' ik.2) : ExplState.step κ b jumps gw2 D s ik = ExplState.step κ b jumps gw2 D' s ik := by
  unfold ExplState.step
  rw [h]

/-- **The state after `k` instructions only depends on the drivers of the instructions `j < k`.** -/
theorem run_congr (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (h : ∀ j < k, D j = D' j) :
    ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_succ, run_succ, ih fun j hj => h j (Nat.lt_succ_of_lt hj)]
    cases spec.2.2[k]? with
    | none => rfl
    | some a => exact step_congr _ _ _ (h k (Nat.lt_succ_self k))

/-- The retained σ-algebra before instruction `k` only depends on the drivers of the instructions `j < k`. -/
theorem pastSigma_congr {Ω : Type u} (spec : ExplSpec) {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ∀ j < k, E j = E' j) : pastSigma κ b jumps spec E k = pastSigma κ b jumps spec E' k := by
  unfold pastSigma
  congr 1
  funext ω i
  rw [run_congr spec (D := fun j => E j ω) (D' := fun j => E' j ω) fun j hj => by rw [h j hj]]

/-! ### The launch record -/

theorem launches_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).2.2.2.1 = Function.update s.2.2.2.1 k (some (s.2.2.2.2.1, θ)) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  split_ifs <;> (try split) <;> rfl

theorem launches_moveAlong (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) :
    (ExplState.moveAlong s right x atMark).2.2.2.1 = s.2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem launches_moveToEnd (s : ExplState) (right : Bool) :
    (ExplState.moveToEnd s right).2.2.2.1 = s.2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem launches_contStep (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    (ExplState.contStep κ b jumps s vStop pref).2.2.2.1 = s.2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first
    | rfl
    | split

/-- The launch record of a flow step: unchanged, or the launch at its own index with the current chart. -/
theorem launches_flowStep (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.flowStep κ b gw2 s k D θ t).2.2.2.1 = s.2.2.2.1 ∨
      (ExplState.flowStep κ b gw2 s k D θ t).2.2.2.1 = Function.update s.2.2.2.1 k (some (s.2.2.2.2.1, θ)) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  repeat' first
    | (right; rw [launches_launch])
    | (left; rfl)
    | split

/-- The launch record of a flow step does not depend on the driver. -/
theorem launches_flowStep_indep (gw2 : Bool) (s : ExplState) (k : ℕ) (D D' : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (t : ℝ≥0∞) :
    (ExplState.flowStep κ b gw2 s k D θ t).2.2.2.1 = (ExplState.flowStep κ b gw2 s k D' θ t).2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  repeat' first
    | (rw [launches_launch, launches_launch])
    | rfl
    | split

/-- **The launch record of a step does not depend on the drivers.** -/
theorem launches_step_indep (gw2 : Bool) (D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ExplState) (ik : Instr × ℕ) :
    (ExplState.step κ b jumps gw2 D s ik).2.2.2.1 = (ExplState.step κ b jumps gw2 D' s ik).2.2.2.1 := by
  obtain ⟨ins, k⟩ := ik
  unfold ExplState.step
  rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · exact launches_flowStep_indep _ _ _ _ _ _ _
  · rfl
  · rfl

/-- The launch record of instruction `k` only depends on the drivers of the instructions `j < k`. -/
theorem launches_run_succ_congr (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ∀ j < k, D j = D' j) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 = (ExplState.run κ b jumps spec D' (k + 1)).2.2.2.1 := by
  rw [run_succ, run_succ, run_congr spec h]
  cases spec.2.2[k]? with
  | none => rfl
  | some a => exact launches_step_indep _ _ _ _ _

/-- A step at index `j` only changes the launch record at `j`. -/
theorem launches_step_of_ne (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ExplState) (ins : Instr) {j k : ℕ}
    (hjk : j ≠ k) : (ExplState.step κ b jumps gw2 D s (ins, j)).2.2.2.1 k = s.2.2.2.1 k := by
  unfold ExplState.step
  rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · rcases launches_flowStep (κ := κ) (b := b) gw2 s j (D j) θ t with h | h
    · exact congrFun h k
    · rw [h, Function.update_of_ne hjk.symm]
  · exact congrFun (launches_contStep s none pref) k
  · exact congrFun (launches_contStep s (some v) pref) k

/-- No launch is recorded at an index not yet run. -/
theorem launches_run_of_le (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n k : ℕ} (hnk : n ≤ k) :
    (ExplState.run κ b jumps spec D n).2.2.2.1 k = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    cases spec.2.2[n]? with
    | none => exact ih (Nat.le_of_succ_le hnk)
    | some a =>
      rw [launches_step_of_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_of_succ_le hnk))]
      exact ih (Nat.le_of_succ_le hnk)

/-- **A launch at instruction `k` has the angle of the instruction.** -/
theorem angle_of_launch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {c : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) : θ = instrAngle spec k := by
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  rw [run_succ] at h
  unfold instrAngle
  cases hk : spec.2.2[k]? with
  | none => rw [hk] at h; rw [h0] at h; exact absurd h (by simp)
  | some a =>
    rw [hk] at h
    simp only at h
    unfold ExplState.step at h
    rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · rcases launches_flowStep (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t
        with e | e
      · simp only at h; rw [e, h0] at h; exact absurd h (by simp)
      · simp only at h; rw [e, Function.update_self] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
    · simp only at h; rw [launches_contStep, h0] at h; exact absurd h (by simp)
    · simp only at h; rw [launches_contStep, h0] at h; exact absurd h (by simp)

end Staged

end Exist

end InteractingSLE
