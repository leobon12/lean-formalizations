/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Launch
import InteractingSLE.Spec.Exist.StagedLawStruct
import InteractingSLE.Spec.Exist.StagedLawRun
import InteractingSLE.Frozen.Spec.scheduleProgram

/-!
# The run of a GW2 schedule: which pieces launch, and in which chart

Packet PROVE-T14-TIP3. Lemma GW2 (`source/spec/p577-624.md` L989–L1038, p. 621): "For each fixed root and finite angle
list, run successive canonical conditional pieces through the proposed ordered time tuple, stopping an unsuccessful
attempt at its first continuation threshold."

A GW2 schedule (`ExplSpec` `⟨x₀, true, scheduleProgram 0 l⟩`) is a *flow program*: instruction `j` runs a piece at angle
`θ j` for own time `Δ j` (`IsFlowProg`), in the GW2 convention (`gw2 = true`: no switch after a threshold). This file
describes its frozen run (`ExplState.run`) deterministically, for any drivers `D`:

* piece `k` launches exactly when every earlier piece stopped strictly before its lifetime (`AllSucc`);
* it is then launched in the chart `succChart x₀ Δ D k`, the root translation followed by the centred Loewner maps of
  the earlier stopped pieces;
* its retained datum is `retOf (Δ k) (D k)`.

## Main results

* `isFlowProg_scheduleProgram`: a schedule program is a flow program, with finite own times;
* `run_gw2`: the status and chart of the run of a GW2 flow program;
* `launches_run_gw2`, `retained_run_gw2`: the launch record and the retained datum of each instruction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw

/-! ### Flow programs -/

/-- `prog` is a **flow program** with angles `θ` and own times `Δ`: its instruction `j` is the flow instruction
`(θ j, Δ j)`. -/
def IsFlowProg (prog : List Instr) (θ : ℕ → ℝ) (Δ : ℕ → ℝ≥0∞) : Prop :=
  ∀ j < prog.length, prog[j]? = some (Sum.inl (θ j, Δ j))

/-- The angle of the `j`-th entry of a schedule. -/
def schedAngle (l : List (ℝ × ℝ≥0)) (j : ℕ) : ℝ := (l.getD j (0, 0)).1

/-- The time of the `j`-th entry of a schedule (`τ₀` before the first one). -/
def schedTime (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) : ℕ → ℝ≥0
  | 0 => τ₀
  | j + 1 => (l.getD j (0, 0)).2

/-- The own time of the `j`-th piece of a schedule: `τ_j − τ_{j−1}`. -/
def schedDelta (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) (j : ℕ) : ℝ≥0∞ :=
  (((l.getD j (0, 0)).2 - schedTime τ₀ l j : ℝ≥0) : ℝ≥0∞)

theorem schedDelta_ne_top (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) (j : ℕ) : schedDelta τ₀ l j ≠ ⊤ :=
  ENNReal.coe_ne_top

theorem length_scheduleProgram (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) : (scheduleProgram τ₀ l).length = l.length := by
  induction l generalizing τ₀ with
  | nil => rfl
  | cons p l ih => simp only [scheduleProgram, List.length_cons, ih]

/-- **A schedule program is a flow program**, with the schedule's angles and own times. -/
theorem isFlowProg_scheduleProgram (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    IsFlowProg (scheduleProgram τ₀ l) (schedAngle l) (schedDelta τ₀ l) := by
  induction l generalizing τ₀ with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | cons p l ih =>
    intro j hj
    rcases j with _ | j
    · rfl
    · have hj' : j < (scheduleProgram p.2 l).length := by
        simpa only [scheduleProgram, List.length_cons, Nat.add_lt_add_iff_right] using hj
      have e1 : (scheduleProgram τ₀ (p :: l))[j + 1]? = (scheduleProgram p.2 l)[j]? := rfl
      have e2 : schedAngle (p :: l) (j + 1) = schedAngle l j := rfl
      have e3 : schedDelta τ₀ (p :: l) (j + 1) = schedDelta p.2 l j := by rcases j with _ | j <;> rfl
      rw [e1, e2, e3]
      exact ih p.2 j hj'

/-! ### Successful pieces and their charts -/

/-- Every piece before `k` stopped strictly before its lifetime. -/
def AllSucc (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Prop := ∀ j < k, Δ j < (D j).2

theorem allSucc_zero (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : AllSucc Δ D 0 :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem allSucc_succ {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} :
    AllSucc Δ D (k + 1) ↔ AllSucc Δ D k ∧ Δ k < (D k).2 := by
  constructor
  · intro h; exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)⟩
  · rintro ⟨h, hk⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h j hj
    · exact hk

theorem AllSucc.mono {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k k' : ℕ} (h : AllSucc Δ D k) (hk : k' ≤ k) :
    AllSucc Δ D k' := fun j hj => h j (lt_of_lt_of_le hj hk)

/-- The chart after the first `k` pieces, all successful: the translation to the root followed by the centred Loewner
maps of the stopped pieces. -/
def succChart (x₀ : ℝ) (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : ℕ → Chart
  | 0 => Chart.id.recenter x₀
  | k + 1 => (succChart x₀ Δ D k).loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))

/-- The chart after the first `k` pieces only depends on their drivers. -/
theorem succChart_congr (x₀ : ℝ) (Δ : ℕ → ℝ≥0∞) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} :
    ∀ {k : ℕ}, (∀ j < k, D j = D' j) → succChart x₀ Δ D k = succChart x₀ Δ D' k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [succChart]
    rw [succChart_congr x₀ Δ fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)]

/-! ### The run -/

/-- A stuck status: a continuation threshold or dead. -/
def IsStuck (st : ExplStatus) : Prop := st = stDead ∨ ∃ o, st = stThr o

/-- A live status: the root or an interior tip. -/
def IsLive (st : ExplStatus) : Prop := st = .inl () ∨ st = stTip

theorem flowStep_of_isStuck {κ : ℝ} {b : ℝ → ℝ} (s : ExplState) (hs : IsStuck (stStatus s)) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    IsStuck (stStatus (ExplState.flowStep κ b true s k D θ t)) ∧
      (ExplState.flowStep κ b true s k D θ t).2.2.2.1 = s.2.2.2.1 ∧
      (ExplState.flowStep κ b true s k D θ t).2.2.1 = s.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with h | ⟨o, h⟩
  · change status = stDead at h
    subst h
    exact ⟨Or.inl rfl, rfl, rfl⟩
  · change status = stThr o at h
    subst h
    exact ⟨Or.inl rfl, rfl, rfl⟩

theorem flowStep_of_isLive {κ : ℝ} {b : ℝ → ℝ} (s : ExplState) (hs : IsLive (stStatus s)) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b true s k D θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with h | h
  · change status = .inl () at h
    subst h
    rfl
  · change status = stTip at h
    subst h
    rfl

/-- The status after a launch with a finite stop: a tip when the piece stopped before its lifetime, stuck otherwise. -/
theorem status_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    (t < D.2 → stStatus (ExplState.launch s k D θ t) = stTip) ∧
      (¬ t < D.2 → IsStuck (stStatus (ExplState.launch s k D θ t))) := by
  have hne : min t D.2 ≠ ⊤ := ne_top_of_le_ne_top ht (min_le_left _ _)
  rw [(launch_eq_of_ne_top s k D θ t hne).2.2.2.2.1]
  refine ⟨fun h => by simp only [lStatus, h, ↓reduceIte], fun h => ?_⟩
  simp only [lStatus, h, ↓reduceIte]
  split_ifs
  · rcases stStatus s with _ | _ | _ | _ | _ | _ <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The run of a GW2 flow program.** Before instruction `k`: if every earlier piece was successful, the status is
live and the chart is `succChart`; otherwise the history is stuck. -/
theorem run_gw2 {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k ≤ spec.2.2.length,
      (AllSucc Δ D k → IsLive (stStatus (ExplState.run κ b jumps spec D k)) ∧
        stChart (ExplState.run κ b jumps spec D k) = succChart spec.1 Δ D k) ∧
      (¬ AllSucc Δ D k → IsStuck (stStatus (ExplState.run κ b jumps spec D k)))
  | 0, _ => by
    refine ⟨fun _ => ⟨Or.inl ?_, ?_⟩, fun h => absurd (allSucc_zero Δ D) h⟩
    · simp [ExplState.run, ExplState.init]
    · simp [ExplState.run, ExplState.init, succChart]
  | k + 1, hk => by
    have ih := run_gw2 hgw hprog hΔ D k (Nat.le_of_succ_le hk)
    have hins : spec.2.2[k]? = some (Sum.inl (θ k, Δ k)) := hprog k hk
    have hrun : ExplState.run κ b jumps spec D (k + 1) =
        ExplState.flowStep κ b true (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) := by
      rw [run_succ, hins]
      change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) = _
      rw [hgw]
    rw [hrun]
    by_cases hs : AllSucc Δ D k
    · obtain ⟨hlive, hchart⟩ := ih.1 hs
      rw [flowStep_of_isLive _ hlive]
      have hst := status_launch (ExplState.run κ b jumps spec D k) k (D k) (θ k) (hΔ k)
      refine ⟨fun hs' => ⟨Or.inr (hst.1 (allSucc_succ.1 hs').2), ?_⟩, fun hs' => ?_⟩
      · have hne : min (Δ k) (D k).2 ≠ ⊤ := ne_top_of_le_ne_top (hΔ k) (min_le_left _ _)
        show (ExplState.launch _ k (D k) (θ k) (Δ k)).2.2.2.2.1 = _
        rw [chart_launch _ k (D k) (θ k) (Δ k) hne]
        change (stChart (ExplState.run κ b jumps spec D k)).loewner _ _ = _
        rw [hchart]
        rfl
      · have : ¬ Δ k < (D k).2 := fun h => hs' (allSucc_succ.2 ⟨hs, h⟩)
        exact hst.2 this
    · have hstuck := ih.2 hs
      refine ⟨fun hs' => absurd (allSucc_succ.1 hs').1 hs, fun _ => ?_⟩
      exact (flowStep_of_isStuck _ hstuck k (D k) (θ k) (Δ k)).1

/-- **The launch record of a GW2 flow program**: instruction `k` launches, in the chart `succChart`, exactly when every
earlier piece was successful. -/
theorem launches_run_gw2 {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < spec.2.2.length) :
    (AllSucc Δ D k → (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (succChart spec.1 Δ D k, θ k)) ∧
      (¬ AllSucc Δ D k → (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) := by
  have h := run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ D k hk.le
  have hins : spec.2.2[k]? = some (Sum.inl (θ k, Δ k)) := hprog k hk
  have hrun : ExplState.run κ b jumps spec D (k + 1) =
      ExplState.flowStep κ b true (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) := by
    rw [run_succ, hins]
    change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) = _
    rw [hgw]
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  rw [hrun]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨hlive, hchart⟩ := h.1 hs
    rw [flowStep_of_isLive _ hlive, launches_launch, Function.update_self]
    change some (stChart (ExplState.run κ b jumps spec D k), θ k) = _
    rw [hchart]
  · rw [(flowStep_of_isStuck _ (h.2 hs) k (D k) (θ k) (Δ k)).2.1]
    exact h0

/-- **The retained datum of a GW2 flow program**: a launched piece retains `retOf (Δ k) (D k)`. -/
theorem retained_run_gw2 {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < spec.2.2.length) (hs : AllSucc Δ D k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.1 k = retOf (Δ k) (D k) := by
  have h := run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ D k hk.le
  have hins : spec.2.2[k]? = some (Sum.inl (θ k, Δ k)) := hprog k hk
  have hrun : ExplState.run κ b jumps spec D (k + 1) =
      ExplState.flowStep κ b true (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) := by
    rw [run_succ, hins]
    change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) (θ k) (Δ k) = _
    rw [hgw]
  rw [hrun, flowStep_of_isLive _ (h.1 hs).1, retained_launch, Function.update_self]
  rfl

end GW2Schedule

end Theorem14

end InteractingSLE
