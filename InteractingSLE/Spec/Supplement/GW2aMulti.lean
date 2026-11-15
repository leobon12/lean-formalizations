/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Exist.StagedLawStruct

/-!
# Lemma GW2a for multi-piece histories: the decomposition into launched pieces

Packet PROVE-T14-BR4. Lemma GW2a (supplement p. 623, `source/spec/p577-624.md` L1040–L1056) is proved by induction
over the pieces of a finite history ("Use the induction datum of GW1 […] GB6 and BW1 apply to the next ordinary
piece"). This file supplies the deterministic bookkeeping of that induction for the histories of GW2's light cone
(`scheduleProgram`, ordinary pieces only, both conventions `gw2 = true` and `gw2 = false`):

* `flowStep_cases`: an ordinary instruction either launches a piece (`ExplState.launch`) or leaves the pieces and the
  connectors unchanged;
* `run_flowProgram`: along a program of ordinary instructions there are no connectors, and every recorded piece is the
  piece launched at some earlier instruction `k`, in the chart of its recorded launch
  (`(run (k + 1)).launches k = some (c, θ)`, the clause of the frozen `IsStagedHistory`), with the driver `E k`
  stopped at `min t_k ζ_k`;
* **`physSet_subset_of_launches`**: the physical set of such a history is its root together with the physical sets of
  its launched pieces;
* **`ae_physSet_subset_of_launches`**: hence a history is almost surely contained in a set `R ω` as soon as its root
  is and each launched piece is (the countable intersection over the instructions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aMulti

open Exist.Staged Exist.StagedLaw

/-- A program of ordinary instructions only (no boundary continuation). -/
def IsFlowProgram (p : List Instr) : Prop := ∀ i ∈ p, ∃ (θ : ℝ) (t : ℝ≥0∞), i = Sum.inl (θ, t)

theorem isFlowProgram_scheduleProgram (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    IsFlowProgram (scheduleProgram τ₀ l) := by
  induction l generalizing τ₀ with
  | nil => intro i hi; simp [scheduleProgram] at hi
  | cons a l ih =>
    intro i hi
    simp only [scheduleProgram, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨_, _, rfl⟩
    · exact ih _ i hi

/-- **An ordinary instruction launches a piece or changes neither the pieces nor the connectors.** -/
theorem flowStep_cases (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) :
    ((ExplState.flowStep κ b gw2 s k D θ t).1 = s.1 ∧ (ExplState.flowStep κ b gw2 s k D θ t).2.1 = s.2.1) ∨
      ExplState.flowStep κ b gw2 s k D θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  split
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · split_ifs
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨rfl, rfl⟩

/-- The piece launched at instruction `k`: its driver `D k` stopped at `min t_k ζ_k`. -/
def stoppedDriver (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : ℝ≥0 → ℝ :=
  fun r => (D k).1 (min (r : ℝ≥0∞) (min (instrTime spec k) (D k).2)).toNNReal

/-- The stop of the piece launched at instruction `k`. -/
def pieceStop (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : ℝ≥0∞ := min (instrTime spec k) (D k).2

/-- **The run of a program of ordinary instructions**: no connectors, and every recorded piece is the piece launched
at an earlier instruction `k`, in its recorded launch chart. -/
theorem run_flowProgram (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {spec : ExplSpec} (hp : IsFlowProgram spec.2.2)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    (ExplState.run κ b jumps spec D n).2.1 = [] ∧
      ∀ q ∈ (ExplState.run κ b jumps spec D n).1, ∃ k < n, ∃ θ : ℝ,
        (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (q.1, θ) ∧
        q.2 = (stoppedDriver spec D k, pieceStop spec D k) := by
  induction n with
  | zero => exact ⟨rfl, fun q hq => by simp [ExplState.run, ExplState.init] at hq⟩
  | succ n ih =>
    obtain ⟨harcs, hpieces⟩ := ih
    have hold : ∀ q ∈ (ExplState.run κ b jumps spec D n).1, ∃ k < n + 1, ∃ θ : ℝ,
        (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (q.1, θ) ∧
        q.2 = (stoppedDriver spec D k, pieceStop spec D k) := fun q hq => by
      obtain ⟨k, hk, θ, h1, h2⟩ := hpieces q hq
      exact ⟨k, Nat.lt_succ_of_lt hk, θ, h1, h2⟩
    rw [run_succ]
    rcases hnth : spec.2.2[n]? with _ | a
    · exact ⟨harcs, hold⟩
    · obtain ⟨θ, t, rfl⟩ := hp a (List.mem_of_getElem? hnth)
      have hit : instrTime spec n = t := by simp [instrTime, hnth]
      change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t).2.1 = [] ∧
        ∀ q ∈ (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t).1, _
      rcases flowStep_cases κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t with ⟨h1, h2⟩ | heq
      · rw [h1, h2]
        exact ⟨harcs, hold⟩
      · rw [heq, arcs_launch, CounterflowRange.pieces_launch]
        refine ⟨harcs, fun q hq => ?_⟩
        rcases List.mem_append.1 hq with hq | hq
        · exact hold q hq
        · rw [List.mem_singleton] at hq
          subst hq
          refine ⟨n, Nat.lt_succ_self n, θ, ?_, ?_⟩
          · rw [run_succ, hnth]
            change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t).2.2.2.1 n = _
            rw [heq, launches_launch, Function.update_self]
          · unfold stoppedDriver pieceStop
            rw [hit]

/-- **The physical set of a history of ordinary instructions** is its root together with the physical sets of its
launched pieces (in their recorded launch charts, with their stopped drivers). -/
theorem physSet_subset_of_launches (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {spec : ExplSpec}
    (hp : IsFlowProgram spec.2.2) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps spec D ⊆ {(spec.1 : ℂ)} ∪
      ⋃ (k : ℕ) (c : Chart) (θ : ℝ) (_ : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)),
        c.tipSet (stoppedDriver spec D k) (pieceStop spec D k) := by
  obtain ⟨harcs, hpieces⟩ := run_flowProgram κ b jumps hp D spec.2.2.length
  intro z hz
  unfold ExplState.physSet at hz
  simp only [harcs, List.not_mem_nil, iUnion_of_empty, iUnion_empty, union_empty] at hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz
    obtain ⟨k, -, θ, h1, h2⟩ := hpieces q hq
    rw [h2] at hzq
    exact Or.inr (mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨q.1, mem_iUnion.2 ⟨θ, mem_iUnion.2 ⟨h1, hzq⟩⟩⟩⟩)

/-- **Containment from the launched pieces** (the countable intersection of GW2a's induction): if almost surely the
root lies in `R ω`, and for every instruction `k` almost surely the launched piece (if any) lies in `R ω`, then almost
surely the whole history lies in `R ω`. -/
theorem ae_physSet_subset_of_launches (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {spec : ExplSpec}
    (hp : IsFlowProgram spec.2.2) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {R : Ω → Set ℂ} (hroot : ∀ᵐ ω ∂P, (spec.1 : ℂ) ∈ R ω)
    (hpiece : ∀ k, ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      c.tipSet (stoppedDriver spec (fun j => E j ω) k) (pieceStop spec (fun j => E j ω) k) ⊆ R ω) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps spec (fun j => E j ω) ⊆ R ω := by
  filter_upwards [hroot, ae_all_iff.2 hpiece] with ω hr hk
  refine (physSet_subset_of_launches κ b jumps hp _).trans (union_subset ?_ ?_)
  · rintro _ rfl
    exact hr
  · refine iUnion_subset fun k => iUnion_subset fun c => iUnion_subset fun θ => iUnion_subset fun hl => ?_
    exact hk k c θ hl

end GW2aMulti

end Theorem14

end InteractingSLE
