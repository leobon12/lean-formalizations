/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzOff
import InteractingSLE.Spec.Supplement.SBTail2SidePhys

/-!
# The offset event is measurable on the event of regular pieces

Packet PROVE-SB2-LCMEAN, round 15 (item 4, gluing over the offset). For a measurable family of drivers regular at
every sample, the physical part of the walk after `n + 1` instructions is, on a measurable event `M` where the
launched pieces are regular, the union of the closures of countably many measurable points (the dense codes of the
pieces' tips and of the arcs, `Side.exists_measurable_piece_dense_code`, `Side.exists_measurable_arc_dense_code`).
The restart test reads the measurable current point and angle of the run (`isMeasState_run`). Hence the offset event
(`Mz.relOffEvent`) agrees on `M` with a measurable event:

* `mem_closure_range_iff`, `measurableSet_mem_closure_range`;
* `statePhysicalSet_run_eq`: the physical part after `n` instructions is the union of the tips and arcs of the first
  `n` instructions;
* `measurableSet_mem_restartSet`;
* **`exists_measurableSet_relOffEvent`**.

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim)

/-- Membership in the closure of a range, through the infimum of the distances. -/
theorem mem_closure_range_iff (x : ℂ) {ι : Type*} (f : ι → ℂ) :
    x ∈ closure (range f) ↔ ⨅ i, edist x (f i) = 0 := by
  rw [Metric.mem_closure_iff_infEDist_zero, Metric.infEDist, iInf_range]

theorem measurableSet_mem_closure_range {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {G : Ω → ι → ℂ}
    (hG : ∀ i, Measurable fun ω => G ω i) (x : ℂ) : MeasurableSet {ω | x ∈ closure (range (G ω))} := by
  have hm : Measurable fun ω => ⨅ i, edist x (G ω i) :=
    Measurable.iInf fun i => (continuous_const.edist continuous_id).measurable.comp (hG i)
  have e : {ω | x ∈ closure (range (G ω))} = (fun ω => ⨅ i, edist x (G ω i)) ⁻¹' {0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_closure_range_iff]
  rw [e]
  exact hm (measurableSet_singleton 0)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The physical part after `n` instructions** is the start point with the tips and arcs of the first `n`
instructions. -/
theorem statePhysicalSet_run_eq (x : ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    statePhysicalSet x (ExplState.run κ b jumps spec D n) = {(x : ℂ)} ∪
      (⋃ k ∈ Finset.range n, GW2aCont.pieceTips κ b jumps spec D k) ∪
        ⋃ k ∈ Finset.range n, ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps spec D k := by
  unfold statePhysicalSet
  rw [GW2aCont.iUnion_pieces_run]
  congr 1
  rw [← image_iUnion₂, ← image_iUnion₂, GW2aCont.iUnion_arcs_run]

/-- The restart test at a measurable run is measurable. -/
theorem measurableSet_mem_restartSet {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState}
    (hS : Exist.StagedLaw.IsMeasState S) (R : ℝ) :
    MeasurableSet {ω | R ∈ GW1W.restartSet κ b jumps (S ω)} := by
  have hpt := hS.2.1
  have hang := hS.2.2.1
  have e : {ω | R ∈ GW1W.restartSet κ b jumps (S ω)} = {ω | R ∈ PiecewiseConstantBoundaryData.jumpSet b jumps} ∩
      ({ω | stPt (S ω) < R} ∩ {ω | -sleLambda κ < rightLim b R + stAngle (S ω) * QuantumZipper.chiC κ}) := by
    ext ω
    simp only [GW1W.restartSet, Finset.mem_filter, mem_ofPred_eq, mem_inter_iff]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.const _) ((measurableSet_lt hpt measurable_const).inter ?_)
  exact measurableSet_lt measurable_const (measurable_const.add (hang.mul measurable_const))

/-- **The offset event agrees with a measurable event on the event of regular pieces.** -/
theorem exists_measurableSet_relOffEvent (hb : IsPiecewiseConstantBoundaryData b jumps) (θ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : ∀ j, Measurable (D j))
    (hDreg : ∀ j ω, IsRegularDriver (D j ω)) {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun i => D i ω) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (D j ω).1 (min (instrTime (boundaryWalkSpec b jumps θ true) j) (D j ω).2))
    (R : ℝ) (o : ℕ) :
    ∃ S : Set Ω, MeasurableSet S ∧ ∀ ω ∈ M, (relOffEvent κ θ b jumps R (fun i => D i ω) o ↔ ω ∈ S) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have hs1 : spec.1 = 0 := rfl
  obtain ⟨F, hFm, hF⟩ := Side.exists_measurable_piece_dense_code hb spec hDm hDreg hM hMreg
  obtain ⟨A, hAm, hA⟩ := Side.exists_measurable_arc_dense_code hb spec hDm hDreg
  -- the entry events
  set Ent' : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range (n + 1),
    ({ω | (R : ℂ) ∈ closure (range (F k ω))} ∪ {ω | (R : ℂ) ∈ closure (range (A k ω))}) with hEnt'
  have hEntm : ∀ n, MeasurableSet (Ent' n) := fun n =>
    Finset.measurableSet_biUnion _ fun k _ =>
      (measurableSet_mem_closure_range (fun i => hFm k i) _).union
        (measurableSet_mem_closure_range (fun i => hAm k i) _)
  have hEnt : ∀ ω ∈ M, ∀ n, Ent κ θ b jumps R (fun i => D i ω) n ↔ ω ∈ Ent' n := by
    intro ω hω n
    unfold Ent
    rw [statePhysicalSet_run_eq]
    have hF' := hF ω hω
    have hA' := hA ω
    constructor
    · rintro ((h0 | h1) | h2)
      · refine mem_iUnion₂.2 ⟨0, Finset.mem_range.2 (by omega), Or.inl ?_⟩
        show (R : ℂ) ∈ closure (range (F 0 ω))
        rw [hF' 0]
        exact Or.inl h0
      · obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h1
        refine mem_iUnion₂.2 ⟨k, hk, Or.inl ?_⟩
        show (R : ℂ) ∈ closure (range (F k ω))
        rw [hF' k]
        exact Or.inr hkR
      · obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h2
        refine mem_iUnion₂.2 ⟨k, hk, Or.inr ?_⟩
        show (R : ℂ) ∈ closure (range (A k ω))
        rw [hA' k]
        exact Or.inr hkR
    · intro h
      obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h
      rcases hkR with hkR | hkR
      · have hkR' : (R : ℂ) ∈ closure (range (F k ω)) := hkR
        rw [hF' k] at hkR'
        rcases hkR' with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨k, hk, h1⟩))
      · have hkR' : (R : ℂ) ∈ closure (range (A k ω)) := hkR
        rw [hA' k] at hkR'
        rcases hkR' with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (mem_iUnion₂.2 ⟨k, hk, h1⟩)
  -- the restart events and the offset at a first entry
  have hrst : ∀ m, MeasurableSet {ω | R ∈ GW1W.restartSet κ b jumps
      (ExplState.run κ b jumps spec (fun i => D i ω) m)} := fun m =>
    measurableSet_mem_restartSet (isMeasState_run hb spec hDm hDreg m) R
  set RO : ℕ → Set Ω := fun e => {ω | relOffOf κ θ b jumps R (fun i => D i ω) e = o} with hRO
  have hROm : ∀ e, MeasurableSet (RO e) := by
    intro e
    set T := {ω | R ∈ GW1W.restartSet κ b jumps (ExplState.run κ b jumps spec (fun i => D i ω) (2 * (e / 2) + 1))}
    have hT : MeasurableSet T := hrst _
    have e1 : RO e = (T ∩ {_ω | e % 2 = 1 ∧ 2 * (e / 2) + 2 = o}) ∪
        ((T ∩ {_ω | e % 2 = 1})ᶜ ∩ {_ω | 2 * (e / 2) = o}) := by
      ext ω
      simp only [hRO, relOffOf, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, T, hspec]
      by_cases h1 : e % 2 = 1 <;> by_cases h2 : R ∈ GW1W.restartSet κ b jumps
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun i => D i ω) (2 * (e / 2) + 1)) <;>
        simp [h1, h2]
    rw [e1]
    exact (hT.inter (MeasurableSet.const _)).union ((hT.inter (MeasurableSet.const _)).compl.inter
      (MeasurableSet.const _))
  refine ⟨⋃ e ∈ Finset.range (o + 2), Ent' e ∩ (⋂ n ∈ Finset.range e, (Ent' n)ᶜ) ∩ RO e,
    Finset.measurableSet_biUnion _ fun e _ => ((hEntm e).inter
      (Finset.measurableSet_biInter _ fun n _ => (hEntm n).compl)).inter (hROm e), fun ω hω => ?_⟩
  rw [relOffEvent_iff]
  simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, Finset.mem_range, exists_prop, hRO,
    mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, by omega, ⟨(hEnt ω hω e).1 h1, fun n hn h4 => h2 n hn ((hEnt ω hω n).2 h4)⟩, h3⟩
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, by omega, ⟨(hEnt ω hω e).2 h1, fun n hn h4 => h2 n hn ((hEnt ω hω n).1 h4)⟩, h3⟩

end InteractingSLE.Theorem14.SB.Mz
