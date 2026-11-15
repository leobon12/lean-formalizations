/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfDet
import InteractingSLE.Spec.Supplement.SB2MzOffM

/-!
# The root event agrees with a measurable event on the event of regular pieces

Packet PROVE-SB2-CONDFIN (Target 1). The root event `RootEv n` (`R` entered by stage `n`, offset `n`) of a measurable,
everywhere regular walk family agrees, on a measurable event where the launched pieces are regular, with a measurable
event (**`exists_measurableSet_rootEv`**): the entry events through the dense codes of tips and arcs and the restart
test, exactly as for the offset event (`Mz.exists_measurableSet_relOffEvent`), with the finite formula
`rootEv_iff`. Deterministic and measure-free (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cf

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep Mz

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The root event agrees with a measurable event on the event of regular pieces.** -/
theorem exists_measurableSet_rootEv (hb : IsPiecewiseConstantBoundaryData b jumps) (θ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : ∀ j, Measurable (D j))
    (hDreg : ∀ j ω, IsRegularDriver (D j ω)) {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun i => D i ω) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (D j ω).1 (min (instrTime (boundaryWalkSpec b jumps θ true) j) (D j ω).2))
    (R : ℝ) (o : ℕ) :
    ∃ S : Set Ω, MeasurableSet S ∧ ∀ ω ∈ M, (RootEv κ θ b jumps R (fun i => D i ω) o ↔ ω ∈ S) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
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
  refine ⟨⋃ e ∈ Finset.range (o + 1), Ent' e ∩ (⋂ n ∈ Finset.range e, (Ent' n)ᶜ) ∩ RO e,
    Finset.measurableSet_biUnion _ fun e _ => ((hEntm e).inter
      (Finset.measurableSet_biInter _ fun n _ => (hEntm n).compl)).inter (hROm e), fun ω hω => ?_⟩
  rw [rootEv_iff]
  simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, Finset.mem_range, exists_prop, hRO,
    mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, by omega, ⟨(hEnt ω hω e).1 h1, fun n hn h4 => h2 n hn ((hEnt ω hω n).2 h4)⟩, h3⟩
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, by omega, ⟨(hEnt ω hω e).2 h1, fun n hn h4 => h2 n hn ((hEnt ω hω n).1 h4)⟩, h3⟩

end InteractingSLE.Theorem14.SB.Cf
