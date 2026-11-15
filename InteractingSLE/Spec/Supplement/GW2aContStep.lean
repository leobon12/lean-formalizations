/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContStepLaunch

/-!
# Lemma GW2a for every program: GW1's inductive step, all instructions

Packet PROVE-GW2AC. GW1's induction datum (`HasStatePair`) passes from one instruction to the next under the regular
conditional laws given the retained pasts (supplement p. 623: "Finite induction proves all the assertions"). By
`run_succ_cases`, an instruction

* keeps the state: the record of the instruction is the fixed empty record, so the regular conditional law given the
  longer retained past is the current one (`ae_condExpKernel_comap_eq_self`), and the datum is inherited;
* kills the history, or ends it: nothing to prove;
* launches a piece: `ae_hasStatePair_succ_of_launch` (GB6, BW1);
* appends a connector: the named input `GW2aConnectorStepStatement` (BR6, BR4a; Corollary BW2 at a general angle).

Main results: **`ae_hasStatePair_succ`** (the step) and **`ae_arc_subset`** (each recorded connector under the
conditional law).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The connector recorded by instruction `k` only depends on the state before it.** -/
theorem arcAt_eq_of_run_eq {spec : ExplSpec} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k) :
    arcAt κ b jumps spec D k = arcAt κ b jumps spec D' k := by
  rw [arcAt_eq_newArc, arcAt_eq_newArc, ← h]
  rcases run_succ_cases (κ := κ) (b := b) (jumps := jumps) spec (ExplState.run κ b jumps spec D k) k
    with hkeep | hdead | ⟨θ, t, -, hl⟩ | ⟨s', -, hmove⟩
  · rw [hkeep D rfl, hkeep D' h.symm]
  · rw [hdead D rfl, hdead D' h.symm]
  · rw [hl D rfl, hl D' h.symm, newArc_of_arcs_eq (arcs_launch _ _ _ _ _),
      newArc_of_arcs_eq (arcs_launch _ _ _ _ _)]
  · rw [hmove D rfl, hmove D' h.symm]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **GW1's inductive step for a boundary-continued program from the root `0`** (module docstring). Named inputs: GB6
(`GW2Later.GB6PrefixPairStatement`), BW1 (`BW1PrefixPairStatement`), GW2a's connector step
(`GW2aConnectorStepStatement`), Theorem 1.3. -/
theorem ae_hasStatePair_succ (hG : GB6PrefixPairStatement.{u}) (hBW1 : BW1PrefixPairStatement.{u})
    (hCon : GW2aConnectorStepStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {p : List Instr} (hp : IsBoundaryContinuedProgram p) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E) (hR : StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (j : ℕ) :
    ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E j ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E j) ω₀),
        HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E (j + 1) ω := by
  have hle := hS.2.1
  have hEm := hS.1
  have hθs : ∀ (k : ℕ) (θ : ℝ) (t : ℝ≥0∞), (⟨0, false, p⟩ : ExplSpec).2.2[k]? = some (Sum.inl (θ, t)) →
      θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := fun _ _ _ hk => angle_mem_Icc_of_getElem hp hk
  filter_upwards [ae_hasStatePair_succ_of_launch hG hBW1 hT13 hκ hκ4 hb hcf hζ' hθs hS hR hreg j,
    hCon κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' p hp E hS hR hreg j,
    ae_ae_run_eq runMeasStatement hb ⟨0, false, p⟩ (fun i _ => hEm i) (fun i _ => hreg i) (k := j) (P := P),
    ae_ae_condExpKernel_succ_eq hle j] with ω₀ hL hC hrun hK hD
  rcases run_succ_cases (κ := κ) (b := b) (jumps := jumps) ⟨0, false, p⟩
      (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) j) j
    with hkeep | hdead | ⟨θ, t, hj, hl⟩ | ⟨s', hs', hmove⟩
  · -- the state is kept: the record is the empty record, the conditional law is the current one
    have hc : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E j) ω₀),
        lastRec κ b jumps ⟨0, false, p⟩ E j ω = readRec (fun _ => 0, 0, false) := by
      filter_upwards [hrun] with ω hω
      refine lastRec_of_noLaunch _ E j ?_
      rw [hkeep _ hω]
      exact launches_run_of_le (κ := κ) (b := b) (jumps := jumps) _ _ le_rfl
    filter_upwards [hrun, hK, ae_condExpKernel_comap_eq_self (measurable_lastRec hle j) hc] with ω hω h1 h2
    intro hlive h' htr
    rw [hkeep _ hω] at hlive htr ⊢
    rw [← h1, h2]
    exact hD hlive h' htr
  · -- the history dies
    filter_upwards [hrun] with ω hω hlive
    rw [hdead _ hω] at hlive
    exact absurd (isTerminal_setDead _) hlive
  · -- a launch
    exact hL hD θ t hj hl
  · -- a connector
    have hne : (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) (j + 1)).2.1 ≠
        (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) j).2.1 := by
      rw [hmove _ rfl]
      exact hs'
    filter_upwards [hC hD hne] with ω hω using hω.2

/-- **Each recorded connector lies in the completed counterflow range under the conditional law** wherever GW1's datum
holds before it (named input: GW2a's connector step; a step that appends no connector records the empty set). -/
theorem ae_arc_subset (hCon : GW2aConnectorStepStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {p : List Instr} (hp : IsBoundaryContinuedProgram p) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E) (hR : StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀),
        ((↑) : ℝ → ℂ) '' arcAt κ b jumps ⟨0, false, p⟩ (fun j => E j ω) k ⊆
          counterflowCompletedRange (fun t => W' t ω) := by
  filter_upwards [hCon κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' p hp E hS hR hreg k,
    ae_ae_run_eq runMeasStatement hb ⟨0, false, p⟩ (fun i _ => hS.1 i) (fun i _ => hreg i) (k := k) (P := P)]
    with ω₀ hC hrun hD
  by_cases hne : (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) (k + 1)).2.1 ≠
      (ExplState.run κ b jumps ⟨0, false, p⟩ (fun i => E i ω₀) k).2.1
  · filter_upwards [hC hD hne] with ω hω using hω.1
  · filter_upwards [hrun] with ω hω
    rw [arcAt_eq_of_run_eq hω, arcAt_of_arcs_eq (not_not.1 hne), image_empty]
    exact empty_subset _

end GW2aCont

end Theorem14

end InteractingSLE
