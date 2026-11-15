/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalSorted

/-!
# GB11: unconditional current faces, relative own futures, and local growth

The exact prefix arms are constructed at finite and infinite cuts and at zero
or positive exits. Sorting their gates constructs the current face without an
orientation input. The separately requested, original-label ordering assertion is
isolated below; it is not an assumption of any source-facing result in this file.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- The exits precede any cuts satisfying the exact global first-visit property. -/
theorem GateSetup.exits_lt_cuts (d : GateSetup) {cutR cutL : ℝ≥0∞}
    (hR : IsWallVisitCut d.γ d.αR d.t cutR) (hL : IsWallVisitCut d.γ d.αL d.t cutL) :
    (d.s₁ : ℝ≥0∞) < cutR ∧ (d.t₁ : ℝ≥0∞) < cutL := by
  have hγc := Sec5.continuous_of_isGeneratingTrace_top d.generating
  constructor
  · apply lt_of_not_ge
    intro hle
    have hv := (mem_wallHitParameters_iff hγc).1 ((hR.2 d.s₁).2 hle)
    exact (not_le.2 d.before_exit) hv
  · apply lt_of_not_ge
    intro hle
    have hv := (mem_wallHitParameters_iff hγc).1 ((hL.2 d.t₁).2 hle)
    rw [← d.shape.contact] at hv
    exact (not_le.2 d.before_exit) hv

/-- Construct the current gate boundary from the two actual, globally selected
prefix arms. Sorting is internal to the face and introduces no new hypothesis. -/
theorem gb11CurrentGateBoundaryStatement : GB11CurrentGateBoundaryStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD t hτt ht
  let d : GateSetup := {
    W' := W', γ := γ, continuous_driver := hW', driver_zero := hW'0,
    generating := hγ, no_simple_interval := hno, αR := αR, αL := αL,
    barrier := hB, pocket_shape := hP, C := C, component := hC,
    s₁ := s₁, t₁ := t₁, s₂ := s₂, t₂ := t₂, shape := hs, c := c, chart := hc,
    exit_limit := hxC, before_entry := hE, confined := hTr, dense_visits := hD,
    t := t, entry_le := hτt, before_exit := ht }
  obtain ⟨cutR, cutL, hR, hL, hltR, hltL⟩ := d.exists_cuts
  obtain ⟨aR⟩ := exists_compactifiedPrefixArc d.barrier.1 d.barrier.2.2.2.2.2.1 hltR hR
  obtain ⟨aL⟩ := exists_compactifiedPrefixArc d.barrier.2.1 d.barrier.2.2.2.2.2.2 hltL hL
  exact (unorderedGateArms hR hL aR aL).nonempty_currentGateBoundary

/-- The relative trace has continuous own futures, including visits to original
real contacts and a current junction at infinity. -/
theorem gb11RelOwnFutureStatement : GB11RelOwnFutureStatement :=
  gb11RelOwnFutureStatement_of_gateBoundary gb11CurrentGateBoundaryStatement

/-- The relative trace has local growth, through the exact own-future criterion
of `GB11LocalGrowthCurve`. There are no residual geometric inputs. -/
theorem gb11RelLocalGrowthStatement : GB11RelLocalGrowthStatement :=
  gb11RelLocalGrowthStatement_of_ownFuture gb11RelOwnFutureStatement

/-- The relative parametrization reduction also has no residual gate input. -/
theorem gb11RelParamStatement : GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_gateBoundary gb11CurrentGateBoundaryStatement

/-- **Separate original-label orientation question.** This exact statement says
that the arm belonging to the originally named right wall has the lesser real
gate. It is stronger than the ordering needed to construct the current face;
the unconditional source-facing results above sort the arms instead. -/
def GB11GateOrderStatement : Prop :=
  ∀ (d : GateSetup) (cutR cutL : ℝ≥0∞), IsWallVisitCut d.γ d.αR d.t cutR →
    IsWallVisitCut d.γ d.αL d.t cutL →
    ∀ (aR : CompactifiedPrefixArc d d.αR d.s₁ cutR)
      (aL : CompactifiedPrefixArc d d.αL d.t₁ cutL), aR.q ≤ aL.q

/-- The original-label selected-arm input reduces solely to its separate
orientation assertion. All arc existence, contact, and physical fields are proved. -/
theorem gb11SelectedGateArmsStatement_of_gateOrder (horder : GB11GateOrderStatement) :
    GB11SelectedGateArmsStatement := by
  intro d cutR cutL hR hL
  obtain ⟨hltR, hltL⟩ := d.exits_lt_cuts hR hL
  obtain ⟨aR⟩ := exists_compactifiedPrefixArc d.barrier.1 d.barrier.2.2.2.2.2.1 hltR hR
  obtain ⟨aL⟩ := exists_compactifiedPrefixArc d.barrier.2.1 d.barrier.2.2.2.2.2.2 hltL hL
  let a := unorderedGateArms hR hL aR aL
  exact ⟨{
    qR := aR.q, qL := aL.q, junction := a.junction,
    rightWall := aR.wall, leftWall := aL.wall,
    gates_le := horder d cutR cutL hR hL aR aL,
    right_continuous := a.right_continuous, left_continuous := a.left_continuous,
    right_injective := a.right_injective, left_injective := a.left_injective,
    right_zero := a.right_zero, left_zero := a.left_zero,
    right_one := a.right_one, left_one := a.left_one, wall_inter := a.wall_inter,
    right_gate_old := a.right_gate_old, left_gate_old := a.left_gate_old,
    right_free := a.right_free, left_free := a.left_free,
    right_physical_outside := a.right_physical_outside,
    left_physical_outside := a.left_physical_outside,
    right_image := aR.image, left_image := aL.image }⟩

end InteractingSLE.Theorem14.GB11Chart
