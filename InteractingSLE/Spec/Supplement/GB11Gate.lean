/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateData

/-!
# GB11: assembly from the remaining joint planar gate geometry

Global first-visit cuts, individual finite/infinite lifts, base intersections,
and the frontier above the real line are proved in the preceding files.
The hypotheses named below are explicit remaining mathematical inputs; this
file does not assert an unconditional source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- **Remaining planar enclosure input:** the selected arms enclose the finite
real part of the current frontier in their incident interval. The non-real part
and the compactification endpoint are already covered unconditionally. -/
def GB11GateRealEnclosureStatement : Prop :=
  ∀ (d : GateSetup) (cutR cutL : ℝ≥0∞), IsWallVisitCut d.γ d.αR d.t cutR →
    IsWallVisitCut d.γ d.αL d.t cutL → ∀ a : SelectedGateArms d cutR cutL,
      ∀ x : ℝ, (x : ℂ) ∈ frontier (ownDomain d.driver d.C d.t) →
        mu x ∈ a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 ∪ gateBase a.qR a.qL

/-- With the real enclosure, the selected prefixes cover the entire compactified
frontier. Above the real line this follows from the proved physical-frontier
transport, the pocket shape, and the global cut selection. -/
theorem SelectedGateArms.frontier_subset {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (hR : IsWallVisitCut d.γ d.αR d.t cutR)
    (hL : IsWallVisitCut d.γ d.αL d.t cutL)
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ frontier (ownDomain d.driver d.C d.t) →
      mu x ∈ a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 ∪ gateBase a.qR a.qL) :
    frontier (mu '' ownDomain d.driver d.C d.t) ⊆
      a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 ∪ gateBase a.qR a.qL := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη := isLoewnerTrace_of_isGeneratingTrace d.generating
  have hCo : IsOpen d.C := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.1)
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.2.1) d.component
  have hCH : d.C ⊆ H := subset_H_of_mem_betweenComponents d.component
  have hOo := isOpen_ownDomain hη hW hW0 d.t.2 hCo hCH
  intro ζ hζ
  rcases frontier_mu_image_subset hOo (fun _ hw => hw.1) hζ with ⟨w, hw, rfl⟩ | he
  · by_cases hwH : w ∈ H
    · exact Or.inl (a.frontier_inter_H_subset hR hL hw hwH)
    · have hwbar := (frontier_ownDomain_image_closure hη hW hW0 d.t.2 hw).1
      have him : w.im = 0 := le_antisymm (not_lt.1 hwH) hwbar
      have hre : (w.re : ℂ) = w := Complex.ext rfl (by simp only [Complex.ofReal_im, him])
      rw [← hre] at hw ⊢
      exact hreal w.re hw
  · rw [mem_singleton_iff] at he
    subst ζ
    exact Or.inl (Or.inl (a.zero_mem_of_frontier hζ))

/-- Construction of the full gate boundary. The base-intersection fields are
proved from the old real base; the outside fields from the physical wall images. -/
def SelectedGateArms.currentGateBoundary {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (hR : IsWallVisitCut d.γ d.αR d.t cutR)
    (hL : IsWallVisitCut d.γ d.αL d.t cutL)
    (hbase : OrdConnected (oldRealBase d.driver d.γ d.t))
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ frontier (ownDomain d.driver d.C d.t) →
      mu x ∈ a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 ∪ gateBase a.qR a.qL) :
    CurrentGateBoundary d.driver d.C d.t where
  qR := a.qR
  qL := a.qL
  junction := a.junction
  rightWall := a.rightWall
  leftWall := a.leftWall
  gates_le := a.gates_le
  right_continuous := a.right_continuous
  left_continuous := a.left_continuous
  right_injective := a.right_injective
  left_injective := a.left_injective
  right_zero := a.right_zero
  left_zero := a.left_zero
  right_one := a.right_one
  left_one := a.left_one
  wall_inter := a.wall_inter
  right_base := wall_inter_gateBase_subset
    (mapsTo_gate_interval_oldTrace hbase a.right_gate_old a.left_gate_old) a.right_free
  left_base := wall_inter_gateBase_subset
    (mapsTo_gate_interval_oldTrace hbase a.right_gate_old a.left_gate_old) a.left_free
  right_outside := wall_disjoint_ownDomain a.right_physical_outside
  left_outside := wall_disjoint_ownDomain a.left_physical_outside
  frontier_subset := a.frontier_subset hR hL hreal

/-- The exact current-gate statement follows from three explicitly named
remaining geometric inputs, with global prefix selection discharged here. -/
theorem gb11CurrentGateBoundaryStatement_of_gateGeometry
    (hbase : GB11OldRealBaseStatement) (harms : GB11SelectedGateArmsStatement)
    (henclose : GB11GateRealEnclosureStatement) : GB11CurrentGateBoundaryStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD t hτt ht
  let d : GateSetup := {
    W' := W', γ := γ, continuous_driver := hW', driver_zero := hW'0,
    generating := hγ, no_simple_interval := hno, αR := αR, αL := αL,
    barrier := hB, pocket_shape := hP, C := C, component := hC,
    s₁ := s₁, t₁ := t₁, s₂ := s₂, t₂ := t₂, shape := hs, c := c, chart := hc,
    exit_limit := hxC, before_entry := hE, confined := hTr, dense_visits := hD,
    t := t, entry_le := hτt, before_exit := ht }
  obtain ⟨cutR, cutL, hR, hL, -, -⟩ := d.exists_cuts
  obtain ⟨a⟩ := harms d cutR cutL hR hL
  have hreal := henclose d cutR cutL hR hL a
  exact ⟨a.currentGateBoundary hR hL (hbase W' γ hW' hW'0 hγ t) hreal⟩

/-- Assembly of continuous relative own futures from the exact remaining gate geometry. -/
theorem gb11RelOwnFutureStatement_of_gateGeometry
    (hbase : GB11OldRealBaseStatement) (harms : GB11SelectedGateArmsStatement)
    (henclose : GB11GateRealEnclosureStatement) : GB11RelOwnFutureStatement :=
  gb11RelOwnFutureStatement_of_gateBoundary
    (gb11CurrentGateBoundaryStatement_of_gateGeometry hbase harms henclose)

/-- Assembly of relative local growth through `GB11LocalGrowthCurve`'s own-future
criterion. No source-facing assumptions have been changed. -/
theorem gb11RelLocalGrowthStatement_of_gateGeometry
    (hbase : GB11OldRealBaseStatement) (harms : GB11SelectedGateArmsStatement)
    (henclose : GB11GateRealEnclosureStatement) : GB11RelLocalGrowthStatement :=
  gb11RelLocalGrowthStatement_of_ownFuture
    (gb11RelOwnFutureStatement_of_gateGeometry hbase harms henclose)

/-- The corresponding parametrization reduction, using the same geometric inputs. -/
theorem gb11RelParamStatement_of_gateGeometry
    (hbase : GB11OldRealBaseStatement) (harms : GB11SelectedGateArmsStatement)
    (henclose : GB11GateRealEnclosureStatement) : GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_gateBoundary
    (gb11CurrentGateBoundaryStatement_of_gateGeometry hbase harms henclose)

end InteractingSLE.Theorem14.GB11Chart
