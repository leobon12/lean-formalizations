/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Conjugate
import InteractingSLE.Spec.Sec7.SideAncOrient

/-!
# The actual flow chart conjugate to the counterflow pocket chart

PROVE-SIDE-COLLAR2. Compose the three existing domain charts, retaining
the chain-rule lift. The Jordan boundary coordinate supplies the flow
uniformizer, for bounded pockets and pockets opening at the flow seed.
The source branch integer exists; compatibility with a prescribed offset
is a separate statement.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.SideC13

open WangWu (negInv)
open SideC12 Aux119Bdry Aux2728Pocket PocketCoord SideAnc PocketJordan Lemma71I PocketMarks

/-- Conjugation by the global inversion with its inherited derivative lift. -/
def conjugateFlowChart (c : Chart) : Chart :=
  infinitySourceChart.trans (c.trans infinitySourceChart)

@[simp] theorem conjugateFlowChart_fwd (c : Chart) (y : ℂ) :
    (conjugateFlowChart c).1 y = conjugateFlowMap c y := rfl

@[simp] theorem conjugateFlowChart_lift (c : Chart) (y : ℂ) :
    (conjugateFlowChart c).2.2 y = conjugateFlowLift c y := rfl

/-- Conformality and the analytic logarithm of the conjugate chart follow
from composition, rather than being new flow/frame assumptions. -/
theorem isDomainChart_conjugate {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) :
    IsDomainChart (negInv '' D) (conjugateFlowChart c) := by
  have h₂ : IsDomainChart D (c.trans infinitySourceChart) := by
    simpa only [hc.image_eq] using hc.trans isDomainChart_infinitySourceChart
  exact isDomainChart_infinitySourceChart.trans h₂

/-- A counterflow chart of the inverted change pocket gives a chart of
the original flow pocket with exactly the three inherited lifts. -/
theorem isDomainChart_conjugate_pocket {C : Set ℂ} {c : Chart}
    (hc : IsDomainChart (negInv '' C) c) : IsDomainChart C (conjugateFlowChart c) := by
  have h := isDomainChart_conjugate hc
  simpa only [image_image, Function.comp_def, WangWu.negInv_negInv, image_id'] using h

/-- Match the conjugate chart to the already constructed boundary
uniformizer on the Cayley image of the original pocket. -/
theorem isFlowChart_conjugate_of_uniformizer {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (hor : IsFlowChartOriented R L r)
    {ψ : ℂ → ℂ} {c : Chart} (hc : IsDomainChart (negInv '' changePocket R L r) c)
    (hf : EqOn c.1 ψ (negInv '' changePocket R L r))
    (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r)
      (jordanUnif (openPt R L r) ψ)) :
    IsFlowChart R L r (jordanUnif (openPt R L r) ψ) (conjugateFlowChart c) := by
  have hC := isDomainChart_conjugate_pocket hc
  refine ⟨h, hor, hU, hC.1, hC.coe_dom, ?_⟩
  intro x hx
  have hp : cayley x ≠ openPt R L r := by
    intro he
    have hmem : openPt R L r ∈ cayley '' changePocket R L r := he ▸ mem_image_of_mem cayley hx
    have hfr := h.openPt_mem_frontier
    rw [(Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H).frontier_eq] at hfr
    exact hfr.2 hmem
  rw [conjugateFlowChart_fwd, conjugateFlowMap, jordanUnif_of_ne hp, hf (mem_image_of_mem negInv hx)]
  congr 2
  exact (cfPt_cayley (H_subset_Hbar' (h.changePocket_subset_H hx))
    (PocketJordan.ne_zero_of_mem_H (h.changePocket_subset_H hx))).symm

/-- Bounded-pocket source flow chart, using the native Jordan coordinate. -/
theorem isFlowChart_conjugate {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hor : IsFlowChartOriented R L r) {ψ : ℂ → ℂ}
    (hψ : PocketWordAssembly.IsCfJordan R L r ψ) {c : Chart}
    (hc : IsDomainChart (negInv '' changePocket R L r) c)
    (hf : EqOn c.1 ψ (negInv '' changePocket R L r)) :
    IsFlowChart R L r (jordanUnif (openPt R L r) ψ) (conjugateFlowChart c) :=
  isFlowChart_conjugate_of_uniformizer h hor hc hf
    (isBdryUniformizer_jordanUnif h.isOpen_changePocket h.changePocket_subset_H
      (h.neg_one_notMem_closure_cayley h0) h.openPt_mem_frontier
      (frontier_subset_closure h.closePt_mem_frontier) h.openPt_ne_closePt hψ)

/-- The same source flow chart when the pocket opens at the flow seed. -/
theorem isFlowChart_conjugate_inf {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hor : IsFlowChartOriented R L r) {ψ : ℂ → ℂ}
    (hψ : PocketSeedOpen.IsCfJordanInf R L r ψ) {c : Chart}
    (hc : IsDomainChart (negInv '' changePocket R L r) c)
    (hf : EqOn c.1 ψ (negInv '' changePocket R L r)) :
    IsFlowChart R L r (jordanUnif (openPt R L r) ψ) (conjugateFlowChart c) := by
  have hop : openPt R L r = -1 := h.openPt_eq_neg_one_iff.2 h0
  have hU := isBdryUniformizer_jordanUnif_inf h.isOpen_changePocket h.changePocket_subset_H
    (hop ▸ h.openPt_mem_frontier) (frontier_subset_closure h.closePt_mem_frontier) h.closePt_ne_neg_one hψ
  rw [← hop] at hU
  exact isFlowChart_conjugate_of_uniformizer h hor hc hf hU

/-- Once the source boundary chart is installed, its inherited lift has
a common integer branch, by the existing two-arc branch theorem. -/
theorem exists_isPocketBranch_conjugate {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {c : Chart} {Ψ : ℂ → ℂ}
    (hc : IsDomainChart (negInv '' changePocket R L r) c)
    (hF : IsFlowChart R L r Ψ (conjugateFlowChart c)) :
    ∃ n : ℤ, Lemma71N.IsPocketBranch L R (conjugateFlowChart c) n := by
  obtain ⟨ℓ, hℓ, hlift⟩ := (isDomainChart_conjugate_pocket hc).2.2
  exact hF.exists_isPocketBranch hℓ (fun _ hz => hlift hz)

end InteractingSLE.Sec7.SideC13
