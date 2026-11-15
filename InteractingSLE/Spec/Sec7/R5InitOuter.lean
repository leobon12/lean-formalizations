/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitTest
import InteractingSLE.Spec.Sec7.R5OutCapacityWire

/-!
# R.5's initial heights on the outer pockets (ruling R88, R98)

Packet PROVE-R5-INIT, outer round. Astra's pocket-mean note (R98) proves the two original-frame facts for every
constant-angle arm, outer arms included (Theorem 9 and Remark 10: no angle bound and no containment of the arm in a
counterflow range), and the outer-pocket R.5 note (`outer_r5_incident_references.txt`, input P6 and §5.2) uses them as
the initial wall heights of the outer pockets. `R5Init.exists_r7InitialHeights_of_flowChart` is stated for any
walls-measurable selection of change pockets of the R.7 arms with a driven traversal and a conformal counterflow
coordinate whose conjugate pocket chart is a flow chart; the outer pocket configurations `HOuter.IsOuterCfg(Inf)`
supply exactly these (`conf`, `bounded`/`seed`, `oriented`, `props`).

* **`twoSeedSplitInputInit_outer`**, **`twoSeedSplitInputInitInf_outer`**: `R5Fresh.TwoSeedSplitInputInit(Inf)` (the
  per-test initial heights with a walls-measurable shift, offset `0` and `X₀ = ∅`) on outer pockets;
* `R7OuterSplitRemainingInit` (def; the premises of `R5Out.R7OuterRelativeCoverMRemaining`, conclusion the two
  per-test inputs) and **`r7OuterSplitRemainingInit_proved`** for every `k > 4`, all weights and margins.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R5Init

open LocalSets WholeField Aux119Bdry Aux119Heights Aux2728Pocket PocketCoord PocketJordan PocketMarks PocketStop
  PocketStopSide PocketStopField PocketTraversal PocketWordAssembly PocketSeedOpen PocketWordPerQ PocketUnionPt
  R7Outer R7Leaves R5Wall Lemma71N Lemma71I SideC13

section Shapes

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {u₀' : ℂ → ℝ}

/-- **The per-test initial heights on bounded outer change pockets** (`X₀ = ∅`, offset `0`). -/
theorem twoSeedSplitInputInit_outer (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {r : ℝ≥0} {G : Set Ω}
    (hcfgP : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    R5Fresh.TwoSeedSplitInputInit k rL rR P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG _ ψ hψ hψm
  have hconf : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfgP ω (hAG hω)).conf
  have hRw := fun t => measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hLw := fun t => measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hCmem : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRw hLw hA hconf hA subset_rfl z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCmem z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const
      (fun ω hω => ⟨subset_closure hω.2, fun he => (hconf ω hω.1).cfPt_openPt_notMem (he ▸ hω.2)⟩)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    WangWu.isOpen_image_negInv (hconf ω hω).isOpen_changePocket (hconf ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hconf ω hω).changePocket_subset_H
  have hψb : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hF : ∀ ω ∈ A, IsFlowChart (R ω) (L ω) r (SideAnc.jordanUnif (openPt (R ω) (L ω) r) (ψ ω))
      (conjugateFlowChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)) := fun ω hω =>
    isFlowChart_conjugate (hcfgP ω (hAG hω)).conf
      (zero_notMem_closure_of_rightLo_pos (hcfgP ω (hAG hω)).conf (hcfgP ω (hAG hω)).bounded)
      (hcfgP ω (hAG hω)).oriented (hψ ω hω) (isDomainChart_pChart hCo hCH hψb hω)
      (fun z _ => by change pFwd A ψ ω z = ψ ω z; rw [pFwd_of_mem hω])
  obtain ⟨n, hn, hI⟩ := exists_r7InitialHeights_of_flowChart hk4 hcfg hD hu₀' hV hA hconf
    (fun ω hω => ((hcfgP ω (hAG hω)).props (hψ ω hω)).1) hψb hψm' hF
  exact ⟨n, hn, 0, ⟨0, by simp⟩, fun _ => ∅, fun _ => finite_empty, hI _⟩

/-- **The per-test initial heights on outer change pockets opening at the flow seed** (`X₀ = ∅`, offset `0`). -/
theorem twoSeedSplitInputInitInf_outer (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {r : ℝ≥0} {G : Set Ω}
    (hcfgI : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    R5Fresh.TwoSeedSplitInputInitInf k rL rR P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG _ ψ hψ hψm
  have hconf : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfgI ω (hAG hω)).conf
  have hRw := fun t => measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hLw := fun t => measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hCmem : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRw hLw hA hconf hA subset_rfl z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCmem z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const (fun _ hω => subset_closure hω.2)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    WangWu.isOpen_image_negInv (hconf ω hω).isOpen_changePocket (hconf ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hconf ω hω).changePocket_subset_H
  have hψb : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hF : ∀ ω ∈ A, IsFlowChart (R ω) (L ω) r (SideAnc.jordanUnif (openPt (R ω) (L ω) r) (ψ ω))
      (conjugateFlowChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)) := fun ω hω =>
    isFlowChart_conjugate_inf (hcfgI ω (hAG hω)).conf (hcfgI ω (hAG hω)).seed (hcfgI ω (hAG hω)).oriented
      (hψ ω hω) (isDomainChart_pChart hCo hCH hψb hω)
      (fun z _ => by change pFwd A ψ ω z = ψ ω z; rw [pFwd_of_mem hω])
  obtain ⟨n, hn, hI⟩ := exists_r7InitialHeights_of_flowChart hk4 hcfg hD hu₀' hV hA hconf
    (fun ω hω => ((hcfgI ω (hAG hω)).props (hψ ω hω)).1) hψb hψm' hF
  exact ⟨n, hn, 0, ⟨0, by simp⟩, fun _ => ∅, fun _ => finite_empty, hI _⟩

end Shapes

/-- **The initial heights on every outer R.7 configuration** (the premises are exactly those of
`R5Out.R7OuterRelativeCoverMRemaining`; the conclusion is the per-test initial-heights input on the two kinds of outer
change pockets). Proved below (`r7OuterSplitRemainingInit_proved`); stated as a `def` for wiring only. -/
def R7OuterSplitRemainingInit (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        HOuter.IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        HOuter.IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      R5Fresh.TwoSeedSplitInputInit k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        R5Fresh.TwoSeedSplitInputInitInf k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The outer pockets' initial heights, proved** for every `k > 4`, all seed weights and margins (R98). -/
theorem r7OuterSplitRemainingInit_proved {k rL rR c c' : ℝ} (hk4 : 4 < k) :
    R7OuterSplitRemainingInit.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q _ G _ _ hconf _ hcfgP hcfgI
  exact ⟨twoSeedSplitInputInit_outer hk4 hcfg hD hu₀' hV (fun ω hω => hcfgP ω hω.1 hω.2),
    twoSeedSplitInputInitInf_outer hk4 hcfg hD hu₀' hV (fun ω hω => hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1)))⟩

end InteractingSLE.Sec7.R5Init
