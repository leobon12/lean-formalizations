/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitOuter
import InteractingSLE.Spec.Sec7.R5InitOuterCover
import InteractingSLE.Spec.Sec7.R5OutRemaining

/-!
# Outer R.5 with no remaining input beyond Aux. lemma 7 (rulings R88, R98)

Packet PROVE-R5-INIT (outer round). R5-OUTER's `R5Out.r7OuterR5MRemainingCompOn_of_liftHeight` names the shared inputs
`R5Ref.R7AmbientLiftWord(Inf)`, `R5Wall.R7OuterLiftWord(Inf)` and `R5Wall.R7InitialHeights`. On outer pockets:
* the ambient lift word is `r7AmbientLiftWord_of_cur_outer` (from the seed-interval landings, `R5InitLiftOut`);
* the initial heights are `twoSeedSplitInputInit_outer` (`R5InitOuter`), enlarged to the exception set by
  `r7InitialHeights_mono`;
* the outer lift word is needed by R5-OUTER's cover only at collars with an ambient half-disc
  (`R5Out.R7OuterAmbientGeometry`), where it is `r7OuterLiftWordAmb_of_seedLand_outer` (`R5InitOuterWord`); at *all*
  collars it would need the reflection `R5Lift.R7OuterRefl`, whose proof uses the clipped wall orders (R97), not
  available on outer arms. R5-OUTER's chain is re-run with that form in `R5InitOuterCover`.

The seed-interval landings come from the counterflow's no-return (`R5Fresh.ae_noReturn_r7_of_aux7`, Aux. lemma 7 at
`k`). Results:
* **`twoSeedOuterLiftHeightAmbInputOn_of_noReturn`** (and `…Inf…`): the shared data of every outer test;
* **`r7OuterR5MRemainingCompOn_of_aux7`**: R5-OUTER's `R5Out.R7OuterR5MRemainingCompOn` from Aux. 7 at `k`;
* **`r7OuterPhaseWordMRemaining_of_aux7`**, **`r7OuterRelativeCoverMRemaining_of_aux7`**,
  **`r7OuterPhaseContMRemaining_of_aux7`**, **`hOuterCont_of_aux7`** (R5-OUTER's downstream adapters), and the
  same from Zhan's Part A inputs (`…_of_partA`, via `R5Fresh.aux7Statement_of_partA`).

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

open LocalSets WholeField PocketCoord PocketJordan PocketMarks PocketStop PocketStopSide PocketStopField
  PocketTraversal PocketWordAssembly PocketSeedOpen PocketWordPerQ PocketUnionPt R7Outer R7Leaves R5Wall R5Phase
  R5Ref R5Out

/-- `R5Wall.R7InitialHeights` is monotone in the exception set. -/
theorem r7InitialHeights_mono {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin (nR + 1) → ℝ} {P : Measure Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {X₀ X : Ω → Set ℂ}
    (hI : R7InitialHeights κ ρL ρR P A γ C xL xR c a h₀ u X₀) (hX : ∀ ω, X₀ ω ⊆ X ω) :
    R7InitialHeights κ ρL ρR P A γ C xL xR c a h₀ u X := by
  intro g₀ hg₀
  filter_upwards [hI g₀ hg₀] with ω hω hA x hx hxX
  exact hω hA x hx fun h => hxX (hX ω h)

section Shared

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {u₀' : ℂ → ℝ}

/-- **The shared lift and height data of a bounded outer test from the counterflow's no-return**: branch and offset of
`twoSeedSplitInputInit_outer`, phase `χ_k·2π curPhaseInt + a`, exception sets `X₀ ∪ outerExc_q`. -/
theorem twoSeedOuterLiftHeightAmbInputOn_of_noReturn (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {r : ℝ≥0} {G : Set Ω}
    (hcfgP : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) (hnr : ∀ᵐ ω ∂P, ω ∈ G → ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    TwoSeedOuterLiftHeightAmbInputOn k rL rR P R L r η G (centredField h'' u₀') u₀' (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) W' ζ' VL VR := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, hX₀f, hInit⟩ := twoSeedSplitInputInit_outer hk4 hcfg hD hu₀' hV hcfgP A hA hAG hPA ψ hψ hψm
  obtain ⟨-, -, -, hC⟩ := hD
  have hcfgA : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfgP ω (hAG hω)
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfgA ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω => by
    have hcf := hcfgA ω hω
    have hp := hcf.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded)
    exact Or.inl ⟨cfPt (openPt (R ω) (L ω) r), cfPt (closePt (R ω) (L ω) r), hp.isBounded,
      hcf.conf.cfPt_openPt_notMem, hψ ω hω⟩
  obtain ⟨hcA, -, -⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hcd := shiftChart_dom_facts hCo hCH hψc n
  have hc := fun ω hω => (hcd ω hω).1
  have hdom := fun ω hω => (hcd ω hω).2.1
  have heq := fun ω hω => (hcd ω hω).2.2
  have hℓ := fun ω hω => (hcA ω hω).2
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω)
  have hnrA : ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ, 0 < t → η ω t ≠ 0 := hnr.mono fun ω hω hA => hω (hAG hA)
  refine ⟨n, hn, a, fun q ω => chiC k * (2 * Real.pi * R5Lift.curPhaseInt R L r η ψ (fun _ => LP.twoSeedXL)
      (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' q ω) + a,
    fun q ω => X₀ ω ∪ outerExc R L r η ψ q ω, fun q => ?_⟩
  have hSeed := r7SeedLand_of_noReturn_outer (q := q) (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR)
    hcfgA hψ hc hdom heq (fun _ => rfl) (fun _ => rfl) hnrA
  have hLC := r7LiftCurGeom_of_seedLand_outer hcfgA hψ hc hdom heq (fun _ => rfl) (fun _ => rfl) hSeed
  refine ⟨fun ω => (hX₀f ω).union (outerExc_finite R L r η ψ q ω),
    Eventually.of_forall fun ω _ _ => R5Lift.phase_mem_lattice _ ha,
    r7AmbientLiftWord_of_cur_outer hcfgA hψ hc hdom heq hℓ (fun _ => rfl) (fun _ => rfl) hC.1.2.2.2.2 hζA
      (Theorem14.GW3Word.flowLineXL_nonpos b' J') (Theorem14.GW3Word.flowLineXR_nonneg b' J') hLC a,
    r7OuterLiftWordAmb_of_seedLand_outer hcfgA hψ hc hdom heq hℓ (fun _ => rfl) (fun _ => rfl) hC.1.2.2.2.2 hζA
      (Theorem14.GW3Word.flowLineXL_nonpos b' J') (Theorem14.GW3Word.flowLineXR_nonneg b' J') hSeed a,
    r7InitialHeights_mono hInit fun ω => subset_union_left, fun ω _ => subset_union_right⟩

/-- **The shared lift and height data of an outer test opening at the flow seed from the counterflow's no-return**. -/
theorem twoSeedOuterLiftHeightAmbInputInfOn_of_noReturn (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {r : ℝ≥0} {G : Set Ω}
    (hcfgI : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) (hnr : ∀ᵐ ω ∂P, ω ∈ G → ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    TwoSeedOuterLiftHeightAmbInputInfOn k rL rR P R L r η G (centredField h'' u₀') u₀' (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) W' ζ' VL VR := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, hX₀f, hInit⟩ :=
    twoSeedSplitInputInitInf_outer hk4 hcfg hD hu₀' hV hcfgI A hA hAG hPA ψ hψ hψm
  obtain ⟨-, -, -, hC⟩ := hD
  have hcfgA : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfgI ω (hAG hω)
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfgA ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : ∀ ω ∈ A, IsJordanCases (cfPocket (R ω) (L ω) r) (ψ ω) := fun ω hω =>
    Or.inr ⟨cfPt (closePt (R ω) (L ω) r), hψ ω hω⟩
  obtain ⟨hcA, -, -⟩ := shiftChart_aux29Facts hCo hCH hJ n
  have hcd := shiftChart_dom_facts hCo hCH hψc n
  have hc := fun ω hω => (hcd ω hω).1
  have hdom := fun ω hω => (hcd ω hω).2.1
  have heq := fun ω hω => (hcd ω hω).2.2
  have hℓ := fun ω hω => (hcA ω hω).2
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω)
  have hnrA : ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ, 0 < t → η ω t ≠ 0 := hnr.mono fun ω hω hA => hω (hAG hA)
  refine ⟨n, hn, a, fun q ω => chiC k * (2 * Real.pi * R5Lift.curPhaseIntInf R L r η ψ (fun _ => LP.twoSeedXL)
      (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' q ω) + a,
    fun q ω => X₀ ω ∪ outerExcInf R L r η ψ q ω, fun q => ?_⟩
  have hSeed := r7SeedLandInf_of_noReturn_outer (q := q) (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR)
    hcfgA hψ hc hdom heq (fun _ => rfl) (fun _ => rfl) hnrA
  have hLC := r7LiftCurGeomInf_of_seedLand_outer hcfgA hψ hc hdom heq (fun _ => rfl) (fun _ => rfl) hSeed
  refine ⟨fun ω => (hX₀f ω).union (outerExcInf_finite R L r η ψ q ω),
    Eventually.of_forall fun ω _ _ => R5Lift.phase_mem_lattice _ ha,
    r7AmbientLiftWordInf_of_cur_outer hcfgA hψ hc hdom heq hℓ (fun _ => rfl) (fun _ => rfl) hC.1.2.2.2.2 hζA
      (Theorem14.GW3Word.flowLineXL_nonpos b' J') (Theorem14.GW3Word.flowLineXR_nonneg b' J') hLC a,
    r7OuterLiftWordInfAmb_of_seedLand_outer hcfgA hψ hc hdom heq hℓ (fun _ => rfl) (fun _ => rfl) hC.1.2.2.2.2 hζA
      (Theorem14.GW3Word.flowLineXL_nonpos b' J') (Theorem14.GW3Word.flowLineXR_nonneg b' J') hSeed a,
    r7InitialHeights_mono hInit fun ω => subset_union_left, fun ω _ => subset_union_right⟩

end Shared

section Close

open MeasureTheory ProbabilityTheory Filter Set Topology
open WangWu Lemma71I PocketMarks PocketAdapt Lemma71C PocketCoupling LawUnique Lemma725RefSafe Lemma725RefChart
  Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PhaseClause PhaseCont OuterCont R5Enl
  StripPocketConfig RefWire HOuter

/-- **Outer R.5's source component clauses from Aux. lemma 7 at `k`** (`R5Out.R7OuterR5MRemainingCompOn`, no other
named input): R5-OUTER's assembly `R5Out.r7OuterR5MRemainingCompOn_of_liftHeight` with the shared data of
`twoSeedOuterLiftHeightAmbInputOn_of_noReturn` (and `…Inf…`) and the ambient-half-disc cover chain. -/
theorem r7OuterR5MRemainingCompOn_of_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) : R5Out.R7OuterR5MRemainingCompOn.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      HOuter.IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  have hae := R5Fresh.ae_noReturn_r7_of_aux7 haux7 hk4 hc hc' hcfg
  have hs := twoSeedOuterLiftHeightAmbInputOn_of_noReturn hk4 hcfg hD hu₀' hV
    (G := {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)}) (fun ω hω => hcfgP ω hω.1 hω.2)
    (fun ω hω => hζG ω hω.1) (R5Fresh.ae_ne_zero_of_trace hae fun ω hω => (hcfgP ω hω.1 hω.2).trace)
  have hsI := twoSeedOuterLiftHeightAmbInputInfOn_of_noReturn hk4 hcfg hD hu₀' hV hcfgI'
    (fun ω hω => hζG ω hω.1) (R5Fresh.ae_ne_zero_of_trace hae fun ω hω => (hcfgI' ω hω).trace)
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  exact ⟨twoSeedR5CompInputOn_of_liftHeightAmb hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2)
      (fun ω hω => hζG ω hω.1) hs,
    twoSeedR5CompInputInfOn_of_liftHeightAmb hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI' (fun ω hω => hζG ω hω.1) hsI⟩


/-- **The outer phase word from Aux. lemma 7 at `k`** (`R5Out.r7OuterPhaseWordMRemaining_of_r5CompOn`). -/
theorem r7OuterPhaseWordMRemaining_of_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) : OuterCont.R7OuterPhaseWordMRemaining.{u} k rL rR c c' :=
  R5Out.r7OuterPhaseWordMRemaining_of_r5CompOn hk4 hc hc' (r7OuterR5MRemainingCompOn_of_aux7 hk4 hc hc' haux7)

/-- **Outer R.5 (R5-OUTER's unchanged relative-cover binder `R5Out.R7OuterRelativeCoverMRemaining`) from Aux. lemma 7
at `k`**. -/
theorem r7OuterRelativeCoverMRemaining_of_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) : R5Out.R7OuterRelativeCoverMRemaining.{u} k rL rR c c' :=
  R5Out.r7OuterRelativeCoverMRemaining_of_phaseWord (r7OuterPhaseWordMRemaining_of_aux7 hk4 hc hc' haux7)

/-- **The outer phase continuity from Aux. lemma 7 at `k`**. -/
theorem r7OuterPhaseContMRemaining_of_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c' :=
  R5Out.r7OuterPhaseContMRemaining_of_relativeCover hk4 hc hc' (r7OuterRelativeCoverMRemaining_of_aux7 hk4 hc hc' haux7)

/-- **The outer R.5 continuity assembly input from Aux. lemma 7** (`R5Out.hOuterCont_of_relativeCover`). -/
theorem hOuterCont_of_aux7 (haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{u} k) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR := by
  apply R5Out.hOuterCont_of_relativeCover
  intro k hk4 rL rR _ _ _
  exact r7OuterRelativeCoverMRemaining_of_aux7 hk4
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith))
      (R7.sixteen_div_lt_four hk4)).le) le_rfl (haux7 k hk4)

/-- **Outer R.5's source component clauses from Zhan's Part A inputs**. -/
theorem r7OuterR5MRemainingCompOn_of_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) : R5Out.R7OuterR5MRemainingCompOn.{u} k rL rR c c' :=
  r7OuterR5MRemainingCompOn_of_aux7 hk4 hc hc' (R5Fresh.aux7Statement_of_partA hk4 hA)

/-- **The outer phase word from Zhan's Part A inputs**. -/
theorem r7OuterPhaseWordMRemaining_of_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) : OuterCont.R7OuterPhaseWordMRemaining.{u} k rL rR c c' :=
  r7OuterPhaseWordMRemaining_of_aux7 hk4 hc hc' (R5Fresh.aux7Statement_of_partA hk4 hA)

/-- **Outer R.5 (`R5Out.R7OuterRelativeCoverMRemaining`) from Zhan's Part A inputs**. -/
theorem r7OuterRelativeCoverMRemaining_of_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) : R5Out.R7OuterRelativeCoverMRemaining.{u} k rL rR c c' :=
  r7OuterRelativeCoverMRemaining_of_aux7 hk4 hc hc' (R5Fresh.aux7Statement_of_partA hk4 hA)

/-- **The outer phase continuity from Zhan's Part A inputs**. -/
theorem r7OuterPhaseContMRemaining_of_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c' :=
  r7OuterPhaseContMRemaining_of_aux7 hk4 hc hc' (R5Fresh.aux7Statement_of_partA hk4 hA)

/-- **The outer R.5 continuity assembly input from Zhan's Part A inputs**. -/
theorem hOuterCont_of_partA (hA : Sec5.PartAInputsSixteenDiv) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR :=
  hOuterCont_of_aux7 fun _ hk4 => R5Fresh.aux7Statement_of_partA hk4 hA

end Close

end InteractingSLE.Sec7.R5Init
