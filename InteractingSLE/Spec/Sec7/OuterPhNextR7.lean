/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterPhNextMeans
import InteractingSLE.Spec.Sec7.OuterPhNextShared

/-!
# R.7 outer phases from R.5 continuity and the shared-side visit step

PROVE-R7-OUTERPHASE continuation. This assembles the unchanged
`OuterIn.R7OuterPhaseSideRemaining` conditionally. The two open propositions
are named with their full Lean types: R.5 up to a continuous phase on every
outer test, and R.6's countable shared-side visits outside the bounded sector.
The phase conditional-law input is discharged using the landed outer marked
union law. No full Theorem 1.2 or 1.3 input is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.OuterPhNext

open WholeField R7Outer R7Leaves RefWire HOuter Hsd PhaseSide
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-- Named open R.5 input on the outer configurations of the original target:
the lattice word and continuity, without the zero-phase selection. -/
def R7OuterPhaseContRemaining (k rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      PhaseClause.TwoSeedPhaseContInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        PhaseClause.TwoSeedPhaseContInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'


/-- Named open R.6 step on every outer configuration; used only outside the
bounded sector. Its exact event-level content is `TwoSeedSharedVisitsInput(Inf)`. -/
def R7OuterSharedVisitsRemaining (k rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedSharedVisitsInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedSharedVisitsInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'


/-- The original outer phase input follows from R.5 with phase continuity
and the named shared-side visit step. Aux. 122 discharges selection when both
weights are strictly below `k - 6`; the shared-side premise is used only in
the complementary sector, including equality at the endpoint. -/
theorem r7OuterPhaseSideRemaining_of_cont_shared {k rL rR : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : R7OuterPhaseContRemaining.{u} k rL rR)
    (hshared : ¬ (rL < k - 6 ∧ rR < k - 6) → R7OuterSharedVisitsRemaining.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hcont P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  by_cases hsmall : rL < k - 6 ∧ rR < k - 6
  · have hk0 : 0 < k := lt_trans (by norm_num) hk4
    have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
    have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
    have hb := isPiecewiseConstant_prop74Data
      (r7A k rR + π * chiC (16 / k)) (r7B k rL + 0)
    have hgff := hcfg.gff
    obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
    obtain ⟨-, hT', hTr, hC⟩ := hD
    obtain ⟨hX, -⟩ := hC.2.2.2
    have hc : 0 ≤ π * chiC (16 / k) :=
      mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
    have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
      (ae_counterflow_trace_r7 hk4 hc le_rfl hgff hcfg.counterflow).mono fun ω hω => hω.1
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
    have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hV.R_meas hV.L_meas
    have hGp : MeasurableSet[wallsSigma P R L]
        {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
      (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
    have hG0 : MeasurableSet[wallsSigma P R L]
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
      convert hGm.diff hGp using 1
      ext ω
      simp only [mem_ofPred_eq, Set.mem_sdiff]
      tauto
    have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
      intro ω hω
      exact hcfgI ω hω.1
        (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
    have hm := twoSeedPhaseMeansInput_of_const_outer hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ
      hV.R_cont hV.L_cont hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL
      hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2) (fun ω hω => hζG ω hω.1)
      (PhaseClause.twoSeedPhaseConstInput_of_cont hk4 hs)
    have hmI := twoSeedPhaseMeansInputInf_of_const_outer hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ
      hV.R_cont hV.L_cont hV.R_zero hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL
      hV.η_meas hG0 hcfgI' (fun ω hω => hζG ω hω.1)
      (PhaseClause.twoSeedPhaseConstInputInf_of_cont hk4 hsI)
    refine ⟨OuterPh.twoSeedPhaseSideInput_of_means_outer
      (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 hrL hsmall.1 hrR hsmall.2 h𝓦 ?_ hm,
      OuterPh.twoSeedPhaseSideInputInf_of_means_outer
        (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 hrL hsmall.1 hrR hsmall.2 h𝓦 hcfgI' hmI⟩
    exact fun ω hω => hcfgP ω hω.1 hω.2
  · obtain ⟨ha, haI⟩ := hshared hsmall P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
      b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
    exact ⟨twoSeedPhaseSideInput_of_cont_shared hs ha,
      twoSeedPhaseSideInputInf_of_cont_shared hsI haI⟩

end InteractingSLE.Sec7.OuterPhNext
