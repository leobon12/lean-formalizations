/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterPhNextR7
import InteractingSLE.Spec.Sec7.OuterInCounterflow
import InteractingSLE.Spec.Sec7.SideVisR7

/-!
# R.6's shared-side visits on every outer R.7 configuration

PROVE-SIDE-VISITS. `OuterPhNext.R7OuterSharedVisitsRemaining` (the R.6 input of
the outer phase assembly) is reduced to the fixed-time R.6 transfer
`R7SharedTransferRemaining` at certified rational visits: the visits themselves
are proved here from the configuration (`IsOuterCfg(Inf)`), Aux. 42 for the
counterflow (`OuterIn.ae_noSimpleArc_counterflow_r7`, Lemma GB10) and the
seed-proper certified frontiers `β_R, β_L` (`IsR7OuterConfig.regular`).

`R7SharedTransferRemaining` is a named, **unproved** statement with all of the
original R.7 premises; its conclusion is the transfer at each deterministic
rational original time. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.SideVis

open WholeField R7Outer R7Leaves RefWire HOuter Hsd PhaseSide
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-- **Named, unproved R.6 transfer on every outer configuration** (supplement
pp. 476–477): the original R.7 premises of `OuterPhNext.R7OuterSharedVisitsRemaining`,
concluding the fixed-time transfer `TwoSeedSharedTransferInput(Inf)` with the
configuration's certified frontiers `β_R, β_L`. -/
def R7SharedTransferRemaining (k rL rR : ℝ) : Prop :=
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
      TwoSeedSharedTransferInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL ∧
        TwoSeedSharedTransferInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL

/-- **R.6's shared-side witnesses on every outer configuration from the fixed-time
transfer**: the visits are proved (Aux. 42 for the counterflow, seed-proper
frontiers, the erasure clocks of `IsOuterCfg(Inf)`). -/
theorem r7OuterSharedVisitsRemaining_of_transfer {k rL rR : ℝ} (hk4 : 4 < k)
    (htr : R7SharedTransferRemaining.{u} k rL rR) :
    OuterPhNext.R7OuterSharedVisitsRemaining.{u} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨ht, htI⟩ := htr P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := lt_trans (by norm_num) hk4
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have h42 := OuterIn.ae_noSimpleArc_counterflow_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow hD hV.η_trace
  have hβ : ∀ᵐ ω ∂P, Sec5.Prop55Half.IsSeedProper (βR ω) ∧ Sec5.Prop55Half.IsSeedProper (βL ω) :=
    hcfg.regular.mono fun ω hω => ⟨hω.2.1, hω.2.2.1⟩
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedSharedVisitsInput_of_transfer (W := fun ω (s : ℝ) => W' s.toNNReal ω) ht
      (fun ω hω => hcfgP ω hω.1 hω.2) h42 hβ,
    twoSeedSharedVisitsInputInf_of_transfer (W := fun ω (s : ℝ) => W' s.toNNReal ω) htI hcfgI' h42 hβ⟩

/-- The outer phase input `OuterIn.R7OuterPhaseSideRemaining` from R.5 with
continuity and the fixed-time R.6 transfer (the latter only outside Aux. 122's
bounded sector). -/
theorem r7OuterPhaseSideRemaining_of_cont_transfer {k rL rR : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htr : ¬ (rL < k - 6 ∧ rR < k - 6) → R7SharedTransferRemaining.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  OuterPhNext.r7OuterPhaseSideRemaining_of_cont_shared hk4 hrL hrR hcont
    fun hbad => r7OuterSharedVisitsRemaining_of_transfer hk4 (htr hbad)

end InteractingSLE.Sec7.SideVis
