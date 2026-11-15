/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6RelCert
import InteractingSLE.Spec.Sec7.R6NestRelWire

/-!
# `R6NestRelRemaining` from the phase-free R.6 certificates on every outer configuration

PROVE-R6-NESTREL. `R6Nest.R6NestRelRemaining k rL rR` (R.6's zero outer phase at deterministic rational relative times,
the recommended R.6 interface of PROVE-R6-NESTED) follows from the named input `R6NestCertRemaining k rL rR`: the
same R.7 premises, concluding the phase-free certificates `TwoSeedNestCertInput(Inf)` for the inner pair. Drop-ins
for the outer phase input: `r7OuterSharedVisitsRemaining_of_cert`, `r7OuterPhaseSideRemaining_of_cont_cert`.

`R6NestCertRemaining` is a named, **unproved** statement with all of the original R.7 premises. R48: nothing here
uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Rel

open WholeField R7Outer R7Leaves RefWire HOuter Hsd PhaseSide SideVis R6Nest
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-- **Named, unproved: R.6 certificates for the nested candidates on every outer configuration** (supplement
pp. 475–477): the original R.7 premises (those of `R6Nest.R6NestRelRemaining`), concluding the phase-free
certificates `TwoSeedNestCertInput(Inf)` for the inner pair `(innerRight k rL R βR, innerLeft k rR L βL)`. -/
def R6NestCertRemaining (k rL rR : ℝ) : Prop :=
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
      TwoSeedNestCertInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL) ∧
        TwoSeedNestCertInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL)

/-- **`R6NestRelRemaining` from the R.6 certificates** (`twoSeedNestRelInput(Inf)_of_cert` on every outer
configuration). -/
theorem r6NestRelRemaining_of_cert {k rL rR : ℝ} (hcert : R6NestCertRemaining.{u} k rL rR) :
    R6NestRelRemaining.{u} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hc, hcI⟩ := hcert P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedNestRelInput_of_cert hc, twoSeedNestRelInputInf_of_cert hcI⟩

/-- **R.6's shared-side witnesses on every outer configuration from the R.6 certificates** (drop-in for
`R6Nest.r7OuterSharedVisitsRemaining_of_nestRel`). -/
theorem r7OuterSharedVisitsRemaining_of_cert (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR) (hcert : R6NestCertRemaining.{u} k rL rR) :
    OuterPhNext.R7OuterSharedVisitsRemaining.{u} k rL rR :=
  r7OuterSharedVisitsRemaining_of_nestRel h55 hk4 hrL hrR (r6NestRelRemaining_of_cert hcert)

/-- **The outer phase input from R.5 with continuity and the R.6 certificates** (drop-in for
`R6Nest.r7OuterPhaseSideRemaining_of_cont_nestRel`): the certificates are needed only outside Aux. 122's bounded
sector. -/
theorem r7OuterPhaseSideRemaining_of_cont_cert (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (hcert : ¬ (rL < k - 6 ∧ rR < k - 6) → R6NestCertRemaining.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_nestRel h55 hk4 hrL hrR hcont fun hbad => r6NestRelRemaining_of_cert (hcert hbad)

end InteractingSLE.Sec7.R6Rel
