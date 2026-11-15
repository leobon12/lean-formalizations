/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeWire

/-!
# The R.6 → R.7 outer-phase chain at arbitrary margins

PROVE-R6-SAFE. The two-outer-arm case of R.6 (supplement p. 476, "Application to two outer arms") passes through the
intermediate mixed pocket `V` bounded by `α_R` and `β_L`, an R.7 configuration with **enlarged margins**
(`OuterGeom.isR7OuterConfig_leftExt`). Its zero-phase words therefore need the R.6 → R.7 wiring chain at arbitrary
margins. The landed chain (`R6Rel.R6NestCertRemaining` → `R6Nest.R6NestRelRemaining` →
`OuterPhNext.R7OuterSharedVisitsRemaining` → `OuterIn.R7OuterPhaseSideRemaining` → `OuterIn.R7OuterSideRemaining`)
fixes the margins `(πχ(16/k), 0)` only in its statements; its proofs are margin-general. Here:

* the margin-general statements `R6NestCertMRemaining`, `R6NestRelMRemaining`, `R7OuterSharedVisitsMRemaining`,
  `R7OuterPhaseSideMRemaining`, `R7OuterSideMRemaining` (definitionally the landed ones at `(πχ(16/k), 0)`,
  `…_std_iff`);
* the chain at arbitrary margins: `r6NestRelMRemaining_of_cert`, `r7OuterSharedVisitsMRemaining_of_nestRel`,
  `r7OuterPhaseSideMRemaining_of_cont_shared`, `r7OuterSideMRemaining_of_phase` (copies of the landed proofs);
* **`r6NestCertMRemaining_of_core_safe`**: the mixed-case certificates at arbitrary margins `c ≥ πχ`, `c′ ≥ 0`
  (R48-safe, `R6Safe.twoSeedNestCertInput(Inf)_of_geom_safe`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open WholeField R7Outer R7Leaves RefWire HOuter Hsd PhaseSide SideVis R6Nest R6Rel OuterPhNext OuterIn
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-! ### The statements at arbitrary margins -/

section Defs

/-- **Named, unproved: R.6 certificates for the nested candidates on every outer configuration, at arbitrary
margins `c, c'`** (supplement pp. 475–477; `R6Rel.R6NestCertRemaining` at `(c, c')`): the original R.7 premises,
concluding the phase-free certificates `TwoSeedNestCertInput(Inf)` for the inner pair
`(innerRight k rL R βR, innerLeft k rR L βL)`. -/
def R6NestCertMRemaining (k rL rR c c' : ℝ) : Prop :=
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedNestCertInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL) ∧
        TwoSeedNestCertInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL)

/-- **Named, unproved R.6 transfer for one nested candidate at a deterministic relative time, on every outer
configuration, at arbitrary margins `c, c'`** (supplement pp. 475–477): the original R.7 premises, concluding
`TwoSeedNestRelInput(Inf)` for the inner pair `(innerRight k rL R βR, innerLeft k rR L βL)`. -/
def R6NestRelMRemaining (k rL rR c c' : ℝ) : Prop :=
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedNestRelInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL) ∧
        TwoSeedNestRelInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL)

/-- Named open R.6 step on every outer configuration at arbitrary margins `c, c'`; used only outside the
bounded sector. Its exact event-level content is `TwoSeedSharedVisitsInput(Inf)`. -/
def R7OuterSharedVisitsMRemaining (k rL rR c c' : ℝ) : Prop :=
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedSharedVisitsInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedSharedVisitsInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'


/-- **The three parts of the outer pockets' two-seed side limits on every R.7 configuration, at arbitrary
margins `c, c'`** (named input): the
premises of `R7OuterSideRemaining`, with the conclusion in the phase form `Hsd.TwoSeedPhaseSideInput(Inf)` — R.5's
lattice-phase word, its constancy, and the phase selection (Aux. lemma 122 for weights in `(−2, k − 6)`, otherwise
R.6's shared-side anchor, follow-up 5 §3.3). -/
def R7OuterPhaseSideMRemaining (k rL rR c c' : ℝ) : Prop :=
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedPhaseSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The zero-phase two-seed side limits of the outer pockets on every R.7 configuration at arbitrary margins
`c, c'`** (`OuterIn.R7OuterSideRemaining` with the margins `(πχ(16/k), 0)` replaced by `(c, c')`). -/
def R7OuterSideMRemaining (k rL rR c c' : ℝ) : Prop :=
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
        IsOuterCfg (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

end Defs

/-! ### The chain at arbitrary margins -/

section Chain

/-- **`R6NestRelMRemaining` from the R.6 certificates** (`R6Rel.r6NestRelRemaining_of_cert` at margins `c, c'`). -/
theorem r6NestRelMRemaining_of_cert {k rL rR c c' : ℝ} (hcert : R6NestCertMRemaining.{u} k rL rR c c') :
    R6NestRelMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hc, hcI⟩ := hcert P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedNestRelInput_of_cert hc, twoSeedNestRelInputInf_of_cert hcI⟩

/-- **R.6's shared-side witnesses on every outer configuration at margins `c, c'`**
(`R6Nest.r7OuterSharedVisitsRemaining_of_nestRel` at arbitrary margins). -/
theorem r7OuterSharedVisitsMRemaining_of_nestRel (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR c c' : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hnest : R6NestRelMRemaining.{u} k rL rR c c') :
    R7OuterSharedVisitsMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hn, hnI⟩ := hnest P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have h42 := OuterIn.ae_noSimpleArc_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have hβ : ∀ᵐ ω ∂P, Sec5.Prop55Half.IsSeedProper (βR ω) ∧ Sec5.Prop55Half.IsSeedProper (βL ω) :=
    hcfg.regular.mono fun ω hω => ⟨hω.2.1, hω.2.2.1⟩
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  refine ⟨twoSeedSharedVisitsInput_of_anchor hk4
      (twoSeedSharedAnchorInput_of_nestRel (W := fun ω (s : ℝ) => W' s.toNNReal ω) hn
        (fun ω hω => hcfgP ω hω.1 hω.2) h42 hβ fun t => ?_),
    twoSeedSharedVisitsInputInf_of_anchor hk4
      (twoSeedSharedAnchorInputInf_of_nestRel (W := fun ω (s : ℝ) => W' s.toNNReal ω) hnI hcfgI' h42 hβ
        fun t => ?_)⟩
  · filter_upwards [ae_exists_nestEvent h55 hk4 hrL hrR hc hc' hcfg hV (StripSys.rt q) t] with ω hω hωG hvis
    exact hω (hζG ω hωG.1) (hconf ω hωG.1) hvis
  · filter_upwards [ae_exists_nestEventInf h55 hk4 hrL hrR hc hc' hcfg hV (StripSys.rt q) t] with
      ω hω hωG hvis
    exact hω (hζG ω hωG.1) (hconf ω hωG.1) hvis

/-- **The outer phase input at margins `c, c'` from R.5 with continuity and the shared-side visit step**
(`OuterPhNext.r7OuterPhaseSideRemaining_of_cont_shared` at arbitrary margins). -/
theorem r7OuterPhaseSideMRemaining_of_cont_shared {k rL rR c c' : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcont : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c')
    (hshared : ¬ (rL < k - 6 ∧ rR < k - 6) → R7OuterSharedVisitsMRemaining.{u} k rL rR c c') :
    R7OuterPhaseSideMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hcont P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  by_cases hsmall : rL < k - 6 ∧ rR < k - 6
  · have hk0 : 0 < k := lt_trans (by norm_num) hk4
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

/-- **The outer pockets' side field at margins `c, c'` from the three parts**
(`OuterIn.r7OuterSideRemaining_of_phase`). -/
theorem r7OuterSideMRemaining_of_phase {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hside : R7OuterPhaseSideMRemaining.{u} k rL rR c c') : R7OuterSideMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  refine ⟨twoSeedSideInput_of_phase_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 ?_ hs,
    twoSeedSideInputInf_of_phase_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 ?_ hsI⟩
  · exact fun ω hω => hcfgP ω hω.1 hω.2
  · exact fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))

end Chain

/-! ### The standard margins and the mixed case at arbitrary margins -/

section Mixed

variable {k rL rR : ℝ}

/-- At the margins `(πχ(16/k), 0)` the margin-general certificates are `R6Rel.R6NestCertRemaining`. -/
theorem r6NestCertMRemaining_std_iff :
    R6NestCertMRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ↔ R6Rel.R6NestCertRemaining.{u} k rL rR := Iff.rfl

/-- At the margins `(πχ(16/k), 0)` the margin-general outer phase input is `OuterIn.R7OuterPhaseSideRemaining`. -/
theorem r7OuterPhaseSideMRemaining_std_iff :
    R7OuterPhaseSideMRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ↔ OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  Iff.rfl

/-- At the margins `(πχ(16/k), 0)` the margin-general side field is `OuterIn.R7OuterSideRemaining`. -/
theorem r7OuterSideMRemaining_std_iff :
    R7OuterSideMRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ↔ OuterIn.R7OuterSideRemaining.{u} k rL rR := Iff.rfl

/-- A margin `c ≥ πχ(16/k)` is nonnegative. -/
theorem nonneg_of_pi_chi_le {c : ℝ} (hk4 : 4 < k) (hcπ : π * chiC (16 / k) ≤ c) : 0 ≤ c :=
  (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith))
    (R7.sixteen_div_lt_four hk4)).le).trans hcπ

/-- **The mixed-case R.6 certificates at arbitrary margins `c ≥ πχ(16/k)`, `c′ ≥ 0`**, R48-safe
(`twoSeedNestCertInput_of_geom_safe`, `twoSeedNestCertInputInf_of_geom_safe` with the core geometry inputs). -/
theorem r6NestCertMRemaining_of_core_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) {c c' : ℝ}
    (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcore : R6Fin.R6GeomCoreMixedRemaining.{u} k rL rR c c')
    (hcoreI : R6Fin.R6GeomCoreMixedInfRemaining.{u} k rL rR c c')
    (hcoreII : R6Fin.R6GeomCoreMixedInfInfRemaining.{u} k rL rR c c')
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    R6NestCertMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedNestCertInput_of_geom_safe h411 h51 h47 h47T haux7 h44 hword
      (R6Fin.r6GeomMixedRemaining_of_core hcore) hk4 hL hR hcπ hc' hmix hcfg hD hu₀' hV hGm hconf hζG hcfgP,
    twoSeedNestCertInputInf_of_geom_safe h411 h51 h47 h47T haux7 h44 hword
      (R6Fin.r6GeomMixedInfRemaining_of_core hcoreI) (R6Fin.r6GeomMixedInfInfRemaining_of_core hcoreII) hk4 hL hR
      hcπ hc' hmix hcfg hD hu₀' hV hGm hconf hζG hcfgI⟩

/-- **The outer phase input at arbitrary margins `c ≥ πχ(16/k)`, `c′ ≥ 0`**, R48-safe: from R.5 with continuity at
these margins, the mixed-case certificates (`r6NestCertMRemaining_of_core_safe`) and, for two outer arms, the input
`htwo`. -/
theorem r7OuterPhaseSideMRemaining_of_core_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) {c c' : ℝ}
    (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcore : R6Fin.R6GeomCoreMixedRemaining.{u} k rL rR c c')
    (hcoreI : R6Fin.R6GeomCoreMixedInfRemaining.{u} k rL rR c c')
    (hcoreII : R6Fin.R6GeomCoreMixedInfInfRemaining.{u} k rL rR c c')
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hcont : R6Rel.R7OuterPhaseContMRemaining.{u} k rL rR c c')
    (htwo : k / 2 - 4 < rL → k / 2 - 4 < rR → R6NestCertMRemaining.{u} k rL rR c c') :
    R7OuterPhaseSideMRemaining.{u} k rL rR c c' :=
  r7OuterPhaseSideMRemaining_of_cont_shared hk4 hL hR (nonneg_of_pi_chi_le hk4 hcπ) hc' hcont fun hbad =>
    r7OuterSharedVisitsMRemaining_of_nestRel
      (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51) hk4 hL hR
      (nonneg_of_pi_chi_le hk4 hcπ) hc' (r6NestRelMRemaining_of_cert
      ((R6Fin.mixed_or_twoOuter hk4 hbad).elim
        (fun hmix => r6NestCertMRemaining_of_core_safe h411 h51 h47 h47T haux7 h44 hcπ hc' hword hcore hcoreI
          hcoreII hk4 hL hR hmix)
        fun h2 => htwo h2.1 h2.2))

end Mixed

end InteractingSLE.Sec7.R6Safe
