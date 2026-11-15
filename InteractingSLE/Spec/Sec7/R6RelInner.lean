/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6NestRelWire
import InteractingSLE.Spec.Sec7.R6NestInner
import InteractingSLE.Spec.Sec7.PhaseContR7
import InteractingSLE.Spec.Sec7.OuterGeomExt

/-!
# R.6's inner pockets: R.5 at arbitrary margins and the inner zero-phase words

PROVE-R6-NESTREL. Lemma R.6 (supplement pp. 475–477) compares an outer R.7 pocket `C` with an inner pocket `U ⊂ C`
bounded by the certified frontiers. The inner pair `(innerRight k rL R βR, innerLeft k rR L βL)` is an R.7
configuration of the same field and counterflow (`R6Nest.IsR7OuterConfig.inner`), with the weights
`(min(rL, d), min(rR, d))`, `d = k/2 − 4`, and with **enlarged margins**
`(πχ + (r7A k rR − r7A k rR'), 0 + (r7B k rL − r7B k rL'))`.

**Margins (finding).** The inner configuration has `max = d`, so its pockets are *extremal* pockets (pocket premises
`IsCfPocketConfig`, Aux. 131), not outer ones. The extremal R.5 inputs `PhaseCont.R7PhaseWordRemaining k rL rR c c'`
and `PhaseClause.R7PhaseContRemaining k rL rR c c'`, and the whole bounded-sector chain behind them, are **already
stated for arbitrary margins `c, c'`**; only the Theorem 1.2 wiring instantiates them at `(πχ, 0)`. So the inner
pocket's R.5 input is `R7PhaseWordRemaining` at the inner weights and margins, and its zero phase is proved here from
it (`r7SideRemaining_of_word`, `inner_side_of_word`). Only the *outer* R.5 input fixes the margins; its
arbitrary-margin form is `R7OuterPhaseContMRemaining` (the intermediate mixed pocket `V` of the two-outer-arm case
is an outer configuration with enlarged margins).

* `R7OuterPhaseContMRemaining` (named, unproved: `OuterPhNext.R7OuterPhaseContRemaining` with margins `c, c'`) and
  its instance `r7OuterPhaseContRemaining_of_marg`;
* `r7SideRemaining_of_word`: Aux. 131/122's bounded-sector chain at arbitrary margins, R.5 up to phase ⇒ the
  zero-phase two-seed words (`Hsd.R7SideRemaining`);
* `innerMarginL_nonneg`, `innerMarginR_nonneg`, `isR7Versions_inner`;
* **`inner_side_of_word`**: the inner pair built from frontier versions carries the zero-phase two-seed words on every
  inner pocket test, from `R7PhaseWordRemaining` at the inner weights and margins.

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

namespace InteractingSLE.Sec7.R6Rel

open WholeField R7Outer R7Leaves RefWire HOuter Hsd PhaseSide R6Nest
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-! ### The outer R.5 input at arbitrary margins -/

section Margins

/-- **R.5 up to phase with continuity on every outer R.7 configuration, at arbitrary margins `c, c'`** (named,
unproved): `OuterPhNext.R7OuterPhaseContRemaining` with the margins `(πχ(16/k), 0)` replaced by `(c, c')`. The
source's proof of R.5 (supplement pp. 474–475) does not depend on the margins; every landed a.s. R.7 geometry result
already takes `0 ≤ c`, `0 ≤ c'`. -/
def R7OuterPhaseContMRemaining (k rL rR c c' : ℝ) : Prop :=
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
      PhaseClause.TwoSeedPhaseContInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        PhaseClause.TwoSeedPhaseContInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- The arbitrary-margin outer R.5 input at the margins `(πχ(16/k), 0)` is `OuterPhNext.R7OuterPhaseContRemaining`. -/
theorem r7OuterPhaseContRemaining_of_marg {k rL rR : ℝ}
    (h : R7OuterPhaseContMRemaining.{u} k rL rR (π * chiC (16 / k)) 0) :
    OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR := h

/-- Conversely, `OuterPhNext.R7OuterPhaseContRemaining` is the arbitrary-margin input at `(πχ(16/k), 0)`. -/
theorem r7OuterPhaseContMRemaining_of_std {k rL rR : ℝ} (h : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR) :
    R7OuterPhaseContMRemaining.{u} k rL rR (π * chiC (16 / k)) 0 := h

/-- **Aux. 131/122's bounded-sector chain at arbitrary margins**: R.5 up to phase on every extremal pocket test
(`PhaseCont.R7PhaseWordRemaining k rL rR c c'`) gives the zero-phase two-seed words (`Hsd.R7SideRemaining`) when both
weights lie in `(−2, k − 6)` — continuity and constancy of the phase (PHASECONT), the phase clause and (M)
(PHASECLAUSE), Aux. 122's selection (PHASESIDE), all landed for arbitrary `c, c' ≥ 0`. -/
theorem r7SideRemaining_of_word {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hrL : -2 < rL) (hrL' : rL < k - 6) (hrR : -2 < rR) (hrR' : rR < k - 6)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c') : Hsd.R7SideRemaining.{u} k rL rR c c' :=
  r7SideRemaining_of_phase hk4 (r7PhaseSideRemaining_of_means hk4 hrL hrL' hrR hrR'
    (PhaseClause.r7PhaseMeansRemaining_of_const hk4 hc hc'
      (PhaseCont.r7PhaseConstRemaining_of_word hk4 hc hc' hword)))

end Margins

/-! ### The inner pockets: versions and zero-phase words -/

section Inner

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The inner left margin `c + (r7A k rR − r7A k rR')` is nonnegative. -/
theorem innerMarginL_nonneg {k rR c : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) :
    0 ≤ c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))) := by
  have := r7A_innerLeft_le hk4 rR
  linarith

/-- The inner right margin `c' + (r7B k rL − r7B k rL')` is nonnegative. -/
theorem innerMarginR_nonneg {k rL c' : ℝ} (hk4 : 4 < k) (hc' : 0 ≤ c') :
    0 ≤ c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4))) := by
  have := r7B_innerRight_le hk4 rL
  linarith

/-- **A version of a certified frontier**: continuous from `0` at every sample, measurable at fixed times, almost
surely equal to the frontier (the output of `OuterGeom.exists_frontierVersion`). -/
def IsFrontierVersion (P : Measure Ω) (β M : Ω → ℝ≥0 → ℂ) : Prop :=
  (∀ ω, Continuous (M ω)) ∧ (∀ ω, M ω 0 = 0) ∧ (∀ t, Measurable fun ω => M ω t) ∧ ∀ᵐ ω ∂P, M ω = β ω

/-- Every R.7 configuration has versions of its two certified frontiers. -/
theorem exists_isFrontierVersion {k rL rR c c' : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    (∃ MR, IsFrontierVersion P βR MR) ∧ ∃ ML, IsFrontierVersion P βL ML :=
  OuterGeom.exists_frontierVersion hcfg

/-- **The inner walls are versions of the inner arms**: replacing each outer wall by the version of its certified
frontier (`innerRight`, `innerLeft`) keeps `IsR7Versions`. -/
theorem isR7Versions_inner {k rL rR : ℝ} {W' : ℝ≥0 → Ω → ℝ} {αR βR βL αL R L MR ML : Ω → ℝ≥0 → ℂ}
    {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) (hMR : IsFrontierVersion P βR MR)
    (hML : IsFrontierVersion P βL ML) :
    IsR7Versions P W' (innerRight k rL αR βR) (innerLeft k rR αL βL) (innerRight k rL R MR)
      (innerLeft k rR L ML) η := by
  obtain ⟨hRc, hR0, hRm, hRae⟩ := hMR
  obtain ⟨hLc, hL0, hLm, hLae⟩ := hML
  by_cases hdR : k / 2 - 4 < rL <;> by_cases hdL : k / 2 - 4 < rR <;>
    simp only [innerRight, innerLeft, hdR, hdL, ↓reduceIte]
  · exact ⟨hRc, hR0, hRm, hRae, hLc, hL0, hLm, hLae, hV.η_cont, hV.η_zero, hV.η_meas, hV.η_trace⟩
  · exact ⟨hRc, hR0, hRm, hRae, hV.L_cont, hV.L_zero, hV.L_meas, hV.L_ae, hV.η_cont, hV.η_zero, hV.η_meas,
      hV.η_trace⟩
  · exact ⟨hV.R_cont, hV.R_zero, hV.R_meas, hV.R_ae, hLc, hL0, hLm, hLae, hV.η_cont, hV.η_zero, hV.η_meas,
      hV.η_trace⟩
  · exact hV

/-- **R.6's inner pockets have the zero-phase two-seed words** (supplement p. 476: "its phase is zero by Aux. 122"):
on an R.7 configuration with margins `c, c' ≥ 0`, walls `R`, `L` and frontier versions `MR`, `ML`, the inner pair
`(innerRight k rL R MR, innerLeft k rR L ML)` carries, on every walls' event of an inner change pocket with the
extremal pocket configuration, the canonical two-seed side limits (`RefWire.TwoSeedSideInput(Inf)`, phase zero) at
the inner weights — from R.5 up to phase at the inner weights and the inner (enlarged) margins alone. -/
theorem inner_side_of_word [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L MR ML : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    (hMR : IsFrontierVersion P βR MR) (hML : IsFrontierVersion P βL ML) (q : ℚ) (hq : 0 < q) (G : Set Ω)
    (hGm : MeasurableSet[wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)] G) (hPG : 0 < P G)
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hcfgP : ∀ ω ∈ G, 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q) →
      IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q)
        (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q)
        (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    TwoSeedSideInput k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
        (wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)) P (innerRight k rL R MR)
        (innerLeft k rR L ML) (StripSys.rt q) η
        {ω | ω ∈ G ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q)}
        (centredField h'' u₀') u₀' ∧
      TwoSeedSideInputInf k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
        (wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)) P (innerRight k rL R MR)
        (innerLeft k rR L ML) (StripSys.rt q) η
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt q)}
        (centredField h'' u₀') u₀' :=
  r7SideRemaining_of_word hk4 (innerMarginL_nonneg hk4 hc) (innerMarginR_nonneg hk4 hc')
    (neg_two_lt_innerRight_weight hk4 hL) (innerRight_weight_lt hk4) (neg_two_lt_innerLeft_weight hk4 hR)
    (innerLeft_weight_lt hk4) hword P h W' ζ' _ βR βL _ _ ζβR ζβL _
    (IsR7OuterConfig.inner h55 hk4 hL hR hc hc' hcfg) b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' _ _ η
    (isR7Versions_inner hV hMR hML) q hq G hGm hPG hconf hζG hcfgP hcfgI

end Inner

end InteractingSLE.Sec7.R6Rel
