/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfFresh

/-!
# Lemma R.5 on the extremal R.7 pockets from the initial heights, two almost-sure facts and the outer collars

Packet PROVE-R5-LIFT2 (third round). `R5Wall.R7SplitRemainingCur` with its two current-chart inputs reduced to
`R5Lift.R7FreshTip(Inf)` (the seed-interval landings in `ℍ` and the fresh interior tip at the left stop, both almost
sure) and `R5Lift.R7OuterRefl(Inf)` (the outer collars' `K_s`-landing), next to the initial heights:

* `TwoSeedSplitInputFresh(Inf)`, `R7SplitRemainingFresh` (defs, **named input**);
* **`twoSeedSplitInputCur_of_fresh`**, **`twoSeedSplitInputCurInf_of_fresh`**;
* **`r7R5RemainingOn_of_splitFresh`**, **`r7PhaseWordRemaining_of_splitFresh`**.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R7Outer R7Leaves StripPocketConfig RefWire R5Phase R5Ref R5Enl PhaseSel

universe u

section Defs

variable {Ω : Type*}

/-- **The split-cover inputs reduced to the initial heights, two almost-sure facts and the outer collars** (bounded
change pocket; named input): `R5Wall.TwoSeedSplitInputCur` with `R5Lift.R7LiftCurGeom` and `R5Lift.R7OuterLiftGeom`
replaced by `R5Lift.R7FreshTip` (at positive capacities) and `R5Lift.R7OuterRefl`. -/
def TwoSeedSplitInputFresh (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ a : ℝ, (∃ m : ℤ, a = m * phaseStep κ) ∧
        ∃ (X₀ : Ω → Set ℂ) (X : ℝ≥0 → Ω → Set ℂ),
          R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
            (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u X₀ ∧
          ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧ (∀ ω, X₀ ω ⊆ X q ω) ∧ (∀ ω, outerExc R L r η ψ q ω ⊆ X q ω) ∧
            (0 < q → R5Lift.R7FreshTip P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) ∧
            R5Lift.R7OuterRefl P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' (X q) q

/-- **The split-cover inputs reduced to the initial heights, two almost-sure facts and the outer collars** (pocket
opening at the flow seed; named input): `R5Wall.TwoSeedSplitInputCurInf` with `R5Lift.R7LiftCurGeomInf` and
`R5Lift.R7OuterLiftGeomInf` replaced by `R5Lift.R7FreshTipInf` (at positive capacities) and `R5Lift.R7OuterReflInf`. -/
def TwoSeedSplitInputFreshInf (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ a : ℝ, (∃ m : ℤ, a = m * phaseStep κ) ∧
        ∃ (X₀ : Ω → Set ℂ) (X : ℝ≥0 → Ω → Set ℂ),
          R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
            (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u X₀ ∧
          ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧ (∀ ω, X₀ ω ⊆ X q ω) ∧ (∀ ω, outerExcInf R L r η ψ q ω ⊆ X q ω) ∧
            (0 < q → R5Lift.R7FreshTipInf P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) ∧
            R5Lift.R7OuterReflInf P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' (X q) q

end Defs

/-- **`TwoSeedSplitInputCur` from the fresh-tip inputs** (bounded change pocket). -/
theorem twoSeedSplitInputCur_of_fresh {Ω : Type*} [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedSplitInputFresh κ rL rR P R L r η G h₀ u W' ζ') :
    TwoSeedSplitInputCur κ rL rR P R L r η G h₀ u W' ζ' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, X, hInit, hq⟩ := hin A hA hAG hPA ψ hψ hψm
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hfacts := shiftChart_cfPocket_facts hcfgA hψ n
  refine ⟨n, hn, a, ha, X₀, X, hInit, fun q => ?_⟩
  obtain ⟨hXf, hX₀, hOX, hfresh, hrefl⟩ := hq q
  exact ⟨hXf, hX₀, hOX,
    R5Lift.r7LiftCurGeom_of_fresh hcfgA hψ (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1)
      (fun ω hω => (hfacts ω hω).2.2) (fun _ => rfl) (fun _ => rfl) hfresh,
    R5Lift.r7OuterLiftGeom_of_fresh hcfgA hψ (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1)
      (fun ω hω => (hfacts ω hω).2.2) (fun _ => rfl) (fun _ => rfl) hfresh hrefl⟩

/-- **`TwoSeedSplitInputCurInf` from the fresh-tip inputs** (pocket opening at the flow seed). -/
theorem twoSeedSplitInputCurInf_of_fresh {Ω : Type*} [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedSplitInputFreshInf κ rL rR P R L r η G h₀ u W' ζ') :
    TwoSeedSplitInputCurInf κ rL rR P R L r η G h₀ u W' ζ' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, X, hInit, hq⟩ := hin A hA hAG hPA ψ hψ hψm
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hfacts := shiftChart_cfPocketInf_facts hcfgA hψ n
  refine ⟨n, hn, a, ha, X₀, X, hInit, fun q => ?_⟩
  obtain ⟨hXf, hX₀, hOX, hfresh, hrefl⟩ := hq q
  exact ⟨hXf, hX₀, hOX,
    R5Lift.r7LiftCurGeomInf_of_fresh hcfgA hψ (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1)
      (fun ω hω => (hfacts ω hω).2.2) (fun _ => rfl) (fun _ => rfl) hfresh,
    R5Lift.r7OuterLiftGeomInf_of_fresh hcfgA hψ (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1)
      (fun ω hω => (hfacts ω hω).2.2) (fun _ => rfl) (fun _ => rfl) hfresh hrefl⟩

/-- **The fresh-tip split-cover inputs on every R.7 configuration** (named input; margins `c`, `c′`): the premises
are exactly those of `R5Enl.R7R5RemainingOn`; the conclusion is `TwoSeedSplitInputFresh(Inf)` against the counterflow's
coupling (force processes `VL`, `VR`, weights `flowLineRho(L/R) k b' J' 0 0`). -/
def R7SplitRemainingFresh (k rL rR c c' : ℝ) : Prop :=
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
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedSplitInputFresh k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' W' ζ' ∧
        TwoSeedSplitInputFreshInf k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' W' ζ'

/-- **`R5Enl.R7R5RemainingOn` at all margins from the fresh-tip split-cover inputs**: `r7R5RemainingOn_of_splitCur`
after `twoSeedSplitInputCur(Inf)_of_fresh` on the two kinds of change pockets. -/
theorem r7R5RemainingOn_of_splitFresh {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hs5 : R7SplitRemainingFresh.{u} k rL rR c c') : R7R5RemainingOn.{u} k rL rR c c' := by
  refine r7R5RemainingOn_of_splitCur hk4 hc hc' ?_
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedSplitInputCur_of_fresh (fun ω hω => hcfgP ω hω.1 hω.2) hs,
    twoSeedSplitInputCurInf_of_fresh (fun ω hω => hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))) hsI⟩

/-- **R.5 up to phase on every R.7 pocket test from the fresh-tip split-cover inputs**:
`R5Enl.r7PhaseWordRemaining_of_r5On` after `r7R5RemainingOn_of_splitFresh`. -/
theorem r7PhaseWordRemaining_of_splitFresh {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hs5 : R7SplitRemainingFresh.{u} k rL rR c c') : PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  r7PhaseWordRemaining_of_r5On hk4 hc hc' (r7R5RemainingOn_of_splitFresh hk4 hc hc' hs5)

end InteractingSLE.Sec7.R5Wall
