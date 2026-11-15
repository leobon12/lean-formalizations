/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HsdSide
import InteractingSLE.Spec.Sec7.HOuterWire

/-!
# Theorem R.7's outer pockets: the two-seed side limits from the source's three parts

Packet PROVE-R7-OUTERIN. The `side` field of `HOuter.R7OuterInputs` asks, on every walls' event of an R.7
configuration with the outer pocket's configuration (`HOuter.IsOuterCfg(Inf)`), for the canonical two-seed side limits
(`RefWire.TwoSeedSideInput(Inf)`, Corollary 3.2 of Astra's follow-up 5, R73) — the same proposition as the extremal
`hsd.side`. As for the extremal pockets (PROVE-HSD, `Hsd.twoSeedSideInput_of_phase`), it follows from the source's three
parts (follow-up 5 §3.1–§3.3): (1) R.5's boundary word up to a lattice phase, (2) constancy of the phase on the positive
lifetime, (3) the phase vanishes at one positive time. For outer pockets (3) is Aux. lemma 122 when both weights lie in
`(−2, k − 6)`, and otherwise R.6's shared-side anchor (follow-up 5 §3.3, Lemma 3.1: transfer of zero phase from an
inner contained mixed pocket, and from an extremal pocket for two outer sides).

* **`twoSeedSideInput_of_phase_outer`**, **`twoSeedSideInputInf_of_phase_outer`**: `TwoSeedSideInput(Inf)` from
  `Hsd.TwoSeedPhaseSideInput(Inf)` on outer configurations (the relative traversal is driven: `IsOuterCfg.props`);
* `R7OuterSideRemaining` (the `side` field on every R.7 configuration), `R7OuterPhaseSideRemaining` (the three parts on
  every R.7 configuration), **`r7OuterSideRemaining_of_phase`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.OuterIn

open WholeField R7Outer R7Leaves RefWire HOuter Hsd
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-! ### The side limits of an outer pocket from the three parts -/

section Side

/-- **The two-seed side limits in a bounded outer change pocket from the three parts** (the same branch `n`):
`PocketStopSide.pocketStopSideLimit_of_phase_common_anchor` on each test; the relative traversal is driven
(`IsOuterCfg.props`). -/
theorem twoSeedSideInput_of_phase_outer {Ω : Type*} {κ rL rR : ℝ} (hκ : 4 < κ) {𝓦 : MeasurableSpace Ω}
    [MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} {W : Ω → ℝ → ℝ} (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseSideInput κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedSideInput κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, a, δ, hph, hcont, hanc⟩ := h A hA hAG hPA ψ hJ hPt
  refine ⟨n, a, hn, ?_⟩
  exact PocketStopSide.pocketStopSideLimit_of_phase_common_anchor hκ
    (fun ω hω => ((hcfg ω (hAG hω)).props (hJ ω hω)).1) (fun _ _ => rfl) (fun _ _ => rfl) hph hcont hanc

/-- **The two-seed side limits in an outer change pocket opening at the flow seed from the three parts**. -/
theorem twoSeedSideInputInf_of_phase_outer {Ω : Type*} {κ rL rR : ℝ} (hκ : 4 < κ) {𝓦 : MeasurableSpace Ω}
    [MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} {W : Ω → ℝ → ℝ} (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseSideInputInf κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedSideInputInf κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, a, δ, hph, hcont, hanc⟩ := h A hA hAG hPA ψ hJ hPt
  refine ⟨n, a, hn, ?_⟩
  exact PocketStopSide.pocketStopSideLimit_of_phase_common_anchor hκ
    (fun ω hω => ((hcfg ω (hAG hω)).props (hJ ω hω)).1) (fun _ _ => rfl) (fun _ _ => rfl) hph hcont hanc

end Side

/-! ### The side field on every R.7 configuration -/

section Remaining

/-- **The `side` field of `HOuter.R7OuterInputs` on every R.7 configuration** (heights `c = πχ(16/k)`, `c′ = 0`, as in
`HOuter.R7OuterRemaining`): for every configuration, decomposition, force-word mean `u₀′` and versions `R`, `L`, `η`,
the `side` field verbatim. -/
def R7OuterSideRemaining (k rL rR : ℝ) : Prop :=
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
      TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The three parts of the outer pockets' two-seed side limits on every R.7 configuration** (named input): the
premises of `R7OuterSideRemaining`, with the conclusion in the phase form `Hsd.TwoSeedPhaseSideInput(Inf)` — R.5's
lattice-phase word, its constancy, and the phase selection (Aux. lemma 122 for weights in `(−2, k − 6)`, otherwise
R.6's shared-side anchor, follow-up 5 §3.3). -/
def R7OuterPhaseSideRemaining (k rL rR : ℝ) : Prop :=
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
      TwoSeedPhaseSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The outer pockets' side field from the three parts** on every R.7 configuration
(`twoSeedSideInput(Inf)_of_phase_outer`; the traversals are driven by the outer configurations of the premises). -/
theorem r7OuterSideRemaining_of_phase {k rL rR : ℝ} (hk4 : 4 < k)
    (hside : R7OuterPhaseSideRemaining.{u} k rL rR) : R7OuterSideRemaining.{u} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  refine ⟨twoSeedSideInput_of_phase_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 ?_ hs,
    twoSeedSideInputInf_of_phase_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 ?_ hsI⟩
  · exact fun ω hω => hcfgP ω hω.1 hω.2
  · exact fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))

end Remaining

end InteractingSLE.Sec7.OuterIn
