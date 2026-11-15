/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5FreshBase
import InteractingSLE.Spec.Supplement.GW4Completion
import InteractingSLE.Foundations.SLE.All

/-!
# Lemma R.5 on the extremal R.7 pockets from the initial heights, the outer collars and the counterflow's no-return

Packet PROVE-R5-FRESHTIP (second round). `R7SplitRemainingSeed` with its per-test clause `0 < q → R7SeedLand(Inf)`
discharged: the seed-interval landings follow from **the counterflow does not return to its start**
(`Theorem14.GW4Ident.CounterflowNoReturnStatement`, the project's named input, reduced in
`Supplement/CounterflowNoReturn` to `CfNoReturn.SeedGermStatement`) by `R5Fresh.r7SeedLand(Inf)_of_noReturn`.

* `TwoSeedSplitInputNR(Inf)`, `R7SplitRemainingNR` (defs, **named input**): the seed-landing bundle without the
  seed-landing clause;
* **`ae_noReturn_r7`**: the no-return statement applied to the R.7 counterflow (parameter `16/k`, infinite lifetime by
  `R7Leaves.ae_counterflow_trace_r7`); `ae_ne_zero_of_trace`: its reading on a counterflow trace `η`;
* **`twoSeedSplitInputSeed(Inf)_of_NR`**, **`r7SplitRemainingSeed_of_NR`**;
* **`r7R5RemainingOn_of_splitNR`**, **`r7PhaseWordRemaining_of_splitNR`**; `r7SplitRemainingNR_of_seed`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses; the no-return input must not be supplied through `counterflowNoReturnStatement_of_theorem13`.
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

namespace InteractingSLE.Sec7.R5Fresh

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause
  PhaseCont R7Outer R7Leaves StripPocketConfig RefWire R5Phase R5Ref R5Enl PhaseSel R5Wall

universe u

section Defs

variable {Ω : Type*}

/-- **The split-cover inputs reduced to the initial heights and the outer collars** (bounded change pocket; named
input): `TwoSeedSplitInputSeed` without its seed-landing clause, which follows from the counterflow's no-return
(`twoSeedSplitInputSeed_of_NR`). -/
def TwoSeedSplitInputNR (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
            R5Lift.R7OuterRefl P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' (X q) q

/-- **The split-cover inputs reduced to the initial heights and the outer collars** (pocket opening at the flow seed;
named input): `TwoSeedSplitInputSeedInf` without its seed-landing clause. -/
def TwoSeedSplitInputNRInf (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
            R5Lift.R7OuterReflInf P A R L r η ψ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' (X q) q

end Defs

/-- **The no-seed split-cover inputs on every R.7 configuration** (named input; margins `c`, `c′`): the premises
are exactly those of `R5Enl.R7R5RemainingOn`; the conclusion is `TwoSeedSplitInputSeed(Inf)` against the counterflow's
coupling (force processes `VL`, `VR`, weights `flowLineRho(L/R) k b' J' 0 0`). -/
def R7SplitRemainingNR (k rL rR c c' : ℝ) : Prop :=
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
      TwoSeedSplitInputNR k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' W' ζ' ∧
        TwoSeedSplitInputNRInf k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' W' ζ'

/-- **The R.7 counterflow does not return to its start** (from the named input `CounterflowNoReturnStatement` at the
flow parameter `16/k ∈ (0, 4)`; the lifetime is infinite almost surely by `R7Leaves.ae_counterflow_trace_r7`). -/
theorem ae_noReturn_r7 (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {αR βR βL αL : Ω → ℝ≥0 → ℂ}
    {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := by positivity
  have hκ4 : 16 / k < 4 := by rw [div_lt_iff₀ hk0]; linarith
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (R7Leaves.ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1
  exact hNR (16 / k) hκ hκ4 _ {0} (isPiecewiseConstant_prop74Data _ _) P h hcfg.gff W' ζ' hcfg.counterflow hζ

/-- The no-return property read on a continuous Loewner trace `η` of the driver (on `ℝ`). -/
theorem ae_ne_zero_of_trace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W' : ℝ≥0 → Ω → ℝ}
    {η : Ω → ℝ → ℂ} {A : Set Ω}
    (hNR : ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0)
    (htr : ∀ ω ∈ A, IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ, 0 < t → η ω t ≠ 0 := by
  filter_upwards [hNR] with ω hω hA t ht
  have hg := IsLoewnerTrace.isGeneratingTrace (w := fun t => W' t ω) (htr ω hA)
  have h1 := hω _ hg t.toNNReal (Real.toNNReal_pos.2 ht)
  simpa only [Real.coe_toNNReal _ ht.le] using h1

/-- **The seed-landing bundle from the no-seed bundle and the counterflow's no-return** (bounded change pocket). -/
theorem twoSeedSplitInputSeed_of_NR {Ω : Type*} [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hnr : ∀ᵐ ω ∂P, ω ∈ G → ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hin : TwoSeedSplitInputNR κ rL rR P R L r η G h₀ u W' ζ') :
    TwoSeedSplitInputSeed κ rL rR P R L r η G h₀ u W' ζ' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, X, hInit, hq⟩ := hin A hA hAG hPA ψ hψ hψm
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hfacts := shiftChart_cfPocket_facts hcfgA hψ n
  refine ⟨n, hn, a, ha, X₀, X, hInit, fun q => ?_⟩
  obtain ⟨hXf, hX₀, hOX, hrefl⟩ := hq q
  exact ⟨hXf, hX₀, hOX, fun _ => R5Fresh.r7SeedLand_of_noReturn hcfgA hψ (fun ω hω => (hfacts ω hω).1)
    (fun ω hω => (hfacts ω hω).2.1) (fun ω hω => (hfacts ω hω).2.2) (fun _ => rfl) (fun _ => rfl)
    (hnr.mono fun ω hω hA => hω (hAG hA)), hrefl⟩

/-- **The seed-landing bundle from the no-seed bundle and the counterflow's no-return** (pocket opening at the flow
seed). -/
theorem twoSeedSplitInputSeedInf_of_NR {Ω : Type*} [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hnr : ∀ᵐ ω ∂P, ω ∈ G → ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hin : TwoSeedSplitInputNRInf κ rL rR P R L r η G h₀ u W' ζ') :
    TwoSeedSplitInputSeedInf κ rL rR P R L r η G h₀ u W' ζ' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, X, hInit, hq⟩ := hin A hA hAG hPA ψ hψ hψm
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hfacts := shiftChart_cfPocketInf_facts hcfgA hψ n
  refine ⟨n, hn, a, ha, X₀, X, hInit, fun q => ?_⟩
  obtain ⟨hXf, hX₀, hOX, hrefl⟩ := hq q
  exact ⟨hXf, hX₀, hOX, fun _ => R5Fresh.r7SeedLandInf_of_noReturn hcfgA hψ (fun ω hω => (hfacts ω hω).1)
    (fun ω hω => (hfacts ω hω).2.1) (fun ω hω => (hfacts ω hω).2.2) (fun _ => rfl) (fun _ => rfl)
    (hnr.mono fun ω hω hA => hω (hAG hA)), hrefl⟩

/-- **The seed-landing input from the no-seed input and the counterflow's no-return**. -/
theorem r7SplitRemainingSeed_of_NR {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) (hs5 : R7SplitRemainingNR.{u} k rL rR c c') :
    R7SplitRemainingSeed.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hae := ae_noReturn_r7 hNR hk4 hc hc' hcfg
  refine ⟨twoSeedSplitInputSeed_of_NR (fun ω hω => hcfgP ω hω.1 hω.2) ?_ hs,
    twoSeedSplitInputSeedInf_of_NR (fun ω hω => hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))) ?_ hsI⟩
  · exact ae_ne_zero_of_trace hae fun ω hω => (hcfgP ω hω.1 hω.2).trace
  · exact ae_ne_zero_of_trace hae fun ω hω => (hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))).trace

/-- **`R5Enl.R7R5RemainingOn` at all margins from the no-seed split-cover inputs and the counterflow's no-return**. -/
theorem r7R5RemainingOn_of_splitNR {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) (hs5 : R7SplitRemainingNR.{u} k rL rR c c') :
    R7R5RemainingOn.{u} k rL rR c c' :=
  r7R5RemainingOn_of_splitSeed hk4 hc hc' (r7SplitRemainingSeed_of_NR hk4 hc hc' hNR hs5)

/-- **R.5 up to phase on every R.7 pocket test from the no-seed split-cover inputs and the counterflow's no-return**. -/
theorem r7PhaseWordRemaining_of_splitNR {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) (hs5 : R7SplitRemainingNR.{u} k rL rR c c') :
    PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  r7PhaseWordRemaining_of_splitSeed hk4 hc hc' (r7SplitRemainingSeed_of_NR hk4 hc hc' hNR hs5)

/-- The seed-landing input implies the no-seed input (forget the clause). -/
theorem r7SplitRemainingNR_of_seed {k rL rR c c' : ℝ} (hs5 : R7SplitRemainingSeed.{u} k rL rR c c') :
    R7SplitRemainingNR.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  refine ⟨fun A hA hAG hPA ψ hψ hψm => ?_, fun A hA hAG hPA ψ hψ hψm => ?_⟩
  · obtain ⟨n, hn, a, ha, X₀, X, hInit, hqq⟩ := hs A hA hAG hPA ψ hψ hψm
    exact ⟨n, hn, a, ha, X₀, X, hInit, fun q => ⟨(hqq q).1, (hqq q).2.1, (hqq q).2.2.1, (hqq q).2.2.2.2⟩⟩
  · obtain ⟨n, hn, a, ha, X₀, X, hInit, hqq⟩ := hsI A hA hAG hPA ψ hψ hψm
    exact ⟨n, hn, a, ha, X₀, X, hInit, fun q => ⟨(hqq q).1, (hqq q).2.1, (hqq q).2.2.1, (hqq q).2.2.2.2⟩⟩

end InteractingSLE.Sec7.R5Fresh
