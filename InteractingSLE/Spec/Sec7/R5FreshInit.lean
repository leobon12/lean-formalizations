/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5FreshNR
import InteractingSLE.Spec.Sec7.WallOrdReflWire
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRoute
import InteractingSLE.Spec.Sec5.CrossRestartLaw

/-!
# Lemma R.5 on the extremal R.7 pockets from the initial heights and Aux. lemma 7

Packet PROVE-R5-FRESHTIP (third round). The last two inputs of `R7SplitRemainingNR` besides the initial heights are
discharged without circularity:

* **the outer collars' `K_s`-landing** `R5Lift.R7OuterRefl(Inf)` by PROVE-WALL-ORDER's `WallOrd.r7OuterRefl(Inf)_shift`
  (with the exceptional sets `X q = X₀ ∪ outerExc q`, finite by `R5Wall.outerExc(Inf)_finite`);
* **the counterflow's no-return** by `CfNoReturn.Route.ae_trace_ne_zero_of_centered`: the R.7 boundary data are barrier
  data (`R7Leaves.r7_cf_bounds`: `b ≤ −λ + πχ/2` on `ℝ₋`, `b ≥ λ − πχ/2` on `ℝ₊`), so both seeds of the counterflow
  word have weight `≥ κ′/2 − 2` and **Aux. lemma 7 at `κ′ = k` alone** gives the no-return
  (`ae_noReturn_r7_of_aux7`). No `LP.TwoSeedComplete`, no R.7 reference and no Lemma 7.25 is used.

Results: `TwoSeedSplitInputInit(Inf)`, `R7SplitRemainingInit` (defs, **named input: exactly the initial heights `hInit`
with a finite exceptional set, per test**); **`r7R5RemainingOn_of_splitInit`** (input `Sec4.Aux7Statement k`),
**`r7R5RemainingOn_of_splitInit_partA`** (input Zhan's Part A, `Sec5.PartAInputsSixteenDiv`), the phase-word twins, and
`r7SplitRemainingInit_of_NR` (the older inputs imply the new one).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses; Aux. lemma 7 enters only through `Sec4.Aux7Statement` (Zhan's Part A inputs, `CrossRestartLaw`).
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

/-- **The split-cover inputs reduced to the initial heights** (bounded change pocket; named input): a walls-measurable
branch `n`, a lattice offset `a` and a finite exceptional set `X₀` with Aux. 119–121's initial heights
(`R7InitialHeights`). -/
def TwoSeedSplitInputInit (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ a : ℝ, (∃ m : ℤ, a = m * phaseStep κ) ∧
        ∃ X₀ : Ω → Set ℂ, (∀ ω, (X₀ ω).Finite) ∧
          R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
            (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u X₀

/-- **The split-cover inputs reduced to the initial heights** (pocket opening at the flow seed; named input). -/
def TwoSeedSplitInputInitInf (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ a : ℝ, (∃ m : ℤ, a = m * phaseStep κ) ∧
        ∃ X₀ : Ω → Set ℂ, (∀ ω, (X₀ ω).Finite) ∧
          R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
            (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u X₀

end Defs

/-- **The initial-heights inputs on every R.7 configuration** (named input; margins `c`, `c′`): the premises
are exactly those of `R5Enl.R7R5RemainingOn`; the conclusion is `TwoSeedSplitInputSeed(Inf)` against the counterflow's
coupling (force processes `VL`, `VR`, weights `flowLineRho(L/R) k b' J' 0 0`). -/
def R7SplitRemainingInit (k rL rR c c' : ℝ) : Prop :=
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
      TwoSeedSplitInputInit k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedSplitInputInitInf k rL rR P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The R.7 counterflow does not return to its start, from Aux. lemma 7 at `k`**: the R.7 boundary data are barrier
data (`R7Leaves.r7_cf_bounds`), so `CfNoReturn.Route.ae_trace_ne_zero_of_centered` applies at the flow parameter
`16/k ∈ (0, 4)` (counterflow parameter `16/(16/k) = k`). -/
theorem ae_noReturn_r7_of_aux7 {k rL rR c c' : ℝ} (haux7 : Sec4.Aux7Statement.{u} k) (hk4 : 4 < k) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {αR βR βL αL : Ω → ℝ≥0 → ℂ}
    {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := by positivity
  have hκ4 : 16 / k < 4 := by rw [div_lt_iff₀ hk0]; linarith
  have e : 16 / (16 / k) = k := by field_simp
  have haux7' : Sec4.Aux7Statement.{u} (16 / (16 / k)) := by rw [e]; exact haux7
  obtain ⟨hbL, hbR⟩ := R7Leaves.r7_cf_bounds (rL := rL) (rR := rR) hk4 hc hc'
  exact CfNoReturn.Route.ae_trace_ne_zero_of_centered hκ hκ4 haux7' (isPiecewiseConstant_prop74Data _ _) hbL hbR
    hcfg.gff hcfg.counterflow

/-- **The seed-landing input from the no-seed input and Aux. lemma 7** (`r7SplitRemainingSeed_of_NR` with the
no-return from `ae_noReturn_r7_of_aux7`). -/
theorem r7SplitRemainingSeed_of_NR_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) (hs5 : R7SplitRemainingNR.{u} k rL rR c c') :
    R7SplitRemainingSeed.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hae := ae_noReturn_r7_of_aux7 haux7 hk4 hc hc' hcfg
  have hI : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := fun ω hω =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  refine ⟨twoSeedSplitInputSeed_of_NR (fun ω hω => hcfgP ω hω.1 hω.2) ?_ hs,
    twoSeedSplitInputSeedInf_of_NR hI ?_ hsI⟩
  · exact ae_ne_zero_of_trace hae fun ω hω => (hcfgP ω hω.1 hω.2).trace
  · exact ae_ne_zero_of_trace hae fun ω hω => (hI ω hω).trace

/-- **The no-seed bundle from the initial heights** (bounded change pocket): `X q = X₀ ∪ outerExc q`, and the outer
collars' `K_s`-landing by `WallOrd.r7OuterRefl_shift`. -/
theorem twoSeedSplitInputNR_of_init {Ω : Type*} [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedSplitInputInit κ rL rR P R L r η G h₀ u) :
    TwoSeedSplitInputNR κ rL rR P R L r η G h₀ u W' ζ' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, hX₀f, hInit⟩ := hin A hA hAG hPA ψ hψ hψm
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  refine ⟨n, hn, a, ha, X₀, fun q ω => X₀ ω ∪ R5Wall.outerExc R L r η ψ q ω, hInit, fun q =>
    ⟨fun ω => (hX₀f ω).union (R5Wall.outerExc_finite R L r η ψ q ω), fun ω => subset_union_left,
      fun ω => subset_union_right, WallOrd.r7OuterRefl_shift n hcfgA hψ fun ω _ => subset_union_right⟩⟩

/-- **The no-seed bundle from the initial heights** (pocket opening at the flow seed). -/
theorem twoSeedSplitInputNRInf_of_init {Ω : Type*} [MeasurableSpace Ω] {κ rL rR : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedSplitInputInitInf κ rL rR P R L r η G h₀ u) :
    TwoSeedSplitInputNRInf κ rL rR P R L r η G h₀ u W' ζ' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, ha, X₀, hX₀f, hInit⟩ := hin A hA hAG hPA ψ hψ hψm
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  refine ⟨n, hn, a, ha, X₀, fun q ω => X₀ ω ∪ R5Wall.outerExcInf R L r η ψ q ω, hInit, fun q =>
    ⟨fun ω => (hX₀f ω).union (R5Wall.outerExcInf_finite R L r η ψ q ω), fun ω => subset_union_left,
      fun ω => subset_union_right, WallOrd.r7OuterReflInf_shift n hcfgA hψ fun ω _ => subset_union_right⟩⟩

/-- **The no-seed input from the initial-heights input** (bounded and seed-opening pockets). -/
theorem r7SplitRemainingNR_of_init {k rL rR c c' : ℝ} (hs5 : R7SplitRemainingInit.{u} k rL rR c c') :
    R7SplitRemainingNR.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedSplitInputNR_of_init (fun ω hω => hcfgP ω hω.1 hω.2) hs,
    twoSeedSplitInputNRInf_of_init (fun ω hω => hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))) hsI⟩

/-- **Lemma R.5 on the extremal R.7 pockets from the initial heights and Aux. lemma 7 at `k`**: `R5Enl.R7R5RemainingOn`
at all margins. -/
theorem r7R5RemainingOn_of_splitInit {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) (hs5 : R7SplitRemainingInit.{u} k rL rR c c') :
    R7R5RemainingOn.{u} k rL rR c c' :=
  r7R5RemainingOn_of_splitSeed hk4 hc hc' (r7SplitRemainingSeed_of_NR_aux7 hk4 hc hc' haux7
    (r7SplitRemainingNR_of_init hs5))

/-- **R.5 up to phase on every R.7 pocket test from the initial heights and Aux. lemma 7 at `k`**. -/
theorem r7PhaseWordRemaining_of_splitInit {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) (hs5 : R7SplitRemainingInit.{u} k rL rR c c') :
    PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  r7PhaseWordRemaining_of_splitSeed hk4 hc hc' (r7SplitRemainingSeed_of_NR_aux7 hk4 hc hc' haux7
    (r7SplitRemainingNR_of_init hs5))

/-- Aux. lemma 7 at `k > 4` from Zhan's Part A inputs (`Sec5.aux7Statement_sixteen_div_of_partA` at `16/k`). -/
theorem aux7Statement_of_partA {k : ℝ} (hk4 : 4 < k) (hA : Sec5.PartAInputsSixteenDiv) :
    Sec4.Aux7Statement.{u} k := by
  have hk0 : 0 < k := by linarith
  have hκ : (0 : ℝ) < 16 / k := by positivity
  have hκ4 : 16 / k < 4 := by rw [div_lt_iff₀ hk0]; linarith
  have h : Sec4.Aux7Statement.{u} (16 / (16 / k)) := Sec5.aux7Statement_sixteen_div_of_partA hA hκ hκ4
  have e : 16 / (16 / k) = k := by field_simp
  rwa [e] at h

/-- **Lemma R.5 on the extremal R.7 pockets from the initial heights and Zhan's Part A inputs**. -/
theorem r7R5RemainingOn_of_splitInit_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) (hs5 : R7SplitRemainingInit.{u} k rL rR c c') :
    R7R5RemainingOn.{u} k rL rR c c' :=
  r7R5RemainingOn_of_splitInit hk4 hc hc' (aux7Statement_of_partA hk4 hA) hs5

/-- **R.5 up to phase on every R.7 pocket test from the initial heights and Zhan's Part A inputs**. -/
theorem r7PhaseWordRemaining_of_splitInit_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) (hs5 : R7SplitRemainingInit.{u} k rL rR c c') :
    PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  r7PhaseWordRemaining_of_splitInit hk4 hc hc' (aux7Statement_of_partA hk4 hA) hs5

/-- The no-seed input implies the initial-heights input (the exceptional set `X₀ ⊆ X 0` is finite). -/
theorem r7SplitRemainingInit_of_NR {k rL rR c c' : ℝ} (hs5 : R7SplitRemainingNR.{u} k rL rR c c') :
    R7SplitRemainingInit.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hs5 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  refine ⟨fun A hA hAG hPA ψ hψ hψm => ?_, fun A hA hAG hPA ψ hψ hψm => ?_⟩
  · obtain ⟨n, hn, a, ha, X₀, X, hInit, hqq⟩ := hs A hA hAG hPA ψ hψ hψm
    exact ⟨n, hn, a, ha, X₀, fun ω => ((hqq 0).1 ω).subset ((hqq 0).2.1 ω), hInit⟩
  · obtain ⟨n, hn, a, ha, X₀, X, hInit, hqq⟩ := hsI A hA hAG hPA ψ hψ hψm
    exact ⟨n, hn, a, ha, X₀, fun ω => ((hqq 0).1 ω).subset ((hqq 0).2.1 ω), hInit⟩

end InteractingSLE.Sec7.R5Fresh
