/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6NestCover
import InteractingSLE.Spec.Sec7.SideVisR7Wire

/-!
# R.6's fixed-time transfer from the nested-pocket transfer

PROVE-R6-NESTED. `SideVis.R7SharedTransferRemaining` (R.6 at each rational original time on every certified visit)
is reduced to the same transfer **on one nested candidate at a time**: `TwoSeedNestTransferInput(Inf)` asks the zero
phase only on `nestEvent … s t`, i.e. when the tip at the rational time `t` lies in the inner pocket at the rational
parameter `s` and that pocket is contained in the outer one. The selection of the nested pocket containing a
certified visit is proved (`R6Nest.ae_exists_nestEvent(Inf)`, supplement pp. 476–477), and the countably many
candidate statements are intersected before the candidate is selected pathwise (the source's quantifier order: "At
each rational original counterflow time the old-germ comparisons hold simultaneously for every fixed pair of
pockets. Intersect these countably many events before selecting `C`, a nested pocket, or a tip visit.").

`R6NestTransferRemaining` is a named, **unproved** statement with all of the original R.7 premises; it is the
transfer from the bounded-sector inner pocket `U` (seed weights `(min(r_L, d), min(r_R, d))`, zero phase by Aux. 122)
to the outer pocket `C` through the shared side (Lemma R.6). R48: nothing here uses Theorem 1.2/1.3,
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

namespace InteractingSLE.Sec7.R6Nest

open PocketTraversal Lemma71C PocketStop PocketWordAssembly PocketSeedOpen
  PocketCoupling PocketJordan Hsd PhaseClause PocketStopField PocketMarks SideVis

section Defs

variable {Ω : Type*}

/-- **Named, unproved R.6 transfer for one nested candidate** (bounded outer pocket): for every coherent phase word
with a continuous phase, at each rational original time `t` and rational inner parameter `s`, almost surely on the
test, a certified visit whose tip lies in the inner pocket of `(R', L')` at `rt s` (contained in the outer pocket)
has zero phase at its relative capacity. -/
def TwoSeedNestTransferInput (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL R' L' : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAll R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ t s : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ visitEvent R L r η βR βL t →
        ω ∈ nestEvent R L r η R' L' s t → δ (visitClock R L r η ψ t ω) ω = 0

/-- **Named, unproved R.6 transfer for one nested candidate** for a pocket opening at the flow seed. -/
def TwoSeedNestTransferInputInf (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL R' L' : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAllInf R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ t s : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ visitEventInf R L r η βR βL t →
        ω ∈ nestEvent R L r η R' L' s t → δ (visitClockInf R L r η ψ t ω) ω = 0

end Defs

section Reduce

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
  {P : Measure Ω} {k rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
  {βR βL R' L' : Ω → ℝ≥0 → ℂ}

/-- **The fixed-time transfer from the nested-candidate transfer** (bounded outer pocket): the countably many
candidate statements are intersected first; then the nested candidate containing the certified visit is selected
pathwise. -/
theorem twoSeedSharedTransferInput_of_nest
    (hnest : TwoSeedNestTransferInput k rL rR 𝓦 P R L r η G h₀ u βR βL R' L')
    (hcover : ∀ t : ℚ, ∀ᵐ ω ∂P, ω ∈ G → ω ∈ visitEvent R L r η βR βL t →
      ∃ s : ℚ, ω ∈ nestEvent R L r η R' L' s t) :
    TwoSeedSharedTransferInput k rL rR 𝓦 P R L r η G h₀ u βR βL := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont t
  have hall : ∀ s : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ visitEvent R L r η βR βL t →
      ω ∈ nestEvent R L r η R' L' s t → δ (visitClock R L r η ψ t ω) ω = 0 :=
    fun s => hnest A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont t s
  filter_upwards [ae_all_iff.2 hall, hcover t] with ω hω hcov hωA hvis
  obtain ⟨s, hs⟩ := hcov (hAG hωA) hvis
  exact hω s hωA hvis hs

/-- **The fixed-time transfer from the nested-candidate transfer** (pocket opening at the flow seed). -/
theorem twoSeedSharedTransferInputInf_of_nest
    (hnest : TwoSeedNestTransferInputInf k rL rR 𝓦 P R L r η G h₀ u βR βL R' L')
    (hcover : ∀ t : ℚ, ∀ᵐ ω ∂P, ω ∈ G → ω ∈ visitEventInf R L r η βR βL t →
      ∃ s : ℚ, ω ∈ nestEvent R L r η R' L' s t) :
    TwoSeedSharedTransferInputInf k rL rR 𝓦 P R L r η G h₀ u βR βL := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont t
  have hall : ∀ s : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ visitEventInf R L r η βR βL t →
      ω ∈ nestEvent R L r η R' L' s t → δ (visitClockInf R L r η ψ t ω) ω = 0 :=
    fun s => hnest A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont t s
  filter_upwards [ae_all_iff.2 hall, hcover t] with ω hω hcov hωA hvis
  obtain ⟨s, hs⟩ := hcov (hAG hωA) hvis
  exact hω s hωA hvis hs

end Reduce

section R7

open WholeField R7Outer R7Leaves RefWire HOuter PhaseSide
open WangWu Lemma71I PocketCoord PocketStopWallsFin PocketStopWalls StripPocketConfig PocketWordPerQ R7Aux131
  R7Pocket

/-- **Named, unproved R.6 transfer for one nested candidate on every outer configuration** (supplement
pp. 475–477): the original R.7 premises of `SideVis.R7SharedTransferRemaining`, concluding the candidate transfer
`TwoSeedNestTransferInput(Inf)` for the inner pair `(innerRight k rL R βR, innerLeft k rR L βL)`. -/
def R6NestTransferRemaining (k rL rR : ℝ) : Prop :=
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
      TwoSeedNestTransferInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL) ∧
        TwoSeedNestTransferInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' βR βL
          (innerRight k rL R βR) (innerLeft k rR L βL)

/-- **R.6's fixed-time transfer on every outer configuration from the nested-candidate transfer**: the nested
pocket of every certified visit is selected by `ae_exists_nestEvent(Inf)` (input `Prop55HalfPlaneStatement`, which
orders the inner pairs of the mixed shapes; R48-safe). -/
theorem r7SharedTransferRemaining_of_nest (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR) (hnest : R6NestTransferRemaining.{u} k rL rR) :
    SideVis.R7SharedTransferRemaining.{u} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hn, hnI⟩ := hnest P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := lt_trans (by norm_num) hk4
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  refine ⟨twoSeedSharedTransferInput_of_nest hn fun t => ?_, twoSeedSharedTransferInputInf_of_nest hnI fun t => ?_⟩
  · filter_upwards [ae_exists_nestEvent h55 hk4 hrL hrR hc le_rfl hcfg hV (StripSys.rt q) t] with ω hω hωG hvis
    exact hω (hζG ω hωG.1) (hconf ω hωG.1) hvis
  · filter_upwards [ae_exists_nestEventInf h55 hk4 hrL hrR hc le_rfl hcfg hV (StripSys.rt q) t] with
      ω hω hωG hvis
    exact hω (hζG ω hωG.1) (hconf ω hωG.1) hvis

/-- **The outer phase input from R.5 with continuity and the nested-candidate transfer** (drop-in for
`SideVis.r7OuterPhaseSideRemaining_of_cont_transfer`): the nested candidate transfer is needed only outside
Aux. 122's bounded sector. -/
theorem r7OuterPhaseSideRemaining_of_cont_nest (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR : ℝ}
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (hnest : ¬ (rL < k - 6 ∧ rR < k - 6) → R6NestTransferRemaining.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  SideVis.r7OuterPhaseSideRemaining_of_cont_transfer hk4 hrL hrR hcont
    fun hbad => r7SharedTransferRemaining_of_nest h55 hk4 hrL hrR (hnest hbad)

end R7

end InteractingSLE.Sec7.R6Nest
