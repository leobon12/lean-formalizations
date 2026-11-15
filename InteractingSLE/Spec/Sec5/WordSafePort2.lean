/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafePort1
import InteractingSLE.Spec.Sec7.PocketWordInWalls
import InteractingSLE.Spec.Sec7.StripPocketVersions
import InteractingSLE.Spec.Sec7.StripWallVersion
import InteractingSLE.Spec.Sec7.StripPocketConfigWalls
import InteractingSLE.Spec.Sec7.StripWallLocal
import InteractingSLE.Spec.Sec7.StripPocketPathLate
import InteractingSLE.Spec.Sec7.StripWallMeanFull
import InteractingSLE.Spec.Sec7.Aux37WallsStrip
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteStrip
import InteractingSLE.Spec.Sec7.PocketWordInStrip
import InteractingSLE.Spec.Sec7.PocketWordInVisitStrip
import InteractingSLE.Spec.Sec5.RestartGenReflect
import InteractingSLE.Spec.Sec5.RestartGenPocket

/-!
# Ports to the two-angle strip system, part 2

Packet PROVE-WORDSAFE. Copies of the pocket-word lemmas below with `StripSys.IsStripSystem` weakened to
`WordSafe.IsTwoAngleStripSystem` (same statements otherwise, same proofs; they read the strip system's
staged histories only at `constSpec θ` and `twoAngleSpec θ₀ t₀ θ`). Calls to ported lemmas are redirected to
the ports (`WordSafe.…`); calls to PROVE-STRIPSYS-SAFE's constant-angle ports go through
`IsTwoAngleStripSystem.toConst`. Each section names its source file. No new mathematics.

Ported: `ae_avoidance`, `ae_regular_leftExtremal`, `stagedPiecesRegular_leftExtremal`, `regStrip_leftExtremal`,
`ae_simple_trace_alpha`, `ae_simple_trace_beta`, `isWallVersion_alpha`, `isWallVersion_beta`,
`ae_isSimpleProper_alpha`, `ae_isSimpleProper_beta`, `isEntranceHistoryLocal_beta`, `isEntranceHistoryLocal_alpha`,
`ae_late_strip`, `lemma62_walls`, `lemma62_walls_rat`, `exists_wallMeans_strip`, `hwit_strip`, `hwitI_strip`,
`hattach_strip`, `hattachI_strip`, `wall_inputs`, `ae_noReturn_counterflow`,
`pocketWordEvolution_of_stripSystem_sideLimit`, `pocketWordEvolution_of_stripSystem_firstHit`,
`hfirstR_of_restartGen'`, `pocketWordEvolution_of_stripSystem_restartGen`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.WordSafe

section
-- from InteractingSLE/Spec/Sec7/PocketWordInWalls.lean
open InteractingSLE.Sec7.PocketWordIn
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real
open StripWall StripSideHeightProb StripPocketPath WangWu
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
Rational-time avoidance follows from Proposition 4.11 for the unchanged extremal flow.
No full-generality determination or trace theorem is used. -/
theorem ae_avoidance (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {β : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) →
      negInv (η ω q) ∉ leftSideOf (range (β ω)) := by
  obtain ⟨hf, F, VL, VR, B, ht, hC⟩ := isFlowLineDriver_leftExtremal
    hS.kappa_pos hS.boundaryData hS.gff hS.isStagedHistory_leftExtremal
  have hβ : IsFlowLine κ b J 0 (π / 2) P h β
      (fun ω => (E StripSys.leftExtremalSpec 0 ω).2) := by
    refine ⟨hf, F, fun t ω => (E StripSys.leftExtremalSpec 0 ω).1 t,
      VL, VR, B, ht, hC, ?_⟩
    filter_upwards [hβtr, WordSafe.ae_simple_trace_leftExtremal_strip hS hleft hright]
      with ω htr hreg
    simpa only [hreg.1, Complex.ofReal_zero, sub_zero] using htr
  have hav := R7Outer.ae_negInv_trace_notMem_leftSideOf h411 hS.kappa_pos hS.kappa_lt_four
    hS.boundaryData (heights_pi_div_two hS.kappa_pos hS.kappa_lt_four hleft hright)
    hS.gff hS.counterflow hβ
  filter_upwards [hav, hS.lifetime, hηtr] with ω ha hζ hη q hq
  have ha' := ha hζ _ hη (q : ℝ).toNNReal
  rwa [Real.coe_toNNReal _ hq] at ha'

end

section
-- from InteractingSLE/Spec/Sec7/StripPocketVersions.lean
open InteractingSLE.Sec7.StripPocketVersions
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open Exist.Staged (IsRegularDriver)
open StripSideHeightProb (catPath)
open Theorem14.StagedReg (regHist regHist_snd isRegularDriver_regHist regularize_eq_of_lt)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The driver of `β = η_{π/2}` is regular almost surely**: infinite lifetime, `0` at `0`, continuous, with a
transient generating trace on `[0, ∞)` (the stage-`0` flow line of `h`; Proposition 4.12 for its (4.4) word). -/
theorem ae_regular_leftExtremal (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧ (Es StripSys.leftExtremalSpec 0 ω).1 0 = 0 ∧
      Continuous (Es StripSys.leftExtremalSpec 0 ω).1 ∧ ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ η ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := StripPocketPath.isFlowLineDriver_leftExtremal hS.kappa_pos hS.boundaryData
    hS.gff hS.isStagedHistory_leftExtremal
  filter_upwards [WordSafe.ae_simple_trace_leftExtremal_strip hS hcumL hcumR, hC.1.2.2.2.2] with ω h1 hp
  obtain ⟨hζ, η, hη, -, -, htr⟩ := h1
  have hc : ContinuousOn (Es StripSys.leftExtremalSpec 0 ω).1
      {t : ℝ≥0 | (t : ℝ≥0∞) < (Es StripSys.leftExtremalSpec 0 ω).2} := hp.2.2.2.1
  rw [hζ] at hc
  exact ⟨hζ, hp.1, continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top), η, hη, htr⟩

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`β = η_{π/2}` is `StagedPiecesRegular`** (R51) for the strip system: its only piece is the stage-`0` flow line of
`h` itself, which is almost surely regular (`WordSafe.ae_regular_leftExtremal`). -/
theorem stagedPiecesRegular_leftExtremal (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    StagedPiecesRegular κ b jumps P StripSys.leftExtremalSpec (Es StripSys.leftExtremalSpec) := by
  filter_upwards [WordSafe.ae_regular_leftExtremal hS hcumL hcumR] with ω hω k θ t c hk _
  obtain ⟨hζ, h0, hc, η, hη, htr⟩ := hω
  obtain ⟨rfl, rfl⟩ := eq_of_leftExtremalSpec_getElem? hk
  rw [hζ, min_self]
  exact ⟨h0, hc.continuousOn, η, hη, fun _ => htr⟩

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The regularized strip family is regular at every sample on `β = η_{π/2}`**, and its driver is almost surely the
original one. -/
theorem regStrip_leftExtremal (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    (∀ ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es StripSys.leftExtremalSpec 0 ω)) ∧
      ∀ᵐ ω ∂P, (StripWall.regStrip κ b jumps P Es StripSys.leftExtremalSpec 0 ω).1 =
        (Es StripSys.leftExtremalSpec 0 ω).1 := by
  have e := StripWall.regStrip_of (WordSafe.stagedPiecesRegular_leftExtremal hS hcumL hcumR)
  refine ⟨fun ω => by rw [e]; exact isRegularDriver_regHist 0 ω, ?_⟩
  rw [e]
  filter_upwards [WordSafe.ae_regular_leftExtremal hS hcumL hcumR] with ω hω
  obtain ⟨hζ, h0, hc, -⟩ := hω
  funext s
  exact regularize_eq_of_lt _ h0 hc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)

end

section
-- from InteractingSLE/Spec/Sec7/StripWallVersion.lean
open InteractingSLE.Sec7.StripWall
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMapInv)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open LoewnerConcat (joinedTrace)
open LQGMetric (DistOn)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
variable {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The wall `α = η^{1,∞}_{−π/2,θ₁}` has a simple transient trace** almost surely (Aux. lemma 130's height choice:
every original-boundary cumulative value nonnegative at every angle in `[−π/2, π/2]`). -/
theorem ae_simple_trace_alpha (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω)) :
    ∀ᵐ ω ∂P, ((Es (StripSys.alphaSpec θ₁) 0 ω).2 = ⊤ ∧ (Es (StripSys.alphaSpec θ₁) 1 ω).2 = ⊤) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  exact ae_simple_trace_catPath hκ hκ4 hS.boundaryData hS.gff (hS.isStagedHistory_alpha hθ₁) hregα
    (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (fun y hy hyJ => by have := hcumR _ hθ₁ y hy hyJ; linarith)
    (by linarith [hθ₁.2, Real.pi_pos]) (by linarith [hθ₁.1, Real.pi_pos])

theorem ae_simple_trace_beta (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω)) :
    ∀ᵐ ω ∂P, ((Es (StripSys.betaSpec r θ₂) 0 ω).2 = ⊤ ∧ (Es (StripSys.betaSpec r θ₂) 1 ω).2 = ⊤) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
        (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hp := StripSys.pi_div_two_mem_Icc
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  exact ae_simple_trace_catPath hκ hκ4 hS.boundaryData hS.gff (hS.isStagedHistory_beta hθ₂ r) hregβ
    (hL44 _ hp) (hcumR _ hp) (hL44 _ hθ₂) (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith)
    (by linarith [hθ₂.2, Real.pi_pos]) (by linarith [hθ₂.1, Real.pi_pos])

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of the wall `α` is a wall version** (`isWallVersion_of_isGeneratingTrace`). -/
theorem isWallVersion_alpha (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    IsWallVersion P (Es (StripSys.alphaSpec θ₁)) 1 α :=
  isWallVersion_of_isGeneratingTrace hregα (WordSafe.ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα) hαc hα0 hαm hαtr

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of the wall `β^{(r)}` is a wall version** (`isWallVersion_of_isGeneratingTrace`). -/
theorem isWallVersion_beta (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
      (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (β ω)) :
    IsWallVersion P (Es (StripSys.betaSpec r θ₂)) r β :=
  isWallVersion_of_isGeneratingTrace hregβ (WordSafe.ae_simple_trace_beta hS hcumL hcumR hθ₂ r hregβ) hβc hβ0 hβm hβtr

end

section
-- from InteractingSLE/Spec/Sec7/StripPocketConfigWalls.lean
open InteractingSLE.Sec7.StripWall
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of the wall `α = η^{1,∞}_{−π/2,θ₁}` is almost surely a simple proper curve** (Aux. lemma 130's
height choice, p. 410). -/
theorem ae_isSimpleProper_alpha (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (α ω) :=
  ae_isSimpleProper_of_catPath hregα (WordSafe.ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα) hαc hα0 hαtr

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of the wall `β^{(r)} = η^{r,∞}_{π/2,θ₂}` is almost surely a simple proper curve**, for every
change time `r` (Aux. lemma 130's height choice, p. 410). -/
theorem ae_isSimpleProper_beta (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
      (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (β ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (β ω) :=
  ae_isSimpleProper_of_catPath hregβ (WordSafe.ae_simple_trace_beta hS hcumL hcumR hθ₂ r hregβ) hβc hβ0 hβtr

end

section
-- from InteractingSLE/Spec/Sec7/StripWallLocal.lean
open InteractingSLE.Sec7.StripWall
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of the wall `β^{(q)}` is entrance-history local** (Lemma 6.2's `hloc`; spec pp. 410–411), for every
rational change time `q > 0` (the source's "one deterministic rational `r`", p. 411): a family `β`, continuous at every
sample, starting at `0`, measurable at fixed times and almost surely a generating trace of the concatenated driver of
the strip system's staged history `η^{q,∞}_{π/2,θ₂}`, is entrance-history local for the centred field `h − u₀`. -/
theorem isEntranceHistoryLocal_beta (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec (q : ℝ≥0) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (Es (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω)) :
    Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hp := StripSys.pi_div_two_mem_Icc
  have hE := hS.isStagedHistory_beta hθ₂ (q : ℝ≥0)
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - π * chiC κ ≤ b y + θ₂ * chiC κ := fun y hy hyJ => by
    have := hcumR _ hθ₂ y hy hyJ; linarith
  obtain ⟨γ, η₁, hγ, hη₁c, hη₁0, hη₁m, hη₁⟩ := exists_wallVersions_twoAngle (θ₀ := π / 2) (θ := θ₂) hκ hκ4
    hS.boundaryData hS.gff hE hregβ (hL44 _ hp) (hcumR _ hp) (hL44 _ hθ₂) hRθ (by linarith [hθ₂.2, Real.pi_pos])
    (by linarith [hθ₂.1, Real.pi_pos])
  have hs := WordSafe.ae_simple_trace_beta hS hcumL hcumR hθ₂ (q : ℝ≥0) hregβ
  have heq := ae_eq_of_isGeneratingTrace_catPath hregβ (hs.mono fun ω hω => hω.1) hβtr
    (hγ.ae_trace.mono fun ω hω => hω.1)
  refine Restart.StagedEntrance.Strip.isEntranceHistoryLocal_strip_refl (θ₀ := π / 2) (θ := θ₂) h44 hκ hκ4
    hS.boundaryData hS.gff hq hE hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂) hRθ hθ₂.2
    (by linarith [hθ₂.1, Real.pi_pos]) hu₀ hβc hβ0 hβm hβtr hη₁c hη₁0 hη₁m (hη₁.mono fun ω hω => hω.1) ?_
  filter_upwards [hη₁, heq] with ω hω he s hs
  rw [he]
  exact ⟨hω.2.2.1 s hs, (hω.2.2.2.2 s hs).2⟩

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of the wall `α = η^{1,∞}_{−π/2,θ₁}` is entrance-history local** (Lemma 6.2's `hloc`;
PROVE-STAGEDLOC2's increasing case `isEntranceHistoryLocal_strip_one`, with the continuation's chart trace and the
join formula from `exists_wallVersions_twoAngle`). -/
theorem isEntranceHistoryLocal_alpha (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hE := hS.isStagedHistory_alpha hθ₁
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - π * chiC κ ≤ b y + θ₁ * chiC κ := fun y hy hyJ => by
    have := hcumR _ hθ₁ y hy hyJ; linarith
  obtain ⟨γ, η₁, hγ, hη₁c, hη₁0, hη₁m, hη₁⟩ := exists_wallVersions_twoAngle (θ₀ := -(π / 2)) (θ := θ₁) (t₀ := 1) hκ
    hκ4 hS.boundaryData hS.gff hE hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) hRθ
    (by linarith [hθ₁.2, Real.pi_pos]) (by linarith [hθ₁.1, Real.pi_pos])
  have hs := WordSafe.ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα
  have heq := ae_eq_of_isGeneratingTrace_catPath hregα (hs.mono fun ω hω => hω.1) hαtr
    (hγ.ae_trace.mono fun ω hω => hω.1)
  refine Restart.StagedEntrance.Strip.isEntranceHistoryLocal_strip_one (θ₀ := -(π / 2)) (θ := θ₁) h44 hκ hκ4
    hS.boundaryData hS.gff hE hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (hcumR _ hθ₁) hθ₁.1
    (by linarith [hθ₁.2, Real.pi_pos]) hu₀ hαc hα0 hαm hαtr hη₁c hη₁0 hη₁m (hη₁.mono fun ω hω => hω.1) ?_
  filter_upwards [hη₁, heq] with ω hω he s hs
  rw [he]
  exact ⟨hω.2.2.1 s hs, (hω.2.2.2.2 s hs).2⟩

end

section
-- from InteractingSLE/Spec/Sec7/StripPocketPathLate.lean
open InteractingSLE.Sec7.StripPocketPath
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open StripSideHeightProb StripGeom LocalSets
open Exist.Staged (IsRegularDriver)
open Restart.StagedEntrance (frozenPath continuous_frozenPath)
open PocketJordan PocketMeas
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**(RS13.3) for the strip system** (p. 411): almost surely `β = η_{π/2}` has points off the complete range of
`α = η^{1,∞}_{−π/2,θ₁}` at arbitrarily late times, for `θ₁ ∈ (−π/2, π/2)`, given the walls' reverse first-visit order
with every point after the seed visited (Lemma 5.7). -/
theorem ae_late_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    {η : Ω → ℝ → ℂ} (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hrev : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω)) :
    ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (α ω) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  set X := WholeField.centredField h u₀ with hXdef
  have hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hm := StripSys.neg_pi_div_two_mem_Icc
  -- the first path `α`
  have hDα : StripWall.IsDetTwoPiece P h (Es (StripSys.alphaSpec θ₁)) :=
    StripWall.isDetTwoPiece_of_heights h44 hκ hκ4 hb hh (hS.isStagedHistory_alpha hθ₁c) hregα (hL44 _ hm)
      (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c) hθ₁c.1 (by linarith [hθ₁c.2])
  have hαdet := hDα.hdet hregα u₀ hαtr
  have hαloc := WordSafe.isEntranceHistoryLocal_alpha h44 hS hcumL hcumR hθ₁c hregα hu₀ hαc hα0 hαm hαtr
  have hαs := WordSafe.ae_simple_trace_alpha hS hcumL hcumR hθ₁c hregα
  have hαsp := WordSafe.ae_isSimpleProper_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαtr
  have hαim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im := by
    filter_upwards [hαsp] with ω hω t
    rcases eq_zero_or_pos t with rfl | ht
    · rw [hα0]; simp
    · exact (hω.2.2.2.1 t ht).le
  obtain ⟨gα, hgα⟩ := StripWall.exists_isLocalSetMean_prefix hX hαc hα0 hαm hαdet hαloc
  have hside₁ := StripWall.ae_sideHeights_second hκ hb hh (hS.isStagedHistory_alpha hθ₁c) hregα
    (hαs.mono fun ω hω => hω.1) hu₀ hαc hα0 hαm hαdet hαloc
    (by filter_upwards [hαtr, hαsp] with ω h1 h2 using ⟨h1, h2.2.1, h2.2.2.2.1⟩) hgα
  -- the second path `β = η_{π/2}`
  have hβs := WordSafe.ae_simple_trace_leftExtremal_strip hS hcumL hcumR
  have hβsp := WordSafe.ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr
  have hβim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (β ω t).im := by
    filter_upwards [hβsp] with ω hω t
    rcases eq_zero_or_pos t with rfl | ht
    · rw [hβ0]; simp
    · exact (hω.2.2.2.1 t ht).le
  have hβdet := WordSafe.hdet_leftExtremal h44 hS hcumL hcumR hregE u₀ hβtr
  have hβtr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (Es StripSys.leftExtremalSpec 0 ω).1 t)
      ((Es StripSys.leftExtremalSpec 0 ω).2) (fun t => β ω t - ((0 : ℝ) : ℂ)) := by
    filter_upwards [hβs, hβtr] with ω h1 h2
    rw [h1.1]
    simpa only [Complex.ofReal_zero, sub_zero] using h2
  have hfl : IsFlowLine κ b jumps 0 (π / 2) P h β (fun ω => (Es StripSys.leftExtremalSpec 0 ω).2) := by
    refine StripWall.isFlowLine_of_isFlowLineDriver
      (isFlowLineDriver_leftExtremal hκ hb hh hS.isStagedHistory_leftExtremal) ?_
    filter_upwards [hβs, hβtr] with ω h1 h2
    rw [h1.1]
    exact h2
  have hζβ : ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ := hβs.mono fun ω hω => hω.1
  have hβloc : ∀ q : ℝ≥0, Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (β ω) q) X P := fun q =>
    Restart.StagedEntrance.isEntranceHistoryLocal_frozenPath_of_isFlowLine hκ hκ4 hb hh hfl hζβ hu₀ hβc hβm q
      (Eventually.of_forall fun ω t _ => rfl)
  have hfz0 : ∀ q : ℝ≥0, ∀ ω, frozenPath (β ω) q 0 = 0 := fun q ω => by
    simp only [frozenPath, min_eq_left (zero_le : (0 : ℝ≥0) ≤ q), hβ0]
  have hβmean : ∀ q : ℝ≥0, ∃ g, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) X P g := fun q => by
    have hloc := StripMark.isLocalSet_range hX (fun ω => continuous_frozenPath (hβc ω)) (hfz0 q)
      (fun t => hβm _) (Restart.StagedEntrance.frozenPath_ae_eq_comp hβdet q) (hβloc q) q
    simp only [image_frozenPath_Icc] at hloc
    exact IsLocalSet.exists_isLocalSetMean hX (StripMark.measurable_range hβc hβm q) hloc
  choose gβ hgβ using hβmean
  have hside₂ : ∀ q ∈ stops, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (β ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q ∩ H) → gβ q ω φ = ∫ z, v z * φ z) →
      ∀ s, 0 < s → s < q →
        HasSideHeights κ (π / 2) (β ω) 0 (Es StripSys.leftExtremalSpec 0 ω).1 q (β ω s) v u₀ := by
    intro q _
    have hg' : IsLocalSetMean (fun ω => frozenPath (β ω) q '' Icc 0 q ∩ H) X P (gβ q) := by
      simpa only [image_frozenPath_Icc] using hgβ q
    have key := Aux119Heights.ae_hasSideHeights_of_isFlowLine hκ hb hh hfl hβtr' hu₀
      (ηc := fun ω => frozenPath (β ω) q) (fun ω => continuous_frozenPath (hβc ω)) (hfz0 q) (fun t => hβm _)
      (Restart.StagedEntrance.frozenPath_ae_eq_comp hβdet q) (hβloc q) q
      (Eventually.of_forall fun ω t ht _ => by simp only [frozenPath, min_eq_left ht]) hg'
    simp only [image_frozenPath_Icc] at key
    filter_upwards [key, hζβ, hβsp] with ω hk hζ hsp v hv hrep s hs1 hs2
    exact hk (by rw [hζ]; exact ENNReal.coe_lt_top) v hv hrep s hs2 (hsp.2.2.2.1 s hs1)
  -- the first visits and the paths
  have hpath : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω) ∧
      Continuous (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1) ∧
      catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1 0 = 0 ∧
      IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω) ∧
      Continuous (Es StripSys.leftExtremalSpec 0 ω).1 ∧ (Es StripSys.leftExtremalSpec 0 ω).1 0 = 0 ∧
      Injective (α ω) ∧ Injective (β ω) ∧ (∀ t, 0 < t → α ω t ∈ H) ∧
      Tendsto (fun t => ‖α ω t‖) atTop atTop ∧ Tendsto (fun t => ‖β ω t‖) atTop atTop ∧
      StrictAntiOn (fun t => cfT (η ω) (α ω t)) (Ioi 0) ∧ StrictAntiOn (fun t => cfT (η ω) (β ω t)) (Ioi 0) := by
    filter_upwards [hαtr, hαs, hαsp, hβtr, hβs, hβsp, hrev] with ω hα1 hα2 hα3 hβ1 hβ2 hβ3 hr
    obtain ⟨hcc, hc0⟩ := StripWall.continuous_catPath_of_isRegularDriver (hregα 0 ω) (hregα 1 ω) hα2.1.1
      hα2.1.2 1
    exact ⟨hα1, hcc, hc0, hβ1, StripWall.continuous_of_isRegularDriver (hregE ω) hβ2.1, (hregE ω).2.1, hα3.2.1,
      hβ3.2.1, hα3.2.2.2.1, hα3.2.2.2.2, hβ3.2.2.2.2, strictAntiOn_cfT hα3.2.1 (hηc ω) hr.1 hr.2.1,
      strictAntiOn_cfT hβ3.2.1 (hηc ω) hr.2.2.1 hr.2.2.2⟩
  have hlate := ae_late_of_sideHeights_frozen hX hαc hα0 hαm hαdet hαloc hαim hβc hβ0 hβm hβdet hβloc hβim
    (W₁ := fun ω => catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1)
    (W₂ := fun ω => (Es StripSys.leftExtremalSpec 0 ω).1) (fun ω => cfT (η ω)) hpath hκ hκ4 hθ₁c.1 hθ₁.2
    (t₀ := 1) stops_countable stops_countable (fun a => (exists_stop_lt a).imp fun q hq => ⟨hq.1, hq.2.le⟩)
    exists_stop_lt (gα := gα) (gβ := gβ) (fun q _ => hgα q) (fun q _ => hgβ q)
    (fun q hq => by
      obtain ⟨n, rfl⟩ := hq
      have key := hside₁ ((n : ℚ≥0) + 2) (one_lt_of_mem_stops ⟨n, rfl⟩)
      filter_upwards [key, hαsp] with ω hk hsp v hv hrep s hs1 hs2
      exact hk v hv hrep s hs1 hs2 (hsp.2.2.2.1 s (lt_of_le_of_lt zero_le hs1)))
    hside₂
  filter_upwards [hlate] with ω hω N
  obtain ⟨t, hNt, ht⟩ := hω N
  exact ⟨t, hNt, fun hmem => ht (subset_closure hmem)⟩

end

section
-- from InteractingSLE/Spec/Sec7/StripWallMeanFull.lean
open InteractingSLE.Sec7.StripWall
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux2728Pocket
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Lemma 6.2's inputs for both strip walls** (spec pp. 410–411): every version `β` of the wall `β^{(q)}` (rational
`q > 0`) and every version `α` of the wall `α` is field determined at fixed times (PROVE-STRIPSYS21/27) and
entrance-history local (`WordSafe.isEntranceHistoryLocal_beta`, `WordSafe.isEntranceHistoryLocal_alpha`) for the
    centred field, and both
are almost surely transient (PROVE-STRIPSYS28). -/
theorem lemma62_walls (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (q : ℝ≥0) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (E (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P ∧
    ∀ᵐ ω ∂P, Tendsto (β ω) atTop (Bornology.cobounded ℂ) ∧ Tendsto (α ω) atTop (Bornology.cobounded ℂ) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh (hS.isStagedHistory_alpha hθ₁) hregα (hL44 _ hm) (hcumR _ hm)
      (hL44 _ hθ₁) (hcumR _ hθ₁) hθ₁.1 (by linarith [hθ₁.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec (q : ℝ≥0) θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh (hS.isStagedHistory_beta hθ₂ (q : ℝ≥0)) hregβ (hL44 _ hp)
      (hcumR _ hp) (hcumL _ hθ₂) (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith) hθ₂.2
      (by linarith [hθ₂.1])
  have htrβ := (WordSafe.isWallVersion_beta hS hcumL hcumR hθ₂ (q : ℝ≥0) hregβ hβc hβ0 hβm hβtr).ae_trace
  have htrα := (WordSafe.isWallVersion_alpha hS hcumL hcumR hθ₁ hregα hαc hα0 hαm hαtr).ae_trace
  refine ⟨hDβ.hdet hregβ u₀ hβtr, WordSafe.isEntranceHistoryLocal_beta h44 hS hcumL hcumR hθ₂ hq hregβ hu₀ hβc hβ0 hβm
      hβtr,
    hDα.hdet hregα u₀ hαtr, WordSafe.isEntranceHistoryLocal_alpha h44 hS hcumL hcumR hθ₁ hregα hu₀ hαc hα0 hαm hαtr, ?_⟩
  filter_upwards [htrβ, htrα] with ω h1 h2
  exact ⟨h1.2.2.2, h2.2.2.2⟩

end

section
-- from InteractingSLE/Spec/Sec7/Aux37WallsStrip.lean
open InteractingSLE.Sec7.Aux37Walls
open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets PocketWordAssembly PocketSeedOpen
  PocketLeftFrontier PocketCoupling
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Lemma 6.2's inputs for the walls `α` and `Lr q`** at a rational stage time `q > 0` indexed by `rt q`
(`WordSafe.lemma62_walls` at `q.toNNRat`). -/
theorem lemma62_walls_rat (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {L α : Ω → ℝ≥0 → ℂ} (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0)
    (hLm : ∀ t, Measurable fun ω => L ω t)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1 (StripSys.rt q)
      (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (L ω))
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal L (WholeField.centredField h u₀) P ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P ∧
    ∀ᵐ ω ∂P, Tendsto (L ω) atTop (Bornology.cobounded ℂ) ∧ Tendsto (α ω) atTop (Bornology.cobounded ℂ) := by
  have e := rt_eq_coe_toNNRat hq.le
  rw [e] at hregβ hLtr
  exact WordSafe.lemma62_walls h44 hS hcumL hcumR hθ₁ hθ₂ (q := q.toNNRat) (Rat.toNNRat_pos.2 hq) hregα hregβ hu₀ hLc
      hL0
    hLm hLtr hαc hα0 hαm hαtr

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The walls' local-set means exist** for the strip system: the mean `gU q` of the walls' union
`wallUnion (Lr q) α`, the means `gL q t` of the prefixes `Lr q '' [0, t] ∩ ℍ` and `gR t` of `α '' [0, t] ∩ ℍ`
(Lemma 6.2's local sets, then Lemma 3.6's means). -/
theorem exists_wallMeans_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω)) :
    (∃ gU : ℚ → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℚ, 0 < q →
      IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q)) ∧
    (∃ gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t)) ∧
    ∃ gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hW : ∀ q : ℚ, 0 < q → _ := fun q hq =>
    WordSafe.lemma62_walls_rat h44 hS hcumL hcumR hθ₁ hθ₂ hq hregα (hregβ q hq) hu₀ (hLc q) (hL0 q) (hLm q) (hLtr q hq)
        hαc
      hα0 hαm hαtr
  have hU : ∀ q : ℚ, ∃ g : Ω → DistOn upperHalfPlaneOpens, 0 < q →
      IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P g := fun q => by
    by_cases hq : 0 < q
    · obtain ⟨hdL, hlL, hdα, hlα, htr⟩ := hW q hq
      obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hX (hLc q) (hL0 q) (hLm q) hdL hlL hαc hα0 hαm hdα hlα htr
      obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hX hUm hUloc
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  have hL : ∀ q : ℚ, ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (g t) := fun q => by
    by_cases hq : 0 < q
    · obtain ⟨hdL, hlL, -⟩ := hW q hq
      obtain ⟨g, hg⟩ := exists_isLocalSetMean_prefix hX (hLc q) (hL0 q) (hLm q) hdL hlL
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose gU hgU using hU
  choose gL hgL using hL
  obtain ⟨-, -, hdα, hlα, -⟩ := hW 1 one_pos
  exact ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, exists_isLocalSetMean_prefix hX hαc hα0 hαm hdα hlα⟩

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Aux. lemma 37's witness exclusion in the bounded change pocket, for the strip pockets** (`hwit` of
`StripPocketPath.pocketWordEvolution_of_stripSystem`, exactly in its type). The inputs are the consumer's own: the
strip system with its heights and angles `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`, the drivers' regularity, versions of
the walls `α`, `β = η_{π/2}`, `Lr q = β^{(q)}` and of the counterflow's trace `η`, Lemma 5.7's reverse visits and the
non-boundary avoidance `hav`. The walls' means, versions, locality, `β`'s simple properness and the common prefix are
derived (`WordSafe.exists_wallMeans_strip`, `WordSafe.lemma62_walls_rat`, `WordSafe.isWallVersion_alpha/beta`,
`WordSafe.ae_isSimpleProper_leftExtremal`, `WordSafe.ae_eq_leftExtremal_of_le`). -/
theorem hwit_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hS.boundaryData
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  obtain ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, gR, hgR⟩ := WordSafe.exists_wallMeans_strip h44 hS hcumL hcumR hθ₁c hθ₂c hregα hregβ hu₀
    hαc hα0 hαm hαtr hLc hL0 hLm hLtr
  have hW : ∀ q : ℚ, 0 < q → _ := fun q hq =>
    WordSafe.lemma62_walls_rat h44 hS hcumL hcumR hθ₁c hθ₂c hq hregα (hregβ q hq) hu₀ (hLc q) (hL0 q) (hLm q) (hLtr q
        hq)
      hαc hα0 hαm hαtr
  exact WordSafe.hwit_of_wallMeans h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀
    (WordSafe.isWallVersion_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαm hαtr) (hW 1 one_pos).2.2.2.1
    (fun q hq => WordSafe.isWallVersion_beta hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq) (hLc q) (hL0 q) (hLm q)
      (hLtr q hq)) (fun q hq => (hW q hq).2.1) hgU hgL hgR hηc hηtr hwalls hwallsL
    (WordSafe.ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr)
    (fun q hq => (WordSafe.ae_eq_leftExtremal_of_le h44 hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq 0) (hLtr q hq)
      hβtr).mono fun ω hω => hω _ le_rfl) hav

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Aux. lemma 37's witness exclusion in the change pocket at the flow seed, for the strip pockets** (`hwitI` of
`StripPocketPath.pocketWordEvolution_of_stripSystem`, exactly in its type), from the consumer's own hypotheses (as
`WordSafe.hwit_strip`; `hwallsL` with both conjuncts, as in the consumer). -/
theorem hwitI_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hS.boundaryData
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  obtain ⟨⟨gU, hgU⟩, ⟨gL, hgL⟩, gR, hgR⟩ := WordSafe.exists_wallMeans_strip h44 hS hcumL hcumR hθ₁c hθ₂c hregα hregβ hu₀
    hαc hα0 hαm hαtr hLc hL0 hLm hLtr
  have hW : ∀ q : ℚ, 0 < q → _ := fun q hq =>
    WordSafe.lemma62_walls_rat h44 hS hcumL hcumR hθ₁c hθ₂c hq hregα (hregβ q hq) hu₀ (hLc q) (hL0 q) (hLm q) (hLtr q
        hq)
      hαc hα0 hαm hαtr
  exact WordSafe.hwitI_of_wallMeans h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀
    (WordSafe.isWallVersion_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαm hαtr) (hW 1 one_pos).2.2.2.1
    (fun q hq => WordSafe.isWallVersion_beta hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq) (hLc q) (hL0 q) (hLm q)
      (hLtr q hq)) (fun q hq => (hW q hq).2.1) hgU hgL hgR hηc hηtr hwalls hwallsL
    (WordSafe.ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr)
    (fun q hq => (WordSafe.ae_eq_leftExtremal_of_le h44 hS hcumL hcumR hθ₂c (StripSys.rt q) (hregβ q hq 0) (hLtr q hq)
      hβtr).mono fun ω hω => hω _ le_rfl) hav

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Aux. lemma 37's attachment constancy in the bounded change pocket, for the strip pockets** (`hattach` of
`StripPocketConfig.pocketWordEvolution_of_stripPocket`): `WordSafe.hwit_strip` and the reduction to rational witnesses
`attachmentConstancy_of_noWitness`. -/
theorem hattach_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (α ω) (Lr q ω) (StripSys.rt q)) (cfArcL (α ω) (Lr q ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) := fun q hq => by
  have hwit := WordSafe.hwit_strip h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm hαtr hβc hβ0 hβtr hLc hL0
      hLm
    hLtr hηc hηtr hwalls hwallsL hav q hq
  have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
    simp only [ae_all_iff]
    exact hwit
  filter_upwards [StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hcumL hcumR hηtr, hwalls, hwallsL q hq, hw]
    with ω htr hwl hwL hwω hconf hpos
  exact attachmentConstancy_of_noWitness hconf hpos htr.1 htr.2.1 htr.2.2 hwl.1 hwL hwl.2
    fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf hpos

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Aux. lemma 37's attachment constancy in the change pocket at the flow seed, for the strip pockets**
(`hattachI` of `StripPocketConfig.pocketWordEvolution_of_stripPocket`): `WordSafe.hwitI_strip`, the counterflow's
transience (Aux. lemma 7 at `κ′ = 16/κ`, `WordSafe.ae_transient_counterflow`) and
    `attachmentConstancyInf_of_noWitness`. -/
theorem hattachI_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (E (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
          (cfArcRInf (α ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (α ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (α ω) (Lr q ω) (StripSys.rt q) 0)) := fun q hq => by
  have hwitI := WordSafe.hwitI_strip h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hregE hαc hα0 hαm hαtr hβc hβ0 hβtr hLc hL0
    hLm hLtr hηc hηtr hwalls hwallsL hav q hq
  have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
    simp only [ae_all_iff]
    exact hwitI
  filter_upwards [StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hcumL hcumR hηtr,
    WordSafe.ae_transient_counterflow haux7 hS hcumL hcumR hηtr, hwalls, hwallsL q hq, hw]
    with ω htr htω hwl hwL hwω hconf h0
  exact ⟨htω, hwL.2, attachmentConstancyInf_of_noWitness hconf h0 htr.1 htr.2.1 htr.2.2 hwl.1 hwL.1 hwl.2 hwL.2
    fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf h0⟩

end

section
-- from InteractingSLE/Spec/Sec7/PocketWordInWalls.lean
open InteractingSLE.Sec7.PocketWordIn
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real
open StripWall StripSideHeightProb StripPocketPath WangWu
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
Determination and entrance-history locality at one positive rational seed.
The four conclusions are precisely the corresponding inputs of the per-seed assembly. -/
theorem wall_inputs (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α L : Ω → ℝ≥0 → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) L) :
    (∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P ∧
    (∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal L (WholeField.centredField h u₀) P := by
  have hw := WordSafe.lemma62_walls_rat h44 hS hleft hright hθ₁ hθ₂ hq hr hl hu₀
    hvL.continuous hvL.zero hvL.measurable hvL.ae_isGeneratingTrace
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace
  exact ⟨hw.2.2.1, hw.2.2.2.1, hw.1, hw.2.1⟩

end

section
-- from InteractingSLE/Spec/Supplement/CounterflowNoReturnRouteStrip.lean
open InteractingSLE.Sec7.StripPocketPath
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The strip system's counterflow does not return to its seed** (`hnohit` of `pocketWordEvolution_of_stripSystem`,
ruling R59), from Aux. lemma 7 at `κ′ = 16/κ`: Aux. lemma 130's heights at the angles `∓π/2` are the barrier bounds
of `CfNoReturn.Route.ae_trace_ne_zero_of_centered`. Every version `η` of the trace avoids `0` at positive times. -/
theorem ae_noReturn_counterflow (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0 := by
  have hno := CfNoReturn.Route.ae_trace_ne_zero_of_centered hS.kappa_pos hS.kappa_lt_four haux7 hS.boundaryData
    (fun x hx hxJ => by have := hcumL _ StripSys.neg_pi_div_two_mem_Icc x hx hxJ; linarith)
    (fun x hx hxJ => by have := hcumR _ StripSys.pi_div_two_mem_Icc x hx hxJ; linarith) hS.gff hS.counterflow
  filter_upwards [hno, hηtr] with ω hω hη t ht
  have h1 := hω _ hη t.toNNReal (Real.toNNReal_pos.2 ht)
  rwa [Real.coe_toNNReal _ ht.le] at h1

end

section
-- from InteractingSLE/Spec/Sec7/PocketWordInStrip.lean
open InteractingSLE.Sec7.PocketWordIn
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real
open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig
open Exist.Staged (IsRegularDriver)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
Assemble the per-seed pocket word with the strip system's own fields and paths.
The positive-seed completion affects no selected rational seed. The two remaining
geometric premises describe visits of the actual walls by the actual counterflow. -/
theorem pocketWordEvolution_of_stripSystem_sideLimit
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (he : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : ∀ q, IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (positiveSeed q)) θ₂))
      (StripSys.rt (positiveSeed q)) (Lr q))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (𝔥 : DistOn upperHalfPlaneOpens) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[wallsSigma P α (Lr q)] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      let d := counterflowObjects hS.counterflow
      PocketSideLimitInput0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u ∧
      PocketSideLimitInputInf0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have hθ₁c := Ioo_subset_Icc_self hθ₁
  have hθ₂c := Ioc_subset_Icc_self hθ₂
  have hvLp : ∀ q : ℚ, 0 < q →
      IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q) :=
    fun q hq => by simpa only [positiveSeed_of_pos hq] using hvL q
  have hw := fun q => WordSafe.wall_inputs h44 hS hleft hright hθ₁c hθ₂c (positiveSeed_pos q)
    hr (hl _ (positiveSeed_pos q)) hu₀ hvα (hvL q)
  have hdα := (hw 1).1
  have hlocα := (hw 1).2.1
  have hdL := fun q => (hw q).2.2.1
  have hlocL := fun q => (hw q).2.2.2
  have hh := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hβsp := WordSafe.ae_isSimpleProper_leftExtremal hS hleft hright he hβc hβ0 hβtr
  have hαsp := WordSafe.ae_isSimpleProper_alpha hS hleft hright hθ₁c hr
    hvα.continuous hvα.zero hvα.ae_isGeneratingTrace
  have hgeomR := hαsp.and hwalls
  have hgeomβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧
      IsWallVisited (β ω) (η ω) := by
    filter_upwards [hβsp, hwalls] with ω hs hv
    exact ⟨hs, hv.2.2.1, hv.2.2.2⟩
  have hgeomL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧
      IsWallReverseVisit (Lr q ω) (η ω) ∧ Lr q ω (StripSys.rt q) = β ω (StripSys.rt q) := by
    intro q hq
    have hv := hvLp q hq
    filter_upwards [WordSafe.ae_isSimpleProper_beta hS hleft hright hθ₂c (StripSys.rt q) (hl q hq)
      hv.continuous hv.zero hv.ae_isGeneratingTrace, hwallsL q hq,
      WordSafe.ae_eq_leftExtremal_of_le h44 hS hleft hright hθ₂c (StripSys.rt q) (hl q hq 0)
        hv.ae_isGeneratingTrace hβtr] with ω hs hvisit hjoin
    exact ⟨hs, hvisit.1, hjoin _ le_rfl⟩
  have hlate := WordSafe.ae_late_strip h44 hS hleft hright hθ₁ hr he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβm hβtr hηc hwalls
  have htrace := StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hleft hright hηtr
  have hnohit := WordSafe.ae_noReturn_counterflow haux7 hS hleft hright hηtr
  have hav := WordSafe.ae_avoidance h411 hS hleft hright hβtr hηtr
  have hwR : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) :=
    hwalls.mono fun _ hv => ⟨hv.1, hv.2.1⟩
  have hattach := WordSafe.hattach_strip h44 hS hleft hright hθ₁ hθ₂ hr hl he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβtr
    (fun q => (hvL q).continuous) (fun q => (hvL q).zero) (fun q => (hvL q).measurable)
    (fun q hq => (hvLp q hq).ae_isGeneratingTrace) hηc hηtr hwR
    (fun q hq => (hwallsL q hq).mono fun _ hv => hv.1) hav
  have hattachI := WordSafe.hattachI_strip h44 haux7 hS hleft hright hθ₁ hθ₂ hr hl he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβtr
    (fun q => (hvL q).continuous) (fun q => (hvL q).zero) (fun q => (hvL q).measurable)
    (fun q hq => (hvLp q hq).ae_isGeneratingTrace) hηc hηtr hwR hwallsL hav
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hk' : 4 < 16 / κ := by
    rw [lt_div_iff₀ hS.kappa_pos]
    linarith only [hS.kappa_lt_four]
  exact pocketWordEvolution_of_stripPocket_sideLimit_perQ hk' hL hLd hR hRd hT hTr hu₀.1 hh
    hC hu' (counterflowObjects_measurable hS.counterflow) hS.lifetime
    hvα.measurable (fun q => (hvL q).measurable) hvα.continuous (fun q => (hvL q).continuous)
    hvα.zero (fun q => (hvL q).zero) hβm hηm hηc hηH hη0
    (hgeomR.mono fun _ hg => ⟨hg.1, hg.2.1, hg.2.2.1⟩) hgeomβ hgeomL hnohit hlate
    (by simpa only [Real.toNNReal_zero] using htrace) hav hattach hattachI
    hdα hdL hlocα hlocL 𝔥 hu hub h𝔥 hside

end

section
-- from InteractingSLE/Spec/Sec7/PocketWordInVisitStrip.lean
open InteractingSLE.Sec7.PocketWordIn
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real
open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig
open Exist.Staged (IsRegularDriver)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
The pocket-word assembly from the actual rational first-contact laws.
All reverse-order visits and positive-time visitation are proved in this theorem. -/
theorem pocketWordEvolution_of_stripSystem_firstHit
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (he : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : ∀ q, IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (positiveSeed q)) θ₂))
      (StripSys.rt (positiveSeed q)) (Lr q))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hfirstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (α ω)) (η ω) q)
    (hfirstE : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (β ω)) (η ω) q)
    (hfirstL : ∀ r : ℚ, 0 < r → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (Lr r ω)) (η ω) q)
    (𝔥 : DistOn upperHalfPlaneOpens) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[wallsSigma P α (Lr q)] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      let d := counterflowObjects hS.counterflow
      PocketSideLimitInput0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u ∧
      PocketSideLimitInputInf0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have hθ₁c := Ioo_subset_Icc_self hθ₁
  have hθ₂c := Ioc_subset_Icc_self hθ₂
  have hvisitR := ae_wall_visits_of_firstHitQ
    (WordSafe.ae_isSimpleProper_alpha hS hleft hright hθ₁c hr
      hvα.continuous hvα.zero hvα.ae_isGeneratingTrace) hηc hη0 hfirstR
  have hvisitE := ae_wall_visits_of_firstHitQ
    (WordSafe.ae_isSimpleProper_leftExtremal hS hleft hright he hβc hβ0 hβtr) hηc hη0 hfirstE
  have hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω) := by
    filter_upwards [hvisitR, hvisitE] with ω hrω heω
    exact ⟨hrω.1, hrω.2, heω⟩
  have hwallsL : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P,
      IsWallReverseVisit (Lr r ω) (η ω) ∧ IsWallVisited (Lr r ω) (η ω) := by
    intro r hrpos
    have hv : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt r) θ₂))
        (StripSys.rt r) (Lr r) := by
      simpa only [positiveSeed_of_pos hrpos] using hvL r
    exact ae_wall_visits_of_firstHitQ
      (WordSafe.ae_isSimpleProper_beta hS hleft hright hθ₂c (StripSys.rt r) (hl r hrpos)
        hv.continuous hv.zero hv.ae_isGeneratingTrace) hηc hη0 (hfirstL r hrpos)
  exact WordSafe.pocketWordEvolution_of_stripSystem_sideLimit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr hwalls hwallsL 𝔥 hu hub h𝔥 hside

end

section
-- from InteractingSLE/Spec/Sec5/RestartGenReflect.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartGen
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps reflField mem_reflJumps)
open Sec7.StripSideHeightProb (catPath)
open Exist.Staged (IsRegularDriver)
open LP (reflectC reflectC_reflectC)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hfirstR`** of `WordSafe.pocketWordEvolution_of_stripSystem_firstHit` from the landed Lemma 4.7 and the
switched law (no relative-angle-`(−π/2)` input). -/
theorem hfirstR_of_restartGen' (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) {α : Ω → ℝ≥0 → ℂ}
    (hvα : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.alphaSpec θ₁)) 1 α) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (α ω)) (η ω) q := by
  intro q hq
  filter_upwards [WordSafe.ae_isFirstHitQ_alpha (η := fun ω (t : ℝ≥0) => η ω t) h47 href hsw hS hleft hright
    (Ioo_subset_Icc_self hθ₁) hvα hηtr q hq] with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

end

section
-- from InteractingSLE/Spec/Sec5/RestartGenPocket.lean
open InteractingSLE.Sec7.PocketWordIn
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real
open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig
open Exist.Staged (IsRegularDriver)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The conditional pocket word from the restart law** (Aux. 130, pp. 410–412): the landed assembly
`WordSafe.pocketWordEvolution_of_stripSystem_firstHit` with its three wall first-exit laws derived from the landed
    Lemma 4.7
and the general switched-wall law. -/
theorem pocketWordEvolution_of_stripSystem_restartGen
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (he : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : ∀ q, IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (positiveSeed q)) θ₂))
      (StripSys.rt (positiveSeed q)) (Lr q))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (𝔥 : DistOn upperHalfPlaneOpens) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[wallsSigma P α (Lr q)] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      let d := counterflowObjects hS.counterflow
      PocketSideLimitInput0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u ∧
      PocketSideLimitInputInf0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have hηtr' := hηtr
  exact WordSafe.pocketWordEvolution_of_stripSystem_firstHit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr
    (WordSafe.hfirstR_of_restartGen' h47 href hsw hS hleft hright hθ₁ hvα hηtr')
    (WordSafe.hfirstE_of_restartGen h47 href hS hleft hright hβtr hηtr')
    (WordSafe.hfirstL_of_restartGen h47 href hsw hS hleft hright hθ₂ hvL hηtr')
    𝔥 hu hub h𝔥 hside

end

end InteractingSLE.Sec7.WordSafe
