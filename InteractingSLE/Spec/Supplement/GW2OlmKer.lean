/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmChain

/-!
# GW2's open lines: the counterflow under the conditional kernel, in the form of the stage-0 union mean

Packet PROVE-GW2-STAGEMEAN, R119 round. Under the conditional kernel of the earlier pieces the launch datum gives a
centred counterflow `W_k` of the launch field (`HasLaunchPairEq`). `GW2Stl.exists_chart_mean_stop_random` asks for it
unpacked: the counterflow field, its translate, its optional hull coupling stated for a WORD `c'` of its boundary data,
the killed driving, the complete generating trace and the no-return clause. The stop `σ_k` must be a stopping time of
the SAME driving filtration, so the unpacking is done once, already in word form:

* **`counterflow_pack`**: from `IsCenteredCounterflowDriver` with infinite lifetime under any probability measure
  (Theorem 1.3 for the trace and no return; `Restart.BoundaryWord.exists_fn_eq` and
  `Exist.isFlowLineDriver_congr_of_eqOn` for the word).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Olm

open Restart Exist

/-- **The counterflow of a GFF, unpacked in word form** (under any probability measure). -/
theorem counterflow_pack (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → DistOn upperHalfPlaneOpens}
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData μ X b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ μ X W ζ) (hζ : ∀ᵐ ω ∂μ, ζ ω = ⊤) :
    ∃ (h' h₁ : Ω → DistOn upperHalfPlaneOpens) (c' : BoundaryWord) (𝓕' : Filtration ℝ≥0 mΩ)
      (VL' : Fin (flowLineNL c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ) (VR' : Fin (flowLineNR c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (_hX' : IsMeasurableKilledDriving W VL' VR' ζ),
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (X ω) (h' ω)) ∧
      (∀ ω, IsTranslateAddConst 0 (0 * chiC (16 / κ)) (h' ω) (h₁ ω)) ∧
      IsOptionalHullCoupling (16 / κ) (flowLineXL c'.fn c'.jumps 0) (flowLineXR c'.fn c'.jumps 0)
        (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0) (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) μ 𝓕' W VL' VR' B' ζ h₁ ∧
      (∀ᵐ ω ∂μ, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
      (∀ᵐ ω ∂μ, ∀ v : ℝ≥0, 0 < v → γ ω v ≠ 0) := by
  classical
  obtain ⟨b', J', h', hb', hT, hfl⟩ := id hcf
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hc'pc : IsPiecewiseConstantBoundaryData c'.fn c'.jumps := BoundaryWord.isPiecewiseConstantBoundaryData c'
  have hfl' : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 μ h' W ζ :=
    (StagedLaw.isFlowLineDriver_congr_of_eqOn hb' hc'pc J' (fun y hy => by rw [hc'J] at *; exact hc'b y hy)).2 hfl
  obtain ⟨h₁, 𝓕', VL', VR', B', htr', hC'⟩ := hfl'
  set γ : Ω → ℝ≥0 → ℂ := fun ω =>
    if h : ∃ g : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ g then h.choose else 0 with hγ
  have hreg := GW2Later.ae_counterflow_regular h13 hκ hcf hζ
  have hcomp : ∀ᵐ ω ∂μ, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hζ, hreg] with ω hζω hrω
    obtain ⟨g, hg, -⟩ := hrω
    have hex : ∃ g : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ g := ⟨g, hg⟩
    refine ⟨hζω, ?_⟩
    simp only [hγ, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hNR : ∀ᵐ ω ∂μ, ∀ v : ℝ≥0, 0 < v → γ ω v ≠ 0 := by
    have hn := GW2Rd.counterflowNoReturn_of_thm13 h13 κ hκ hκ4 b J hb μ X hG W ζ hcf hζ
    filter_upwards [hn, hcomp] with ω hnω hc v hv
    exact hnω (γ ω) hc.2 v hv
  exact ⟨h', h₁, c', 𝓕', VL', VR', B', γ, hC'.2.2.2.1, hT, htr', hC', hcomp, hNR⟩

end InteractingSLE.Theorem14.GW2Olm
