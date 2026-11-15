/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVStmt

/-!
# The lifetime clause and Galmarino rule at a measurable exit version

R66: only pathwise uses of the exit identity need changing. The coupling and
its adaptedness remain at the measurable stop; the raw exit is used only
inside almost-sure pathwise arguments.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open StoppedExtend FlowStopIdentG FlowStopIdentCM StoppedExtendWF

/-- The automatic lifetime clause holds at any almost-sure exit version. -/
theorem isStoppedFlowLineL_of_ae_exit
    {κ θ y : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ} {O : Set ℝ} {V : Set ℂ}
    {S : Type u} [MeasurableSpace S] {Q₀ Q : Measure S}
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q]
    {H₀ Ĥ : S → DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U e : S → ℝ≥0∞}
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) (hO : IsOpen O)
    (hbbR : ∀ a ∈ O, b a = bR a) (hV : IsOpen V)
    (hVO : ∀ z ∈ V, z.im = 0 → z.re ∈ O) (hQQ₀ : Q ≪ Q₀)
    (hflow : IsFlowLine κ b J y θ Q₀ H₀ Γ U)
    (he : e =ᵐ[Q] fun ω => RLC.exitTime V (Γ ω) (U ω))
    (hstop : IsStoppedFlowLine κ bR JR y θ Q Ĥ Γ e) :
    IsStoppedFlowLineL κ bR JR y θ V Q Ĥ Γ e := by
  obtain ⟨H₀', 𝓕₀, W₀, VL₀, VR₀, B₀, -, hC₀, hgen₀⟩ := hflow
  obtain ⟨Ĥ', 𝓕, W, VL, VR, B, htr, hC, hgen⟩ := hstop
  refine ⟨Ĥ', 𝓕, W, VL, VR, B, htr, hC, hgen, ?_⟩
  filter_upwards [hC₀.1.ae_isIntegratedSLEPath.filter_mono hQQ₀.ae_le,
    (hC₀.1.ae_tendsto_threshold hκ).filter_mono hQQ₀.ae_le,
    hgen₀.filter_mono hQQ₀.ae_le, hC.1.ae_path, hC.2.1, hgen, he]
    with ω hp hlimits hg hpR hcR hgR heω T heT hmem
  rw [heω] at hpR hgR hcR heT
  have hU := FlowStopIdentLL.eq_lifetime_at_exit_of_generatingTrace hV hg heT hmem
  obtain ⟨c, hc⟩ : ∃ c : ℝ, 0 < T → Tendsto (W₀ · ω) (𝓝[<] T) (𝓝 c) := by
    by_cases hT : 0 < T
    · obtain ⟨c, zL, zR, hlim, -⟩ := hlimits T hT hU
      exact ⟨c, fun _ => (continuous_fst.tendsto _).comp hlim⟩
    · exact ⟨0, fun hpos => (hT hpos).elim⟩
  exact FlowStopIdentLL.thresholdCondition_at_exit_continuous hκ hb hbR hO hbbR hV hVO hp hg hpR hgR
    heT hmem c hc (hcR T heT)


/-- The exit-version lifetime clause gives the same Galmarino rule almost surely. -/
theorem isStoppedFlowLineG_of_L_ae_exit {κ θ y : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    {V : Set ℂ} (hV : IsOpen V) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {Γ : Ω → ℝ≥0 → ℂ} {U e : Ω → ℝ≥0∞}
    (hb : ∀ᵐ ω ∂P, FlowPathFacts κ b J y θ (Γ ω) (U ω))
    (he : e =ᵐ[P] fun ω => RLC.exitTime V (Γ ω) (U ω))
    (hL : IsStoppedFlowLineL κ bR Ĵ y θ V P h Γ e) :
    IsStoppedFlowLineG κ bR Ĵ y θ P h Γ e := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen, hlife⟩ := hL
  let R := flowRule (SeedStop κ b J y θ V) y V
    (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
  have hR : ∀ᵐ ω ∂P, e ω = R (LawUnique.killedHistory W VL VR e ω) := by
    filter_upwards [hSC.1.ae_path, hSC.2.1, hgen, hlife, hb, he]
      with ω hp hc hg hl hf heω
    obtain ⟨w, vL, vR, β, hp₀, hg₀⟩ := hf
    have hs := exitTime_seed (θ := θ) hV hp₀ hg₀
    exact flowRule_killedHistory hV hp hc hg hl heω
      (fun h => heω.trans (hs.1 h)) (fun h => heω.symm ▸ hs.2 h)
  exact ⟨h', 𝓕, W, VL, VR, B, R, htr, hSC, measurable_flowRule _ _ _ _ _,
    isHistGalmarino_flowRule _ _ _ _ _, hR, hgen⟩

/-- The measurable-stop successor with the lifetime clause follows from its plain form. -/
theorem flowLineStopIdentCMIVStatement_of_stopped (h : CMIStoppedVStatement.{u}) :
    FlowLineStopIdentCMIVStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q
    hq hFq hFΔ y θ S _ Q₀ _ H₀ hH s hsle hslim Λ hΛm hΛ k hk hprob Γ U hΓ
  obtain ⟨e, hem, he, ν, hν, hstop⟩ := h κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO
    V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ y θ Q₀ H₀ hH s hsle hslim Λ hΛm hΛ
    k hk hprob Γ U hΓ
  refine ⟨e, hem, he, ν, hν, ?_⟩
  have hμ : (Q₀.prod ν).map Prod.fst = Q₀ := Measure.map_fst_prod.trans (by simp)
  have hflow := FlowStopIdentLift.isFlowLine_fst (C := ℕ → ℝ) hμ hΓ
  have hac : (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν ≪ Q₀.prod ν :=
    (withDensity_absolutelyContinuous _ _).prod Measure.AbsolutelyContinuous.rfl
  have he' := hac.ae_le (ConverseBefore.ae_fst_of_ae (P₀ := ν) he)
  exact isStoppedFlowLineL_of_ae_exit hκ hb hbR hO hbO hV
    (fun z hz => hNO z (hVN (subset_closure hz))) hac hflow he' hstop

end InteractingSLE.Restart.FlowStopIdentCMI
