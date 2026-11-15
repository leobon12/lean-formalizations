/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdTop
import InteractingSLE.Spec.Supplement.RelSafeS4

/-!
# Integrability in GW2's relative safe law

Packet PROVE-GW2-SAFE. The joint-chart field is the dual own-chart field
(`GW2Fb.isChartTransport_own_of_joint`). Consequently GB6's existing Gaussian
integrability theorem applies at the retained parameter `16 / κ`, without a
restriction on that parameter. Raising the field by `θχ(κ)` preserves integrability.
The result is then transferred to each conditioned canonical law appearing in
`GW2Rd.GW2RdSafeStatement`. This proves its integrability clause only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  GW2JointKernel GW2Rd

section Integrable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b' : ℝ → ℝ} {J' : Finset ℝ} {h h' Hc : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}

/-- The raised GW2 chart field is integrable on the live counterflow record event. -/
theorem integrable_indicator_raised_chartField (hκ : 0 < κ)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (s : ℝ≥0) (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ)
        (chiC κ) (h ω) (Hc ω)) (θ : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    Integrable ((gb6Rec s W ζ ⁻¹' gb6TS s).indicator
      fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) P := by
  have hk : 0 < 16 / κ := by positivity
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hcf' : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ :=
    (isFlowLineDriver_congr_of_eqOn hb' c'.isPiecewiseConstantBoundaryData J' hc'b).2 (hc'J ▸ hcf)
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hown : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω → γ ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => W r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC (16 / κ))) (chiC (16 / (16 / κ))) (h' ω) (Hc ω) := by
    filter_upwards [hHc, hζ, ae_driver_zero_continuousOn hcf] with ω hω hz hd _ hsH
    have hc : Continuous fun t => W t ω := by
      rw [← continuousOn_univ]
      exact hd.2.mono fun t _ => by simp only [hz, ENNReal.coe_lt_top, mem_ofPred_eq]
    exact GW2Fb.isChartTransport_own_of_joint hκ
      (hc.comp continuous_real_toNNReal) (by
        change W (Real.toNNReal 0) ω = 0
        rw [Real.toNNReal_zero]
        exact hd.1)
      s.2 (hT ω) (hω hsH)
  have hi := Supp8.RelSafeS.integrable_indicator_chartField hk hG' hcf' hγ s hHcm hown φ
  have hrec := (measurable_recOf_cfE hcf s).2
  have hE : MeasurableSet (gb6Rec s W ζ ⁻¹' gb6TS s) := hrec (measurableSet_gb6TS s)
  have ha : Integrable ((gb6Rec s W ζ ⁻¹' gb6TS s).indicator
      fun _ : Ω => θ * chiC κ * (∫ z, φ z)) P := (integrable_const _).indicator hE
  have heq : ((gb6Rec s W ζ ⁻¹' gb6TS s).indicator
      fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) =
      (gb6Rec s W ζ ⁻¹' gb6TS s).indicator (fun ω => Hc ω φ) +
        (gb6Rec s W ζ ⁻¹' gb6TS s).indicator (fun _ => θ * chiC κ * (∫ z, φ z)) := by
    classical
    funext ω
    by_cases hω : ω ∈ gb6Rec s W ζ ⁻¹' gb6TS s
    · simp only [Pi.add_apply, indicator_of_mem hω]
      exact WangWu.Shift.flowField_zero_apply _ _ _
    · simp only [Pi.add_apply, indicator_of_notMem hω, zero_add]
  rw [heq]
  exact hi.add ha

/-- The integrability clause of `GW2RdSafeStatement`, for every type and version. -/
theorem integrable_canonFld_gw2 (hκ : 0 < κ)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (s : ℝ≥0) (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ)
        (chiC κ) (h ω) (Hc ω)) (θ : ℝ) (c' : BoundaryWord)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t))
    {V : Ω → ℝ≥0∞} (hVm : Measurable V) (w : WordType) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun y : CanonSpace => canonFld y φ)
      ((P.map fun ω => (gb6Rec s W ζ ω,
        relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))[|
          typeEvent κ w (gw2Word κ θ c') (gb6TS s)]) := by
  have hrec : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  have hraised : Measurable fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) :=
    (Exist.measurable_flowField 0 _).comp hHcm
  have hΦ := hrec.prodMk (measurable_relVar hraised hRm hVm)
  have hS := measurableSet_typeEvent (k := κ) (w := w)
    (measurable_gw2Word κ θ c') (measurableSet_gb6TS s)
  have hE : MeasurableSet (gb6Rec s W ζ ⁻¹' gb6TS s) := hrec (measurableSet_gb6TS s)
  have hi := (integrable_indicator_iff hE).1
    (integrable_indicator_raised_chartField hκ hb' hT hcf hζ hγ s hHcm hHc θ φ)
  have hφm : Measurable fun y : CanonSpace => canonFld y φ :=
    (LQGMetric.measurable_distOn_apply φ).comp measurable_canonFld
  have hon : IntegrableOn (fun y : CanonSpace => canonFld y φ)
      (typeEvent κ w (gw2Word κ θ c') (gb6TS s))
      (P.map fun ω => (gb6Rec s W ζ ω,
        relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω)) := by
    unfold IntegrableOn
    rw [Measure.restrict_map hΦ hS]
    refine (integrable_map_measure hφm.aestronglyMeasurable hΦ.aemeasurable).2 ?_
    exact hi.mono_set fun ω hω => hω.1
  by_cases h0 : (P.map fun ω => (gb6Rec s W ζ ω,
      relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))
        (typeEvent κ w (gw2Word κ θ c') (gb6TS s)) = 0
  · rw [cond_eq_zero_of_meas_eq_zero h0]
    exact integrable_zero_measure
  · unfold ProbabilityTheory.cond
    exact hon.smul_measure (ENNReal.inv_ne_top.2 h0)

end Integrable

end InteractingSLE.Theorem14.GW2Sf
