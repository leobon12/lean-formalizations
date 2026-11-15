/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWMarks

/-! # Null-completed slit wiring on the physical small-gap glued measure -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Asm Aux61ULoc Aux61ChLoc WangWu LawUnique GlueCond Cond44Ref CfRegQ
open CrossCond.Theta Coupling WholeField LocalSets
open Sec7.PocketStopWallsFin (regHull ae_regHull_eq)
universe u

/-- The null-completed comparison wiring in the exact original-field binders
of `nullRuleMarksFacts_gluedQ`. The angle bounds and infinite own lifetime
are derived from the physical flow-line word. -/
theorem exists_slitWiring_null_gluedQ {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (h12 : θ₁ < θ₂) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (ζ : Ω → ℝ≥0∞)
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) (({0} : Finset ℝ) : Set ℝ))
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ} {Bm : ℝ≥0 → Ω → ℝ}
    (hC : IsOptionalHullCoupling κ (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)
      (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) P 𝓕 W VL VR Bm
      ζ (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω)))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂)
        (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineXL (Sec7.prop74Data a b) {0} 0)
        (flowLineXR (Sec7.prop74Data a b) {0} 0))
      (forceJumpSet (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)) u₀)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) (s : ℝ≥0)
    {μ : Measure (Ω × HistorySpace 0 0)} [IsProbabilityMeasure μ]
    (hμ : μ = glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
    (D : MarksData μ) (hF : MarksFacts μ D)
    (c : D.ι → HistorySpace 0 0 × HistorySpace (flowLineNL (Sec7.prop74Data a b) {0} 0)
      (flowLineNR (Sec7.prop74Data a b) {0} 0) → Chart)
    (hc : ∀ i, Aux61FibData.IsMeasChart (c i)) (r : D.ι → ℝ≥0)
    (q : D.index → ℝ≥0) (uph : D.index → Ω → ℂ → ℝ)
    (huph : ∀ j ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ
        (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂)
        (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) (fun i => VL i (q j) ω - W (q j) ω)
        (fun i => VR i (q j) ω - W (q j) ω))
      (forceJumpSet (fun i => VL i (q j) ω - W (q j) ω)
        (fun i => VR i (q j) ω - W (q j) ω)) (uph j ω))
    (hfield : D.field = fun p => Exist.flowField 0 (θ₂ * chiC κ) (h p.1)) (hmean₀ : D.originalMean = u₀)
    (hscale : D.scale = 0) (hconstant : D.constant = chiC κ) (hdata : ∀ i, (D.data i).κ = κ)
    (hmarks : ∀ i t, D.baseMarks i t = nullMarks
      (ruleMarks stopRec (capacityRule (c i) (r i) t)
        (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ)
    (hcontains : ∀ i t, ∀ᵐ p ∂μ,
      unionAt (fun p => cfHullQ s p.2) (fun v p => fwdHull (fun v : ℝ => W v.toNNReal p.1) (v : ℝ))
        (fun p => capacityRule (c i) (r i) t (stopRec s p.2, killedHistory W VL VR ζ p.1)) p ⊆ D.liveSets i t p)
    (hpatch : ∀ j i t, D.patches j i t = fun p => hullAt (q j) (killedHistory W VL VR ζ p.1))
    (hmean : ∀ j i t, D.mean j i t = fun p => couplingMean κ (fun v : ℝ => W v.toNNReal p.1)
      (q j) (uph j p.1))
    (hevent : ∀ j i t, D.comparisonEvent j i t =
      liveEv (D.Z i) (D.B i) (D.code i) 0 ∩
        {p | (q j : ℝ≥0∞) ≤ capacityRule (c i) (r i) t
          (stopRec s p.2, killedHistory W VL VR ζ p.1)}) :
    ∃ G : SlitWiringData (D.toAsmData hF), SlitWiring μ (D.toAsmData hF) G := by
  have hFword := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by
    have hχ := Sec4.chiC_pos hκ hκ4
    have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
    linarith only [hb, hθχ])
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hFword h44
  let θ := θ₂ - θ₁ + π / 2
  have hXeq : (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) =
      fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω)) := by
    funext ω
    rw [Prop51G.cfField_flowField_eq_cfFieldT κ θ₁ θ₂]
  have hμθ : μ = glueMeasure P k (fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω)))
      ((measurable_cfFieldT κ θ).comp hC.2.1) := by
    rw [hμ]
    congr 1
  have hlaw' : P.map (fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω))) = P₂.map h₂ := by
    rw [← hXeq]
    exact hlaw
  have hθb := Prop51G.cfThetaBounds_prop74 (a := a) (b := b) (θ₁ := θ₁) (θ₂ := θ₂) hκ hb (by
    have hχ := Sec4.chiC_pos hκ hκ4
    have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
    linarith only [ha, hθχ])
  have hseed := ae_seedLine_of_admissible hκ hκ4.le hFword hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hseed.mono fun _ hω => hω.1
  have hreg : ∀ᵐ p ∂μ, ∀ t : ℝ≥0,
      regHull W ζ t p.1 = fwdHull (fun v : ℝ => W v.toNNReal p.1) (t : ℝ) := by
    rw [hμθ]
    exact ae_glue_fst (μ := P) k ((measurable_cfFieldT κ θ).comp hC.2.1) (ae_regHull_eq hC hζ)
  apply exists_slitWiring_of_null_capacityRules hC hκ hζ hθb hcf hlaw' hk hu₀ hμθ D hF c hc r s q uph huph
    hfield hmean₀ hscale hconstant hdata hmarks _ hpatch hmean hevent
  intro i t
  filter_upwards [hcontains i t, hreg] with p hp hr
  have he : unionAt (fun p => cfHullQ s p.2) (fun v p => regHull W ζ v p.1)
      (fun p => capacityRule (c i) (r i) t (stopRec s p.2, killedHistory W VL VR ζ p.1)) p =
      unionAt (fun p => cfHullQ s p.2) (fun v p => fwdHull (fun v : ℝ => W v.toNNReal p.1) (v : ℝ))
        (fun p => capacityRule (c i) (r i) t (stopRec s p.2, killedHistory W VL VR ζ p.1)) p := by
    simp only [unionAt, hr]
  rw [he]
  exact hp

end InteractingSLE.Sec5.Aux61SlitW
