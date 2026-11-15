/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ULocStop
import InteractingSLE.Spec.Sec5.Prop51GQExit

/-!
# (P1) at the binders of `Aux61UnionK.GluedLocalCoverOn`

Packet PROVE-AUX61-UNIONLOC. At the binders of `Prop51G.GluedQ` / `Aux61UnionK.GluedLocalCoverOn` (a flow line of angle
`θ₂` of the field `h` with the data of Figure 7.1, an independent centred counterflow of `h + (θ₁ − π/2)χ` glued through
its kernel `k` given the field), **`exists_unionLoc_gluedQ`** exposes the flow line's driving coupling `(W, V, ζ)` (with
`ζ = ∞` and `η` its generating trace almost surely, and its regularized hull equal to its Loewner hull almost surely), a
bounded harmonic extension `u₀` of its force data, and, for every counterflow time `s` and every measurable Galmarino
rule `ρ` of (the counterflow record at `s`, the flow's killed history), the history-marked locality of
`ℍ ∩ (K_s ∪ K̃_T)` at the rule stop `T` for the marks `σ(counterflow record at s, flow history stopped at T)` and the
centred field `h + θ₂χ − 𝔥₀` of the flow line's coupling, on the glued measure of `GluedLocalCoverOn`.

The translation to the θ-glued space at `θ = θ₂ − θ₁ + π/2` is the one of `Prop51G.fwdFirstExitQOn_smallGap`
(`Prop51G.cfField_flowField_eq_cfFieldT`, `Prop51G.cfThetaBounds_prop74`, `Cond44Ref.ae_seedLine_of_admissible`).

R48 / R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or
Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Aux61ULoc

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ WholeField LocalSets CrossCond.Theta Coupling
open Sec7.PocketStopWallsFin (regHull ae_regHull_eq)

/-- **(P1) at the binders of `GluedLocalCoverOn`**: the flow line's driving coupling, its harmonic extension, and the
history-marked locality of the counterflow hull with the flow hull at every measurable Galmarino rule stop of the two
records, on the glued measure of `Aux61UnionK.GluedLocalCoverOn`. -/
theorem exists_unionLoc_gluedQ {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) (({0} : Finset ℝ) : Set ℝ))
    (hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) :
    ∃ (W : ℝ≥0 → Ω → ℝ) (VL : Fin (flowLineNL (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ) (u₀ : ℂ → ℝ),
      (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - ((0 : ℝ) : ℂ)) ∧
        ∀ t : ℝ≥0, regHull W ζ t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) ∧
      IsBoundedHarmonicExtension
        (forceBoundaryData κ (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂)
          (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineXL (Sec7.prop74Data a b) {0} 0)
          (flowLineXR (Sec7.prop74Data a b) {0} 0))
        (forceJumpSet (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)) u₀ ∧
      ∀ (s : ℝ≥0) (ρ : HistorySpace 0 0 × HistorySpace (flowLineNL (Sec7.prop74Data a b) {0} 0)
          (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0∞),
        Measurable ρ → IsGalmarinoRule stopRec ρ →
        @IsHistoryAvoidanceLocal (Ω × HistorySpace 0 0)
          (ruleMarks stopRec ρ (fun p => stopRec s p.2) fun p => killedHistory W VL VR ζ p.1)
          Prod.instMeasurableSpace
          (unionAt (fun p => cfHullQ s p.2) (fun r p => regHull W ζ r p.1)
            fun p => ρ (stopRec s p.2, killedHistory W VL VR ζ p.1))
          (fun p => centredField (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω)) u₀ p.1)
          (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
            ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hC, htr⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  subst hh'
  set θ := θ₂ - θ₁ + π / 2 with hθdef
  have hXeq : (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) =
      fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω)) := by
    funext ω
    rw [Prop51G.cfField_flowField_eq_cfFieldT κ θ₁ θ₂]
  have hμ : glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)) =
      glueMeasure P k (fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω)))
        ((measurable_cfFieldT κ θ).comp hC.2.1) := by
    congr 1
  have hlaw' : P.map (fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω))) = P₂.map h₂ := by
    rw [← hXeq]
    exact hlaw
  have hθb := Prop51G.cfThetaBounds_prop74 (a := a) (b := b) (θ₁ := θ₁) (θ₂ := θ₂) hκ hb (by linarith)
  have hseed := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hseed.mono fun _ hω => hω.1
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂)
    (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)
  refine ⟨W, VL, VR, u₀, ?_, hu₀, fun s ρ hρ hG => ?_⟩
  · filter_upwards [hζ, htr, ae_regHull_eq hC hζ] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rw [hμ]
    exact isHistoryAvoidanceLocal_unionAt_rule_cfGlueT hC hκ hζ hθb hcf hlaw' hk hu₀ s hρ hG

end InteractingSLE.Sec5.Aux61ULoc
