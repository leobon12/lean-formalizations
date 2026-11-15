/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceFacts
import InteractingSLE.Spec.Sec5.Aux61MarksOn

/-! # The original source setting and its actual chosen own coupling -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Cov Aux61Kernel Prop51G Cond44Ref WangWu LawUnique GlueCond
universe u

/-- The exact source binders of the dyadic fibre leaf, collected as data. -/
structure SourceSetting where
  t : ℚ
  windowCode : Aux61Kernel.WinCode
  t_pos : 0 < t
  κ : ℝ
  κ_pos : 0 < κ
  κ_lt_four : κ < 4
  a : ℝ
  b : ℝ
  θ₁ : ℝ
  θ₂ : ℝ
  angle_lt : θ₁ < θ₂
  small_gap : ¬ IsLargeGap κ θ₁ θ₂
  bound_right : sleLambda κ - θ₁ * chiC κ ≤ b
  bound_left : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a
  Ω : Type u
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  field : Ω → DistOn upperHalfPlaneOpens
  path : Ω → ℝ≥0 → ℂ
  life : Ω → ℝ≥0∞
  gff : IsGFFWithBoundaryData P field (Sec7.prop74Data a b) (({0} : Finset ℝ) : Set ℝ)
  flow : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P field path life
  Ω₂ : Type u
  [mΩ₂ : MeasurableSpace Ω₂]
  P₂ : Measure Ω₂
  [prob₂ : IsProbabilityMeasure P₂]
  field₂ : Ω₂ → DistOn upperHalfPlaneOpens
  W₂ : ℝ≥0 → Ω₂ → ℝ
  life₂ : Ω₂ → ℝ≥0∞
  counterflow : IsCenteredCounterflowDriver κ P₂ field₂ W₂ life₂
  field_law : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (field ω))) = P₂.map field₂
  kernel : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)
  [markov : IsMarkovKernel kernel]
  kernel_law : P₂.map (fun ω => (field₂ ω, cfHistory W₂ life₂ ω)) = P₂.map field₂ ⊗ₘ kernel
  s : ℚ
  s_pos : 0 < s

attribute [instance] SourceSetting.mΩ SourceSetting.prob SourceSetting.mΩ₂ SourceSetting.prob₂ SourceSetting.markov

namespace SourceSetting
variable (S : SourceSetting.{u})

abbrev nL : ℕ := flowLineNL (Sec7.prop74Data S.a S.b) {0} 0
abbrev nR : ℕ := flowLineNR (Sec7.prop74Data S.a S.b) {0} 0
abbrev xL : Fin S.nL → ℝ := flowLineXL (Sec7.prop74Data S.a S.b) {0} 0
abbrev xR : Fin S.nR → ℝ := flowLineXR (Sec7.prop74Data S.a S.b) {0} 0
abbrev ρL : Fin S.nL → ℝ := flowLineRhoL S.κ (Sec7.prop74Data S.a S.b) {0} 0 S.θ₂
abbrev ρR : Fin S.nR → ℝ := flowLineRhoR S.κ (Sec7.prop74Data S.a S.b) {0} 0 S.θ₂
abbrev ownField : S.Ω → DistOn upperHalfPlaneOpens := fun ω => Exist.flowField 0 (S.θ₂ * chiC S.κ) (S.field ω)
abbrev counterField : S.Ω → DistOn upperHalfPlaneOpens :=
  fun ω => cfField S.κ (Exist.flowField 0 (S.θ₁ * chiC S.κ) (S.field ω))
abbrev measCounterField : Measurable S.counterField :=
  (measurable_cfField S.κ).comp ((Exist.measurable_flowField 0 _).comp S.gff.1)
abbrev μ : Measure (S.Ω × HistorySpace 0 0) := glueMeasure S.P S.kernel S.counterField S.measCounterField

instance instProbability : IsProbabilityMeasure S.μ := inferInstance

/-- Witnesses of the given flow line's own optional-hull coupling. -/
structure OwnCoupling where
  filt : Filtration ℝ≥0 S.mΩ
  W : ℝ≥0 → S.Ω → ℝ
  VL : Fin S.nL → ℝ≥0 → S.Ω → ℝ
  VR : Fin S.nR → ℝ≥0 → S.Ω → ℝ
  noise : ℝ≥0 → S.Ω → ℝ
  coupling : IsOptionalHullCoupling S.κ S.xL S.xR S.ρL S.ρR S.P filt W VL VR noise S.life S.ownField
  trace : ∀ᵐ ω ∂S.P, IsGeneratingTrace (fun t => W t ω) (S.life ω) (fun t => S.path ω t - (0 : ℝ))

/-- Choose the actual coupling supplied by `IsFlowLine`; no coupling
existence hypothesis is added to the source statement. -/
def own : S.OwnCoupling := Classical.choice (by
  obtain ⟨𝓕, W, VL, VR, B, hC, htr⟩ := exists_coupling_of_flowLine S.flow
  exact ⟨⟨𝓕, W, VL, VR, B, hC, htr⟩⟩)

/-- The concrete MARKS source object for this setting and these restart choices. -/
abbrev marksData (F : SourceRestartData S.Ω S.nL S.nR) : MarksData S.μ :=
  sourceMarksData F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    S.ρL S.ρR S.xL S.xR S.path S.μ

/-- The original physical restart/window event. -/
abbrev windowEvent (p : S.Ω × HistorySpace 0 0) : Prop :=
  Aux61Kernel.RestartWindowEvent (Prop411Q.cfDrv p.2) S.s
    (fun t : ℝ => S.path p.1 t.toNNReal) S.t S.windowCode

end SourceSetting
end InteractingSLE.Sec5.Aux61SlitW
