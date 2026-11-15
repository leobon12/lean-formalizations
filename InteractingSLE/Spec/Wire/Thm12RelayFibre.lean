/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61UnionKRestart

/-! # The corrected fibre route on explicit restart codes

PROVE-WIRE-PARTA. Data are explicit arguments. No leaf refers to a choice of a
weaker existence statement. Canonical PC1 and glued locality are supplied by
Aux61UnionK; the remaining analytic fact is IsChartLocalAt for exitCode.
-/
set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped NNReal ENNReal
namespace InteractingSLE.Wire.Relay
open Sec5 Sec5.Aux61Fib Sec5.Aux61FibData Sec5.Aux61UnionK
open Restart.FlowStopIdentCMI (CMCut)
open Sec5.Aux61Win (IsCutoffOn)

/-- The actual restart objects; laws are specified separately for these explicit objects. -/
structure RestartData (X : Type u) [MeasurableSpace X] where
  ι : Type
  [countable : Countable ι]
  β : ι → Type u
  [mβ : ∀ i, MeasurableSpace (β i)]
  Z : ∀ i, X → β i
  B : ∀ i, Set (β i)
  event : ι → Set X
  chart : ι → X → Chart
  path : ι → X → ℝ≥0 → ℂ
  life : ι → X → ℝ≥0∞
  window : ι → Set ℂ
  field : X → DistOn upperHalfPlaneOpens
  scale : ℝ
  constant : ℝ
  data : ∀ i, β i → FibData
  left : ι → ℝ
  right : ι → ℝ
  cutoff : ∀ i, β i → CMCut
  neighbourhood : ∀ i, β i → Set ℂ
  kappa : ι → ℝ
  boundary : ι → ℝ → ℝ
  jumps : ι → Finset ℝ
  harmonicPart : ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens

attribute [instance] RestartData.countable RestartData.mβ

/-- FIBDATA's geometric and measurable restart requirements, on the supplied data. -/
structure RestartFacts {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (D : RestartData X) : Prop where
  measurable_Z : ∀ i, Measurable (D.Z i)
  measurable_B : ∀ i, MeasurableSet (D.B i)
  spec : ∀ i, IsRestartSpec (D.event i) (D.chart i) (D.path i) (D.life i)
  open_window : ∀ i, IsOpen (D.window i)
  zero_window : ∀ i, (0 : ℂ) ∈ D.window i
  landing : ∀ i, IsLanding (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i)
  injective_path : ∀ i, ∀ x ∈ D.event i, InjOn (D.path i x) {v | (v : ℝ≥0∞) < D.life i x}
  continuous_lift : ∀ i, ∀ x ∈ D.event i, ContinuousOn (D.chart i x).2.2 (D.chart i x).dom
  measurable_field : Measurable D.field
  data_window : ∀ i z, (D.data i z).V = D.window i
  data_clearance : ∀ i z, (D.data i z).ℓ = clr (D.window i)
  reference : ∀ i, ∀ z ∈ D.B i,
    Aux61Cov.RefWin (D.data i z).κ (D.data i z).bR (D.data i z).JR (Ioo (D.left i) (D.right i))
  exit : ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i →
    x ∈ exitEv (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i)
  cover : ∀ᵐ x ∂μ, E x → ∃ i, D.Z i x ∈ D.B i
  visit : ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → E x →
    exitCode (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) D.scale D.constant D.field x ∈
      visitSet (D.left i) (D.right i)
  cutoff : ∀ i, ∀ z ∈ D.B i,
    IsCutoffOn (D.cutoff i z) (D.data i z).q (D.neighbourhood i z) (D.data i z).O₀ ∧
      (D.data i z).buffer ⊆ D.neighbourhood i z
  word : ∀ i z, (D.data i z).κ = D.kappa i ∧ (D.data i z).bR = D.boundary i ∧ (D.data i z).JR = D.jumps i
  measurable_correction : ∀ i, Measurable fun p : D.β i × ℂ => (D.data i p.1).q p.2
  measurable_cutoff : ∀ i, Measurable fun p : D.β i × ℂ => (D.cutoff i p.1).f p.2
  measurable_source : ∀ i, Measurable fun p : D.β i × ℂ => QuantumZipper.K3.greenDensity (D.cutoff i p.1).f p.2

/-- The remaining local-set decomposition, for the literal exitCode and canonical mean. -/
def RestartLocal {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : RestartData X) : Prop :=
  ∀ i (r : ℝ≥0), IsChartLocalAt μ (D.Z i) (D.B i)
    (exitCode (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) D.scale D.constant D.field) r
    (fun x => canonMean (D.data i (D.Z i x)) (D.cutoff i (D.Z i x))
      (ULift.up.{u} (exitCode (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i)
        D.scale D.constant D.field x)) r) (D.harmonicPart i r)

/-- The corrected source assembly supplies PC1, kernel measurability and glued locality. -/
theorem localCover_of_restart {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    (D : RestartData X) (hF : RestartFacts μ E D) (hL : RestartLocal μ D) : HasFibreLocalCover μ E :=
  hasFibreLocalCover_of_restart D.Z hF.measurable_Z D.B hF.measurable_B D.event D.chart D.path D.life hF.spec
    D.window hF.open_window hF.zero_window hF.landing hF.injective_path hF.continuous_lift
    D.field hF.measurable_field D.scale D.constant D.data hF.data_window hF.data_clearance
    D.left D.right hF.reference hF.exit hF.cover hF.visit D.cutoff D.neighbourhood hF.cutoff
    D.kappa D.boundary D.jumps hF.word hF.measurable_correction hF.measurable_cutoff hF.measurable_source
    D.harmonicPart hL

open Sec4 Sec5.Aux61R2 Sec5.Aux61Cov Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique

def RestartDataOn :=
  ∀ (t : ℚ) (_c : WinCode), ∀ _ht : 0 < t,
  ∀ κ : ℝ, ∀ (_hκ : 0 < κ) (_hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (_h12 : θ₁ < θ₂) (_hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (_hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (_ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (_hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ _hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ _hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ _hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ _hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (_hs : 0 < s),
            RestartData (Ω × HistorySpace 0 0)

def RestartFactsOn (D : RestartDataOn.{u}) : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            RestartFacts (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (fun p => RestartWindowEvent
        (Prop411Q.cfDrv p.2) s (fun v : ℝ => η p.1 v.toNNReal) t c) (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh
        hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def RestartLocalOn (D : RestartDataOn.{u}) : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            RestartLocal (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb
        ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- The exact dyadic-cover input from the explicit restart construction and its one local law. -/
theorem dyCover_of_restart (D : RestartDataOn.{u}) (hF : RestartFactsOn D) (hL : RestartLocalOn D) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact hasDyActFibreCover_of_localCover (localCover_of_restart (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl
    P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hF t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs) (hL t c ht κ hκ hκ4 a b θ₁
      θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs))

end InteractingSLE.Wire.Relay
