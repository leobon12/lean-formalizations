/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12RelayFibre
import InteractingSLE.Spec.Sec5.Aux61MeanIdSlit

/-! # Fibre covers from physical marked locality and slit mean identification

Every field, set and sigma algebra is explicit data. Boundary hypotheses quantify
valid Gaussian decompositions, never the witness of a weaker existential.
-/
set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H fwdMapInv chiC)
open QuantumZipper.CA (cayleyInv)
open InteractingSLE.Sec5.Aux61FibK (codeFiltration)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal
namespace InteractingSLE.Wire.Beacon
open Sec5 Sec5.Aux61Fib Sec5.Aux61FibData Sec5.Aux61UnionK Sec5.Aux61ChLoc Sec5.Aux61MeanId
  WholeField LocalSets

/-- The literal restart code, with no selected-record witness. -/
abbrev fibreCode {X : Type u} [MeasurableSpace X] (D : Relay.RestartData X) (i : D.ι) : X → FibCode :=
  exitCode (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i) D.scale D.constant D.field

/-- Canonical PC1 mean on the literal restart code. -/
abbrev fibreMean {X : Type u} [MeasurableSpace X] (D : Relay.RestartData X) (i : D.ι) (r : ℝ≥0) : X → ℂ → ℝ :=
  fun x => canonMean (D.data i (D.Z i x)) (D.cutoff i (D.Z i x)) (ULift.up.{u} (fibreCode D i x)) r

/-- Physical marked sets and histories, data only. -/
structure MarkedData {X : Type u} [MeasurableSpace X] (D : Relay.RestartData X) where
  originalMean : ℂ → ℝ
  history : D.ι → ℝ≥0 → MeasurableSpace X
  sets : D.ι → ℝ≥0 → X → Set ℂ

/-- The source conditioning sigma algebra of the marked physical set. -/
abbrev fibreSigma {X : Type u} [MeasurableSpace X] (D : Relay.RestartData X) (C : MarkedData D)
    (i : D.ι) (r : ℝ≥0) : MeasurableSpace X :=
  germSigma (liveSet (liveEv (D.Z i) (D.B i) (fibreCode D i) r) (C.sets i r))
    (centredField D.field C.originalMean) ⊔ C.history i r

/-- Measurability, regularity and harmonic-representative context for the supplied marked sets. -/
structure MarkedContext {X : Type u} [mX : MeasurableSpace X] (D : Relay.RestartData X)
    (C : MarkedData D) : Prop where
  lift_harmonic : ∀ i, ∀ x ∈ D.event i, InnerProductSpace.HarmonicOnNhd (D.chart i x).2.2 (D.chart i x).dom
  mean_harmonic : InnerProductSpace.HarmonicOnNhd C.originalMean H
  history_le : ∀ i r, C.history i r ≤ mX
  Z_le : ∀ i r, (D.mβ i).comap (D.Z i) ≤ C.history i r
  code_le : ∀ i (r : ℝ≥0), (codeFiltration.{u} r).comap (fun x => ULift.up.{u} (fibreCode D i x)) ≤ C.history i r
  event_measurable : ∀ i r, MeasurableSet[C.history i r] (D.event i)
  chart_measurable : ∀ i r, @IsMeasChart X (C.history i r) (D.chart i)
  sets_measurable : ∀ i r, Measurable[mX, hittingSigma] (C.sets i r)
  sets_closed : ∀ i r x, C.sets i r x ⊆ H ∧ IsOpen (H \ C.sets i r x)

def MarkedZeroField {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Relay.RestartData X)
    (C : MarkedData D) : Prop := IsZeroBoundaryGFF upperHalfPlaneOpens (centredField D.field C.originalMean) μ

def MarkedLocal {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Relay.RestartData X)
    (C : MarkedData D) : Prop :=
  ∀ i r, IsHistoryAvoidanceLocal (C.history i r) (C.sets i r) (centredField D.field C.originalMean) μ

def MarkedGeometry {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Relay.RestartData X)
    (C : MarkedData D) : Prop :=
  ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (r : ℝ≥0∞) < (fibreCode D i x).life →
    H \ C.sets i r x = (D.chart i x).2.1 '' (H \ chartHull (fibreCode D i) r x)

def MeanHarmonic {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Relay.RestartData X) : Prop :=
  ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (r : ℝ≥0∞) < (fibreCode D i x).life →
    InnerProductSpace.HarmonicOnNhd (fibreMean D i r x) (H \ chartHull (fibreCode D i) r x)

/-- Source logarithmic growth and finite-exception slit limits for valid decompositions. -/
def SlitBoundary {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Relay.RestartData X)
    (C : MarkedData D) : Prop :=
  ∀ i (r : ℝ≥0) (g : X → DistOn upperHalfPlaneOpens),
    IsChartGaussAt μ (D.Z i) (D.B i) (fibreCode D i) r (fibreSigma D C i r) g →
    ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (r : ℝ≥0∞) < (fibreCode D i x).life → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ chartHull (fibreCode D i) r x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull (fibreCode D i) r x →
        g x ψ = ∫ z, v z * ψ z) →
      (∃ K : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
        |v (fwdMapInv (fun t : ℝ => FibCode.driver t.toNNReal (fibreCode D i x)) r (cayleyInv ζ)) -
          fibreMean D i r x (fwdMapInv (fun t : ℝ => FibCode.driver t.toNNReal (fibreCode D i x)) r (cayleyInv ζ))| ≤
        K * (1 + Real.log (1 / (1 - ‖ζ‖)))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y : ℝ, y ∉ S →
        Tendsto (fun z => v (fwdMapInv (fun t : ℝ => FibCode.driver t.toNNReal (fibreCode D i x)) r z) -
          fibreMean D i r x (fwdMapInv (fun t : ℝ => FibCode.driver t.toNNReal (fibreCode D i x)) r z))
          (𝓝[H] (y : ℂ)) (𝓝 0)

/-- The marked-locality and slit-mean assemblies produce the exact fibre cover. -/
theorem localCover_of_marked {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {E : X → Prop} (D : Relay.RestartData X) (hF : Relay.RestartFacts μ E D) (C : MarkedData D)
    (hC : MarkedContext D C) (hZ : MarkedZeroField μ D C) (hL : MarkedLocal μ D C)
    (hG : MarkedGeometry μ D C) (hH : MeanHarmonic μ D) (hS : SlitBoundary μ D C) :
    HasFibreLocalCover μ E := by
  apply hasFibreLocalCover_of_restart_marked D.Z hF.measurable_Z D.B hF.measurable_B D.event D.chart D.path D.life
    hF.spec D.window hF.open_window hF.zero_window hF.landing hF.injective_path hF.continuous_lift hC.lift_harmonic
    D.field hF.measurable_field D.scale D.constant D.data hF.data_window hF.data_clearance D.left D.right
    hF.reference hF.exit hF.cover hF.visit D.cutoff D.neighbourhood hF.cutoff D.kappa D.boundary D.jumps hF.word
    hF.measurable_correction hF.measurable_cutoff hF.measurable_source hC.mean_harmonic hZ C.history hC.history_le
    hC.Z_le hC.code_le hC.event_measurable hC.chart_measurable C.sets hC.sets_measurable hC.sets_closed hL hG
  intro i r g hg
  have hY := (hF.spec i).measurable_exitCode (hF.open_window i) (hF.zero_window i) (hF.landing i)
    (hF.injective_path i) (hF.continuous_lift i) hF.measurable_field D.scale D.constant
  exact (isChartMeanAt_of_slit hY (hF.measurable_B i) hg (hH i r) (hS i r g hg)) g hg

open Sec4 Sec5.Aux61R2 Sec5.Aux61Cov Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
  WangWu Restart Exist.StagedLaw LocalExt Coupling LawUnique

def MarkedDataOn (D : Relay.RestartDataOn.{u}) :=
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
            MarkedData (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh
        hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def MarkedContextOn (D : Relay.RestartDataOn.{u}) (C : MarkedDataOn D) : Prop :=
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
            MarkedContext (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh
        hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
      (C t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def MarkedZeroFieldOn (D : Relay.RestartDataOn.{u}) (C : MarkedDataOn D) : Prop :=
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
            MarkedZeroField (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
      (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
      (C t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def MarkedLocalOn (D : Relay.RestartDataOn.{u}) (C : MarkedDataOn D) : Prop :=
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
            MarkedLocal (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
      (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
      (C t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def MarkedGeometryOn (D : Relay.RestartDataOn.{u}) (C : MarkedDataOn D) : Prop :=
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
            MarkedGeometry (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
      (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
      (C t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def MeanHarmonicOn (D : Relay.RestartDataOn.{u}) : Prop :=
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
            MeanHarmonic (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
      (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def SlitBoundaryOn (D : Relay.RestartDataOn.{u}) (C : MarkedDataOn D) : Prop :=
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
            SlitBoundary (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
      (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
      (C t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- The small-gap dyadic cover from the explicit physical marked-set leaves. -/
theorem dyCover_of_marked (D : Relay.RestartDataOn.{u}) (hF : Relay.RestartFactsOn D) (C : MarkedDataOn D)
    (hC : MarkedContextOn D C) (hZ : MarkedZeroFieldOn D C) (hL : MarkedLocalOn D C)
    (hG : MarkedGeometryOn D C) (hH : MeanHarmonicOn D) (hS : SlitBoundaryOn D C) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  apply hasDyActFibreCover_of_localCover
  exact localCover_of_marked
    (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hF t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (C t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hC t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hZ t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hL t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hG t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hH t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hS t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hGap hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

end InteractingSLE.Wire.Beacon
