/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12DawnFibres

/-!
# Source-setting quantifiers for the new fibre kernel leaves

PROVE-WIRE-PARTA. Every predicate below is applied to the same chosen cover
records, with the same glued measure and small-gap window as Night's interface.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Dawn
open Sec4 Sec5 Sec5.Aux61Fib Sec5.Aux61FibK Sec5.Aux61R2 Sec5.Aux61Cov
open Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique

def GluedKernelDataOn (hGeo : Night.GluedFibreGeometryOn.{u}) :=
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
            FibreKernelData (Classical.choose (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂
              hcf hlaw k hk s hs))

def GluedDataMeasOn (hGeo : Night.GluedFibreGeometryOn.{u}) (K : GluedKernelDataOn hGeo) : Prop :=
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
            FibreDataMeas (Classical.choose (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂
              hcf hlaw k hk s hs)) (K t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk
              s hs)

def GluedSigmaOn (hGeo : Night.GluedFibreGeometryOn.{u}) (K : GluedKernelDataOn hGeo) : Prop :=
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
            FibreSigma (Classical.choose (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf
              hlaw k hk s hs)) (K t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s
              hs)

def GluedChartOn (hGeo : Night.GluedFibreGeometryOn.{u}) (K : GluedKernelDataOn hGeo) : Prop :=
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
            FibreChart (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (Classical.choose (hGeo t c ht κ hκ
        hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)) (K t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG
        hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def GluedPC1On (hGeo : Night.GluedFibreGeometryOn.{u}) (K : GluedKernelDataOn hGeo) : Prop :=
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
            FibrePC1 (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (Classical.choose (hGeo t c ht κ hκ
        hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)) (K t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG
        hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

def GluedLocalOn (hGeo : Night.GluedFibreGeometryOn.{u}) : Prop :=
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
            FibreLocal (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (Classical.choose (hGeo t c ht κ hκ
        hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs))

/-- The newest chart, mean and locality leaves assemble the corrected source cover. -/
theorem dyCover_of_chart (hGeo : Night.GluedFibreGeometryOn.{u}) (K : GluedKernelDataOn hGeo)
    (hm : GluedDataMeasOn hGeo K) (hs : GluedSigmaOn hGeo K)
    (hc : GluedChartOn hGeo K) (hp : GluedPC1On hGeo K) (hl : GluedLocalOn hGeo) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs'
  let D := Classical.choose (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs')
  have hg := Classical.choose_spec (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k
    hk s hs')
  have hdm := hm t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'
  have hsig := hs t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'
  have hchart := hc t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'
  have hpc := hp t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'
  have hloc := hl t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'
  let data := K t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs'
  have hmeas := fibreMeas_of_data D data hdm
  have hint := fibreIntegral_of_chart D data hg hdm hsig hchart hpc
  exact Night.hasDyCover_of_glued D hg hmeas hint (fibreMembers_of_local D hg hmeas hint hloc)

end InteractingSLE.Wire.Dawn
