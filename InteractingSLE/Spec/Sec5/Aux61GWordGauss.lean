/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GRecBoundary
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLocal

/-! # Initial Gaussian decomposition before the boundary field is supplied

Only the physical facts at time zero are needed. In particular this theorem
does not take `MarksFacts`, whose initial-boundary field is being constructed.
The conditional mean is obtained from the existing marked chart theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWord
open Aux61Marks (MarksData)
open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec IsMeasChart)
open Aux61GInst (HasAccessLanding)
open Aux61ChLoc (IsChartGaussAt liveSet liveEv)
open Aux61UnionK (chartHull)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal)

universe u
variable {X : Type u} [mX : MeasurableSpace X] {μ : Measure X}

/-- Construct the actual initial mean from the time-zero physical marked
set, without an assumed initial Gaussian mean or initial boundary assertion. -/
theorem exists_initialGauss_of_physical_marks [IsProbabilityMeasure μ]
    (D : MarksData μ) (i : D.ι)
    (hB : MeasurableSet (D.B i))
    (hs : IsRestartSpec (D.event i) (D.chart i) (D.path i) (D.life i))
    (hV : IsOpen (D.window i)) (hV0 : (0 : ℂ) ∈ D.window i)
    (hland : HasAccessLanding (D.event i) (D.chart i) (D.path i) (D.life i) (D.window i))
    (hinj : ∀ x ∈ D.event i, InjOn (D.path i x) {r | (r : ℝ≥0∞) < D.life i x})
    (hliftc : ∀ x ∈ D.event i, ContinuousOn (D.chart i x).2.2 (D.chart i x).dom)
    (hlift : ∀ x ∈ D.event i,
      InnerProductSpace.HarmonicOnNhd (D.chart i x).2.2 (D.chart i x).dom)
    (hhm : Measurable D.field)
    (hu₀ : InnerProductSpace.HarmonicOnNhd D.originalMean H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens D.cfield μ)
    (hmarks : D.baseMarks i 0 ≤ mX)
    (hZ : (D.mβ i).comap (D.Z i) ≤ D.baseMarks i 0)
    (hY : (codeFiltration.{u} 0).comap
      (fun x => ULift.up.{u} (D.code i x)) ≤ D.baseMarks i 0)
    (hE : MeasurableSet[D.baseMarks i 0] (D.event i))
    (hc : @IsMeasChart X (D.baseMarks i 0) (D.chart i))
    (hAm : Measurable[mX, hittingSigma] (D.baseSets i 0))
    (hAc : ∀ x, D.baseSets i 0 x ⊆ H ∧ IsOpen (H \ D.baseSets i 0 x))
    (hloc : IsHistoryAvoidanceLocal (D.baseMarks i 0) (D.baseSets i 0) D.cfield μ)
    (hgeo : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (0 : ℝ≥0∞) < (D.code i x).life →
      H \ D.baseSets i 0 x = (D.chart i x).2.1 '' (H \ chartHull (D.code i) 0 x)) :
    ∃ g : X → DistOn upperHalfPlaneOpens,
      IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0 (D.sigma i 0) g := by
  obtain ⟨g, hg⟩ := Aux61GInst.exists_isChartGaussAt_accessExit hB hs hV hV0 hland
    hinj hliftc hlift hhm hu₀ hh0 0 hmarks hZ hY hE hc hAm hAc hloc hgeo
  refine ⟨g, ?_⟩
  rw [Aux61GRec.sigma_zero_eq_marks]
  change IsChartGaussAt μ (D.Z i) (D.B i) (D.code i) 0
    (D.baseMarks i 0 ⊔ germSigma (D.liveSets i 0) D.cfield) g
  rw [sup_comm]
  exact hg

end InteractingSLE.Sec5.Aux61GWord
