/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvMarks
import InteractingSLE.Spec.Sec5.CfConvClock

/-!
# The canonical coarse chart clause in the exact record coordinates

Packet PROVE-CFCHART2. This is the conversion part of `CfGivenChartStatement` for a positive
prefix time: all changes of versions, filtrations, marks, charts and field constants are
performed here. No new probability input is used in this conversion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfConv

open LawUnique CfGiven CfChart Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart Sec7.PocketTraversal

section Convert

variable {Z Ω : Type*} [MeasurableSpace Z] [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR mL mR : ℕ} {κ θ : ℝ} {ρL : Fin (mL + 1) → ℝ}
  {ρR : Fin (mR + 1) → ℝ} {xL : Fin mL → ℝ} {xR : Fin mR → ℝ}
  {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ}
  {ζ : Z → ℝ≥0∞} {s : ℝ≥0} {E : Set (Z × HistorySpace 0 0)} {ι : Ω → Z × HistorySpace 0 0}
  {h h' : Ω → DistOn upperHalfPlaneOpens} {R : Ω → RecData}

/-- Convert a coarse canonical chart clause to the record chart, with the exact field shift,
geometric marks and infinite lifetime. Also obtain an everywhere continuous adapted version
of the driver and an almost surely generating trace. -/
theorem exists_converted_chart (hι : Measurable ι) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hEtop : ∀ p ∈ E, qT W VL VR ζ s E p = ⊤) (hEae : ∀ᵐ ω ∂P, ι ω ∈ E)
    (hs : 0 < s) (hR : Measurable R)
    (hReq : ∀ ω, R ω = recOf (s : ℝ≥0∞) ((fun t => W t (ι ω).1), ζ (ι ω).1))
    (hreg : ∀ ω, IsRegularDriver ((fun t => W t (ι ω).1), ζ (ι ω).1))
    (hh' : Measurable h') (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h' ω))
    (hcan : IsChartCanon (16 / κ) ρL ρR P (Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι)
      (fun t ω => qW W VL VR ζ s E t (ι ω))
      (fun i t ω => qVL xL W VL VR ζ s E i t (ι ω))
      (fun j t ω => qVR xR W VL VR ζ s E j t (ι ω))
      (fun ω => (qT W VL VR ζ s E (ι ω) : ℝ≥0∞)) (fun ω => fChart W VL VR ζ s (ι ω))
      (-((π - θ) * chiC κ)) (-chiC κ) (fun ω => -h' ω)) :
    ∃ (𝓑 : Filtration ℝ≥0 mΩ) (V : ℝ≥0 → Ω → ℝ),
      MeasurableSpace.comap R inferInstance ≤ 𝓑 0 ∧
      (∀ ω, V 0 ω = 0) ∧ (∀ ω, Continuous fun t => V t ω) ∧ StronglyAdapted 𝓑 V ∧
      (∀ᵐ ω ∂P, ∀ t, V t ω = qW W VL VR ζ s E t (ι ω)) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓑 V
        (geomLW V (fun ω => recordXL s xL (R ω))) (geomRW V (fun ω => recordXR s xR (R ω)))
        (fun _ => ⊤) (fun ω => cfChart (R ω)) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => V t ω) ⊤ (qTr W VL VR ζ s E (ι ω)) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → WangWu.negInv (qTr W VL VR ζ s E (ι ω) u) ∈ QuantumZipper.H ∧
            WangWu.negInv (WangWu.histLine (ι ω).2 (ℓ u)) =
              (recChart (R ω)).2.1 (WangWu.negInv (qTr W VL VR ζ s E (ι ω) u)) := by
  let 𝓐 := Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι
  let A : Set Ω := ι ⁻¹' E
  have hA : MeasurableSet A := hι hE
  let V := eventDriver A (fun t ω => qW W VL VR ζ s E t (ι ω))
  have hVeq : ∀ ω ∈ A, ∀ t, V t ω = qW W VL VR ζ s E t (ι ω) := fun ω hω => eventDriver_eq hω
  have hV0 : ∀ ω, V 0 ω = 0 := eventDriver_zero fun ω _ =>
    (isKilledCurve_qgCurve (q := s) hEg (ι ω)).kcW_zero
  have hVc : ∀ ω, Continuous fun t => V t ω := continuous_eventDriver fun ω hω =>
    continuous_qW_of_top hEg (hEtop (ι ω) hω)
  have hVa : StronglyAdapted 𝓐 (fun t ω => qW W VL VR ζ s E t (ι ω)) := fun t =>
    (((stronglyAdapted_qW_raw (xL := xL) (xR := xR) hX hE hEg t).measurable).comp
      (comap_measurable ι)).stronglyMeasurable
  have hhh : Measurable fun ω => -h' ω := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp hh').neg
  have hc1 := IsChartCanon.regularize_top hA hEae (fun ω hω => hEtop (ι ω) hω) hhh hcan
  have hrec : ∀ t, MeasurableSpace.comap R inferInstance ≤ aeSigma P (𝓐 t) := by
    intro t
    have heq : R = fun ω => recOf (s : ℝ≥0∞) ((fun r => W r (ι ω).1), ζ (ι ω).1) := funext hReq
    rw [heq]
    exact recordSigma_le_aeSigma (xL := xL) (xR := xR) (E := E) hι hX
      (hEae.mono fun ω hω => hEg (ι ω) hω) t
  have hc2 := IsChartCanon.observe_record hR hhh
    (fun t => (hrec t).trans (aeSigma_mono (le_eventFiltration 𝓐 A hA t))) hc1
  let 𝓑 := recordFiltration (eventFiltration 𝓐 A hA) R hR
  have hc3 : IsChartCanon (16 / κ) ρL ρR P 𝓑 V
      (geomLW V (fun ω => recordXL s xL (R ω))) (geomRW V (fun ω => recordXR s xR (R ω)))
      (fun _ => ⊤) (fun ω => cfChart (R ω)) (-((π - θ) * chiC κ)) (-chiC κ) (fun ω => -h' ω) := by
    apply IsChartCanon.congr_data_ae hc2
    filter_upwards [hEae] with ω hω
    have hg := hEg (ι ω) hω
    refine ⟨rfl, ?_, fun _ => rfl, ?_, ?_⟩
    · rw [hReq]
      exact (fChart_eq_cfChart hg (hreg ω)).symm
    · intro i t
      exact (qVL_eq_geomLW (hEtop (ι ω) hω) (hVeq ω hω)
        (by rw [hReq]; exact recordXL_recOf xL hg (hreg ω) hs hω) i t).symm
    · intro j t
      exact (qVR_eq_geomRW (hEtop (ι ω) hω) (hVeq ω hω)
        (by rw [hReq]; exact recordXR_recOf xR hg (hreg ω) hs hω) j t).symm
  have hc4 := IsChartCanon.unshift_field htr (fun ω => isConformal_cfChart (R ω))
    (fun ω => continuousOn_lift_cfChart (R ω)) hVc hc3
  refine ⟨𝓑, V, le_sup_right, hV0, hVc, ?_, hEae.mono fun ω hω => hVeq ω hω, ?_, ?_⟩
  · intro t
    exact (stronglyAdapted_eventDriver 𝓐 hA hVa t).mono le_sup_left
  · exact (isChartCouplingCharFunConst_iff_canon (fun ω => isConformal_cfChart (R ω))
      (fun ω => (hVc ω).comp continuous_real_toNNReal)).2 hc4
  · filter_upwards [hEae] with ω hω
    refine ⟨?_, ?_⟩
    · have hw : (fun t => V t ω) = fun t => qW W VL VR ζ s E t (ι ω) := funext (hVeq ω hω)
      rw [hw]
      exact isGeneratingTrace_kcTr_top (isKilledCurve_qgCurve (q := s) hEg (ι ω)) (hEtop (ι ω) hω)
    · rw [hReq]
      exact exists_physical_clock hEg hω (hEtop (ι ω) hω) (hreg ω)

end Convert

end InteractingSLE.Sec5.CfConv
