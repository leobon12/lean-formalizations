/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYLimit
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVAssembly

/-!
# A reference-kernel converse for a general actual mean

Only the reference word is finite. The input field and driver below may have
been obtained by tilting a coupling with an arbitrary harmonic actual mean.
There is no assumption that the actual field or driver has a finite-word law.
The clock data are explicit: two announcements, the reference threshold bound,
and strict-stop locality. Terminal locality is proved by the landed filled-hull
limit, and the landed converse supplies the Brownian enlargement.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Restart Sec7.PocketTraversal

/-- Reference data after the general-mean tilt. The clock and strict-stop
kernel/locality are the hypotheses used by the CMI converse; no original
optional-hull coupling or original finite word is part of this setting. -/
structure ReferenceSetting (S : Type u) [m : MeasurableSpace S] where
  κ : ℝ
  κ_pos : 0 < κ
  b : ℝ → ℝ
  J : Finset ℝ
  y : ℝ
  θ : ℝ
  P : Measure S
  prob : IsProbabilityMeasure P
  field : S → DistOn upperHalfPlaneOpens
  chartField : S → DistOn upperHalfPlaneOpens
  measurable_field : Measurable chartField
  translate : ∀ ω, IsTranslateAddConst y (θ * QuantumZipper.chiC κ) (field ω) (chartField ω)
  Γ : S → ℝ≥0 → ℂ
  e : S → ℝ≥0∞
  W : ℝ≥0 → S → ℝ
  zero : ∀ ω, W 0 ω = 0
  continuous : ∀ ω, Continuous (W · ω)
  filt : Filtration ℝ≥0 m
  rightContinuous : filt.IsRightContinuous
  adapted : StronglyAdapted filt W
  stopping : IsStoppingTime filt fun ω => (e ω : WithTop ℝ≥0)
  nullSets : ∀ A, MeasurableSet A → P A = 0 → MeasurableSet[filt 0] A
  T : ℕ → S → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq filt P e T
  killed : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL b J y)
    (geomRW W fun _ => flowLineXR b J y) e
  driving_le : drivingFiltration P killed ≤ filt
  σ : ℕ → S → ℝ≥0
  referenceAnnouncing : Coupling.IsAnnouncingSeq (drivingFiltration P killed) P e σ
  threshold : ∀ᵐ ω ∂P, e ω ≤ MartChar.thresholdTime
    (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) (W · ω)
    (fun i t => geomLW W (fun _ => flowLineXL b J y) i t ω)
    (fun j t => geomRW W (fun _ => flowLineXR b J y) j t ω)
  kernel : Coupling.MartMeans.IsCouplingCharFun κ (flowLineRhoL κ b J y θ)
    (flowLineRhoR κ b J y θ) P filt W (geomLW W fun _ => flowLineXL b J y)
    (geomRW W fun _ => flowLineXR b J y) e chartField
  locality : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime filt τ),
    (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < e ω) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0)) chartField P
  trace : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (fun t => Γ ω t - y)

namespace ReferenceSetting
variable {S : Type u} [MeasurableSpace S] (D : ReferenceSetting S)

/-- The announced clock is positive, so the time-zero kernel is available. -/
theorem ae_pos : ∀ᵐ ω ∂D.P, 0 < D.e ω :=
  (D.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h

/-- The reference Gaussian field law is a consequence of the kernel at zero. -/
theorem gaussian (u₀ : ℂ → ℝ)
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
        (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y))
      (forceJumpSet (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)) u₀) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => D.chartField ω φ - ∫ z, u₀ z * φ z) D.P := by
  let _ := D.prob
  have hF := Theorem15.isOrderedForceWord_flowLine D.b D.J D.y
  apply Sec7.Lemma71J.isZBGFFProcess_of_isCouplingCharFun D.kernel D.measurable_field _ hu₀
  filter_upwards [D.ae_pos] with ω hω
  exact ⟨hω, (D.continuous ω).continuousOn, D.zero ω,
    fun i => geomLW_zero D.continuous D.zero (hF.2.1 i),
    fun j => geomRW_zero D.continuous D.zero (hF.2.2.2 j)⟩

/-- Strict-stop locality extends through the exit by increasing filled hulls.
This is the Y-stage CMI argument, independent of the law of the actual mean. -/
theorem locality_le {τ : S → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration D.P D.killed) τ)
    (hτe : ∀ᵐ ω ∂D.P, (τ ω : ℝ≥0∞) ≤ D.e ω ∧ τ ω ≠ ⊤) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField D.P := by
  let _ := D.prob
  have hs₀ := Coupling.isStoppingTime_untopD hτ (hτe.mono fun _ h => h.2)
  have hs' : IsStoppingTime D.filt fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
    fun t => D.driving_le t _ (hs₀ t)
  let s : ℕ → S → ℝ≥0 := fun n ω => min ((τ ω).untopD 0) (D.T n ω)
  let u₀ := LocalExt.bheAt D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ)
    (flowLineRhoR D.κ D.b D.J D.y D.θ) (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt D.κ
    (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
    (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
  have hH : IsHarmonicDistOn (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) H :=
    WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hg : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (WholeField.centredField D.chartField u₀) D.P := by
    refine ⟨WholeField.measurable_centredField D.measurable_field u₀, ?_⟩
    have he : (fun φ ω => WholeField.centredField D.chartField u₀ ω φ) =
        fun φ ω => D.chartField ω φ - ∫ z, u₀ z * φ z := by
      funext φ ω
      exact WholeField.centredField_apply D.chartField hu₀.1 ω φ
    rw [he]
    exact D.gaussian u₀ hu₀
  have hloc : ∀ n, IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) (s n ω))
      (WholeField.centredField D.chartField u₀) D.P := by
    intro n
    have hsn : IsStoppingTime D.filt fun ω => (s n ω : WithTop ℝ≥0) := by
      simpa only [s, WithTop.coe_min] using hs'.min (D.announcing.1 n)
    have hlt : ∀ᵐ ω ∂D.P, (s n ω : ℝ≥0∞) < D.e ω :=
      (D.announcing.2.2.1 n).mono fun ω h => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt h
    have hl := D.locality _ hsn hlt
    simp only [WithTop.untopD_coe] at hl
    exact WholeField.IsLocalSet.sub_dist hl hH
  have hlim : ∀ᵐ ω ∂D.P, Tendsto (fun n => (s n ω : ℝ≥0∞)) atTop
      (𝓝 (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞)) := by
    filter_upwards [RetAux79.ae_tendsto_of_isAnnouncingSeq D.announcing, hτe] with ω ht hτω
    have hle : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) ≤ D.e ω := by
      change (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ (D.e ω : WithTop ℝ≥0)
      rw [Coupling.coe_untopD_of_ne_top hτω.2]
      exact hτω.1
    simpa only [s, ENNReal.coe_min, min_eq_left hle] using
      (tendsto_const_nhds (x := (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞))).min ht
  have hl := FlowStopIdentCMI.cmiXHullLocalityLimitStatement D.P _ hg D.W D.zero D.continuous
    s (fun ω => (τ ω).untopD 0) (fun ω => monotone_const.min (D.announcing.2.1 ω))
    (fun _ _ => min_le_left _ _) hlim hloc
  have hadd := Coupling.IsLocalSet.add_dist hl hH
  simpa only [WholeField.centredField, sub_add_cancel] using hadd

/-- The general actual-mean converse: the reference kernel and clock data
produce a stopped reference flow on an independent Brownian enlargement. -/
theorem exists_isStoppedFlowLine :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      StoppedExtend.IsStoppedFlowLine D.κ D.b D.J D.y D.θ (D.P.prod ν)
        (fun p => D.field p.1) (fun p => D.Γ p.1) (fun p => D.e p.1) := by
  let _ := D.prob
  let _ := D.rightContinuous
  have hF := Theorem15.isOrderedForceWord_flowLine D.b D.J D.y
  have hinit : ∀ᵐ ω ∂D.P, 0 < D.e ω ∧
      ContinuousOn (D.W · ω) {t | (t : ℝ≥0∞) < D.e ω} ∧ D.W 0 ω = 0 ∧
      (∀ i, geomLW D.W (fun _ => flowLineXL D.b D.J D.y) i 0 ω = flowLineXL D.b D.J D.y i) ∧
      ∀ j, geomRW D.W (fun _ => flowLineXR D.b D.J D.y) j 0 ω = flowLineXR D.b D.J D.y j := by
    filter_upwards [D.ae_pos] with ω hω
    exact ⟨hω, (D.continuous ω).continuousOn, D.zero ω,
      fun i => geomLW_zero D.continuous D.zero (hF.2.1 i),
      fun j => geomRW_zero D.continuous D.zero (hF.2.2.2 j)⟩
  have hint := fun φ => Coupling.MartMeans2.integrable_apply_of_isCouplingCharFun D.kernel hinit φ
    ((LQGMetric.measurable_distOn_apply φ).comp D.measurable_field)
  obtain ⟨ν, hν, 𝓕, B, hc⟩ := FlowStopIdentCMI.exists_stoppedHullCoupling_prod_of_clock D.κ_pos
    hF.2.1 hF.2.2.2 hF.1 hF.2.2.1 D.zero D.continuous D.adapted D.stopping D.nullSets D.announcing
    D.measurable_field hint D.gaussian D.kernel D.threshold D.killed D.driving_le
    D.referenceAnnouncing.1
    (fun ω n m hnm => WithTop.coe_le_coe.2 (D.referenceAnnouncing.2.1 ω hnm))
    (ae_all_iff.2 D.referenceAnnouncing.2.2.1)
    (RetAux79.ae_tendsto_of_isAnnouncingSeq D.referenceAnnouncing) (fun _ => D.locality_le)
  refine ⟨ν, hν, D.chartField ∘ Prod.fst, 𝓕, fun t p => D.W t p.1,
    fun i t p => geomLW D.W (fun _ => flowLineXL D.b D.J D.y) i t p.1,
    fun j t p => geomRW D.W (fun _ => flowLineXR D.b D.J D.y) j t p.1,
    B, fun p => D.translate p.1, hc, ?_⟩
  exact ConverseBefore.ae_fst_of_ae (P₀ := ν) D.trace

end ReferenceSetting
end InteractingSLE.Sec5.Aux61R45
