/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45ClockThreshold
import InteractingSLE.Spec.Sec5.Aux61R45Converse

/-! # General actual-mean clocks for the reference-kernel converse -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart Sec7.PocketTraversal
open LQGMetric (DistOn)
open QuantumZipper (fwdHull)

/-- A constructed window clock. Its two announcing sequences are the same
sequence in the actual and reference histories. All coordinates belong to the
reference word; the source carries only its driver. -/
structure ReferenceClock {S : Type u} [MeasurableSpace S] (D : ClockSource S)
    (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) (V : Set ℂ) where
  e : S → ℝ≥0∞
  measurable : Measurable e
  le_source : ∀ ω, e ω ≤ D.U ω
  ae_exit : e =ᵐ[D.P] fun ω => RLC.exitTime V (D.Γ ω) (D.U ω)
  W : ℝ≥0 → S → ℝ
  zero : ∀ ω, W 0 ω = 0
  continuous : ∀ ω, Continuous (W · ω)
  adapted : StronglyAdapted D.driving W
  stopping : IsStoppingTime D.driving fun ω => (e ω : WithTop ℝ≥0)
  T : ℕ → S → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq D.driving D.P e T
  agree : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω
  killed : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL b J D.y)
    (geomRW W fun _ => flowLineXR b J D.y) e
  referenceAnnouncing : Coupling.IsAnnouncingSeq (drivingFiltration D.P killed) D.P e T
  threshold : ∀ᵐ ω ∂D.P, e ω ≤ MartChar.thresholdTime
    (flowLineRhoL κ b J D.y θ) (flowLineRhoR κ b J D.y θ) (W · ω)
    (fun i t => geomLW W (fun _ => flowLineXL b J D.y) i t ω)
    (fun j t => geomRW W (fun _ => flowLineXR b J D.y) j t ω)
  trace : ∀ᵐ ω ∂D.P, IsGeneratingTrace (W · ω) (e ω) (fun t => D.Γ ω t - D.y)

namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- Automatic clock construction outside the original finite-word coupling.
The named inputs `hU_announcing` and `hU_leftLimit` identify precisely the
source-lifetime facts still required. No reference clock, threshold estimate,
reference evolution or stopped-flow-line law is assumed. -/
theorem exists_referenceClock (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ)
    {V : Set ℂ} (hV : IsOpen V) (hVc : Vᶜ.Nonempty) (hstart : (D.y : ℂ) ∈ V)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J D.y θ)
      (flowLineRhoR κ b J D.y θ) 0 (flowLineXL b J D.y) (flowLineXR b J D.y))
    {R : ℕ → S → ℝ≥0} (hU_announcing : Coupling.IsAnnouncingSeq D.driving D.P D.U R)
    (hU_leftLimit : ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = D.U ω →
      ∃ c : ℝ, Tendsto (D.W₀ · ω) (𝓝[<] T) (𝓝 c))
    (hinterior : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < D.U ω →
      D.Γ ω t ∈ QuantumZipper.H) :
    Nonempty (ReferenceClock D κ b J θ V) := by
  obtain ⟨e, hem, heU, he, hes, T, hT⟩ := D.exists_announced_exit hV hVc hstart hU_announcing
  have hpos : ∀ᵐ ω ∂D.P, 0 < e ω :=
    (hT.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h
  obtain ⟨W, hW0, hWc, hWa, hag⟩ := D.exists_adapted_driver heU hes hpos hU_leftLimit
  have hX : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL b J D.y)
      (geomRW W fun _ => flowLineXR b J D.y) e :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore
      (MartChar.adaptedBefore_of_stronglyAdapted hes hWa)
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes
        (stronglyAdapted_geomLW hWa hWc measurable_const i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes
        (stronglyAdapted_geomRW hWa hWc measurable_const j))
  have hg := D.generatingTrace_of_agree heU hag
  refine ⟨{
    e := e, measurable := hem, le_source := heU, ae_exit := he,
    W := W, zero := hW0, continuous := hWc, adapted := hWa, stopping := hes,
    T := T, announcing := hT, agree := hag, killed := hX,
    referenceAnnouncing := D.announcing_reference heU hW0 hWc hag hX hT,
    threshold := ?_, trace := hg }⟩
  apply threshold_of_interior_trace hW0 hWc (FlowStopIdentLL.flowLineXL_nonpos_seed b J D.y)
    (FlowStopIdentLL.flowLineXR_nonneg_seed b J D.y) hseed hg
  filter_upwards [hinterior] with ω hH t ht hte
  change 0 < (D.Γ ω t - (D.y : ℂ)).im
  have hHt : 0 < (D.Γ ω t).im := hH t ht (hte.trans_le (heU ω))
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hHt

end ClockSource

namespace ReferenceClock
variable {S : Type u} [MeasurableSpace S] {D : ClockSource S}
  {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {V : Set ℂ}
  (C : ReferenceClock D κ b J θ V)

/-- The reference history is contained in the actual completed history. -/
theorem driving_le : drivingFiltration D.P C.killed ≤ D.driving := by
  have hraw := Ito.killedDrivingFiltration_le
    (MartChar.adaptedBefore_of_stronglyAdapted C.stopping C.adapted)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted C.stopping
      (stronglyAdapted_geomLW C.adapted C.continuous measurable_const i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted C.stopping
      (stronglyAdapted_geomRW C.adapted C.continuous measurable_const j)) C.killed
  have hid : usualAugmentation D.driving D.P = D.driving := by
    rw [Ito.usualAugmentation_eq_rightCont]
    have hn : Ito.nullAugmented D.driving D.P = D.driving :=
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration D.killed) D.P
    rw [hn]
    exact Filtration.rightCont_self _
  exact (Ito.usualAugmentation_mono hraw D.P).trans hid.le

/-- Assemble the landed converse setting from the constructed clock and
strict-stop analytic data. Its fields remain definitionally the supplied data,
so both the converse and the stopped GB7a adapter can consume it. -/
def toReferenceSetting (hκ : 0 < κ)
    (field chartField : S → DistOn upperHalfPlaneOpens)
    (hm : Measurable chartField)
    (htranslate : ∀ ω, IsTranslateAddConst D.y (θ * QuantumZipper.chiC κ) (field ω) (chartField ω))
    (hkernel : Coupling.MartMeans.IsCouplingCharFun κ (flowLineRhoL κ b J D.y θ)
      (flowLineRhoR κ b J D.y θ) D.P D.driving C.W
      (geomLW C.W fun _ => flowLineXL b J D.y)
      (geomRW C.W fun _ => flowLineXR b J D.y) C.e chartField)
    (hlocality : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.driving τ),
      (∀ᵐ ω ∂D.P, (τ ω : ℝ≥0∞) < C.e ω) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) chartField D.P) :
    ReferenceSetting S := {
    κ := κ, κ_pos := hκ, b := b, J := J, y := D.y, θ := θ,
    P := D.P, prob := D.prob, field := field, chartField := chartField,
    measurable_field := hm, translate := htranslate, Γ := D.Γ,
    e := C.e, W := C.W, zero := C.zero, continuous := C.continuous,
    filt := D.driving, rightContinuous := D.driving_rightContinuous,
    adapted := C.adapted, stopping := C.stopping,
    nullSets := fun _A hA h0 => Ito.measurableSet_usualAugmentation_of_null hA h0 0,
    T := C.T, announcing := C.announcing, killed := C.killed,
    driving_le := C.driving_le, σ := C.T, referenceAnnouncing := C.referenceAnnouncing,
    threshold := C.threshold, kernel := hkernel, locality := hlocality, trace := C.trace }

/-- Feed the constructed clock directly to the landed general-mean converse.
Only the strict-stop reference kernel and locality remain analytic inputs. -/
theorem exists_isStoppedFlowLine (hκ : 0 < κ)
    (field chartField : S → DistOn upperHalfPlaneOpens)
    (hm : Measurable chartField)
    (htranslate : ∀ ω, IsTranslateAddConst D.y (θ * QuantumZipper.chiC κ) (field ω) (chartField ω))
    (hkernel : Coupling.MartMeans.IsCouplingCharFun κ (flowLineRhoL κ b J D.y θ)
      (flowLineRhoR κ b J D.y θ) D.P D.driving C.W
      (geomLW C.W fun _ => flowLineXL b J D.y)
      (geomRW C.W fun _ => flowLineXR b J D.y) C.e chartField)
    (hlocality : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.driving τ),
      (∀ᵐ ω ∂D.P, (τ ω : ℝ≥0∞) < C.e ω) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) chartField D.P) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      StoppedExtend.IsStoppedFlowLine κ b J D.y θ (D.P.prod ν)
        (fun p => field p.1) (fun p => D.Γ p.1) (fun p => C.e p.1) := by
  exact (C.toReferenceSetting hκ field chartField hm htranslate hkernel hlocality).exists_isStoppedFlowLine

end ReferenceClock
end InteractingSLE.Sec5.Aux61R45
