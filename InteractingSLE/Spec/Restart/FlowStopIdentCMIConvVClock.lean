/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVAssembly
import InteractingSLE.Spec.Restart.RetPlumbProofInputsFiltration

/-!
# Explicit data and the remaining regularized clock construction

The records contain the original setting and the analytic clock data needed
by the converse. `CMIVPositiveClockStatement` names an unfinished construction;
it is not asserted here and is not a substitute for `CMIConverseVStatement`.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7.PocketTraversal

/-- The original explicit-shift setting, with its original chart coupling. -/
structure CMIVSetting (S : Type u) [m : MeasurableSpace S] where
  κ : ℝ
  κ_pos : 0 < κ
  κ_lt_four : κ < 4
  b : ℝ → ℝ
  bR : ℝ → ℝ
  J : Finset ℝ
  JR : Finset ℝ
  b_pc : IsPiecewiseConstantBoundaryData b J
  bR_pc : IsPiecewiseConstantBoundaryData bR JR
  O : Set ℝ
  O_open : IsOpen O
  boundary_eq : ∀ x ∈ O, b x = bR x
  N : Set ℂ
  N_open : IsOpen N
  N_real : ∀ z ∈ N, z.im = 0 → z.re ∈ O
  V : Set ℂ
  V_open : IsOpen V
  V_bounded : Bornology.IsBounded V
  closureV_subset : closure V ⊆ N
  a : ℝ
  c : ℝ
  interval_subset : Icc a c ⊆ O
  closureV_real : ∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c
  hull_subset : FlowStopIdentCM.shiftHullSet V a c ⊆ N
  F : CMCut
  q : ℂ → ℝ
  q_extension : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ JR : Finset ℝ) : Set ℝ) q
  cutoff_eq : ∀ z ∈ N, z ∈ H → F.f z = q z
  cutoff_harmonic : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0
  y : ℝ
  θ : ℝ
  Q₀ : Measure S
  Q₀_prob : IsProbabilityMeasure Q₀
  H₀ : S → DistOn upperHalfPlaneOpens
  H₀_gff : IsGFFWithBoundaryData Q₀ H₀ b J
  s : ℕ → TestOn upperHalfPlaneOpens
  s_bound : ∀ n z, |s n z| ≤ |F.src z|
  s_limit : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))
  Λ : S → ℝ
  Λ_measurable : Measurable Λ
  pairing_limit : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))
  k : ℝ
  k_pos : 0 < k
  tilt_prob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))
  Γ : S → ℝ≥0 → ℂ
  U : S → ℝ≥0∞
  h' : S → DistOn upperHalfPlaneOpens
  filt : Filtration ℝ≥0 m
  W₀ : ℝ≥0 → S → ℝ
  VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ
  VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ
  B₀ : ℝ≥0 → S → ℝ
  translate : ∀ x, IsTranslateAddConst y (θ * QuantumZipper.chiC κ) (H₀ x) (h' x)
  coupling : IsOptionalHullCoupling κ (flowLineXL b J y) (flowLineXR b J y)
    (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) Q₀ filt W₀ VL₀ VR₀ B₀ U h'
  trace : ∀ᵐ x ∂Q₀, IsGeneratingTrace (W₀ · x) (U x) (fun t => Γ x t - y)
  killed : IsMeasurableKilledDriving W₀ VL₀ VR₀ U

namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)
/-- The explicit comparison measure. -/
def tilt : Measure S := D.Q₀.withDensity fun x => ENNReal.ofReal (D.k * Real.exp (-D.Λ x))
/-- The original driving filtration. -/
def driving := drivingFiltration D.Q₀ D.killed
/-- The shifted chart field whose reference kernel is already proved. -/
def chartField : S → DistOn upperHalfPlaneOpens := fun ω => D.h' ω + chartShift D.F D.q D.y
/-- The shifted field in physical coordinates. -/
def shiftedField : S → DistOn upperHalfPlaneOpens := fun ω => D.H₀ ω +
  SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => D.q z - D.F.f z)
end CMIVSetting

/-- A regularized positive clock, including the two announcements used by the
landed converse and the passage to the stopped driving sigma algebra. -/
structure CMIVClock {S : Type u} [MeasurableSpace S] (D : CMIVSetting S) where
  e : S → ℝ≥0∞
  measurable : Measurable e
  ae_exit : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω)
  W : ℝ≥0 → S → ℝ
  zero : ∀ ω, W 0 ω = 0
  continuous : ∀ ω, Continuous (W · ω)
  adapted : StronglyAdapted D.driving W
  stopping : IsStoppingTime D.driving fun ω => (e ω : WithTop ℝ≥0)
  announce : ℕ → S → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq D.driving D.Q₀ e announce
  pathData : ∀ (τ : S → WithTop ℝ≥0) (_hτ : IsStoppingTime D.driving τ),
    (∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < e ω) →
    ∀ᵐ ω ∂D.Q₀, StopPathData D.b D.J D.y D.N D.W₀ W D.VL₀ D.VR₀ τ ω
  threshold : ∀ᵐ ω ∂D.Q₀, e ω ≤ MartChar.thresholdTime
    (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W · ω)
    (fun i t => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
    (fun j t => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω)
  killed : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL D.bR D.JR D.y)
    (geomRW W fun _ => flowLineXR D.bR D.JR D.y) e
  σ : ℕ → S → WithTop ℝ≥0
  σ_stopping : ∀ n, IsStoppingTime (drivingFiltration D.Q₀ killed) (σ n)
  σ_monotone : ∀ ω, Monotone fun n => σ n ω
  σ_lt : ∀ᵐ ω ∂D.Q₀, ∀ n, (σ n ω : ℝ≥0∞) < e ω
  σ_limit : ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (e ω))

/-- Remaining clock construction: regularize the exit and freeze the original
driver, announce the exit in both driving filtrations, and check threshold locality. -/
def CMIVPositiveClockStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (D : CMIVSetting S),
    ¬ FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V → Nonempty (CMIVClock D)

/-- Remaining tilt-locality input, at finite reference-driving stops through
the regularized exit. This includes the terminal stop, where passage from below is needed. -/
def CMIVTiltLocalityStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (D : CMIVSetting S) (C : CMIVClock D)
    (τ : S → WithTop ℝ≥0) (_hτ : IsStoppingTime (drivingFiltration D.tilt C.killed) τ),
    (∀ᵐ ω ∂D.tilt, (τ ω : ℝ≥0∞) ≤ C.e ω ∧ τ ω ≠ ⊤) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField D.tilt

end InteractingSLE.Restart.FlowStopIdentCMI
