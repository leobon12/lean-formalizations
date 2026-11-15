/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GHistGauss
import InteractingSLE.Spec.Sec5.Aux61GContData
import InteractingSLE.Spec.Sec6.Prop61Mean

/-! # Reference continuation of a localized initial mean

Outside the selected history event the distribution is chosen to be the
reference mean. Thus the boundary identification required by the cutoff
construction holds there automatically.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GHist
open Aux61Fib (FibData FibCode)
open Aux61ChLoc (IsChartGaussAt)

/-- The initial reference harmonic function read as a distribution. -/
def referenceDist (d : FibData) : DistOn upperHalfPlaneOpens :=
  smoothDist upperHalfPlaneOpens (Aux61GlueK.refMean0 d)

theorem referenceDist_harmonic (d : FibData) : IsHarmonicDistOn (referenceDist d) H :=
  WholeField.isHarmonicDistOn_smoothDist (Aux61GlueK.refMean0_ext d).1

theorem referenceDist_apply (d : FibData) (ψ : TestOn upperHalfPlaneOpens) :
    referenceDist d ψ = ∫ z, Aux61GlueK.refMean0 d z * ψ z :=
  Coupling.smoothDist_apply_eq
    (fun z hz => ((Aux61GlueK.refMean0_ext d).1 z hz).1.continuousAt.continuousWithinAt) ψ

/-- Every harmonic representative of the reference distribution equals
the reference function on H. -/
theorem eqOn_reference_of_pairings (d : FibData) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v H)
    (hrep : ∀ ψ : TestOn upperHalfPlaneOpens, referenceDist d ψ = ∫ z, v z * ψ z) :
    EqOn v (Aux61GlueK.refMean0 d) H := by
  apply Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl hv
    (Aux61GlueK.refMean0_ext d).1
  intro ψ _
  exact (hrep ψ).symm.trans (referenceDist_apply d ψ)

universe u
variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β] {μ : Measure X} [IsFiniteMeasure μ]
  {Z : X → β} {B : Set β} {Y : X → FibCode}
  {h₀ : X → DistOn upperHalfPlaneOpens}

/-- The history factor may equal the actual mean on B and the reference
mean off B, preserving the initial Gaussian law and almost-sure harmonicity. -/
theorem exists_reference_history_factor (d : FibData) (hZ : Measurable Z)
    (hY : Measurable Y) (hB : MeasurableSet B) (hh₀ : Measurable[mβ.comap Z] h₀)
    (hG : IsChartGaussAt μ Z B Y 0 𝒢 h₀)
    (hlive : ∀ᵐ x ∂μ, Z x ∈ B → (0 : ℝ≥0∞) < (Y x).life) :
    ∃ T₀ : β → DistOn upperHalfPlaneOpens, Measurable T₀ ∧
      (∀ x, Z x ∈ B → T₀ (Z x) = h₀ x) ∧
      (∀ b ∉ B, T₀ b = referenceDist d) ∧
      (∀ᵐ b ∂μ.map Z, IsHarmonicDistOn (T₀ b) H) ∧
      IsChartGaussAt μ Z B Y 0 𝒢 (fun x => T₀ (Z x)) := by
  obtain ⟨T, hT, he, -, hharm, -⟩ :=
    exists_initial_harmonic_history_factor hZ hY hB hh₀ hG hlive
  classical
  let T₀ : β → DistOn upperHalfPlaneOpens := B.piecewise T (fun _ => referenceDist d)
  have hT₀ : Measurable T₀ := hT.piecewise hB measurable_const
  have he₀ : ∀ x, Z x ∈ B → T₀ (Z x) = h₀ x := by
    intro x hx
    exact (piecewise_eq_of_mem B T _ hx).trans (he x hx)
  refine ⟨T₀, hT₀, he₀, fun b hb => piecewise_eq_of_notMem B T _ hb, ?_, ?_⟩
  · filter_upwards [hharm] with b hb
    by_cases hbB : b ∈ B
    · simpa only [T₀, piecewise_eq_of_mem B T _ hbB] using hb
    · rw [show T₀ b = referenceDist d from piecewise_eq_of_notMem B T _ hbB]
      exact referenceDist_harmonic d
  · exact isChartGaussAt_of_mean_eqOn hY hB hG
      (hT₀.comp (Measurable.of_comap_le hG.marksZ)) he₀

end InteractingSLE.Sec5.Aux61GHist
