/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetEndLimit
import InteractingSLE.Spec.Sec5.Aux61R45ClockAssembly

/-!
# Finite driver left limits for every clock source

Packet PROVE-T15-RET2. PROVE-AUX61-R45's clock constructors for an arbitrary `ClockSource`
(`exists_adapted_driver`, `exists_referenceClock`) take the named input `hU_leftLimit`: almost surely the actual
driver has a finite left limit at a finite positive source lifetime. A clock source carries a driver continuous before
its lifetime from `0` (`regular`) and a continuous generating trace through the lifetime (`trace`), so the deterministic
`Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace` gives that input for **every** clock source
(`ClockSource.ae_leftLimit_of_trace`). The two constructors without it: `exists_adapted_driver_of_trace`,
`exists_referenceClock_of_trace`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61R45.ClockSource

variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- **Every clock source has finite driver left limits at a finite positive lifetime** (no named input). -/
theorem ae_leftLimit_of_trace :
    ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = D.U ω →
      ∃ c : ℝ, Tendsto (D.W₀ · ω) (𝓝[<] T) (𝓝 c) := by
  filter_upwards [D.regular, D.trace] with ω hr hg T hT hTU
  rw [← hTU] at hr hg
  exact Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace hg hr.1 hr.2 hT

/-- `exists_adapted_driver` without its named input `hU_leftLimit`. -/
theorem exists_adapted_driver_of_trace {e : S → ℝ≥0∞}
    (heU : ∀ ω, e ω ≤ D.U ω)
    (hest : IsStoppingTime D.driving fun ω => (e ω : WithTop ℝ≥0))
    (hpos : ∀ᵐ ω ∂D.P, 0 < e ω) :
    ∃ W : ℝ≥0 → S → ℝ, (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous (W · ω)) ∧
      StronglyAdapted D.driving W ∧
      ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω :=
  D.exists_adapted_driver heU hest hpos D.ae_leftLimit_of_trace

/-- `exists_referenceClock` without its named input `hU_leftLimit`; the announcement of the source lifetime and
the interior condition remain. -/
theorem exists_referenceClock_of_trace (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ)
    {V : Set ℂ} (hV : IsOpen V) (hVc : Vᶜ.Nonempty) (hstart : (D.y : ℂ) ∈ V)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J D.y θ)
      (flowLineRhoR κ b J D.y θ) 0 (flowLineXL b J D.y) (flowLineXR b J D.y))
    {R : ℕ → S → ℝ≥0} (hU_announcing : Coupling.IsAnnouncingSeq D.driving D.P D.U R)
    (hinterior : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < D.U ω →
      D.Γ ω t ∈ QuantumZipper.H) :
    Nonempty (ReferenceClock D κ b J θ V) :=
  D.exists_referenceClock κ b J θ hV hVc hstart hseed hU_announcing D.ae_leftLimit_of_trace hinterior

end InteractingSLE.Sec5.Aux61R45.ClockSource
