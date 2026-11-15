/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR10Comparison
import InteractingSLE.Spec.Restart.StoppedCont

/-!
# Actual slow-comparison windows from the local stopped SDE

The landed continuation theorem supplies the full finite-force model
and its projection. Thus a local physical SDE through the recording stop
already gives the required slow window, without any model-law input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem GW2TipSystem.RootN4 GW2TipSystem.RootL6
  GW2TipSystem.RootV7 Sec5

/-- The stopped SDE supplies the slow comparison outright: its continuation,
probability space, projection and first-zero restart window are all constructed.
The physical sample may stop strictly earlier than the local SDE. -/
theorem exists_slowWindow_of_stoppedEvolution {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {nL₀ nR₀ : ℕ}
    (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (mL mR : ℕ)
    (φ : ℕ → ℝ) (hφ : ∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (xL : Fin (mL + nL₀) → ℝ) (xR : Fin (mR + nR₀ + 1) → ℝ)
    (a : ℝ) (hy : (a, xL, xR) ∈ Prop59Stage.startsU)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (mL + nL₀) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (mR + nR₀ + 1) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL xR
      (angleWordL κ φ mL ρL₀) (angleWordR κ φ mR ρR₀) P 𝓕 W VL VR B V)
    (hc : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T))
    {sample : Ω → DriverRecord} (hsample : Measurable sample)
    (hstop : ∀ᵐ ω ∂P, (sample ω).1 ≤ V ω)
    (hread : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ω).1 →
      (sample ω).2 q = a + W q ω) :
    ∃ win : RootS5.RestartWindow.{u} κ (Prop59Stage.stageDriftBound κ ρL₀ ρR₀)
      (Icc (-angleWeightBound κ) (angleWeightBound κ)),
      win.e.P win.slowEvent ≤ (P.map sample) slowSet := by
  obtain ⟨Ω', mΩ', P', hP', π, hπ, 𝓕', W', VL', VR', B', ζ', hmarginal, hE', hag⟩ :=
    Restart.StoppedCont.stoppedContinuationStatement hκ xL xR
      (angleWordL κ φ mL ρL₀) (angleWordR κ φ mR ρR₀) hy.2.2.1
      P 𝓕 W VL VR B V hE hc
  let e : EvolutionData.{u} (mL + nL₀) (mR + nR₀ + 1) :=
    ⟨Ω', mΩ', P', 𝓕', W', VL', VR', B', ζ'⟩
  let model : AngleModel.{u} κ ρL₀ ρR₀ :=
    { mL := mL, mR := mR, φ := φ, hφ := hφ, xL := xL, xR := xR,
      a := a, hy := hy, e := e, hE := hE', buffer := fun _ => ⊤,
      bufferMeas := measurable_const }
  have hstop' : ∀ᵐ ξ ∂P', (sample (π ξ)).1 ≤ V (π ξ) :=
    ae_of_ae_map hπ.aemeasurable (hmarginal.symm ▸ hstop)
  have hread' : ∀ᵐ ξ ∂P', ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (sample (π ξ)).1 →
        (sample (π ξ)).2 q = a + W q (π ξ) :=
    ae_of_ae_map hπ.aemeasurable (hmarginal.symm ▸ hread)
  apply exists_slowWindow_on_extension hκ hκ4 model hπ hmarginal hsample
  · filter_upwards [hstop', hag] with ξ hs hξ
    change (sample (π ξ)).1 ≤ min ⊤ (ζ' ξ)
    rw [min_top_left]
    exact hs.trans hξ.1
  · filter_upwards [hstop', hread', hag] with ξ hs hr hξ
    intro q hq
    change (sample (π ξ)).2 q = a + W' q ξ
    rw [hr q hq, (hξ.2 q (hq.trans_le hs)).1]

end InteractingSLE.Theorem14.GW2JDetR10
