/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC16R7Relift
import InteractingSLE.Spec.Sec7.SideC15ReadyBranch

/-! # R100's zero-offset chart and its inherited source branch

PROVE-SIDE-COLLAR2. Relift the counterflow chart by `2π(n-1)`.
The maps stay fixed and the source branch becomes one. The relift is
measurable in the incoming walls; no partition of the test is used.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC17
open PocketStopSide PocketStopField Aux119Heights SideC12 SideC13

/-- The R100 counterflow frame, with negative-shift integer `1-n`. -/
def zeroFrameChart (c : Chart) (n : ℤ) : Chart := shiftChart c (1 - n)

theorem conjugateFlowMap_zeroFrameChart (c : Chart) (n : ℤ) (z : ℂ) :
    conjugateFlowMap (zeroFrameChart c n) z = conjugateFlowMap c z := rfl

theorem zeroFrameChart_lift (c : Chart) (n : ℤ) (z : ℂ) :
    (zeroFrameChart c n).2.2 z = c.2.2 z + 2 * π * ((n : ℝ) - 1) := by
  simp only [zeroFrameChart, shiftChart, Int.cast_sub, Int.cast_one]
  ring

theorem isDomainChart_zeroFrameChart {D : Set ℂ} {c : Chart}
    (hc : IsDomainChart D c) (n : ℤ) : IsDomainChart D (zeroFrameChart c n) :=
  SideC16.isDomainChart_shiftChart hc (1 - n)

theorem conjugateFlowLift_zeroFrameChart (c : Chart) (n : ℤ) (z : ℂ) :
    conjugateFlowLift (zeroFrameChart c n) z + 2 * π =
      conjugateFlowLift c z + 2 * π * n := by
  dsimp only [conjugateFlowLift, zeroFrameChart, shiftChart]
  simp only [Int.cast_sub, Int.cast_one]
  ring

/-- The actual inherited branch is one after R100's relift, on both
walls and for every prefix in the definition of `IsPocketBranch`. -/
theorem isPocketBranch_zeroFrameChart {L R : ℝ≥0 → ℂ} {c : Chart} {n : ℤ}
    (hn : Lemma71N.IsPocketBranch L R (conjugateFlowChart c) n) :
    Lemma71N.IsPocketBranch L R (conjugateFlowChart (zeroFrameChart c n)) 1 := by
  intro WL WR hL hR ξ s q hsq
  obtain ⟨hl, hr⟩ := hn WL WR hL hR ξ s q hsq
  constructor
  · intro hξ hland
    convert hl hξ hland using 1
    funext y
    change conjugateFlowLift (zeroFrameChart c n) _ + 2 * π * (1 : ℤ) - _ = _
    rw [Int.cast_one, mul_one, conjugateFlowLift_zeroFrameChart]
    rfl
  · intro hξ hland
    convert hr hξ hland using 1
    funext y
    change conjugateFlowLift (zeroFrameChart c n) _ + 2 * π * (1 : ℤ) - _ = _
    rw [Int.cast_one, mul_one, conjugateFlowLift_zeroFrameChart]
    rfl

/-- Relifting preserves the walls-measurable pocket-chart record. -/
theorem isPocketChartOn_zeroFrameChart {Ω : Type*} {𝓦 : MeasurableSpace Ω}
    {A : Set Ω} {D : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart}
    (hc : PocketCoupling.IsPocketChartOn 𝓦 A D ψ c)
    (hDm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ D ω})
    {n : Ω → ℤ} (hn : Measurable[𝓦] n) :
    PocketCoupling.IsPocketChartOn 𝓦 A D ψ (fun ω => zeroFrameChart (c ω) (n ω)) :=
  isPocketChartOn_shift hc hDm (SideC16.measurable_canonicalShift hn)

end InteractingSLE.Sec7.SideC17
