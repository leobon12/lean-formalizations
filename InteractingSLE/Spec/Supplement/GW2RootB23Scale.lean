/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Prefix
import InteractingSLE.Spec.Sec7.CounterflowProbDilation
import InteractingSLE.Spec.Sec5.Prop59NodeTreeScale

/-!
# Dilation of the actual observable relative experiment

Packet PROVE-T14-GW2ROOT2. Reuse the landed closed-endpoint generating
trace dilation in the source's `a W(t/a²)` convention. The scaled
driver and tip remain total Borel functions of the retained records.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootB23

open Exist.StagedLaw Sec7.Dilation

/-- The source dilation convention for a closed-endpoint generating trace. -/
theorem isGeneratingTrace_scale {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ) {a : ℝ≥0} (ha : 0 < a) :
    IsGeneratingTrace (fun u => (a : ℝ) * w (u / a ^ 2))
      (((a ^ 2 : ℝ≥0) : ℝ≥0∞) * T) (fun u => ((a : ℝ) : ℂ) * γ (u / a ^ 2)) := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hd := hγ.dilate (inv_ne_zero ha2)
  have hew : Sec7.Dilation.dilPath (a ^ 2)⁻¹ w =
      fun u => (a : ℝ) * w (u / a ^ 2) := by
    funext u
    simp only [Sec7.Dilation.dilPath, NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv,
      Real.sqrt_sq a.coe_nonneg, inv_inv, div_eq_inv_mul]
  have hT : T / (((a ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (((a ^ 2 : ℝ≥0) : ℝ≥0∞) * T) := by
    rw [ENNReal.coe_inv ha2, div_eq_mul_inv, inv_inv, mul_comm]
  rw [hew, hT] at hd
  simpa only [NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv,
    Real.sqrt_sq a.coe_nonneg, inv_inv, div_eq_inv_mul] using hd

/-- The driver in the chart dilated by `a`. -/
def scaledRelativeDriverRead (a s v u : ℝ≥0) (p : RecData × RecData) : ℝ :=
  (a : ℝ) * relativeDriverRead s v (u / a ^ 2) p

/-- The corresponding dilated tip in its dilated capacity time. -/
def scaledRelativeTipRead (a s v u : ℝ≥0) (p : RecData × RecData) : ℂ :=
  ((a : ℝ) : ℂ) * RootA22.relativeTipRead s v (u / a ^ 2) p

def scaledRelativeObservationRead (a s v u : ℝ≥0) (p : RecData × RecData) : ℝ × ℂ :=
  (scaledRelativeDriverRead a s v u p, scaledRelativeTipRead a s v u p)

theorem measurable_scaledRelativeDriverRead (a s v u : ℝ≥0) :
    Measurable (scaledRelativeDriverRead a s v u) :=
  measurable_const.mul (measurable_relativeDriverRead s v (u / a ^ 2))

theorem measurable_scaledRelativeTipRead (a s v u : ℝ≥0) :
    Measurable (scaledRelativeTipRead a s v u) :=
  measurable_const.mul (RootA22.measurable_relativeTipRead s v (u / a ^ 2))

theorem measurable_scaledRelativeObservationRead (a s v u : ℝ≥0) :
    Measurable (scaledRelativeObservationRead a s v u) :=
  (measurable_scaledRelativeDriverRead a s v u).prodMk
    (measurable_scaledRelativeTipRead a s v u)

theorem scaledRelativeDriverRead_zero (a s v : ℝ≥0) (p : RecData × RecData) :
    scaledRelativeDriverRead a s v 0 p = 0 := by
  simp only [scaledRelativeDriverRead, zero_div, relativeDriverRead_zero, mul_zero]

end InteractingSLE.Theorem14.GW2TipSystem.RootB23
