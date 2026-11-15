/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzStage
import InteractingSLE.Spec.Supplement.GW2RzAdapt

/-!
# GW2's open lines: the root-`x` stage capacities as real functions

Packet PROVE-GW2-STAGEMEAN, R121 round. With a finite cap `V`, the root-`x` line clock capped by `V` read as `ℝ≥0`:

* `capA`: `A u = (min (physClockX (T + u)) V).toNNReal`; `capA_zero`: `A 0` is the stage start;
* **`continuous_capA`**, `monotone_capA`, `stgStart_le_capA`;
* **`coe_toNNReal_stgClockX`**: the stage clock (as a real) is `A t − a₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Psm

open GW2Rz

variable {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  {V : Ω → ℝ≥0∞}

/-- The root-`x` line clock at `T + u`, capped by `V`, as `ℝ≥0`. -/
def capA (x₀ : ℝ) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (V : Ω → ℝ≥0∞)
    (T u : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (physClockX x₀ s Wα ζα W GT (T + u) ω) (V ω)).toNNReal

theorem capA_zero (T : ℝ≥0) (ω : Ω) : capA x₀ s Wα ζα W GT V T 0 ω = stgStartX x₀ s Wα ζα W GT V T ω := by
  simp only [capA, add_zero, stgStartX, stgStartMX]

section Cont

variable (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

include hGT hs₀ hx₀ in
theorem continuous_capA (T : ℝ≥0) {ω : Ω} (hV : V ω ≠ ⊤) :
    Continuous fun u => capA x₀ s Wα ζα W GT V T u ω := by
  have hc : Continuous fun u : ℝ≥0 => min (physClockX x₀ s Wα ζα W GT (T + u) ω) (V ω) :=
    (continuous_min_physClockX hGT hs₀ hx₀ ω).comp (continuous_const.add continuous_id)
  have hne : ∀ u : ℝ≥0, min (physClockX x₀ s Wα ζα W GT (T + u) ω) (V ω) ≠ ⊤ := fun u =>
    ne_top_of_le_ne_top hV (min_le_right _ _)
  refine continuous_iff_continuousAt.2 fun u => ?_
  exact (ENNReal.tendsto_toNNReal (hne u)).comp hc.continuousAt

include hGT hs₀ hx₀ in
theorem monotone_capA (T : ℝ≥0) {ω : Ω} (hV : V ω ≠ ⊤) : Monotone fun u => capA x₀ s Wα ζα W GT V T u ω := by
  intro u v huv
  have h : min (physClockX x₀ s Wα ζα W GT (T + u) ω) (V ω) ≤ min (physClockX x₀ s Wα ζα W GT (T + v) ω) (V ω) :=
    monotone_min_physClockX hGT hs₀ hx₀ (V := V) ω (add_le_add le_rfl huv)
  exact ENNReal.toNNReal_mono (ne_top_of_le_ne_top hV (min_le_right _ _)) h

include hGT hs₀ hx₀ in
theorem stgStart_le_capA (T : ℝ≥0) {ω : Ω} (hV : V ω ≠ ⊤) (u : ℝ≥0) :
    stgStartX x₀ s Wα ζα W GT V T ω ≤ capA x₀ s Wα ζα W GT V T u ω := by
  rw [← capA_zero T ω]
  exact monotone_capA hGT hs₀ hx₀ T hV zero_le

include hGT hs₀ hx₀ in
/-- **The stage clock is `A t − a₀`.** -/
theorem coe_toNNReal_stgClockX (T t : ℝ≥0) {ω : Ω} (hV : V ω ≠ ⊤) :
    ((stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal : ℝ) =
      (capA x₀ s Wα ζα W GT V T t ω : ℝ) - stgStartX x₀ s Wα ζα W GT V T ω := by
  have hle := stgStartM_leX hGT hs₀ hx₀ (V := V) T t ω
  have hne1 : min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) ≠ ⊤ :=
    ne_top_of_le_ne_top hV (min_le_right _ _)
  have hne0 : stgStartMX x₀ s Wα ζα W GT V T ω ≠ ⊤ := ne_top_of_le_ne_top hne1 hle
  unfold stgClockX capA stgStartX
  rw [ENNReal.toNNReal_sub hne0, NNReal.coe_sub (ENNReal.toNNReal_mono hne1 hle)]

end Cont

end InteractingSLE.Theorem14.GW2Psm
