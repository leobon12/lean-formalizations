/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase
import InteractingSLE.Spec.Supplement.SBLuDense
import InteractingSLE.Spec.Supplement.SB2McPart

/-!
# B's stopped stage piece in `IsStageS2`'s orientation

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`). **`stopTrace_facts`**: for a regular piece `e` and `0 < t < ζ`, the
driver stopped at `min t ζ = t` (the form of `Mi.sb2StopDrv`) is continuous from `0`, and its negation has a global
Loewner trace equal to the reflected chosen trace `ρ ∘ trOf e` on `[0, t]` (`BW1Prop.exists_frozen_trace_close`, the
reflection `Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace`).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Sx

/-- **B's stopped piece**: continuity of the stopped driver and the reflected global trace of its negation. -/
theorem stopTrace_facts {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hpr : GW1P.PieceRegular e.1 e.2) {t : ℝ≥0} (ht0 : 0 < t)
    (hte : (t : ℝ≥0∞) < e.2) :
    Continuous (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) e.2)).toNNReal) ∧
      (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) e.2)).toNNReal) 0 = 0 ∧
      ∃ η : ℝ → ℂ,
        IsLoewnerTrace (fun x : ℝ => -e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) e.2)).toNNReal) η ∧
        ∀ r ∈ Icc (0 : ℝ) t, η r = LP.reflectC (LuM.trOf e r.toNNReal) := by
  have hmin : min (t : ℝ≥0∞) e.2 = t := min_eq_left hte.le
  simp only [hmin]
  have hα : IsGeneratingTrace e.1 t (LuM.trOf e) := Lk.isGeneratingTrace_mono (LuM.isGeneratingTrace_trOf hpr) hte.le
  have hw : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ t} := hpr.2.1.mono fun s hs => le_trans hs hte.le
  obtain ⟨αr, hαr, heq⟩ := BW1Prop.exists_frozen_trace_close hα hw hpr.1 ht0
  refine ⟨(CounterflowRange.continuous_stopped hw).comp continuous_real_toNNReal, ?_, fun r => LP.reflectC (αr r),
    Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hαr, fun r hr => by
      show LP.reflectC (αr r) = _
      rw [heq r hr]⟩
  show e.1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (t : ℝ≥0∞)).toNNReal = 0
  have h0 : min (0 : ℝ≥0∞) (t : ℝ≥0∞) = 0 := min_eq_left zero_le
  rw [Real.toNNReal_zero, ENNReal.coe_zero, h0, ENNReal.toNNReal_zero]
  exact hpr.1

end InteractingSLE.Theorem14.SB.Sx
