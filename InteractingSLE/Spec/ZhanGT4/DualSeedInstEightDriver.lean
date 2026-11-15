/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstStopped

/-!
# The actual Eight stopped driver

Packet PROVE-ZHAN-GT4-A22. The Brownian driver used above is literally
the rectangle-wise `frzPath`, including negative real times.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4

/-- The two conventions for extending a stopped original driver agree. -/
theorem seedStoppedDriver_eq_frzPath {Ω : Type*} (σ p : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) (ω : Ω) :
    seedStoppedDriver σ p B T ω = A1EightSeed.frzPath (fun u ω => σ * B u ω) p (T ω) ω := by
  funext u
  have he : (max 0 (min u (T ω : ℝ))).toNNReal = min u.toNNReal (T ω) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (le_max_left _ _), NNReal.coe_min, Real.coe_toNNReal']
    calc
      max 0 (min u (T ω : ℝ)) = min (max 0 u) (max 0 (T ω : ℝ)) := max_min_distrib_left _ _ _
      _ = min (max u 0) (T ω : ℝ) := by rw [max_eq_right (T ω).coe_nonneg, max_comm 0 u]
  simp only [seedStoppedDriver, A1EightSeed.frzPath, A1Ref.stopDrv, Strip.extPath, he]

end InteractingSLE.ZhanGT4
