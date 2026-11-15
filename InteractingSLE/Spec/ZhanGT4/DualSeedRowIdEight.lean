/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdRecord

/-!
# The actual Eight rectangle field and its original source charge

Packet PROVE-ZHAN-GT4-A22. Identify the landed `eightRec` field with the
concrete first-view field and compute the exact amalgamated original charge.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4

/-- The two Eight seeds fuse to zero original opposite charge. The opposite
reference marginal is the ordinary large-parameter chordal driving law. -/
theorem mirrorSourceCharge_eightRR {κ : ℝ} (hκ : A2X.kh κ ≠ 0) :
    mirrorSourceCharge (A2X.kh κ) (A1EightSeed.eightRR κ) = 0 := by
  have hk : κ ≠ 0 := by
    intro he
    subst κ
    norm_num [A2X.kh] at hκ
  simp only [mirrorSourceCharge, A1EightSeed.eightRR, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, A2X.smallEightRhoL, A2X.smallEightRhoR]
  field_simp [hk]
  ring

/-- On its rectangle, the actual Eight field is the field of the single
second driver stopped at the rectangle exit. Equality holds at every first
time, since the underlying records are identical. -/
theorem eightHeightField_eq_seedSView {X Y : Type*} (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ)
    (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (W₂ : ℝ≥0 → Y → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) (T : Y → ℝ≥0)
    (hc : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (T y)))
    (h0 : ∀ y, W₂ 0 y = 0) (s : ℝ) (t : ℝ≥0) (y : Y) :
    seedHeightField (A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (min (t : ℝ) (T y)) =
      seedHeightField (fun v y => seedSView (A2X.kh κ) (A1EightSeed.eightRR κ)
        (A1EightSeed.eightDrv W₁ S₁ m x) (A1EightSeed.frzPath W₂ p (T y) y)
        (seedSrcClock (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) (A1EightSeed.frzPath W₂ p (T y) y))
        (seedSrcDriver (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) (A1EightSeed.frzPath W₂ p (T y) y))
        (A1EightSeed.eightMarks VL₁ VR₁ x) v) y s (min (t : ℝ) (T y)) := by
  unfold seedHeightField
  rw [eightRec_eq_seedSView κ p W₁ VL₁ VR₁ W₂ S₁ m x y (hc y) (h0 y)
    (le_min t.coe_nonneg (T y).coe_nonneg) (min_le_right _ _)]

end InteractingSLE.ZhanGT4
