/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseRead

/-!
# Deterministic surviving observation points on bounded capacity horizons

PROVE-POCKET-SIDEIN. Reuse the uniform-height forward existence theorem
for a driver continuous only before its lifetime. One fixed point per
integer horizon works for every driver; no path-dependent choice is needed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

/-- The deterministic observation point at height `4 * (N + 1)`. -/
def capacityProbePoint (N : ℕ) : ℂ := PhaseClause.farPt (4 * N + 3)

theorem capacityProbePoint_im (N : ℕ) :
    (capacityProbePoint N).im = 4 * ((N : ℝ) + 1) := by
  simp only [capacityProbePoint, PhaseClause.farPt, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

/-- There is a larger finite time still inside both the lifetime and the
chosen capacity horizon. This is an order interval, not a visit witness. -/
theorem exists_larger_live_capacity {T : ℝ≥0∞} {t B : ℝ≥0}
    (htT : (t : ℝ≥0∞) < T) (htB : t < B) :
    ∃ r : ℝ≥0, t < r ∧ (r : ℝ≥0∞) < T ∧ r < B := by
  obtain ⟨r₀, htr₀, hr₀T⟩ := WithTop.lt_iff_exists_coe_btwn.1 htT
  obtain ⟨r, htr, hrr⟩ := exists_between (lt_min (WithTop.coe_lt_coe.1 htr₀) htB)
  exact ⟨r, htr, lt_of_le_of_lt
    (WithTop.coe_le_coe.2 (hrr.le.trans (min_le_left _ _))) hr₀T,
    hrr.trans_le (min_le_right _ _)⟩

/-- The chosen point survives every live time below its integer horizon.
Only pre-lifetime continuity of the driver is used. -/
theorem capacityProbePoint_mem_active {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) {N : ℕ} {t : ℝ≥0}
    (htT : (t : ℝ≥0∞) < T) (htN : t < (N : ℝ≥0) + 1) :
    capacityProbePoint N ∈ H \ QuantumZipper.fwdHull (Ito.rpath w) t := by
  obtain ⟨r, htr, hrT, hrN⟩ := exists_larger_live_capacity htT htN
  have hy : 0 < 4 * ((N : ℝ) + 1) := by positivity
  have hBound : (r : ℝ) ≤ (4 * ((N : ℝ) + 1)) ^ 2 / 8 := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hr : (r : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hrN
    nlinarith only [hN, hr, sq_nonneg (N : ℝ)]
  have hSol := PhaseClause.exists_isForwardSol_rpath_of_im_ge
    hw hrT hy (le_of_eq (capacityProbePoint_im N).symm) hBound
  exact ⟨by change 0 < (capacityProbePoint N).im; rw [capacityProbePoint_im]; exact hy,
    QuantumZipper.LoewnerAlgebra.not_mem_fwdHull_of_sol
      t.coe_nonneg (NNReal.coe_lt_coe.2 htr) hSol⟩

end InteractingSLE.Sec7.PocketStopSide
