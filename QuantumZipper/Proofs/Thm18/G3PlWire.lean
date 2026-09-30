import QuantumZipper.Proofs.Thm18.G3PlMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): wiring

`g3TWedgePlainStmt_of_honest : G3PlHonestStmt → G3TWedgePlainStmt`, and T5-G from curve removal
and the honest comparison (`g3TWedgeGeoStmt_of_curve_honest`). Window order as in D85: fixed
`δ` (from the honest comparison), small `U`, the margin `m`, small `η < m`, the weight bound
`M = Z/U`, large `L`. Own `ε`-bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- ENNReal arithmetic of the wiring. -/
theorem g3pl_arith2 {u K H B e : ℝ≥0∞} (hu0 : u ≠ 0) (hut : u ≠ ⊤) (hB : B ≤ u * e)
    (hKH : K ≤ H + B) : u⁻¹ * K ≤ u⁻¹ * H + e := by
  have h1 : u⁻¹ * B ≤ e := by
    calc u⁻¹ * B ≤ u⁻¹ * (u * e) := by gcongr
      _ = e := by rw [← mul_assoc, ENNReal.inv_mul_cancel hu0 hut, one_mul]
  calc u⁻¹ * K ≤ u⁻¹ * (H + B) := by gcongr
    _ = u⁻¹ * H + u⁻¹ * B := by rw [mul_add]
    _ ≤ u⁻¹ * H + e := by gcongr

/-- ENNReal arithmetic of the wiring. -/
theorem g3pl_arith {u K H J B e : ℝ≥0∞} (hu0 : u ≠ 0) (hut : u ≠ ⊤) (hB : B ≤ u * e)
    (hHK : H ≤ K + B) (hJH : u⁻¹ * J ≤ u⁻¹ * H + e) : u⁻¹ * J ≤ u⁻¹ * K + e + e := by
  have h1 : u⁻¹ * B ≤ e := by
    calc u⁻¹ * B ≤ u⁻¹ * (u * e) := by gcongr
      _ = e := by rw [← mul_assoc, ENNReal.inv_mul_cancel hu0 hut, one_mul]
  calc u⁻¹ * J ≤ u⁻¹ * H + e := hJH
    _ ≤ u⁻¹ * (K + B) + e := by gcongr
    _ = u⁻¹ * K + u⁻¹ * B + e := by rw [mul_add]
    _ ≤ u⁻¹ * K + e + e := by gcongr

end R18
end QuantumZipper
