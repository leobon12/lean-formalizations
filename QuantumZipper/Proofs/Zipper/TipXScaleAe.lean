import QuantumZipper.Proofs.Zipper.TipXScaleCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC (scaling), part 5: the scaled configuration and the a.s. per-piece comparison

Task TX-SC (handoff `handoff/TIPX-ROUTE.md`, decision D51). For `a = 2^{-k}` the scaled pair is
`B^{(k)} = a⁻¹ B(a² ·)` (`scB`, a Brownian motion by `IsBrownianReal.smul`) and
`X^{(k)} = nrm (sfTrunc (X(a·) + Q log a))` (`scNrm`): a gauge-normalized free field
(`F2.TruncRescaleFreeStmt`, D27 frontier node; `RegUnif.isFreeGFFModConstH_nrmF`) independent of
`B^{(k)}` (`F2.indepFun_sfTrunc_rescale`, `RegUnif.indepFun_nrmF`). `ae_piece_le_scaled`: a.s.,
for all `t ∈ [0, T']`, `A_k(a² t) ≤ c · A^{(k)}_0(t)` and `T_k(a² t) ≤ c · T^{(k)}_0(t)`.

Own elementary bookkeeping (Brownian scaling: Mörters–Peres, *Brownian Motion*, Lemma 1.7).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

variable {Ω : Type} [MeasurableSpace Ω]

/-- The Brownian motion of the `2^{-k}`-scaled configuration. -/
def scB (k : ℕ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  F2.bmScale ((radius k ^ 2).toNNReal) B

theorem sqrt_toNNReal_radius_sq (k : ℕ) : √(((radius k ^ 2).toNNReal : ℝ≥0) : ℝ) = radius k := by
  rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sqrt_sq (radius_pos k).le]

theorem scB_eq (k : ℕ) (B : ℝ≥0 → Ω → ℝ) :
    scB k B = fun t ω => B (Real.toNNReal (radius k ^ 2) * t) ω / radius k := by
  funext t ω
  simp only [scB, F2.bmScale, sqrt_toNNReal_radius_sq]
  ring

theorem drive_scB (κ : ℝ) (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    drive κ (scB k B) ω = scDrv (radius k) (drive κ B ω) := by
  funext r
  rw [scB_eq]
  simp only [drive, scDrv]
  rw [Real.toNNReal_mul (sq_nonneg _)]
  ring

end WedgeUnzip
end QuantumZipper
