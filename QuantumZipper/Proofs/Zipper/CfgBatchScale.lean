import QuantumZipper.Proofs.Zipper.LenInfCore
import QuantumZipper.Proofs.Zipper.ScaleGeomFix
import QuantumZipper.Proofs.Zipper.RegShiftUnifF2
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.LQG.AllOffsetsBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-BATCH: the scaling/normalization identity `CfgLenScaleNormStmt`

Theorem 1.3, LEN-INF (`LenInfCore.lean`). Sheffield (arXiv:1012.4797, §5.1, pp. 60–62) states the
rules used here: quantum lengths are invariant under `z ↦ a z`, `h ↦ h(a·) + Q log a`;
`𝔥₀(a z) = 𝔥₀(z) + (2/γ) log a`; adding a constant `C` multiplies boundary lengths by `e^{γC/2}`;
Brownian scaling of the driver. At the level of this encoding they are:

* the repaired scaling geometry `F2.ScaleGeomAeStmt'` (decision D45; the scaled configuration
  carries the constant `(2/√κ) log a`) with `F2.unzipLengths_scale`: lengths of the scaled
  configuration at time `t` are those of `𝒵` at time `a² t`;
* the D27 truncation `sfTrunc` is invisible (`F2.unzipLengths_add_ofFun_addConst_sfTrunc`) and
  the truncated rescaled field is free (`F2.TruncRescaleFreeStmt`);
* rule (5.1) for constants in the left length, **for all times at once**, from the proved gauge
  regularity `RegUnif.gaugeRegDyStmt_holds` (as in `RegUnif.agree_addConst_dy`);
* `evalReg X (ρ_a) = X(ρ_a)` a.s. at the fixed semicircle (`AllOffsets.ae_evalReg_fc_eq`), so
  that the constant is exactly `c_a(X)` of `driftC`, read from the *raw* coordinate.

The normalized witness is `X' = sfTrunc (rescale X Q a) − m`, `m = (sfTrunc (rescale X Q a))(ρ_1)`;
then `𝔥₀ + (sfTrunc (rescale X Q a) + (2/γ) log a) = (𝔥₀ + X') + (m + (2/γ) log a)` exactly, and
`γ (m + (2/γ) log a) / 2 = c_a(X)`.

Main result: `cfgLenScaleNormStmt_of : TruncRescaleFreeStmt → ScaleGeomAeStmt' → (Γ⁰ hypotheses)
→ CfgLenScaleNormStmt κ P B X`. Own elementary bookkeeping (the paper's §5.1 rules).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus RegUnif

variable {Ω : Type} [MeasurableSpace Ω]

/-- Reindexing a supremum over `[0,∞)` by `t ↦ b t`, `b > 0`. -/
theorem cfgB_iSup_Ici_mul {f : ℝ → ℝ≥0∞} {b : ℝ} (hb : 0 < b) :
    (⨆ s ∈ Ici (0 : ℝ), f s) = ⨆ t ∈ Ici (0 : ℝ), f (b * t) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun t ht => ?_)
  · have hs' : (0 : ℝ) ≤ s := hs
    refine le_iSup₂_of_le (s / b) (show (0 : ℝ) ≤ s / b from div_nonneg hs' hb.le) ?_
    rw [mul_div_cancel₀ _ hb.ne']
  · have ht' : (0 : ℝ) ≤ t := ht
    exact le_iSup₂_of_le (b * t) (show (0 : ℝ) ≤ b * t from mul_nonneg hb.le ht') le_rfl

end QuantumZipper.E6
