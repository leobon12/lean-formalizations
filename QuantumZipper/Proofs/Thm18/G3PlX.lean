import QuantumZipper.Proofs.Thm18.G3PlWire
import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.G2FixMixRoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): the honest Palm window in boundary-point form

The honest Palm-window integral `g3plHon` (Palm length `ℓ` uniform on `(0, U ∧ ν_C[−δ, 0]]`) is
rewritten, by the quantile change of variables `x = lenLeft ν_C ℓ` (`ν_C[x, 0] = ℓ`, no atoms,
positive on intervals), as the integral over boundary points `x < 0` of the window
`ν_C[x, 0] ≤ U ∧ ν_C[−δ, 0]` against `ν_C`, with the length partner `g3zPartner` of
`R18G3Defs` (Sheffield, arXiv:1012.4797, p. 71, Figure 1.7). This is the form of the wedge
integral `g3zWedgePalmCyl0`, so the remaining node `G3PlHonestXStmt` compares the same
Palm-window functional of the wedge and of `h_C`.
Own bookkeeping on top of `g1_setLIntegral_lenLeft_eq_win` (quantile transform).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The honest Palm window of boundary points (capped at `ν_C[−δ, 0]`). -/
def g3plXWin (γ δ U : ℝ) (ω : Ω₀) : Set ℝ :=
  {b | b < 0 ∧ g3plV γ ω (Icc b 0) ≤ ENNReal.ofReal U ∧
    g3plV γ ω (Icc b 0) ≤ g3plV γ ω (Icc (-δ) 0)}

end R18
end QuantumZipper
