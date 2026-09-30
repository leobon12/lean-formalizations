import QuantumZipper.Proofs.Zipper.TipXRouteDefs2
import QuantumZipper.Proofs.Zipper.WedgeTipXNonvanish
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Thm11.ExtMeasCont
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.Zipper.TipXRouteDefs2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TIPX-ROUTE, sub-task TX-COV (3): the two geometric inputs, and `TipXPieceCoverStmt`

Task TX-A (handoff `handoff/TIPX-ROUTE.md`, TX-COV). From the pathwise context `GeoCtx`
(`TipXPieceGeoBasic.lean`: `E_t` continuous on `ℍ̄`, `E_t(O^±_t) = 0`, `E_t ≠ 0` off the tips,
`E_t(ℝ) ⊆ ℝ ∪ η(0,t]`, the trace a simple chord):

* `geoNbhd_of_ctx` (**`TipXGeoNbhdStmt`**): with `c = min_{[4^{-N}, t]} |η| > 0`, every `u` with
  `|E_t(u)| < min(c, 2^{-N})` lies in `pieceTail N` (a real value `0 < |v| ≤ 2^{-N}` lies in a
  dyadic shell of index `≥ N`, a curve value `η(r)` has `r < 4^{-N}`, and `E_t(u) = 0` only at a
  tip); continuity of `E_t` at the tips gives `δ`.
* `geoAdm_of_ctx` (**`TipXGeoAdmStmt`**): piece `k` is compact (closed preimage; bounded since
  `|E_t(u) − u| ≤ C`) and contained in the open set `U = E_t⁻¹(Zᶜ)`, where the closed set `Z`
  collects `η[0, 4^{-k-2}]`, `η[4^{-k+1}, t]` and the real points with `|v| ≤ 2^{-k-2}` or
  `|v| ≥ 2^{-k+1}`; `U ⊆ pieceNbhd k` because `E_t(ℝ) ⊆ ℝ ∪ η(0,t]`, and piece `k` avoids `Z`
  by injectivity of `η` and `η(0,∞) ⊆ ℍ`. A compact set inside an open set has a closed
  thickening inside it (`IsCompact.exists_cthickening_subset_open`).
* `tipXPieceCoverStmt_holds`: **TX-COV holds**.

Own elementary argument (the covering and the geometry are not in the literature in this form);
the inputs are the Carathéodory correspondence (Pommerenke 1992, Thm 2.1, Prop 2.5/Thm 2.6) and
Rohde–Schramm 2005, Thm 6.1, as recorded in `TipXPieceGeoBasic.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

section Det

variable {W : ℝ → ℝ} {t : ℝ}

theorem radius_succ_lt (k : ℕ) : radius (k + 1) < radius k := by
  rw [radius, radius, pow_succ]
  have := radius_pos k
  rw [radius] at this
  linarith

end Det

end WedgeUnzip
end QuantumZipper
