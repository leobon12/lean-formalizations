import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeLogImDom
import QuantumZipper.Proofs.Zipper.UnifGaugeNodes
import QuantumZipper.Proofs.LQG.FractionalMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TIPX-ROUTE, sub-task TX-DEF: capacity pieces, covering and moment statements

Task TX-A (handoff `handoff/TIPX-ROUTE.md`, decision D51). Notation: `E_t = F2.extInv W t`
(`= f_t⁻¹`, extended to `ℝ`), `η = trace W`, `O^±_t` the tips (`tipSet`).

## Definitions (time-`t` picture, all subsets of `ℝ`)
* `capPre W t a b`: the `E_t`-preimage of the curve piece `η[a, b]`;
* `bdryPre W t a b`: the `E_t`-preimage of the boundary pieces `{v ∈ ℝ : a ≤ |v| ≤ b}`;
* `piece W t k`: the `k`-th piece, preimage of `η[4^{-k-1}, 4^{-k}]` (both sides) and of
  `±[2^{-k-1}, 2^{-k}]`;
* `pieceTail W t k = (⋃_{m ≥ k} piece m) ∪ {O^±_t}`;
* `pieceNbhd W t k`: preimage of `η[4^{-k-2}, 4^{-k+1}]` and `±[2^{-k-2}, 2^{-k+1}]`, i.e. the
  pieces `k-1, k, k+1` (for `k = 0` the "piece `-1`" `η[1,4] ∪ ±[1,2]` is used, so that no natural
  number subtraction enters);
* `pieceAdm W t k r`: the level `r > 0` is **admissible** for piece `k` (`cthickening r (piece k)`
  stays in `pieceNbhd k`); `pieceAdmUpTo W t k r`: admissible for all pieces `j ≤ k`
  (this is "`r ≤ σ_k(t)`" with the monotone scale `σ_k = min_{j ≤ k}` of the handoff);
* `pieceLam W k = min_{[4^{-k-2}, 4^{-k+1}]} |η| ∧ 2^{-k-2}` (the weight scale `λ_k`);
* `pieceA`, `pieceT`: the per-time quantities `A_k(t)` (weighted mass of piece `k` at all levels
  `r ≤ σ_k(t)`) and `T_k(t)` (weighted mass of the tail `≥ k+1` at the levels `r ≤ σ_k(t)` that are
  not admissible for piece `k+1`);
* `pieceSupA`, `pieceSupT`: their suprema over the window `t ∈ [s, T]`.

## Statements
* `TipXPieceCoverStmt` (TX-COV, pathwise): a.s., for every field `x`, every `t > 0` and `N`, some
  `δ > 0` makes `Σ_j (A_{j+N}(t) + T_{j+N}(t))` an eventual (along `goodFilter`) upper bound of the
  weighted mass of the `δ`-neighbourhood of the tips.
* `TipXPieceMomStmt` (TX-SC/TX-U1/TX-U2, normalized samples): a.e.-measurable majorants `A_k`,
  `T_k` of the window suprema (for `k ≥ k₀`) with `E[A_k^p], E[T_k^p] ≤ C ρ^k`.
* `TipYWPieceStmtN`: `TipYWPieceStmt` for gauge-normalized samples (`RegUnif.IsNrmSample`).

Proved here (own elementary bookkeeping): `tipYWPieceN_of_cover_mom`.

**Deviation from the handoff (recorded in the report):** the handoff defines `pieceSupA/T` as
suprema over *rational* times for a.e.-measurability. Then the covering at a real time `t` would
need a continuity-in-time argument that is not available. Here the suprema run over all real
`t ∈ [s, T]` and all real levels, and a.e.-measurability is moved into `TipXPieceMomStmt`, which
asks for a.e.-measurable **majorants** of these suprema (what the transport argument produces:
bounds uniform in `t`). Nothing is weakened.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## Pieces -/

/-! ## Per-piece quantities -/

/-! ## Statements -/

/-! ## Bookkeeping -/

/-- Tails of a nonnegative series decrease: `Σ_j f (j + M) ≤ Σ_j f (j + N)` for `N ≤ M`. -/
theorem tsum_tail_mono_of_le (f : ℕ → ℝ≥0∞) {N M : ℕ} (h : N ≤ M) :
    ∑' j, f (j + M) ≤ ∑' j, f (j + N) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : ∀ j : ℕ, f (j + (N + d)) = (fun j => f (j + N)) (j + d) := fun j => by
    show f (j + (N + d)) = f (j + d + N)
    rw [Nat.add_right_comm, Nat.add_assoc]
  rw [tsum_congr e]
  exact ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective d) (fun j => f (j + N))

end WedgeUnzip
end QuantumZipper
