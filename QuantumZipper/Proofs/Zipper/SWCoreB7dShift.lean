import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowMain
import QuantumZipper.Proofs.Zipper.Cor15MarkovFieldLaw
import QuantumZipper.Proofs.Zipper.B5VHccMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (1): the anchored flow maps depend only on the increments after the anchor

For an anchor `q ≥ 0` and `s ≥ q`, the reversed driver `vrev W s` on `[0, s − q]` reads the driver
`W = drive κ B ω` only on `[q, s]`, through increments. Hence the anchored flow maps
`ψ_s = revMapExt (vrev W s) (s − q)` (= `flowFam W q ![s, W s]`) and the window flows
`F_s = realRevMap (vrev W T) (T − s)` are functions of the shifted path
`shiftPath q (pathOf B ω)` alone (`revMapExt_vrev_shift`, `realRevMap_vrev_shift`), through the
driver `shDrv κ q p r = √κ · p ((r − q)⁺)`. This is the independence structure used in the D70
transfer (the anchor field `Y_q` of `cor15UnzipVersionStmt_holds` is independent of the shifted
path). Own elementary bookkeeping.
-/

noncomputable section

open Set
open scoped NNReal

namespace QuantumZipper
namespace SWCore

open B2 RevMapExtension

theorem revMapExt_congr_drive {W W' : ℝ → ℝ} {T : ℝ} (h : EqOn W W' (Icc 0 T)) (z : ℂ) :
    revMapExt W T z = revMapExt W' T z := by
  have hP : IsCRevSol W z T = IsCRevSol W' z T := by
    funext u
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s hs => by rw [← h hs]; exact h2 s hs⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s hs => by rw [h hs]; exact h2 s hs⟩
  unfold revMapExt
  rw [hP]

variable {Ω : Type*}

end SWCore
end QuantumZipper
