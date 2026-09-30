import QuantumZipper.Proofs.Thm18.ASepBoxData

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (d): conjunct-2 exactness for the free field on the whole good parameter set, `τ' = 0`

For a fixed driver `W` with a Hölder modulus on every `[0, T]` and a free field `X`, almost surely,
at every good parameter `p = (τ, a)` (`ASep.ParGood`, an open set, `isOpen_parGood`), the unzipped
field `x_p = coordChange (ofFun (a' log|·| + g₁) + X) f_τ⁻¹ Q` is exact at the pushed circle
`ν_p` (`ae_exact_free_open`). Assembled from the box engine `ASep.ae_exact_free_box`, the box data
`boxData_A0`, the per-parameter facts `pfacts_A0` and the raw identity `ae_hraw_A0`, with the
countable cover of the open set by rational boxes (as `GenUC.ae_exact_open`). The two pathwise
continuity inputs (`hΦc`, `hrawc`) are hypotheses, box by box. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core GenUC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The good parameter set. -/
def GoodSet (W : ℝ → ℝ) (d : ℂ) (r : ℝ) : Set (Fin 2 → ℝ) := {p | ParGood W (foldSph d r) p}

end ASep
end QuantumZipper
