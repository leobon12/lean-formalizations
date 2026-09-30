import QuantumZipper.Proofs.Zipper.FibreGaussMaxMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TC-3 (tip core, D63) (2): the offset tip family as a Gaussian process

Offset version of `FibreGaussMaxSetup`. Parameters `i = (u, s, b) ∈ ℚ × ℚ × ℚ` with `u ∈ [0,1]`,
`s ∈ (-1,1)`, `b ∈ [1,2]` (`TipRegOff`); `ν i = νT W s b u`, `W = Wof κ 1 f`. The reference
parameter is `(0,0,1)` (circle `fc(0,1)`), the intermediate parameter of `g, h` is `(h.1, g.2)`
(time step at the circle of `g`, then space/radius step at time `h.1`). Own elementary
bookkeeping, following `FibreGaussMaxSetup`.
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace TipCore

open RegUnif CharFun TwoPoint RegCont KolmD RegSample

/-- Offset tip parameters `(u, s, b)`. -/
abbrev OffIdx : Type := ℚ × ℚ × ℚ

variable {κ C : ℝ} {f : C(Icc (0 : ℝ) 1, ℝ)}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end TipCore
end QuantumZipper
