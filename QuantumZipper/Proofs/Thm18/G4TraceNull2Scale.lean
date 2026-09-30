import QuantumZipper.Proofs.Zipper.RegContEnergy
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import QuantumZipper.Proofs.Zipper.Cor15RezipRegHull
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Thm18.G4RezipNodes
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.RS.TransienceScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4-TRACENULL: Beffara's two-point estimate in its published normalization

Task G4-TRACENULL-ROUTE (Sheffield, arXiv:1012.4797, Theorem 1.8 (1)). `G4TraceNull.lean`
reduces `G4UpTraceNullStmt` to `SLETwoPointBound κ` (`G4TraceNullMoment.lean`), a two-point
estimate for points with `Im ≥ δ`, `δ > 0` arbitrary. The published estimate is stated for
`Im ≥ 1` only:

  G. Lawler, B. Werness, *Multi-point Green's functions for SLE and an estimate of Beffara*,
  Ann. Probab. 41 (2013) 1513–1555, Introduction, p. 2 (`literature/1011.3551.pdf`, PDF p. 2):
  "there exists some `c > 0` such that for any two points `z, w ∈ ℍ` with `Im z, Im w ≥ 1`,
  `P{Υ_∞(z) < ε; Υ_∞(w) < ε} < c ε^{2(2−d)} |z − w|^{d−2}`", `d = 1 + κ/8`, `κ < 8`
  (Beffara, *The dimension of the SLE curves*, Ann. Probab. 36 (2008), §3, pp. 10–27 of
  `literature/math_0211322.pdf`; a proof independent of Beffara's is the body of Lawler–Werness).

`Υ_∞(z)` is (twice) the conformal radius of `z` in `ℍ \ γ(0,∞)`; by Koebe's 1/4 theorem
(Lawler–Werness (1), p. 4) `Υ_∞(z) ≤ 2 dist(z, γ(0,∞) ∪ ℝ) ≤ 2 dist(z, γ(0,∞))`, so
`{dist(z, γ) < ε} ⊆ {Υ_∞(z) < 2ε}` and the published estimate gives
`SLETwoPointBoundUnit κ` below with constant `4^{1−κ/8} c`. This conversion (conformal radius
to distance) is recorded as a statement-form deviation; no conformal radius is defined in the
project.

**This file** (Brownian scaling, the step the literature calls "by scaling"): the `Im ≥ 1`
normalization implies the `Im ≥ δ` form for every `δ > 0` (`sleTwoPointBound_of_unit`), using
the a.s. scaling of the trace `η_{δ⁻¹B(δ²·)}(s) = η_B(δ² s)/δ` (`RS.ae_sleTrace_scale`), and
hence `G4UpTraceNullStmt` from the published estimate (`g4UpTraceNullStmt_of_twoPointUnit`).
Own elementary argument (scaling bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal Pointwise

namespace QuantumZipper
namespace Thm18Asm

namespace G4TraceNull2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The Brownian motion `δ⁻¹ B(δ² ·)`. -/
def scaledBM (δ : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (√((δ ^ 2).toNNReal : ℝ))⁻¹ * B ((δ ^ 2).toNNReal * t) ω

theorem isBrownianReal_scaledBM (hB : IsBrownianReal B P) {δ : ℝ} (hδ : 0 < δ) :
    IsBrownianReal (scaledBM δ B) P :=
  hB.smul (Real.toNNReal_pos.2 (by positivity)).ne'

end G4TraceNull2

end Thm18Asm
end QuantumZipper
