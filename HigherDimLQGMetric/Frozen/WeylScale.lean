import HigherDimLQGMetric.Frozen.ContMetricPt
import HigherDimLQGMetric.Frozen.ContMetricInstMetricSpace
import Mathlib.Analysis.ConstantSpeed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Frozen definition: `weylScale`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 69–74 (Axiom (III): "the right side minimizes the integral of `e^{ξf}` against `D_h`-arclength over
paths with the prescribed endpoints"), [1] (1.4): `(e^{ξ f}·D)(z, w) = inf ∫_0^{len(P;D)} e^{ξ f(P(t))} dt`
over paths from `z` to `w` parametrized by `D`-length (unit speed on `[0, L]`, `L = len(P; D)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Weyl scaling `(e^{ξ f}·D)(z, w) := inf ∫_0^L e^{ξ f(P(t))} dt` over paths `P : [0, L] → ℝ^d` from
`z` to `w` parametrized by `D`-length. -/
def weylScale {d : ℕ} (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (z w : Rd d) : ℝ≥0∞ :=
  ⨅ (L : ℝ) (P : ℝ → Rd d) (_ : 0 ≤ L) (_ : ContinuousOn (D.pt ∘ P) (Icc 0 L))
    (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = z) (_ : P L = w),
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))

end HigherDimLQGMetric
