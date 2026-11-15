import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary

import InteractingSLE.Frozen.Spec.IsFilling

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `η` is a continuous generating trace on `[0, T]` (on `[0, ∞)` when `T = ∞`) of the chordal
Loewner chain (1.6) driven by `w` (Specification p. 3, "Loewner maps, hulls and clocks"; Theorem
1.3, p. 4): `η 0 = 0`, `η` is continuous on `{t | t ≤ T}`, and for every `t < T` the filled hull
`K_t = QuantumZipper.fwdHull w t` (the points of `ℍ` swallowed by time `t`) is the filling of
`η([0, t])`. No hull is asserted at `t = T` itself. -/
def IsGeneratingTrace (w : ℝ≥0 → ℝ) (T : ℝ≥0∞) (η : ℝ≥0 → ℂ) : Prop :=
  η 0 = 0 ∧ ContinuousOn η {t | (t : ℝ≥0∞) ≤ T} ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      IsFilling (QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t) (η '' Set.Icc 0 t)

end InteractingSLE
