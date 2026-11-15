-- FROZEN_ANCHOR_PREFIX_BEGIN
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Spec.Provider.IsPiecewiseConstantBoundaryData_existsUnique_isBoundedHarmonicExtension

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Well-definedness of the bounded harmonic extension of finite piecewise-constant boundary
data** (companion of Theorem 1.5, p. 5, and of the convention on p. 2: "their harmonic extension
means the bounded harmonic extension"; p. 457, §3.1). If `b` is locally constant off the finite
set `jumps`, it has a bounded harmonic extension in `ℍ` (with boundary values `b` off `jumps`),
and it is unique on `ℍ`. This certifies that the universally quantified extensions in
`IsGFFWithBoundaryData` are non-vacuous and that the predicate does not depend on their choice
(style of `existsUnique_isBoundedHarmonicExtension_forceBoundaryData`, ruling R19 (1)). -/
theorem IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u ∧
      ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension b jumps v → EqOn v u QuantumZipper.H :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.IsPiecewiseConstantBoundaryData_existsUnique_isBoundedHarmonicExtension
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
