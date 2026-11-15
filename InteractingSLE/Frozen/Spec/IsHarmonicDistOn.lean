import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary

import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The distribution `T` on `ℍ` is harmonic on the open set `U ⊆ ℍ`: on test functions supported
in `U` it is given by a harmonic function. -/
def IsHarmonicDistOn (T : LQGMetric.DistOn upperHalfPlaneOpens) (U : Set ℂ) : Prop :=
  ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v U ∧
    ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → T φ = ∫ z, v z * φ z

end InteractingSLE
