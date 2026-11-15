import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import InteractingSLE.Frozen.Spec.rightSideOf
import InteractingSLE.Frozen.Spec.leftSideOf

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The components between the right walk `R` and the left walk `L` (Lemma GW3, p. 636: "a nondegenerate Jordan
component between consecutive common contacts"; Theorem GW4 proof, p. 637: "their closed between-region is exactly
`𝓑 = R ∪ L ∪ ⋃_j C_j`"): the connected components of `ℍ \ (R ∪ L)` whose points lie neither on the right of `R` nor
on the left of `L`. (All points of one component of `ℍ \ (R ∪ L)` lie in one component of `ℍ \ R` and of `ℍ \ L`, so
the side conditions do not depend on the chosen point `z`.) -/
def betweenComponents (R L : Set ℂ) : Set (Set ℂ) :=
  {C | ∃ z ∈ QuantumZipper.H \ (R ∪ L), z ∉ rightSideOf R ∧ z ∉ leftSideOf L ∧
    C = connectedComponentIn (QuantumZipper.H \ (R ∪ L)) z}

end InteractingSLE
