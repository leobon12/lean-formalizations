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

import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension

import InteractingSLE.Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData
set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Well-definedness of the bounded harmonic extension of force-word data** (companion of
Theorem 1.1, p. 9, and of the convention on p. 2). For all weights `(ρL; ρR)` and every state of the force word
the boundary data has a bounded harmonic extension in `ℍ`, and it is unique on `ℍ`. This certifies that the
universally quantified extensions in `IsOptionalHullCoupling` are non-vacuous and that the
specification does not depend on their choice. (The statement does not involve the initial positions, so it is
stated for all weights; `Equiv12.lean` proves it equivalent to the form over ordered force words.) -/
theorem existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ : ℝ) {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR)
        (forceJumpSet vL vR) u ∧
      ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR)
        (forceJumpSet vL vR) v → EqOn v u QuantumZipper.H :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
