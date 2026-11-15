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

import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

import InteractingSLE.Spec.Provider.exists_isOptionalHullCoupling
set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 1.1** (Specification p. 9; Miller–Sheffield, *Imaginary Geometry I*, Thm 1.1).
Fix `κ > 0` and an ordered force word. There is a coupling of the integrated `SLE_κ(ρ)` driving
process (and hence of its hulls `K`) with a field `h = h⁰ + 𝔥₀`, `h⁰` a zero-boundary GFF on
`ℍ`, satisfying the optional hull specification: for every stopping time `τ < T_*` a.s. of the
usual augmentation of the driving filtration, `K_τ` is a local set of `h` and, conditionally on
`𝓕_τ`, the restriction of `h` to `ℍ \ K_τ` has the law `𝔥_τ + h̃⁰ ∘ f_τ`. -/
theorem exists_isOptionalHullCoupling (κ : ℝ) (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.exists_isOptionalHullCoupling
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
