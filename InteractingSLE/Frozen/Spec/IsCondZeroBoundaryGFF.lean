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

/-- Conditionally on the σ-algebra `𝒢`, the random distribution `X` on `ℍ` is a zero-boundary GFF
on the random open set `U ω ⊆ ℍ`, extended by zero to `ℍ` (Lemma 3.6 (iii), p. 52), under `P`: for every
test function `φ`, `E[exp(i (X, φ)) | 𝒢] = exp(−½ ‖φ‖²_{H⁻¹(U)})` almost surely, with the dual
Dirichlet norm `QuantumZipper.zeroGFFTestCov (U ω) φ φ` (normalization `(2π)⁻¹∫∇f·∇g`). By
linearity of `X ω` this fixes all joint conditional characteristic functions. -/
def IsCondZeroBoundaryGFF {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (𝒢 : MeasurableSpace Ω) (U : Ω → Set ℂ) (X : Ω → LQGMetric.DistOn upperHalfPlaneOpens) :
    Prop :=
  ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
    condExp 𝒢 P (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ)

end InteractingSLE
