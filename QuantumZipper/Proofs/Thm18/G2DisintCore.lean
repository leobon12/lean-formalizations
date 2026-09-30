import QuantumZipper.Proofs.Thm18.G2DisintBase
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration: the rooted integral in product form

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66) conditions on `h₀` and integrates the
Gaussian coefficient `α` out. Abstractly: if `Y ⊥ α` under `P`, the root is sampled from a
measure `ν(Y)` that depends on `Y` only (the boundary measure on the margin, which the bump does
not see), then

`E ∫_M H(Y, x, α) ν(Y)(dx) = ∫ law(Y)(dy) ∫_M ν(y)(dx) ∫ N(da) H(y, x, a)`, `N = law α`

(`g2_core_transfer`), with the root masses truncated at `K` so that the kernel `y ↦ ν(y)|_M` is
finite (the truncation error is handled by dominated convergence with `E ν[−δ, 0] < ∞`).
Own bookkeeping (independence = product law, Tonelli; AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

section Core

variable {E : Type*} [MeasurableSpace E]

/-- The truncated root kernel `y ↦ ν(y)|_M` if `ν(y)(M) ≤ K`, else `0`. -/
def g2RootKer (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ} (hM : MeasurableSet M)
    (K : ℝ≥0∞) : Kernel E ℝ where
  toFun e := if ν e M ≤ K then (ν e).restrict M else 0
  measurable' := by
    refine Measurable.ite (measurableSet_le ((Measure.measurable_coe hM).comp hν)
      measurable_const) ?_ measurable_const
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.restrict_apply hs]
    exact (Measure.measurable_coe (hs.inter hM)).comp hν

theorem g2RootKer_apply (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ}
    (hM : MeasurableSet M) (K : ℝ≥0∞) (e : E) :
    g2RootKer ν hν hM K e = if ν e M ≤ K then (ν e).restrict M else 0 := rfl

instance g2RootKer_finite (ν : E → Measure ℝ) (hν : Measurable ν) {M : Set ℝ}
    (hM : MeasurableSet M) (K : ℝ≥0∞) [Fact (K ≠ ⊤)] :
    IsFiniteKernel (g2RootKer ν hν hM K) := by
  refine ⟨⟨K, (Fact.out : K ≠ ⊤).lt_top, fun e => ?_⟩⟩
  rw [g2RootKer_apply]
  split_ifs with h
  · rwa [Measure.restrict_apply_univ]
  · simp

end Core

end Thm18Asm
end QuantumZipper
