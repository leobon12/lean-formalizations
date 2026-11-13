-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, sle8_thm_1_1_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import InteractingSLE.SLE8.Provider.ContinuousTrace

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8

/-- **Continuity of the SLE₈ trace.** SLE₈ note `source/sle8-continuity.pdf`, Theorem 1.1, p. 1.

Let `B` be a standard real Brownian motion and `W_t = √8 B_t`. Almost surely the limit
`γ(t) = lim_{y ↓ 0} F_t(iy)` of the centered inverse Loewner maps `F_t(z) = g_t⁻¹(W_t + z)`
exists locally uniformly for `t ∈ [0, ∞)` and defines a continuous `γ : [0, ∞) → \overline{ℍ}`
with `γ(0) = 0`; for every `t ≥ 0`, the domain `H_t = {z ∈ ℍ : T_z > t}` is the unbounded
connected component of `ℍ \ γ([0, t])`. -/
theorem ae_exists_continuous_trace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) =>
            QuantumZipper.fwdMapInv (QuantumZipper.drive 8 B ω) t (y * Complex.I))
          γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ QuantumZipper.Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t,
              connectedComponentIn (QuantumZipper.H \ γ '' Icc 0 t) z =
                QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) ∧
            ¬ Bornology.IsBounded
              (QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.SLE8.Provider.ae_exists_continuous_trace
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE.SLE8
-- FROZEN_ANCHOR_SUFFIX_END
