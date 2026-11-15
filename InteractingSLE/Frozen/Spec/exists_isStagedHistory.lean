-- FROZEN_ANCHOR_PREFIX_BEGIN
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
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.IsStagedHistory
import InteractingSLE.Frozen.Spec.IsBoundaryContinuedProgram
import InteractingSLE.Frozen.Spec.StagedPiecesRegular
import InteractingSLE.Spec.Provider.exists_isStagedHistory

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Realizations of the staged histories exist** (companion of Theorem 1.4; GW1 p. 618: "There is a
field-determined … curve `R` with the following construction"; GW2 p. 621; GW2a p. 623). For a GFF `h` on `ℍ` with
a finite piecewise-constant boundary word `b` (locally constant off `jumps`), on any standard Borel probability
space carrying it, there is a family of drivers realizing every prescribed staged history whose ordinary angles lie
in `[−π/2, π/2]` (the histories the source uses: GW1's walks, GW2's schedules, GW2a's boundary-continued histories)
as conditional flow lines of `h`, every launched piece almost surely a continuous curve with a continuous generating
trace (`StagedPiecesRegular`; ruling R51). This certifies that the universally quantified realizations in the three
Theorem 1.4 declarations below are non-vacuous. -/
theorem exists_isStagedHistory {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) ∧ StagedPiecesRegular κ b jumps P spec (E spec) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.exists_isStagedHistory
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
