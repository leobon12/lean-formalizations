import HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Frozen definition: `TendstoInProbLU`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 85–86, 1573–1576 ("converge in probability locally uniformly"): convergence in probability with
respect to the local uniform topology on functions `ℝ^d × ℝ^d → ℝ` (for every `R, δ > 0`, the outer
probability that the sup distance on `B̄_R × B̄_R` is `≥ δ` tends to `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Convergence in probability in the local uniform topology on functions `ℝ^d × ℝ^d → ℝ`. -/
def TendstoInProbLU {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → Rd d × Rd d → ℝ) (l : Filter ι) (Y : Ω → Rd d × Rd d → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun i => P {ω | ENNReal.ofReal δ ≤
      ⨆ p ∈ Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R,
        edist (X i ω p) (Y ω p)}) l (𝓝 0)

end HigherDimLQGMetric
