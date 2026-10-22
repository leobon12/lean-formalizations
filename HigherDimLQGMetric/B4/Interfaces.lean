import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Weak.DetDefs
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.ContMetricInternal

/-!
# Interface statements of block B4 (orchestrator-owned)

For the interface pattern between L9b ([1] Prop 4.2, running) and L9c ([1] Theorem 1.6): `lfppDistIn`, `lfppSetDistIn`
verbatim from MA6 Details (c) (`planning/audits/statements/MA6Surface.lean.txt`, §PhaseB), and `Prop42Shape`, MA6's
statement of `prop42` as a proposition (all binders universally quantified, in the same order). L9b proves `Prop42Shape`
from the B3/B2 interface hypotheses; L9c consumes it. Workers import this module and never edit or redefine it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd IsLFPPKernel)

variable {d : ℕ}

/-- internal convolution-LFPP distance `D^ε_h(x, y; V)` (paths in `V`) -/
def lfppDistIn (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d) (V : Set (Rd d)) (x y : Rd d) : ℝ≥0∞ :=
  ⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P x y ∧ MapsTo P (Icc 0 1) V},
    lfppLen ξ (convMollify κ ε h) P.1

/-- `D^ε_h(A, B; V)` -/
def lfppSetDistIn (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d) (V A B : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ (x ∈ A) (y ∈ B), lfppDistIn κ ξ ε h V x y

/-- **[1] Prop 4.2** (MA6's `prop42`) as a proposition -/
def Prop42Shape : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ : ℝ}, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ {κ : Rd d → ℝ}, IsLFPPKernel κ → ∀ {D : DistRd d → ContMetric d} {c : ℝ → ℝ},
    IsWeakExpMetric d ξ D c → ∀ {ζ : ℝ}, 0 < ζ → ζ < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        Tendsto (fun ε => P {ω | ¬ ∀ z ∈ U, ∀ w ∈ U,
            ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppSetDistIn κ ξ ε (h ω)
                (Metric.thickening (ε ^ (1 - ζ)) U) (Metric.ball z (ε ^ (1 - ζ)))
                (Metric.ball w (ε ^ (1 - ζ))) ≤ ENNReal.ofReal C * (D (h ω)).internal U z w ∧
            setDistIn (D (h ω)) (Metric.thickening (ε ^ (1 - ζ)) U) (Metric.ball z (ε ^ (1 - ζ)))
                (Metric.ball w (ε ^ (1 - ζ))) ≤
              ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppDistIn κ ξ ε (h ω) U z w)})
          (𝓝[>] 0) (𝓝 0)

end HigherDimLQGMetric
