import HigherDimLQGMetric.Shell.Defs
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric

/-!
# Interface statements shared between packets (orchestrator-owned)

Statements that one packet proves and other packets consume before it lands (the interface pattern: a consumer takes the
named `Prop` as a hypothesis, the assembly discharges it). Defined once here so that producer and consumers agree
verbatim. Workers import this module and never edit it (WORKERS.md).

* `normDiam ξ Q D h U K 𝕣 z = 𝕣^{-ξQ} e^{-ξ h_𝕣(z)} sup_{x,y ∈ z+𝕣K} D_h(x, y; z+𝕣U)`, the normalized internal diameter
  (MA6 Details (c), verbatim);
* `E5SharpMoment d ξ Q D`: the conclusion of MA6's `e5_sharp` ((E5), moment form) for one assignment `D`; packet W3 proves
  `IsSharpWeakExpMetric d ξ Q D → E5SharpMoment d ξ Q D` for `d ≥ 3`, `ξ > 0`, `√(2d) < Q`; consumed by M2b (D-SF5) and
  W3b ([S] Lemma 2.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- the normalized internal diameter `𝕣^{-ξQ} e^{-ξ h_𝕣(z)} sup_{x,y ∈ z+𝕣K} D_h(x, y; z+𝕣U)` (MA6 Details (c)) -/
def normDiam (ξ Q : ℝ) (D : DistRd d → ContMetric d) (h : DistRd d) (U K : Set (Rd d)) (𝕣 : ℝ)
    (z : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal ((𝕣 ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * sphereAvg h 𝕣 z))) *
    ⨆ (x ∈ affineSet 𝕣 z K) (y ∈ affineSet 𝕣 z K), (D h).internal (affineSet 𝕣 z U) x y

/-- **(E5), moment form**, for one assignment `D`: the conclusion of MA6's `e5_sharp` (Details (c)). -/
def E5SharpMoment (d : ℕ) (ξ Q : ℝ) (D : DistRd d → ContMetric d) : Prop :=
  ∀ {U K : Set (Rd d)}, IsOpen U → IsCompact K → IsConnected K → K ⊆ U → ∀ {p : ℝ}, 0 < p →
    p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ →
    ∃ M : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : Rd d,
      ∫⁻ ω, normDiam ξ Q D (h ω) U K 𝕣 z ^ p ∂P ≤ ENNReal.ofReal M

end HigherDimLQGMetric
