import HigherDimLQGMetric.DGZ.Sec41Defs
import HigherDimLQGMetric.DGZ.Functionals
import HigherDimLQGMetric.Frozen.IsContinuousMetric
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Interface statements of block B2 (orchestrator-owned)

The statements of [2] §5 that packet L4c proves and that packet L5a consumes before L4c lands (the interface pattern:
the consumer takes the named `Prop` as a hypothesis, the assembly discharges it). Copied verbatim from MA7 Details (c)
(`planning/audits/statements/MA7Statements.lean.txt`). Workers import this module and never edit it (WORKERS.md);
L4c proves `∀ d κ ξ Q, Cor52Shape d κ ξ Q` (via the restricted `Prop51Shape` of ruling M23 (iii)).

The export shapes of MA7 Details (c) §F (added 10-21 21:15 for the interface pattern between L5a/L5b, which prove
them, and L5c, which consumes them): `HolderTightShape`, `NondegShape`, `DistInfShape`, `normMetricC`, `DGZThm12Shape`,
`aHat`, `RealEpsAdapterShape`, verbatim from MA7 §F, except that MA7's copies of `IsMetricFn` and `IsContinuousMetric`
are replaced by the identical frozen definitions (`HigherDimLQGMetric.Frozen.IsMetricFn`, `.IsContinuousMetric`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- **DGZ Cor 5.2, the direction used** (MA7 D-5.2): `a_{n-k}^{(q)} ≤ C 2^{(1-ξQ+ε)k} a_n^{(q')}` -/
def Cor52Shape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ ε > 0, ∀ q q' : ℝ≥0∞, 0 < q → q < q' → q' < 1 → ∃ C > 0,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n k : ℕ, k ≤ n →
        aQ P H ξ (n - k) q ≤ C * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * aQ P H ξ n q'

/-- **DGZ Prop 5.1, the direction used, for the pair `(0, e₁)`** (MA7 D-5.1) -/
def Prop51Shape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ ε > 0, ∃ c > 0, ∃ N : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n k : ℕ, N ≤ n → 1 ≤ k → (k : ℝ) ≤ c * n →
        P {ω | lfppDistance d ξ (fun z => H (n + k) z ω) ≤
            c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H n z ω)} ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-(c * n)))

/-! ## §F. Exports (what [1] consumes), normalized by `λ_n = a_n^{(1/2)}` -/

/-- **Hölder tightness** (DGZ Lemma 6.2 + Prop 6.3 + (6.3), quantitative): for a bounded connected
open `V` with `closure V ⊆ U` (`U` open; `U = univ` gives the whole-space metric) -/
def HolderTightShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ β : ℝ, 0 < β → β < ξ * (Q - Real.sqrt (2 * d)) →
    ∀ U V : Set (Rd d), IsOpen U → IsOpen V → IsConnected V → Bornology.IsBounded V →
      closure V ⊆ U → ∀ θ > 0, ∃ M : ℝ,
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
            P {ω | ∃ x ∈ V, ∃ y ∈ V, M * aQ P H ξ n 2⁻¹ * ‖x - y‖ ^ β <
              lfppDistOn ξ (fun z => H n z ω) U x y} ≤ ENNReal.ofReal θ

/-- **non-degeneracy** (DGZ Prop 6.4 + (6.3)): crossing distances are `≥ δ λ_n` with high
probability, for every hypercubic shell -/
def NondegShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ (c : Rd d) (r₁ r₂ : ℝ), 0 < r₂ → r₂ < r₁ → ∀ θ > 0, ∃ δ > 0, ∃ N : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
        P {ω | acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤ δ * aQ P H ξ n 2⁻¹} ≤ ENNReal.ofReal θ

/-- **distance to infinity** (DGZ Lemma 6.7 + (6.3)) -/
def DistInfShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ r T θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧ ∃ N : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
        P {ω | acrossDist ξ (fun z => H n z ω) 0 R r ≤ T * aQ P H ξ n 2⁻¹} ≤ ENNReal.ofReal θ

/-! ### Qualitative DGZ Theorem 1.2 (laws on `C(ℝ^d × ℝ^d, ℝ)`), in MA0's `TightOver` style -/

open Classical in
/-- `a⁻¹ D^ξ(φ)` as an element of `C(ℝ^d × ℝ^d, ℝ)`; junk `0` if not continuous (continuity of the
LFPP metric of a continuous field is a lemma of packet L3b) -/
def normMetricC (ξ : ℝ) (φ : Rd d → ℝ) (a : ℝ) : C(Rd d × Rd d, ℝ) :=
  if h : Continuous (fun p : Rd d × Rd d => a⁻¹ * lfppMetric ξ φ p.1 p.2) then ⟨_, h⟩ else 0

/-- **DGZ Theorem 1.2** (the qualitative statement) -/
def DGZThm12Shape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H →
        (∀ n, AEMeasurable (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n 2⁻¹)) P) ∧
        IsTightMeasureSet {μ | ∃ n : ℕ,
          μ = P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n 2⁻¹))} ∧
        ∀ μ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
          μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) | ∃ n : ℕ,
            (ν : Measure C(Rd d × Rd d, ℝ)) =
              P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n 2⁻¹))} →
          ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContinuousMetric D

/-! ### The adapter for [1] Lemma 3.3: all real `ε`, whole-space medians -/

/-- `â_ε`: median of the whole-space distance `D[H_{ε,1}](0, e₁)` -/
def aHat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : ℝ → Rd d → Ω → ℝ) (ξ ε : ℝ) : ℝ :=
  LQGMetric.lowerQuantile (P.map fun ω => lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d)) 2⁻¹

/-- **[1]-facing adapter** (MA7 D-ADP): for continuous versions `G ε` of `H_{ε,1}` at every real
`ε ∈ (0,1)`: Hölder tightness and non-degeneracy normalized by `â_ε`, uniformly in `ε` -/
def RealEpsAdapterShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ β : ℝ, 0 < β → β < ξ * (Q - Real.sqrt (2 * d)) →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (G : ℝ → Rd d → Ω → ℝ),
      IsWhiteNoise P W → (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε)) →
      (∀ R θ : ℝ, 0 < R → 0 < θ → ∃ M : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹,
        P {ω | ∃ x ∈ Metric.closedBall (0 : Rd d) R, ∃ y ∈ Metric.closedBall (0 : Rd d) R,
          M * aHat P G ξ ε * ‖x - y‖ ^ β < lfppMetric ξ (fun z => G ε z ω) x y} ≤
            ENNReal.ofReal θ) ∧
      (∀ (c : Rd d) (r₁ r₂ θ : ℝ), 0 < r₂ → r₂ < r₁ → 0 < θ → ∃ δ > 0, ∃ ε₀ > 0,
        ∀ ε ∈ Ioo (0 : ℝ) ε₀,
          P {ω | lfppSetDist ξ (fun z => G ε z ω) univ (Metric.sphere c r₂) (Metric.sphere c r₁)
            ≤ δ * aHat P G ξ ε} ≤ ENNReal.ofReal θ) ∧
      -- confinement ([1] Lemma 3.3's use of DGZ Lemma 6.7 with Prop 6.3)
      (∀ r θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | lfppSetDist ξ (fun z => G ε z ω) univ (Metric.sphere 0 r) (Metric.sphere 0 R) ≤
          ⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
            lfppMetric ξ (fun z => G ε z ω) p.1 p.2} ≤ ENNReal.ofReal θ) ∧
      -- the exponent of the whole-space median (`â_ε = ε^{1 - ξQ + o(1)}`; MA0 finding I3)
      Tendsto (fun ε => Real.log (aHat P G ξ ε) / Real.log ε) (𝓝[>] 0) (𝓝 (1 - ξ * Q))

end DGZ

end HigherDimLQGMetric
