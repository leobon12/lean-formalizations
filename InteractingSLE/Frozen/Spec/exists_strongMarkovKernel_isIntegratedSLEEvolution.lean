-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_exists_strongMarkovKernel_isIntegratedSLEEvolution_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
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
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Spec.Provider.exists_strongMarkovKernel_isIntegratedSLEEvolution

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 2.2, the Markov sentence** (arXiv:1201.1496v2 p. 40: "Under this law, the values W_t, B_t, and V_t^{i,q}
taken together are a continuous multidimensional Markovian process indexed by t"; Specification p. 21). For `a > 0` and
weights `(ρL; ρR)` there is one time-homogeneous kernel `Q` on finite-time cylinder events of the state
`(W, V^L, V^R, B)` such that: (law) for every ordered force word, `Q` at a state is the killed-state law of any integrated
`SLE_a(ρ)` evolution started there (translated by `(w, b)`); (measurable) `Q` is measurable on separated states;
(continuous) the state paths are almost surely continuous before the lifetime `ζ`; (strong Markov) at every finite
stopping time `T`, for `A ∈ 𝓕_T` inside `{T < ζ}`, the future killed state is distributed by `Q` at the state at `T`;
and for every `A ∈ 𝓕_T` and at least one future time, the same identity integrated over `A ∩ {T < ζ}` (the killed
future is empty from `ζ` on). `T = 0` and unseparated (entrance) words are included. Not covered: measurability of `Q`
at unseparated states, a Mathlib `Kernel`/semigroup packaging, future events beyond finite-time cylinders, and
infinite stopping times. Requested by the external audit of 2026-11-15 (ruling R122; audit AUD-AF-T22). -/
theorem exists_strongMarkovKernel_isIntegratedSLEEvolution :
    ∀ (a : ℝ), 0 < a → ∀ (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      ∃ Q : ∀ n : ℕ, (Fin n → ℝ≥0) → (Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) →
          ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ → ℝ≥0∞,
        -- (law)
        (∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ), IsOrderedForceWord xL xR → ∀ (w b : ℝ)
          {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
          {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
          {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
          IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
          ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (K j)) →
            Q n ts K (w, (fun i => w + xL i), (fun j => w + xR j), b) =
              P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
                (w + W (ts j) ω, (fun i => w + VL i (ts j) ω), (fun i => w + VR i (ts j) ω),
                  b + B (ts j) ω) ∈ K j}) ∧
        -- (measurable)
        (∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
          (∀ j, MeasurableSet (K j)) →
          Measurable fun x : {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ // ∀ i j, x.2.1 i < x.2.2.1 j} =>
            Q n ts K x.1) ∧
        -- (continuous)
        (∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
          {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
          {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
          IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
          ∀ᵐ ω ∂P, ContinuousOn (fun t => (W t ω, (fun i => VL i t ω), (fun i => VR i t ω), B t ω))
            {t | (t : ℝ≥0∞) < ζ ω}) ∧
        -- (strong Markov)
        (∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
          {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
          {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
          IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
          ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (A : Set Ω),
            MeasurableSet[hT.measurableSpace] A → (∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω) →
            ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
              (∀ j, MeasurableSet (K j)) →
              P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
                  (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
                    B (T ω + ts j) ω) ∈ K j}) =
                ∫⁻ ω in A, Q n ts K (W (T ω) ω, (fun i => VL i (T ω) ω), (fun i => VR i (T ω) ω),
                  B (T ω) ω) ∂P) ∧
        -- (strong Markov, every event of `𝓕_T`: the killed state is the cemetery from `ζ` on)
        ∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
          {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
          {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
          IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
          ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (A : Set Ω),
            MeasurableSet[hT.measurableSpace] A →
            ∀ (n : ℕ), 0 < n →
            ∀ (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
              (∀ j, MeasurableSet (K j)) →
              P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
                  (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
                    B (T ω + ts j) ω) ∈ K j}) =
                ∫⁻ ω in A ∩ {ω | (T ω : ℝ≥0∞) < ζ ω}, Q n ts K (W (T ω) ω, (fun i => VL i (T ω) ω),
                  (fun i => VR i (T ω) ω), B (T ω) ω) ∂P :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.exists_strongMarkovKernel_isIntegratedSLEEvolution
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
