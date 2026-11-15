import InteractingSLE.Spec.AuditFix.Markov

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/exists_strongMarkovKernel_isIntegratedSLEEvolution.lean`.

The statement is the frozen anchor's; the proof is the closed theorem
`InteractingSLE.AuditFix.integratedSLEStrongMarkov_holds` (external-audit response, ruling R122).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Spec.Provider

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
  by exact InteractingSLE.AuditFix.integratedSLEStrongMarkov_holds

end InteractingSLE.Spec.Provider
