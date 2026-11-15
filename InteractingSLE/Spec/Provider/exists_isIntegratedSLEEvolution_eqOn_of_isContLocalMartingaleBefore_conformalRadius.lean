import InteractingSLE.Spec.Sec2.T26PvMain

/-!
# Provider for the frozen anchor `InteractingSLE/Frozen/Spec/exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius.lean` (sealed)

**Theorem 2.6.** The statement is the frozen anchor's with all arguments implicit and its hypotheses as
auto-parameters (provider convention); the proof is the closed provider
`InteractingSLE.Sec2.T26Pv.Seal.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius` (PROVE-T26-PROVIDER).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Spec.Provider

theorem exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius {κ : ℝ}
    (hκ : 0 < κ := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} {hη : ∀ t, StronglyMeasurable (η t)}
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t) := by assumption)
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, Measurable (VL i t) := by assumption) (hVR : ∀ j t, Measurable (VR j t) := by assumption)
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop := by assumption)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω) := by assumption)
    {z : ℂ} (hz : z ∈ QuantumZipper.H := by assumption)
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
      IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
          (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
            (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
              (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
          (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) ∧
        ∃ A : ℝ≥0 → Ω → ℝ,
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
            (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) →
            ∃ r₀ r : ℝ, IsConformalRadius QuantumZipper.H z r₀ ∧
              IsConformalRadius (connectedComponentIn (QuantumZipper.H \
                QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t) z) z r ∧
              A t ω = Real.log (r₀ / r)) ∧
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z ^ 2 - A t ω) := by assumption) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
      MeasurePreserving π P' P ∧
      ∃ (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B : ℝ≥0 → Ω' → ℝ) (ζ : Ω' → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' W' VL' VR' B ζ ∧
          ∀ᵐ ω' ∂P', ∀ t : ℝ≥0,
            (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal (π ω')) z)
              (continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
                (fun j s => VR j s (π ω'))) →
            W' t ω' = W t (π ω') ∧ (∀ i, VL' i t ω' = VL i t (π ω')) ∧
              ∀ j, VR' j t ω' = VR j t (π ω')  := by
  exact InteractingSLE.Sec2.T26Pv.Seal.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius

end InteractingSLE.Spec.Provider
