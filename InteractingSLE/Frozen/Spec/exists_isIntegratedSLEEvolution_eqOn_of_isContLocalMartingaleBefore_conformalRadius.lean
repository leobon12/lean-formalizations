-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.couplingMean
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import InteractingSLE.Frozen.Spec.usualAugmentation
import InteractingSLE.Frozen.Spec.IsRightForceImage
import InteractingSLE.Frozen.Spec.IsLeftForceImage
import InteractingSLE.Frozen.Spec.continuationThreshold
import InteractingSLE.Frozen.Spec.IsContLocalMartingaleBefore
import InteractingSLE.Frozen.Spec.IsConformalRadius
import InteractingSLE.Spec.Provider.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 2.6 (one-point martingale characterization)**, Specification §2.3, p. 40. In the setting of Theorem 2.4
(`exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore`), fix one deterministic `z ∈ ℍ` and let
`σ = min (τ_z, T_*)`. Suppose that `𝔥_t(z)` (for every choice of the bounded harmonic extensions) is a continuous local
martingale in the usual augmentation of the curve filtration before `σ`, with
`⟨𝔥(z)⟩_t = log (crad(ℍ, z) / crad(ℍ ∖ K_t, z))` before `σ`, the conformal radius taken in the component of
`ℍ ∖ K_t` containing `z`. The bracket identity is stated by its defining property: a process `A` that equals
`log (crad(ℍ, z) / crad(ℍ ∖ K_t, z))` before `σ` almost surely (`IsConformalRadius`) makes `𝔥_t(z)² − A_t` a continuous
local martingale before `σ` (Revuz–Yor IV (1.8)). Then the driving process is `SLE_κ(ρ)` up to `σ`: on an extension
`π : Ω' → Ω` there is an integrated `SLE_κ(ρ)` evolution whose driver and force points agree, before `σ`, with `W` and
the `V^{i,q}`. -/
theorem exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius {κ : ℝ}
    (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, Measurable (VL i t)) (hVR : ∀ j t, Measurable (VR j t))
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω))
    {z : ℂ} (hz : z ∈ QuantumZipper.H)
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
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z ^ 2 - A t ω)) :
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
              ∀ j, VR' j t ω' = VR j t (π ω') :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
