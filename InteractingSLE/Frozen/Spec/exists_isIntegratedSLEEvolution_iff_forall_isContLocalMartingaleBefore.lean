-- FROZEN_ANCHOR_PREFIX_BEGIN
-- Frozen anchor (theorem, spec_exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
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
import InteractingSLE.Spec.Provider.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Theorem 2.4 (martingale characterization of `SLE_κ(ρ)`)**, Specification §2.3, pp. 34–35, with the horizon of
ruling R109. Let `κ > 0` and let `(xL; xR)` be an ordered force word with weights `(ρL; ρR)`. Let `η` be a random
continuous curve in `ℍ̄` from `0` to `∞` whose Loewner driving function `W` (a random process with `W_0 = 0`, L815) is
almost surely continuous: almost surely `W` is continuous, `W 0 = 0`, `η` is a continuous generating trace of the
Loewner chain driven by `W` on `[0, ∞)`, `η` stays in `ℍ̄`, and `|η(t)| → ∞`. Let `V^{i,q}` be the force-point
processes, almost surely the geometric images of the force points (`IsLeftForceImage`, `IsRightForceImage`), let
`T_*` be their continuation threshold (`continuationThreshold`) and `𝔥_t` the harmonic function of Theorem 1.1
(`couplingMean`, for every choice of the bounded harmonic extensions `𝔥⁰_t`). Then `W` and the `V^{i,q}` can be coupled
with a standard Brownian motion `B` to describe an integrated `SLE_κ(ρ)` evolution up to the continuation threshold —
on an extension `π : Ω' → Ω` of the probability space — if and only if, for every `z ∈ ℍ`, `𝔥_t(z)` is a continuous
local martingale in the usual augmentation of the filtration of the curve before `z` is absorbed by `K_t` and before
the continuation threshold. -/
theorem exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, Measurable (VL i t)) (hVR : ∀ j t, Measurable (VR j t))
    (hηW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (fun t => η t ω) ∧
      (∀ t, η t ω ∈ closure QuantumZipper.H) ∧ Tendsto (fun t => ‖η t ω‖) atTop atTop)
    (hV : ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
      ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω)) :
    (∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
        MeasurePreserving π P' P ∧
        ∃ (𝓕' : Filtration ℝ≥0 mΩ') (B : ℝ≥0 → Ω' → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' (fun t ω' => W t (π ω'))
            (fun i t ω' => VL i t (π ω')) (fun j t ω' => VR j t (π ω')) B
            (fun ω' => continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
              (fun j s => VR j s (π ω')))) ↔
      ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
        (∀ ω t, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
          (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
        ∀ z ∈ QuantumZipper.H,
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact InteractingSLE.Spec.Provider.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end InteractingSLE
-- FROZEN_ANCHOR_SUFFIX_END
