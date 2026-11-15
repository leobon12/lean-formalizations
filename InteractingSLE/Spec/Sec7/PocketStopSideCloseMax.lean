/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCloseLaws

/-!
# The walls law at the maximum with an ordinary reference stop

PROVE-STRIPSYS38. Apply STRIPSYS41's frozen-coupling producer to the maximum
stop, using `isMarkedStop_max_ordinary`. Monotonicity identifies its hull with
the union of the two stopped hulls. The reference's stopped information is
retained. The original left-stop Galmarino property is the only stop input.

R68 as amended: this is a walls law, so its initial information is the walls
information. Add the exterior-field germ only after filling the pocket exterior,
at the stage-union law; no walls law with that germ among its marks is claimed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling PocketStopWallsFin

/-- STRIPSYS41's walls law also retains an ordinary reference's stopped history
at the maximum. No determination of either stopped hull is required. -/
theorem pocketStopWallsLaw_max_reference_of_coupling
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {Γ : Ω → Set ℂ} {q : ℝ≥0}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀)
        (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P]
          (fun ω => markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T : Ω → ℝ≥0∞}
    (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤)
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) (drivingFiltration P hX) X T)
    (hS0 : locPrefixSigma 𝓦 A γ q ≤
      MeasurableSpace.comap X inferInstance ⊔ ⨆ t, drivingFiltration P hX t)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)) :
    PocketStopWallsLaw (𝓦 ⊔ hτ.measurableSpace) P A γ Γ
      (fun ω => regHull W ζ (T ω).toNNReal ω ∪ regHull W ζ (τ ω) ω) (centredField h u₀) q := by
  have hGmax : IsMarkedStop (locPrefixSigma (𝓦 ⊔ hτ.measurableSpace) A γ q)
      (drivingFiltration P hX) X (fun ω => max (T ω) (τ ω)) := by
    rw [locPrefixSigma_sup_info]
    exact isMarkedStop_max_ordinary hG hτ
  refine pocketStopWallsLaw_regHull hC hκ hu₀ hX hζ hXm hΓ hW ?_ hGmax ?_
  · intro ω hω hq
    refine ⟨max_lt (hT ω hω hq) ENNReal.coe_lt_top, ?_⟩
    rcases le_total (T ω) (τ ω : ℝ≥0∞) with hle | hle
    · rw [max_eq_right hle, ENNReal.toNNReal_coe]
      exact union_eq_right.2 (regHull_mono W ζ ω
        (by simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono ENNReal.coe_ne_top hle))
    · rw [max_eq_left hle]
      exact union_eq_left.2 (regHull_mono W ζ ω
        (by simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono (hT ω hω hq).ne hle))
  · intro M hM
    rw [locPrefixSigma_sup_info] at hM
    exact marked_max_information_le hS0 hτ M hM

end InteractingSLE.Sec7.PocketStopSide
