/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalLocal
import InteractingSLE.Spec.Supplement.SBS3PrimeMeans

/-!
# S3: protected mean comparison for two actual staged histories

Both sets are measurable versions of actual explored sets of the same
field. Field determination gives conditional independence; R51 gives the
unbounded lower components. The component form of Proposition 3.8 then
constructs the comparison through an actual union local-set mean.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- The actual means of two explored sets satisfy the protected component
comparison. No independence, locality or unboundedness premise remains. -/
theorem ae_markedUnionMeans_stages
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {s₁ s₂ : ExplSpec}
    {E₁ E₂ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₁ : IsStagedHistory κ b jumps P h s₁ E₁)
    (hE₂ : IsStagedHistory κ b jumps P h s₂ E₂)
    (hR₁ : StagedPiecesRegular κ b jumps P s₁ E₁)
    (hR₂ : StagedPiecesRegular κ b jumps P s₂ E₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k₁ k₂ : ℕ)
    {A B : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A) (hB : Measurable[mΩ, hittingSigma] B)
    (hAeq : ∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps s₁ E₁ k₁ ω)
    (hBeq : ∀ᵐ ω ∂P, B ω = WalkLaw.stageSet κ b jumps s₂ E₂ k₂ ω)
    {GA GB : Ω → DistOn upperHalfPlaneOpens}
    (hGA : IsLocalSetMean A (WholeField.centredField h u₀) P GA)
    (hGB : IsLocalSetMean B (WholeField.centredField h u₀) P GB) :
    ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        GA ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω →
        GB ω φ = ∫ z, vB z * φ z) →
      ∀ p : ℂ, p ∈ A ω ∪ {z : ℂ | z.im = 0} → p ∈ B ω ∪ {z : ℂ | z.im = 0} →
      ∀ rA > 0, ∀ rB > 0,
        MarkedUnionMeans (A ω) (B ω)
          (FinRel.freeNear (B ω) (A ω) p rA ∩ FinRel.freeNear (A ω) (B ω) p rB) p vA vB := by
  obtain ⟨hAloc, hAdet, hAunb⟩ :=
    stageSet_version_local_determined h12p h13 hκ hκ4 hb hh hE₁ hR₁ hu₀ k₁ hA hAeq
  obtain ⟨hBloc, -, hBunb⟩ :=
    stageSet_version_local_determined h12p h13 hκ hκ4 hb hh hE₂ hR₂ hu₀ k₂ hB hBeq
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hci := Sec6.condIndepEv_of_le_aeSigma hh0.measurable.comap_le hB.comap_le hAdet
  exact ae_markedUnionMeans_of_freeNear hh0 hA hB hci hAloc hBloc hAunb hBunb hGA hGB

end InteractingSLE.Theorem14.SB.S3
