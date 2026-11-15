/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideEndLaws
import InteractingSLE.Spec.Sec7.PocketStopSideEndMax
import InteractingSLE.Spec.Sec7.PocketStopSideEndPieces
import InteractingSLE.Spec.Sec7.PocketStopSideClose

/-!
# Side limits from raw union laws with the exterior projection retained

PROVE-STRIPSYS38. The current raw union law is supplied by STRIPSYS41. The raw
reference union laws are obtained by filling the maximum-stop walls laws of
`EndMax` (bounded) or `CloseMax`; `CloseLaws` transfers them from T⁰(q) to T(q). REF6 supplies the
enlargement by the same exterior projection for all these laws.

This assembly no longer assumes any enlarged union law. The remaining inputs
are the two-set mark measurability, individual reference local sets and their
own heights, and the incident cover and phase alignment. `EndPieces` discharges
finite landings in both Jordan shapes and states the precise geometric inputs
still required. This is a conditional helper, not an unconditional strip theorem.
Use the parameter κ′ and χ(κ′) of the counterflow's own field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling

/-- Enlarging the chart's information preserves all its geometric data. -/
theorem isPocketChartOn_mono_info {Ω : Type*} {𝓦 ℳ : MeasurableSpace Ω} (hle : 𝓦 ≤ ℳ)
    {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart}
    (hc : IsPocketChartOn 𝓦 A C ψ c) : IsPocketChartOn ℳ A C ψ c :=
  ⟨hc.1, fun z => (hc.2 z).mono hle le_rfl⟩

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The unchanged side-limit predicate, with all exterior-enlarged union laws
derived from raw laws. No field determination of the counterflow occurs. The
incident cover and the reference heights/phase remain explicit obligations. -/
theorem pocketStopSideLimit_pChart_of_raw_reference_laws {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ) (hA : MeasurableSet[𝓦] A)
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ (pChart A C ψ) q ω = C ω ∩ (H \ Fnow ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    {h₀ hB : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hhB : Measurable[germSigma (Lemma725RefMarks.extA A C) h₀] hB)
    (hRawUnion : PocketStopUnionLaw 𝓦 P A γ C Fnow h₀ q)
    {referenceInfo : CoverRef → MeasurableSpace Ω} (hInfo : ∀ i, referenceInfo i ≤ mΩ)
    (hRawReferenceUnion : ∀ i, PocketStopUnionLaw (𝓦 ⊔ referenceInfo i) P A γ C
      (fun ω => Fnow ω ∪ referenceHull Fold i ω) h₀ q)
    (hReferenceMarks : ∀ i, MeasurableSpace.comap (activeCompl A γ (pChart A C ψ) q) hittingSigma ⊔
      MeasurableSpace.comap (referenceSet C Fold i) hittingSigma ≤
        locPrefixSigma ((𝓦 ⊔ MeasurableSpace.comap hB inferInstance) ⊔ referenceInfo i) A γ q)
    (hBm : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet C Fold i))
    (hBloc : ∀ i, IsLocalSet (referenceSet C Fold i) h₀ P)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (referenceSet C Fold i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet C Fold i ω)) z))
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (referenceSet C Fold i) h₀ P (gB i))
    {faces : CoverRef → Ω → Set ℝ}
    (hpieces : IncidentReferenceCover P A γ (pChart A C ψ) C Fnow Fold q
      (fun ω => forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)) faces)
    {u : ℂ → ℝ} {liftB : CoverRef → Ω → ℂ → ℝ} {height : CoverRef → Ω → ℝ → ℝ}
    (hReferenceOwnHeights : ReferenceHeightLimits (chiC κ) P A γ (pChart A C ψ) C Fold q
      u faces gB liftB height)
    {branch : CoverRef → Ω → ℝ → ℤ}
    (hInheritedArguments : ReferenceLiftLimits P A γ (pChart A C ψ) q faces liftB branch)
    {n : Ω → ℤ} (hn : Measurable[𝓦 ⊔ MeasurableSpace.comap hB inferInstance] n) {a : ℝ}
    (hPhaseZero : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ i ξ, ξ ∈ faces i ω → height i ω ξ + chiC κ *
        (2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω) = forceBoundaryData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a) :
    IsPocketChartOn (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) A C ψ
        (fun ω => shiftChart (pChart A C ψ ω) (n ω)) ∧
      PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q := by
  have h𝓦 : 𝓦 ≤ mΩ := le_sup_left.trans hpre
  have hEm := Lemma725RefMarks.measurable_extA hA hCin
  have hhBm : Measurable hB := hhB.mono (germSigma_le (hEm.mono h𝓦 le_rfl) hh₀.measurable) le_rfl
  have hpre' : locPrefixSigma (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) A γ q ≤ mΩ := by
    rw [locPrefixSigma_sup_info]
    exact sup_le hpre hhBm.comap_le
  have hU := pocketStopUnionLaw_sup_pocketExterior hh₀ hpre hA hCin hhB hRawUnion
  have hUref : ∀ i, PocketStopUnionLaw
      ((𝓦 ⊔ MeasurableSpace.comap hB inferInstance) ⊔ referenceInfo i) P A γ C
      (fun ω => Fnow ω ∪ referenceHull Fold i ω) h₀ q := by
    intro i
    have hbasei : 𝓦 ≤ 𝓦 ⊔ referenceInfo i := le_sup_left
    have hprei : locPrefixSigma (𝓦 ⊔ referenceInfo i) A γ q ≤ mΩ := by
      rw [locPrefixSigma_sup_info]
      exact sup_le hpre (hInfo i)
    have hUi := pocketStopUnionLaw_sup_pocketExterior hh₀ hprei (hbasei _ hA)
      (fun U hUo hUH => hbasei _ (hCin U hUo hUH)) hhB (hRawReferenceUnion i)
    have heq : (𝓦 ⊔ referenceInfo i) ⊔ MeasurableSpace.comap hB inferInstance =
        (𝓦 ⊔ MeasurableSpace.comap hB inferInstance) ⊔ referenceInfo i := by ac_rfl
    rwa [heq] at hUi
  have hbase : 𝓦 ≤ 𝓦 ⊔ MeasurableSpace.comap hB inferInstance := le_sup_left
  exact pocketStopSideLimit_pChart_of_reference_union_laws hpre' hγ
    (isPocketChartOn_mono_info hbase hc) (fun z => hbase _ (hCm z)) hCo hact hFo
    hh₀ hU hBm hBloc hReferenceMarks hUref hBunb hgB hpieces
    hReferenceOwnHeights hInheritedArguments hn hPhaseZero

end InteractingSLE.Sec7.PocketStopSide
