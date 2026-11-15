/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCoverPieces
import InteractingSLE.Spec.Sec7.PocketStopSideCoverLaws

/-!
# The shifted pocket side limit from its physical reference pieces

PROVE-STRIPSYS38. This assembles the physical reference cover and exact inherited
argument calculation with the walls' stopping law and the reference local-set facts.
Hitting measurability, locality and the active complement's unbounded-component
condition are proved here, rather than passed to the comparison theorem as inputs.

The remaining hypotheses are explicit: physical selection, own reference heights,
transition arguments and word/phase alignment, determination of the stopped filled
set, and the local-set facts for the filled rational references. STRIPSYS37's walls
law remains named. This is conditional work, not an unconditional strip-system theorem.
Use parameter `κ = κ′` here, the counterflow parameter established in `exists_realization`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The side-limit predicate for the shifted canonical pocket chart, via the original
`pocketStopSideLimit_of_referenceCover`. The listed geometric and field inputs remain
separate obligations; in particular `hword` is the exact phase-zero identification. -/
theorem pocketStopSideLimit_pChart_of_pieces {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C Γ Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0}
    (h𝓦 : 𝓦 ≤ mΩ) (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ (pChart A C ψ) q ω = C ω ∩ (H \ Fnow ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hW : PocketStopWallsLaw 𝓦 P A γ Γ Fnow h₀ q)
    (hKdet : MeasurableSpace.comap (activeCompl A γ (pChart A C ψ) q) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h₀ inferInstance) P)
    (hBm : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet C Fold i))
    (hBloc : ∀ i, IsLocalSet (referenceSet C Fold i) h₀ P)
    (hBdet : ∀ i, MeasurableSpace.comap (referenceSet C Fold i) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h₀ inferInstance) P)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (referenceSet C Fold i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet C Fold i ω)) z))
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (referenceSet C Fold i) h₀ P (gB i))
    {faces : CoverRef → Ω → Set ℝ}
    (hpieces : PhysicalReferenceCover P A γ (pChart A C ψ) C Fnow Fold q
      (fun ω => forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)) faces)
    {u : ℂ → ℝ} {liftB : CoverRef → Ω → ℂ → ℝ} {height : CoverRef → Ω → ℝ → ℝ}
    (hheight : ReferenceHeightLimits (chiC κ) P A γ (pChart A C ψ) C Fold q u faces gB liftB height)
    {branch : CoverRef → Ω → ℝ → ℤ}
    (hlift : ReferenceLiftLimits P A γ (pChart A C ψ) q faces liftB branch)
    {n : Ω → ℤ} (hn : Measurable[𝓦] n) {a : ℝ}
    (hword : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ i ξ, ξ ∈ faces i ω → height i ω ξ + chiC κ *
        (2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω) = forceBoundaryData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a) :
    IsPocketChartOn 𝓦 A C ψ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) ∧
      PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q := by
  have hshift := isPocketChartOn_shift hc hCm hn
  have hact' : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ
      (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω = C ω ∩ (H \ Fnow ω) := hact
  obtain ⟨hKm, hKloc⟩ := activeCompl_localFacts_of_wallsLaw hh₀ h𝓦 hpre hCm hCo hΓC hfr hact' hFo hW
  have hKdet' : MeasurableSpace.comap
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h₀ inferInstance) P := by
    rw [activeCompl_shift]
    exact hKdet
  have hKunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω)) z) :=
    Eventually.of_forall
      (not_isBounded_lowerUnion_activeCompl (q := q) hγ (fun ω hω => (hshift.1 ω hω).1))
  have hcover := pocketStopBoundaryCover_of_pieces hγ (fun ω hω => (hc.1 ω hω).1)
    hact hpieces hheight hlift hword
  exact ⟨hshift, pocketStopSideLimit_of_referenceCover hh₀ hKm hKloc hKdet' hKunb
    hBm hBloc hBdet hBunb hgB hcover⟩

end InteractingSLE.Sec7.PocketStopSide
