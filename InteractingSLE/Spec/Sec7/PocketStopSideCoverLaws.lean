/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCoverGeometry
import InteractingSLE.Spec.Sec5.CrossRestartKernelField

/-!
# Local-set and complementary-component inputs for the pocket comparison

PROVE-STRIPSYS38. The active set's hitting measurability and locality follow from
the walls' marked stopping law by STRIPSYS35's filling transfer. The counterflow
hull at an own-filtration stop has the existing marked law at every positive
parameter, and its local-set property is transported and centered directly.
No claim is made here that the enlarged pocket time is such an own-filtration stop.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling

/-- Filling the pocket exterior unions the two complementary sets. -/
theorem lowerUnion_extHullSet (C F : Set ℂ) :
    lowerUnion (extHullSet C F) = Cᶜ ∪ lowerUnion F := by
  ext z
  simp only [lowerUnion, extHullSet, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
  constructor
  · rintro (⟨hzH, hzC | hzF⟩ | hzlow)
    · exact Or.inl hzC
    · exact Or.inr (Or.inl hzF)
    · exact Or.inr (Or.inr hzlow)
  · rintro (hzC | hzF | hzlow)
    · by_cases hzH : z ∈ H
      · exact Or.inl ⟨hzH, Or.inl hzC⟩
      · exact Or.inr (le_of_not_gt hzH)
    · by_cases hzH : z ∈ H
      · exact Or.inl ⟨hzH, Or.inr hzF⟩
      · exact Or.inr (le_of_not_gt hzH)
    · exact Or.inr hzlow

/-- Filling a simply connected pocket exterior preserves the absence of bounded
complementary components of a reference hull. No connectivity of the intersection
of the two active domains is assumed. -/
theorem not_isBounded_lowerUnion_extHullSet {C F : Set ℂ} (hCo : IsOpen C)
    (hCsc : IsSimplyConnected C)
    (hF : ∀ p ∈ lowerUnion F, ¬ IsBounded (connectedComponentIn (lowerUnion F) p)) :
    ∀ p ∈ lowerUnion (extHullSet C F),
      ¬ IsBounded (connectedComponentIn (lowerUnion (extHullSet C F)) p) := by
  rw [lowerUnion_extHullSet]
  intro p hp hb
  rcases hp with hp | hp
  · exact not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hCo hCsc hp
      (hb.subset (connectedComponentIn_mono p subset_union_left))
  · exact hF p hp (hb.subset (connectedComponentIn_mono p subset_union_right))

/-- Hitting measurability and locality of the active complement from the walls' law.
`hW` is the precise STRIPSYS37 input, still explicit when that packet is unavailable. -/
theorem activeCompl_localFacts_of_wallsLaw {Ω : Type*} {𝓦 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0}
    {C Γ F : Ω → Set ℂ} (h𝓦 : 𝓦 ≤ mΩ) (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F ω))
    (hW : PocketStopWallsLaw 𝓦 P A γ Γ F h₀ q) :
    Measurable[mΩ, hittingSigma] (activeCompl A γ c q) ∧
      IsLocalSet (activeCompl A γ c q) h₀ P := by
  have hU := pocketStopUnionLaw_of_wallsLaw h𝓦 hpre hCm hCo hΓC hfr hW
  have hK := pocketStopLaw_activeCompl hpre hact hCo hFo hU
  exact ⟨hK.1, ((isLocalSet_tfae hh₀ hK.1 hK.2.1).out 1 4).1
    (IsHistoryAvoidanceLocal.isAvoidanceLocal hK.2.2.1)⟩

/-- Both local-set facts of an own-stop strip hull, reusing the positive-parameter
counterflow hull law. Applying this at the enlarged `T(q)` still requires its stop
and chart-identification hypotheses; none is silently inferred from the strip system. -/
theorem stripHull_localFacts {q κ' : ℝ} (hq : 0 < q) (hκ' : 0 < κ') {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h h' : Ω → DistOn upperHalfPlaneOpens}
    {a k : ℝ} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (htr : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k (h ω) (h' ω))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = (Sec4.stripCounterflowChart q).2.1 ''
      QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    IsHistoryAvoidanceLocal hτ.measurableSpace A
        (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P ∧
      IsLocalSet A (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P := by
  refine ⟨Sec5.CrossRestart.isHistoryAvoidanceLocal_stripInv_hull hq hκ' hC htr hu₀ hh0
    hX hτ hτζ hA hAK, ?_⟩
  obtain ⟨-, -, -, hX', hker⟩ := hC
  have hraw := (hker τ hτ hτζ).1
  have hlocal := WholeField.IsLocalSet.sub_dist
    (Sec5.CrossRestart.isLocalSet_stripInv_image hq hraw htr)
    (WholeField.isHarmonicDistOn_smoothDist hu₀)
  exact Coupling.IsLocalSet.congr_set hlocal hAK

end InteractingSLE.Sec7.PocketStopSide
