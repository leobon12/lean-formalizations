/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertJoint
import InteractingSLE.Spec.Sec7.PhaseContMeas
import InteractingSLE.Spec.Sec7.PocketStopSideCoverGeometry

/-!
# A pocket's active complement at its own relative time is a stop pocket

PROVE-R6-CERT. The canonical set `K_q = ℍ ∖ activeDom` of a pocket at relative time `q`
(`PocketStop.activeCompl`, the set whose local-set mean carries R.5's word) is an `R6Cert.IsStopPocket` for its marked
stop, as soon as the stop is finite exactly on the live event, the walls miss the pocket, and the relative active
domain misses the hull at the stop (the facts recorded for every configuration type by the landed walls-law
assemblies). Its locality follows from the single-pocket walls–hull law.

* **`isStopPocket_activeCompl`**;
* `activeCompl_regular_of_driven`, **`isLocalSet_of_isStopPocket`**.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cert

open PocketStopWallsFin PocketStopWalls PocketStop PocketCoupling PocketUnionPt PocketStopSide LocalSets WholeField
  PocketTraversal Lemma71C

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The active complement at relative time `q` is a stop pocket** for a marked stop `T` that is finite exactly on
the live event `A ∩ {q < ζ}`, walls `Γ` missing the pocket `C`, and a hull process `K` whose value at the stop misses
the relative active domain `C ∩ ψ⁻¹(ℍ ∖ K_q)`. -/
theorem isStopPocket_activeCompl {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} {K : ℝ≥0 → Ω → Set ℂ} {Γ : Ω → Set ℂ} (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u) {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω}) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω)) {q : ℝ≥0}
    {T : Ω → ℝ≥0∞} (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) 𝓕 X T)
    (hS0 : ∀ M, MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, 𝓕 r] M)
    (hTlive : ∀ ω, T ω < ⊤ → ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω))
    (hTfin : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤)
    (hΓC : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → Disjoint (H ∩ Γ ω) (C ω))
    (hKC : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      C ω ∩ ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) ⊆ H \ K (T ω).toNNReal ω) :
    IsStopPocket 𝓕 X K Γ (locPrefixSigma 𝓦 A γ q) T (activeCompl A γ c q) := by
  refine ⟨hG, hS0, PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc q,
    fun ω hT z hz => ?_, fun ω hT z hz => ?_⟩
  · obtain ⟨hωA, hl⟩ := hTlive ω hT
    obtain ⟨hcc, hdom, hfwd⟩ := hc ω hωA
    refine ⟨hz.1, fun hzD => ?_⟩
    rw [activeDom_eq hωA hl, PhaseCont.inv_image_diff_eq hcc hdom hfwd (hψ ω hωA)] at hzD
    obtain ⟨hzC, hzK⟩ := hzD
    rcases hz.2 with hzΓ | hzT
    · exact Set.disjoint_left.1 (hΓC ω hωA hl) ⟨hz.1, hzΓ⟩ hzC
    · exact (hKC ω hωA hl ⟨hzC, (hψ ω hωA).2.mapsTo hzC, hzK⟩).2 hzT
  · have hl : ¬ (ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)) := fun hl => (hTfin ω hl.1 hl.2).ne hT
    exact ⟨hz, by rw [activeDom_eq_empty hl]; exact fun h => h⟩

/-- **The active complement of a driven traversal in a conformal chart is relatively closed in `ℍ`**, at every
sample. -/
theorem activeCompl_regular_of_driven {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal) (ω : Ω) :
    activeCompl A γ c q ω ⊆ H ∧ IsOpen (H \ activeCompl A γ c q ω) := by
  refine ⟨sdiff_subset, ?_⟩
  rw [activeCompl, Set.sdiff_sdiff_right_self]
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [activeDom_eq_relChart_dom hl.1 hl.2 (hγ ω hl.1) (hc ω hl.1)]
    exact QuantumZipper.isOpen_H.inter (relChart c γ q ω).dom.isOpen
  · rw [activeDom_eq_empty hl, inter_empty]; exact isOpen_empty

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A stop pocket's set is local** (hitting-measurable and local for the centred field), from the single-pocket
walls–hull law at its marked stop. -/
theorem isLocalSet_of_isStopPocket {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) {Γ : Ω → Set ℂ} (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => LocalSets.markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T : Ω → ℝ≥0∞} {E : Ω → Set ℂ} (hP : IsStopPocket (drivingFiltration P hX) X (regHull W ζ) Γ ℳ T E)
    (hℳ : ℳ ≤ mΩ) (hreg : ∀ᵐ ω ∂P, E ω ⊆ H ∧ IsOpen (H \ E ω)) :
    Measurable[mΩ, hittingSigma] E ∧ IsLocalSet E (centredField h u₀) P := by
  have hJ := isHistoryAvoidanceLocal_walls_regHull_markedStop hC hκ hu₀ hX hζ hXm hΓ hW hP.marked hP.marks_le
  have hcov : ∀ ω, wallsHullAt Γ (regHull W ζ) T ω ⊆ E ω := fun ω => by
    by_cases hT : T ω < ⊤
    · rw [wallsHullAt, ite_eq_left hT]; exact hP.cover ω hT
    · rw [wallsHullAt, ite_eq_right hT]; exact hP.top ω (not_lt_top_iff.1 hT)
  have hloc := isHistoryAvoidanceLocal_of_joint hJ hP.meas (Eventually.of_forall hcov)
  have hm : Measurable[mΩ, hittingSigma] E := hP.meas.mono hℳ le_rfl
  exact ⟨hm, ((isLocalSet_tfae (isZeroBoundaryGFF_centredField hC hu₀) hm hreg).out 1 4).1
    hloc.isAvoidanceLocal⟩

end InteractingSLE.Sec7.R6Cert
