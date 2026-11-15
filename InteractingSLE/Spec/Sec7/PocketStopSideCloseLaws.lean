/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCloseStops
import InteractingSLE.Spec.Sec7.PocketStopSideFinalComparison
import InteractingSLE.Spec.Sec7.PocketStopSideCoverLaws

/-!
# From the landed stopped laws to the active and reference comparison laws

PROVE-STRIPSYS38. The law at the maximum of the left pocket stop and an ordinary
reference stop is sufficient after the common exterior is filled. The two set
marks must be measurable for that retained history. Outside the live event the
active set is H, so no extra condition on the reference's value there is needed
beyond its inclusion in H. No field determination appears.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling PocketStopWallsFin

variable {Ω : Type*} {𝓦 ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Directly consume STRIPSYS41's union law at T(q). The intermediate walls law
and its filling hypotheses need not be supplied a second time. -/
theorem activeCompl_localFacts_of_unionLaw {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {C F : Ω → Set ℂ}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F ω))
    (hU : PocketStopUnionLaw 𝓦 P A γ C F h₀ q) :
    Measurable[mΩ, hittingSigma] (activeCompl A γ c q) ∧ IsLocalSet (activeCompl A γ c q) h₀ P := by
  have hK := pocketStopLaw_activeCompl hpre hact hCo hFo hU
  exact ⟨hK.1, ((isLocalSet_tfae hh₀ hK.1 hK.2.1).out 1 4).1
    (IsHistoryAvoidanceLocal.isAvoidanceLocal hK.2.2.1)⟩

/-- Filling the same exterior commutes with taking the union of two hulls. -/
theorem extHullSet_union (C F G : Set ℂ) :
    extHullSet C (F ∪ G) = extHullSet C F ∪ extHullSet C G := by
  ext z
  simp only [extHullSet, mem_inter_iff, mem_union]
  tauto

omit mΩ in
/-- The current active set union a reference is exactly the filled maximum
hull on the live event, and H off that event. -/
theorem activeCompl_union_reference_eq_liveExt {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {C F G B : Ω → Set ℂ} {q : ℝ≥0}
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hBH : ∀ ω, B ω ⊆ H)
    (hBeq : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → B ω = extHullSet (C ω) (G ω)) :
    (fun ω => activeCompl A γ c q ω ∪ B ω) = liveExt A γ C (fun ω => F ω ∪ G ω) q := by
  funext ω
  rw [activeCompl_eq_liveExt hact]
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [liveExt_of_live hl, liveExt_of_live hl, hBeq ω hl.1 hl.2, extHullSet_union]
  · rw [liveExt_of_not_live hl, liveExt_of_not_live hl]
    exact union_eq_left.2 (hBH ω)

omit [IsProbabilityMeasure P] in
/-- The marked-union input of the comparison follows from the filled union law
at the maximum stop, with the two set marks in its retained information. -/
theorem isHistoryAvoidanceLocal_active_reference_of_unionLaw
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {C F G B : Ω → Set ℂ} {q : ℝ≥0}
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hBH : ∀ ω, B ω ⊆ H)
    (hBeq : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → B ω = extHullSet (C ω) (G ω))
    (hmarks : MeasurableSpace.comap (activeCompl A γ c q) hittingSigma ⊔
      MeasurableSpace.comap B hittingSigma ≤ locPrefixSigma ℳ A γ q)
    (hUmax : PocketStopUnionLaw ℳ P A γ C (fun ω => F ω ∪ G ω) h₀ q) :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (activeCompl A γ c q) hittingSigma ⊔ MeasurableSpace.comap B hittingSigma)
      (fun ω => activeCompl A γ c q ω ∪ B ω) h₀ P := by
  obtain ⟨E, -, hEloc, hEq⟩ := hUmax
  have hloc := isHistoryAvoidanceLocal_liveExt (measurableSet_live (𝓦 := ℳ) A γ q) hEloc hEq
  rw [← activeCompl_union_reference_eq_liveExt hact hBH hBeq] at hloc
  exact fun U G hUH hG hd M hM => hloc U G hUH hG hd M (hmarks _ hM)

omit [IsProbabilityMeasure P] in
/-- R67 also transfers a comparison law after adjoining any fixed reference.
This is the equality needed after taking the maximum with its ordinary stop. -/
theorem pocketStopUnionLaw_union_of_ext_eq {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {C F₀ F₁ G : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {q : ℝ≥0}
    (hF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      extHullSet (C ω) (F₀ ω) = extHullSet (C ω) (F₁ ω))
    (hU : PocketStopUnionLaw 𝓦 P A γ C (fun ω => F₀ ω ∪ G ω) h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ C (fun ω => F₁ ω ∪ G ω) h₀ q := by
  obtain ⟨E, hEm, hEloc, hEq⟩ := hU
  refine ⟨E, hEm, hEloc, fun ω hω hq => (hEq ω hω hq).trans ?_⟩
  rw [extHullSet_union, extHullSet_union, hF ω hω hq]

omit [IsProbabilityMeasure P] in
/-- The actual bounded strip pocket's maximum-reference law transfers from T⁰(q)
to the unchanged right-stop consumer, with no new probabilistic argument. -/
theorem pocketStopUnionLaw_stopHull_reference_of_stopHull0 {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {R L : Ω → ℝ≥0 → ℂ} {r q : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {G : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hcfg : ∀ ω ∈ A, PocketWordAssembly.IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hU : PocketStopUnionLaw 𝓦 P A γ (fun ω => PocketJordan.cfPocket (R ω) (L ω) r)
      (fun ω => stopHull0 R L r W η ψ q ω ∪ G ω) h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ (fun ω => PocketJordan.cfPocket (R ω) (L ω) r)
      (fun ω => stopHull R L r W η ψ q ω ∪ G ω) h₀ q :=
  pocketStopUnionLaw_union_of_ext_eq (fun ω hω _ => extHullSet_stopHull0 (hcfg ω hω) q) hU

omit [IsProbabilityMeasure P] in
/-- The same R67 reference transfer for a pocket opening at the flow seed. -/
theorem pocketStopUnionLaw_stopHullInf_reference_of_stopHull0Inf {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {R L : Ω → ℝ≥0 → ℂ} {r q : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {G : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hcfg : ∀ ω ∈ A, PocketSeedOpen.IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hU : PocketStopUnionLaw 𝓦 P A γ (fun ω => PocketJordan.cfPocket (R ω) (L ω) r)
      (fun ω => stopHull0Inf R L r W η ψ q ω ∪ G ω) h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ (fun ω => PocketJordan.cfPocket (R ω) (L ω) r)
      (fun ω => stopHullInf R L r W η ψ q ω ∪ G ω) h₀ q :=
  pocketStopUnionLaw_union_of_ext_eq (fun ω hω _ => extHullSet_stopHull0Inf (hcfg ω hω) q) hU

end InteractingSLE.Sec7.PocketStopSide
