/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCBoxKernel
import InteractingSLE.Spec.Restart.RetPlumbProofFilled
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart

/-!
# First-contact assembly in the active component

This successor uses the filling of the physical explored union for locality.
Bounded swallowed components are retained inside the local obstacle. The original
`FCPlumbAssembly` is unchanged; its driver transfer and path bridge are reused.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open Chart DomainMarkov DomainMarkov.Aux79 K2 WholeField Sec7.PocketTraversal
open Coupling Sec2.Assembly LocalSets FCAux79

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The compact physical prefix of a capped pair, including its boundary points.
The finite cap also covers the branch on which the paths never meet. -/
def shCompactPrefix (η₁ η₂ : Ω → ℝ≥0 → ℂ) (m t₁ t₂ : ℝ≥0) (ω : Ω) : Set ℂ :=
  (η₁ ω '' Icc 0 (capT m (recFst (fullHist η₁ η₂ ω) + t₁))) ∪
    (η₂ ω '' Icc 0 (capT m (recSnd (fullHist η₁ η₂ ω) + t₂)))

/-- Clipping a stopped range at a time after which the path is frozen preserves its image. -/
theorem image_le_eq_image_capT {f : ℝ≥0 → ℂ} {m : ℝ≥0}
    (hfr : ∀ s, m ≤ s → f s = f m) (T : ℝ≥0∞) :
    f '' {s | (s : ℝ≥0∞) ≤ T} = f '' Icc 0 (capT m T) := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨min s m, ⟨zero_le, le_capT_iff.2 ⟨min_le_right _ _, ?_⟩⟩, ?_⟩
    · exact (ENNReal.coe_le_coe.2 (min_le_left _ _)).trans hs
    · by_cases hsm : s ≤ m
      · rw [min_eq_left hsm]
      · rw [min_eq_right (le_of_not_ge hsm), hfr s (le_of_not_ge hsm)]
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, (le_capT_iff.1 hs.2).2, rfl⟩

omit mΩ in
/-- The raw shifted union is the compact prefix intersected with the upper half-plane. -/
theorem shUnion_eq_shCompactPrefix_inter {η₁ η₂ : Ω → ℝ≥0 → ℂ} {m : ℝ≥0}
    (hfr₁ : ∀ ω s, m ≤ s → η₁ ω s = η₁ ω m)
    (hfr₂ : ∀ ω s, m ≤ s → η₂ ω s = η₂ ω m) (t₁ t₂ : ℝ≥0) (ω : Ω) :
    shUnion η₁ η₂ t₁ t₂ ω = shCompactPrefix η₁ η₂ m t₁ t₂ ω ∩ H := by
  rw [shUnion_eq, image_le_eq_image_capT (hfr₁ ω), image_le_eq_image_capT (hfr₂ ω)]
  rfl

omit mΩ in
theorem isCompact_shCompactPrefix {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (m t₁ t₂ : ℝ≥0) (ω : Ω) : IsCompact (shCompactPrefix η₁ η₂ m t₁ t₂ ω) :=
  (isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω))

omit mΩ in
/-- Closed hits of a finite prefix are read from its killed history. Only the coordinates
before the recorded stopping time are used. -/
theorem isDyadicHitMeasurable_image_capT {ℋ : MeasurableSpace Ω}
    {f : Ω → ℝ≥0 → ℂ} {ζ T : Ω → ℝ≥0∞}
    (hc : ∀ ω, Continuous (f ω))
    (hhist : Measurable[ℋ] (fun ω => khistOf (Sec6.pathCoord (f ω)) (ζ ω) (T ω)))
    (m : ℝ≥0) :
    @IsDyadicHitMeasurable Ω ℋ (fun ω => f ω '' Icc 0 (capT m (T ω))) := by
  let _ : MeasurableSpace Ω := ℋ
  let Y : Ω → KHist := fun ω => khistOf (Sec6.pathCoord (f ω)) (ζ ω) (T ω)
  have hT : Measurable T := (measurable_fst.comp measurable_fst).comp hhist
  have hq (j k : ℕ) :
      Measurable fun ω => (Y ω).1.2 ((k : ℚ≥0) / 2 ^ j) :=
    (measurable_pi_apply _).comp ((measurable_snd.comp measurable_fst).comp hhist)
  intro n i
  let Q := dyadicSquare n i
  have he : {ω | (Q ∩ f ω '' Icc 0 (capT m (T ω))).Nonempty} =
      ⋂ a : ℕ, ⋃ j : ℕ, ⋃ k : ℕ,
        ({ω | dyTime j k ≤ capT m (T ω)} ∩
          {ω | Metric.infDist ((Y ω).1.2 ((k : ℚ≥0) / 2 ^ j)) Q <
            1 / ((a : ℝ) + 1)}) := by
    ext ω
    have heq : ∀ j k, dyTime j k ≤ capT m (T ω) →
        (Y ω).1.2 ((k : ℚ≥0) / 2 ^ j) = f ω (dyTime j k) := by
      intro j k hjk
      have hcast : (((k : ℚ≥0) / 2 ^ j : ℚ≥0) : ℝ≥0) = dyTime j k := by
        simp [dyTime]
      have hle := (le_capT_iff.1 hjk).2
      simp only [Y, khistOf, Sec6.histOf, Sec6.stopCoord, Sec6.pathCoord, hcast,
        hle, ite_true]
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    have hhit : (Q ∩ f ω '' Icc 0 (capT m (T ω))).Nonempty ↔
        ∃ s ≤ capT m (T ω), f ω s ∈ Q := by
      constructor
      · rintro ⟨z, hzQ, s, hs, rfl⟩
        exact ⟨s, hs.2, hzQ⟩
      · rintro ⟨s, hs, hsQ⟩
        exact ⟨_, hsQ, s, ⟨zero_le, hs⟩, rfl⟩
    rw [hhit, exists_mem_iff_dyTime (hc ω).continuousOn
      (isClosed_dyadicSquare n i) (PairData.dyadicSquare_nonempty n i)]
    constructor <;> intro h a <;> obtain ⟨j, k, hjk, hdist⟩ := h a
    · exact ⟨j, k, hjk, by rw [heq j k hjk]; exact hdist⟩
    · exact ⟨j, k, hjk, by rw [← heq j k hjk]; exact hdist⟩
  rw [he]
  exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun k =>
      (measurableSet_le measurable_const (measurable_capT m hT)).inter
        (measurableSet_lt ((Metric.continuous_infDist_pt Q).measurable.comp (hq j k))
          measurable_const)

omit mΩ in
/-- The compact shifted prefix is dyadic-hit measurable in its labelled killed histories. -/
theorem isDyadicHitMeasurable_shCompactPrefix {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (m t₁ t₂ : ℝ≥0) :
    @IsDyadicHitMeasurable Ω
      (MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) inferInstance)
      (shCompactPrefix η₁ η₂ m t₁ t₂) := by
  let ℋ := MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) inferInstance
  have hh : Measurable[ℋ] (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) := comap_measurable _
  have h₁ := isDyadicHitMeasurable_image_capT hc₁ (measurable_fst.comp hh) m
  have h₂ := isDyadicHitMeasurable_image_capT hc₂ (measurable_snd.comp hh) m
  intro n k
  have he : {ω | (dyadicSquare n k ∩ shCompactPrefix η₁ η₂ m t₁ t₂ ω).Nonempty} =
      {ω | (dyadicSquare n k ∩
        η₁ ω '' Icc 0 (capT m (recFst (fullHist η₁ η₂ ω) + t₁))).Nonempty} ∪
      {ω | (dyadicSquare n k ∩
        η₂ ω '' Icc 0 (capT m (recSnd (fullHist η₁ η₂ ω) + t₂))).Nonempty} := by
    ext ω
    simp [shCompactPrefix, inter_union_distrib_left, union_nonempty]
  rw [he]
  exact (h₁ n k).union (h₂ n k)

/-- Filling a capped shifted prefix preserves its history-marked locality.
The filling is measurable in those histories, by the preceding closed-hit lemma. -/
theorem isHistoryAvoidanceLocal_fill_shCompactPrefix
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {m t₁ t₂ : ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω}
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => η₁ ω s) (hm₂ : ∀ s, Measurable fun ω => η₂ ω s)
    (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂)
    (hfr₁ : ∀ ω s, m ≤ s → η₁ ω s = η₁ ω m)
    (hfr₂ : ∀ ω s, m ≤ s → η₂ ω s = η₂ ω m)
    (hloc : IsHistoryAvoidanceLocal
      (mΩ ⊓ aeSigma (MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂)
        inferInstance) P) (shUnion η₁ η₂ t₁ t₂) h P) :
    IsHistoryAvoidanceLocal
      (mΩ ⊓ aeSigma (MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂)
        inferInstance) P)
      (fun ω => fillH (shCompactPrefix η₁ η₂ m t₁ t₂ ω)) h P := by
  let ℋ := MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t₁ t₂) inferInstance
  have hfill : Measurable[ℋ, hittingSigma]
      (fun ω => fillH (shCompactPrefix η₁ η₂ m t₁ t₂ ω)) :=
    @RetAux79.measurable_fillH_of_dyadic Ω ℋ _
      (isDyadicHitMeasurable_shCompactPrefix hc₁ hc₂ ζ₁ ζ₂ m t₁ t₂)
      (isCompact_shCompactPrefix hc₁ hc₂ m t₁ t₂)
  let _ : MeasurableSpace Ω := mΩ
  have hℋm : ℋ ≤ mΩ := by
    exact (measurable_shHist hm₁ hm₂ hζ₁ hζ₂ t₁ t₂).comap_le
  apply RetAux79.isHistoryAvoidanceLocal_of_enlargement hloc
  · intro ω z hz
    have hzK : z ∈ shCompactPrefix η₁ η₂ m t₁ t₂ ω := by
      rw [shUnion_eq_shCompactPrefix_inter hfr₁ hfr₂] at hz
      exact hz.1.1
    exact mem_fillH_of_mem_closure hz.2 (subset_closure hzK)
  · exact hfill.mono
      (le_inf (by exact hℋm) (le_aeSigma ℋ P)) le_rfl

/-- The filled capped locality input is obtained from the two flow lines. One pair of
capped versions works at every shifted line, and its filled prefixes are measurable. -/
theorem exists_filled_capped_locality
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ,
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ s, Measurable fun ω => ηc₁ ω s) ∧ (∀ s, Measurable fun ω => ηc₂ ω s) ∧
      (∀ ω s, m ≤ s → ηc₁ ω s = ηc₁ ω m) ∧ (∀ ω s, m ≤ s → ηc₂ ω s = ηc₂ ω m) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s)) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) ∧
      ∀ t₁ t₂ : ℝ≥0,
        (∀ ω, IsCompact (shCompactPrefix ηc₁ ηc₂ m t₁ t₂ ω)) ∧
        Measurable[mΩ, hittingSigma]
          (fun ω => fillH (shCompactPrefix ηc₁ ηc₂ m t₁ t₂ ω)) ∧
        IsHistoryAvoidanceLocal
          (mΩ ⊓ aeSigma (MeasurableSpace.comap
            (shHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m)
              (fun ω => cutLife (ζ₂ ω) m) t₁ t₂) inferInstance) P)
          (fun ω => fillH (shCompactPrefix ηc₁ ηc₂ m t₁ t₂ ω)) (centredField h u₀) P := by
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hfr₁, hfr₂, ha₁, ha₂, hlines⟩ :=
    exists_capped_shUnion_local_kernels hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m
  have hζ₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζ₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hfr₁, hfr₂, ha₁, ha₂, fun t₁ t₂ => ?_⟩
  have hcompact := isCompact_shCompactPrefix hc₁ hc₂ m t₁ t₂
  have hfill := @RetAux79.measurable_fillH_of_dyadic Ω
    (MeasurableSpace.comap (shHist ηc₁ ηc₂
      (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) t₁ t₂) inferInstance) _
    (isDyadicHitMeasurable_shCompactPrefix hc₁ hc₂ _ _ m t₁ t₂) hcompact
  refine ⟨hcompact, hfill.mono
    (measurable_shHist hm₁ hm₂ hζ₁ hζ₂ t₁ t₂).comap_le le_rfl, ?_⟩
  exact isHistoryAvoidanceLocal_fill_shCompactPrefix hc₁ hc₂ hm₁ hm₂ hζ₁ hζ₂ hfr₁ hfr₂
    (hlines t₁ t₂).2.1

/-- Locality data for the active component of a physical explored union.
The local obstacle includes every bounded swallowed pocket. -/
structure FCActiveLineLocality {P : Measure Ω} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {c : Ω → Chart}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (ℋ : Filtration ℝ≥0 mΩ)
    (A : ℝ≥0 → Ω → Set ℂ) : Prop where
  bounded : ∀ t ω, Bornology.IsBounded (A t ω)
  measurableFilled : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => fillH (A t ω))
  markedLocal : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (fun ω => fillH (A t ω))
    (centredField h u₀) P
  chartDomain : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
    H \ fillH (A t ω) = (c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))

/-- The exact remaining comparison of physical information with capped information:
their joined sigma algebra has the same completed trace on each physical box.
This condition records information on the boxes, without a global inclusion of filtrations. -/
def FCBoxTraceCompatibility (P : Measure Ω) (𝒢 : ℝ≥0 → MeasurableSpace Ω)
    (𝒦 : ℝ≥0 → ℕ → MeasurableSpace Ω) (B : ℝ≥0 → ℕ → Set Ω) : Prop :=
  ∀ t m D, MeasurableSet[𝒦 t m ⊔ 𝒢 t] D →
    MeasurableSet[aeSigma (𝒦 t m) P] (D ∩ B t m) ∧
      MeasurableSet[aeSigma (𝒢 t) P] (D ∩ B t m)

/-- The existing measurable relative capacity clock, as an `ℝ≥0` process in physical time. -/
def fcCapacityClock (d : PairData Ω) (E : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (cClock d E d.s₀ d.η₁ d.ζ₁ ω t).toNNReal

/-- Continuity of the concrete first-contact capacity clock, including its finite endpoint. -/
theorem continuous_fcCapacityClock {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω))
      (d.ζ₁ ω - d.s₀ ω)) (ω : Ω) :
    Continuous fun t => fcCapacityClock d E t ω :=
  continuous_real_toNNReal.comp (hs.continuous_cClock hd hclk ω)

/-- Clamping at the physical lifetime makes the concrete clock nondecreasing everywhere. -/
theorem monotone_fcCapacityClock {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω))
      (d.ζ₁ ω - d.s₀ ω)) (ω : Ω) :
    Monotone fun t => fcCapacityClock d E t ω := by
  classical
  by_cases hω : ω ∈ E
  · have hclamp : ∀ r : ℝ≥0, chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) r =
        chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)
          (min (r : ℝ≥0∞) (d.ζ₁ ω - d.s₀ ω)).toNNReal := by
      intro r
      unfold chartClock
      rw [IsContSpec.image_cPath_clamp hω r]
    intro a b hab
    unfold fcCapacityClock
    rw [hs.cClock_eq hd hω]
    change (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) a).toNNReal ≤
      (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) b).toNNReal
    rw [hclamp a, hclamp b]
    apply Real.toNNReal_le_toNNReal
    apply (hclk ω hω).strictMonoOn.monotoneOn
      (min_le_sub (d.s₀ ω) (d.ζ₁ ω) a) (min_le_sub (d.s₀ ω) (d.ζ₁ ω) b)
    simp only [toNNReal_min_coe]
    split_ifs
    · exact hab
    · exact min_le_min_right _ hab
  · intro a b _
    simp [fcCapacityClock, cClock, hω]

theorem fcCapacityClock_zero {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω))
      (d.ζ₁ ω - d.s₀ ω)) (ω : Ω) : fcCapacityClock d E 0 ω = 0 := by
  classical
  by_cases hω : ω ∈ E
  · unfold fcCapacityClock
    rw [hs.cClock_eq hd hω, (hclk ω hω).zero, Real.toNNReal_zero]
  · simp [fcCapacityClock, cClock, hω]

theorem measurable_fcCapacityClock {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁) (t : ℝ≥0) :
    Measurable (fcCapacityClock d E t) :=
  (hs.measurable_cClock hd t).real_toNNReal

/-- Adaptedness of the clock reduces to information about the chart prefix, using
the existing hitting-measurable capacity functional. -/
theorem measurable_fcCapacityClock_of_prefix {ℋ : MeasurableSpace Ω}
    {d : PairData Ω} {E : Set Ω} (hE : MeasurableSet[ℋ] E) (t : ℝ≥0)
    (hprefix : Measurable[ℋ, hittingSigma]
      (fun ω => cPath d E d.s₀ d.η₁ d.ζ₁ ω '' Icc 0 t)) :
    Measurable[ℋ] (fcCapacityClock d E t) := by
  let _ : MeasurableSpace Ω := ℋ
  exact (Measurable.ite hE
    (((measurable_hcapHit.comp hprefix).ennreal_toReal).div_const 2) measurable_const).real_toNNReal

/-- The concrete clock reaches every capacity below its existing `cLife` lifetime. -/
theorem exists_le_fcCapacityClock {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω))
      (d.ζ₁ ω - d.s₀ ω)) {ω : Ω} (hω : ω ∈ E) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < cLife d E d.s₀ d.η₁ d.ζ₁ ω) :
    ∃ t, q ≤ fcCapacityClock d E t ω := by
  classical
  rw [cLife, if_pos hω, hs.cClock_eq hd hω] at hq
  obtain ⟨t, ht⟩ := RetAux79.exists_le_toNNReal_of_lt_capLife (hclk ω hω) hq
  refine ⟨t, ?_⟩
  simpa only [fcCapacityClock, hs.cClock_eq hd hω] using ht

/-- Any canonical clock has the same capacity lifetime as the concrete measurable
clock on its good event. No regularity of the supplied chart path off that event is required. -/
theorem ae_canon_life_eq_cLife {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁) {P : Measure Ω}
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ E → U₁ ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω := by
  classical
  filter_upwards [hcanon] with ω hcan hω
  have hpath : cPath d E d.s₀ d.η₁ d.ζ₁ ω = cPath d univ d.s₀ d.η₁ d.ζ₁ ω := by
    funext r
    rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  rw [cLife, if_pos hω, hs.cClock_eq hd hω, hpath]
  exact ((hcan (hs.subset hω)).1 (hs.lt ω hω)).2

/-- Coordinate adaptation suffices for the whole generated driver filtration to be
contained in the time change. The remaining measurability input concerns only the
actual driver coordinates, rather than every event of the generated filtration. -/
theorem fcDriverFiltration_le_timeChange {Y : Type*} [MeasurableSpace Y]
    (β : Ω → Y) (W : ℝ≥0 → Ω → ℝ) (hβ : Measurable β) (hW : ∀ q, Measurable (W q))
    {𝓖 : Filtration ℝ≥0 mΩ} {Qc : ℝ≥0 → Ω → ℝ≥0}
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hβ0 : Measurable[𝓖 0] β)
    (hprefix : ∀ q, Measurable[timeChange 𝓖 Qc hQa q] (W q)) (q : ℝ≥0) :
    fcDriverFiltration β W hβ hW q ≤ timeChange 𝓖 Qc hQa q := by
  change MeasurableSpace.comap β inferInstance ⊔
    (⨆ r : ℝ≥0, ⨆ (_ : r ≤ q), MeasurableSpace.comap (W r) inferInstance) ≤ _
  refine sup_le ?_ (iSup₂_le fun r hr => ?_)
  · exact hβ0.comap_le.trans ((le_timeChange_zero (𝓖 := 𝓖) (Qc := Qc) (hQa := hQa)).trans
      ((timeChange 𝓖 Qc hQa).mono (zero_le (a := q))))
  · exact (hprefix r).comap_le.trans ((timeChange 𝓖 Qc hQa).mono hr)

theorem measurableSet_fcDriverFiltration_cut {Y : Type*} [MeasurableSpace Y]
    (β : Ω → Y) (W : ℝ≥0 → Ω → ℝ) (hβ : Measurable β) (hW : ∀ q, Measurable (W q))
    {𝓖 : Filtration ℝ≥0 mΩ} {Qc : ℝ≥0 → Ω → ℝ≥0}
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hβ0 : Measurable[𝓖 0] β)
    (hprefix : ∀ q, Measurable[timeChange 𝓖 Qc hQa q] (W q))
    {q : ℝ≥0} {D : Set Ω} (hD : MeasurableSet[fcDriverFiltration β W hβ hW q] D)
    (t : ℝ≥0) : MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}) :=
  measurableSet_inter_of_timeChange
    (fcDriverFiltration_le_timeChange β W hβ hW hQa hβ0 hprefix q D hD) t

/-- Compact safe events for the concrete clock follow from hitting measurability
of the chart hull and physical measurability of the threshold lifetime. -/
theorem measurableSet_fcCapacityClock_safe {d : PairData Ω} {E : Set Ω}
    {ℋ : MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {t : ℝ≥0}
    (hQ : Measurable[ℋ] (fcCapacityClock d E t)) (hV : Measurable[ℋ] V)
    (hWc : ∀ ω, Continuous fun q => W q ω)
    (hHull : Measurable[ℋ, hittingSigma]
      (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (fcCapacityClock d E t ω)))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    MeasurableSet[ℋ] (lineSafe (fcCapacityClock d E) W V C t) := by
  apply RetAux79.measurableSet_lineSafe_of_hull hC hCH
    (RetAux79.measurableSet_lineLive hQ hV) hHull
  intro ω
  exact ⟨QuantumZipper.fwdHull_mono.2 _,
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((hWc ω).comp continuous_real_toNNReal)
      (fcCapacityClock d E t ω).coe_nonneg⟩

/-- Two sigma algebras with the same completed trace on an event give the same
conditional expectation there. This is the two-sided form of `ae_condExp_eq_of_trace`. -/
theorem ae_condExp_eq_on_of_common_trace {P : Measure Ω} [IsProbabilityMeasure P]
    {𝒦 𝒢 : MeasurableSpace Ω} (h𝒦 : 𝒦 ≤ mΩ) (h𝒢 : 𝒢 ≤ mΩ) {B : Set Ω}
    (htr : ∀ D, MeasurableSet[𝒦 ⊔ 𝒢] D →
      MeasurableSet[aeSigma 𝒦 P] (D ∩ B) ∧ MeasurableSet[aeSigma 𝒢 P] (D ∩ B))
    {X : Ω → ℂ} (hX : Integrable X P) :
    ∀ᵐ ω ∂P, ω ∈ B → P[X | 𝒢] ω = P[X | 𝒦] ω := by
  let _ : MeasurableSpace Ω := mΩ
  have h₁ := ae_condExp_eq_of_trace (𝒦 := 𝒦) le_sup_left (sup_le h𝒦 h𝒢)
    (fun D hD => (htr D hD).1) hX
  have h₂ := ae_condExp_eq_of_trace (𝒦 := 𝒢) le_sup_right (sup_le h𝒦 h𝒢)
    (fun D hD => (htr D hD).2) hX
  filter_upwards [h₁, h₂] with ω h₁ω h₂ω hω
  exact (h₂ω hω).symm.trans (h₁ω hω)

/-- Capped line kernels and their identified means glue to one conditioning sigma algebra.
The local-set mean can depend on the cap. At each line a box containing the sample is
selected once, and the same selection is used for the kernel and the mean identity. -/
theorem exists_common_lineMean_of_box_kernels
    {P : Measure Ω} [IsProbabilityMeasure P] {κ a : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (𝒢 : ℝ≥0 → MeasurableSpace Ω) (h𝒢 : ∀ t, 𝒢 t ≤ mΩ)
    (𝒦 : ℝ≥0 → ℕ → MeasurableSpace Ω) (h𝒦 : ∀ t m, 𝒦 t m ≤ mΩ)
    (B : ℝ≥0 → ℕ → Set Ω) (hcover : ∀ t ω, ω ∈ F → ∃ m, ω ∈ B t m)
    (htr : FCBoxTraceCompatibility P 𝒢 𝒦 B)
    (M : ℝ≥0 → ℕ → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ t m (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ F → ω ∈ B t m → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦 t m] ω =
        Complex.exp (Complex.I * (M t m ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
            ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)))
              φ φ : ℝ) : ℂ)))
    (hmean : ∀ t m (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ F → ω ∈ B t m → ω ∈ lineSafe Qc W ζ (tsupport ψ) t →
        Chart.chartTransport (hc ω) 1 a (chiC κ) (M t m ω) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (Qc t ω)
            (bheProc κ ρL ρR W VL VR ω (Qc t ω)) z * ψ z) :
    ∃ Mline : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      FCLineKernelStatement (P := P) (F := F) (Qc := Qc) (c := c) (W := W)
        (ζ := ζ) (h := h) 𝒢 Mline ∧
      FCLineMeanStatement (P := P) (κ := κ) (ρL := ρL) (ρR := ρR)
        (F := F) (Qc := Qc) (c := c) (W := W) (VL := VL) (VR := VR)
        (ζ := ζ) hc a Mline := by
  classical
  let j : ℝ≥0 → Ω → ℕ := fun t ω =>
    if hB : ∃ m, ω ∈ B t m then Nat.find hB else 0
  have hj : ∀ t ω, ω ∈ F → ω ∈ B t (j t ω) := by
    intro t ω hω
    have he := hcover t ω hω
    simpa only [j, dif_pos he] using Nat.find_spec he
  refine ⟨fun t ω => M t (j t ω) ω, ?_, ?_⟩
  · intro t φ
    have hce : ∀ m, ∀ᵐ ω ∂P, ω ∈ B t m →
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢 t] ω =
          P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦 t m] ω := fun m =>
      ae_condExp_eq_on_of_common_trace (h𝒦 t m) (h𝒢 t) (htr t m)
        (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh))
    filter_upwards [ae_all_iff.2 (hker t · φ), ae_all_iff.2 hce]
      with ω hk hceω hω hlt hsupp
    exact (hceω (j t ω) (hj t ω hω)).trans (hk (j t ω) hω (hj t ω hω) hlt hsupp)
  · intro t ψ
    filter_upwards [ae_all_iff.2 (hmean t · ψ)] with ω hm hω hs
    exact hm (j t ω) hω (hj t ω hω) hs

/-- First-contact determination with locality on the active component. The
force-coordinate regularity is derived from the stopped continuous segment driver.
The remaining line laws and concrete clock facts are explicit inputs. -/
theorem firstContactCanonCondDet_of_active_lineMean
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓖 : Filtration ℝ≥0 mΩ} {live E : Set Ω}
    (hliveMeas : MeasurableSet live) (hliveG0 : MeasurableSet[𝓖 0] live)
    (β : Ω → BoundaryWord) (hβ : Measurable β)
    (hType : ∀ ω ∈ live, β ω ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    (hE : MeasurableSet E)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ ω ∈ E, Sec7.Lemma71C.IsSegCurve (InteractingSLE.Restart.realPath (Γ ω)))
    (hsegMeas : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω))
        (fcDriverStopTime U q ω))
    (hLiveNatural : MeasurableSet[fcSegmentNaturalFiltration β hβ hE hsegMeas 0] live)
    (hstopCont : FCStoppedDriverContinuous E Γ U)
    (hthreshold : ∀ᵐ ω ∂P, ω ∈ live →
      U ω = fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω)
    (htrace : ∀ᵐ ω ∂P, ω ∈ live →
      IsGeneratingTrace (fun t => fcSegmentProcess E Γ U t ω)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω) (Γ ω))
    (Qc : ℝ≥0 → Ω → ℝ≥0)
    (hQcCont : ∀ ω, Continuous fun t => Qc t ω)
    (hQcMono : ∀ ω, Monotone fun t => Qc t ω)
    (hQc0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (hcapMeas : ∀ q D, MeasurableSet[fcSegmentNaturalFiltration β hβ hE hsegMeas q] D → ∀ t,
      MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ live →
      (q : ℝ≥0∞) < fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω → ∃ t, q ≤ Qc t ω)
    (hSline : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] (lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (tsupport ψ) t))
    (hSball : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] (lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (ballsK Fb) t))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (hHc : Measurable Hc)
    (htransport : ∀ ω, Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) =
      Exist.flowField 0 (θ * chiC κ) (Hc ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) (P.restrict live))
    (hseed : ∀ᵐ ω ∂P, ω ∈ live → ¬ ForceWord.ThresholdCondition ρL ρR 0
      (fcWordLeftPositions κ θ nL nR ρL ρR β ω) (fcWordRightPositions κ θ nL nR ρL ρR β ω))
    {S : Type} [mS : MeasurableSpace S] (X : Ω → S) (hX : Measurable X)
    (Hs : S → DistOn upperHalfPlaneOpens) (hHs : Measurable Hs)
    (Γs : S → ℝ≥0 → ℂ) (Us : S → ℝ≥0∞)
    (hΓsCont : ∀ s, ContinuousOn (Γs s) {t | (t : ℝ≥0∞) ≤ Us s})
    (Ws : ℝ≥0 → S → ℝ) (Ls : S → ℝ≥0∞)
    (hWsCont : ∀ s, ContinuousOn (fun t => Ws t s) {t | (t : ℝ≥0∞) < Ls s})
    (hHsState : ∀ ω, Hs (X ω) = Hc ω)
    (hΓState : ∀ ω, Γs (X ω) = Γ ω)
    (hUState : ∀ ω, Us (X ω) = U ω)
    (hWState : ∀ t ω, Ws t (X ω) = fcSegmentProcess E Γ U t ω)
    (hLState : ∀ ω, Ls (X ω) = fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω)
    (A : ℝ≥0 → Ω → Set ℂ)
    {ℋlocal : Filtration ℝ≥0 mΩ}
    (hGlocal : ∀ t, 𝓖 t ≤ ℋlocal t)
    (hLocal : FCActiveLineLocality (P := P) (F := live) (Qc := Qc) (h := h) (u₀ := u₀)
      (c := c) (W := fcSegmentProcess E Γ U)
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) ℋlocal A)
    {𝒢L : ℝ≥0 → MeasurableSpace Ω}
    (h𝓖L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝓖Lm : ∀ t, 𝒢L t ≤ mΩ)
    (Mline : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (B : ℕ → Set Ω)
    (hcover : ∀ t ω, ω ∈ live →
      (Qc t ω : ℝ≥0∞) < fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω → ∃ m, ω ∈ B m)
    (hbox : FCBoxKernelStatement (P := P) (F := live) (Qc := Qc) (c := c)
      (W := fcSegmentProcess E Γ U)
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (h := h) 𝒢L Mline B)
    (hlineMean : FCLineMeanStatement (P := P) (κ := κ) (ρL := ρL) (ρR := ρR)
      (F := live) (Qc := Qc) (c := c) (W := fcSegmentProcess E Γ U)
      (VL := geomLW (fcSegmentProcess E Γ U) (fcWordLeftPositions κ θ nL nR ρL ρR β))
      (VR := geomRW (fcSegmentProcess E Γ U) (fcWordRightPositions κ θ nL nR ρL ρR β))
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) hc (θ * chiC κ) Mline)
    {Fcode : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFcode : IsCanonicalFlowCode κ θ Fcode)
    {Gcode : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hGcode : IsCanonicalDriverCode κ θ Gcode)
    {K : Kernel BoundaryWord S} [IsMarkovKernel K]
    (hjoint : (P.restrict live).map (fun ω => (β ω, X ω)) = (P.restrict live).map β ⊗ₘ K)
    (hgff : ∀ᵐ b ∂(P.restrict live).map β,
      b.IsSorted ∧ IsGFFWithBoundaryData (K b) Hs b.fn b.jumps) :
    ∀ᵐ ω ∂P, ω ∈ live →
      IsCodeMatch (Fcode ((β ω, 0), Hc ω)) (Γ ω) (U ω) := by
  classical
  let W : ℝ≥0 → Ω → ℝ := fcSegmentProcess E Γ U
  let ζ : Ω → ℝ≥0∞ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β
  let xL : Ω → Fin nL → ℝ := fcWordLeftPositions κ θ nL nR ρL ρR β
  let xR : Ω → Fin nR → ℝ := fcWordRightPositions κ θ nL nR ρL ρR β
  let 𝓗 : Filtration ℝ≥0 mΩ := fcSegmentNaturalFiltration β hβ hE hsegMeas
  let hWmeas : ∀ t, Measurable (W t) := by
    intro t
    change Measurable (fun ω => fcSegmentDriver E Γ U t ω)
    exact fcSegmentDriverMeasurable hE hsegMeas t
  have hW0 : ∀ ω, W 0 ω = 0 := fcSegmentDriver_zero hseg
  have hWcont : ∀ ω, Continuous fun t => W t ω := continuous_fcSegmentDriver hstopCont
  have hNatural : 𝓗 = fcDriverFiltration β W hβ hWmeas := by rfl
  have hFilAdapt := fcDriverFiltration_adapted β W hβ hWmeas
  have hWadapt : StronglyAdapted 𝓗 W := by
    rw [hNatural]
    exact hFilAdapt.2
  have hβadapt : Measurable[𝓗 0] β := by
    rw [hNatural]
    exact hFilAdapt.1
  have hxL0 : Measurable[𝓗 0] xL := by
    change Measurable[𝓗 0] (fun ω => FCDet.typeXL κ θ nL nR ρL ρR (β ω))
    exact (FCDet.measurable_typeXL κ θ nL nR ρL ρR).comp hβadapt
  have hxR0 : Measurable[𝓗 0] xR := by
    change Measurable[𝓗 0] (fun ω => FCDet.typeXR κ θ nL nR ρL ρR (β ω))
    exact (FCDet.measurable_typeXR κ θ nL nR ρL ρR).comp hβadapt
  have hreg : ∀ᵐ ω ∂P, ω ∈ live → IsForceReg W (geomLW W xL) (geomRW W xR) ζ ω :=
    ae_of_all P fun ω _ => isForceReg_fcSegmentProcess hseg hstopCont xL xR ζ ω
  have hker := fcLineKernel_of_boxwise (P := P) (F := live) (Qc := Qc) (c := c)
    (W := W) (ζ := ζ) (h := h) 𝒢L Mline B hcover hbox
  have hSafeLaw := hasSafeLaw_of_FCLineMean (P := P) (κ := κ) (ρL := ρL) (ρR := ρR)
    (𝓖 := 𝓖) (𝓗' := 𝓗) (F := live) hliveG0 (hc := hc) hdom hfwd hliftm hliftc
    (h := h) hhm (θ * chiC κ) hQcCont hQcMono hQc0 hQa hcapMeas hreach hreg hSline
    𝒢L h𝓖L h𝓖Lm Mline hker hlineMean
  have hSafeMembers := hasSafeMembers_of_lineLocal (P := P) (nL := nL) (nR := nR)
    (𝓖 := 𝓖) (𝓗' := 𝓗) (F := live) (Qc := Qc) (W := W) (ζ := ζ) (VL := geomLW W xL)
    (VR := geomRW W xR) (h := h) hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift
    (θ * chiC κ) (chiC κ) hQcCont hQcMono hQc0 hQa hcapMeas hreach hreg hSball
    (fun t => ℋlocal t) hGlocal (fun t => ℋlocal.le t) (fun t ω => fillH (A t ω))
    hLocal.measurableFilled
    (fun t ω => ⟨fillH_subset_H _, isOpen_H_diff_fillH (hLocal.bounded t ω)⟩)
    hLocal.markedLocal hLocal.chartDomain
  have hSafeLaw' : HasSafeLaw κ ρL ρR P 𝓗 live ζ W (geomLW W xL) (geomRW W xR)
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) := by
    simpa only [htransport] using hSafeLaw
  have hSafeMembers' : HasSafeMembers P 𝓗 live ζ W
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) := by
    simpa only [htransport] using hSafeMembers
  have hdriver := FCDet.ae_driverCodeMatch_of_hasSafeLaw_on (P := P) hκ
    (𝓗 := 𝓗) (M := live) hLiveNatural hβadapt hType hW0 hWcont hWadapt
    (Hc := Hc) hHc hint hseed hSafeLaw' hSafeMembers' hGcode
  have hdriverζ : ∀ᵐ ω ∂P, ω ∈ live →
      IsDriverCodeMatch (Gcode (β ω, Hc ω)) (fun t => W t ω) (ζ ω) := by
    filter_upwards [hdriver] with ω hdrv hωlive
    change IsDriverCodeMatch (Gcode (β ω, Hc ω)) (fun t => W t ω)
      (FCDet.thr ρL ρR W (fun ω => FCDet.typeXL κ θ nL nR ρL ρR (β ω))
        (fun ω => FCDet.typeXR κ θ nL nR ρL ρR (β ω)) ω)
    exact hdrv hωlive
  have hdriverState : ∀ᵐ ω ∂P, ω ∈ live →
      IsDriverCodeMatch (Gcode (β ω, Hs (X ω))) (fun t => Ws t (X ω)) (Ls (X ω)) := by
    filter_upwards [hdriverζ] with ω hdrv hωlive
    have hWfun : (fun t => Ws t (X ω)) = (fun t => W t ω) := funext fun t => by
      exact hWState t ω
    simpa only [hHsState ω, hWfun, hLState ω] using hdrv hωlive
  have hWzero : ∀ᵐ ω ∂P, ω ∈ live → Ws 0 (X ω) = 0 := by
    filter_upwards [ae_of_all _ fun ω => hW0 ω] with ω hzero hωlive
    rw [hWState 0 ω]
    exact hzero
  have htraceState : ∀ᵐ ω ∂P, ω ∈ live →
      IsGeneratingTrace (fun t => Ws t (X ω)) (Ls (X ω)) (Γs (X ω)) := by
    filter_upwards [htrace] with ω htr hωlive
    have hWfun : (fun t => Ws t (X ω)) = (fun t => W t ω) := funext fun t => by
      exact hWState t ω
    simpa only [hWfun, hLState ω, hΓState ω] using htr hωlive
  have hUL : ∀ᵐ ω ∂P, ω ∈ live → Us (X ω) = Ls (X ω) := by
    filter_upwards [hthreshold] with ω hω hωlive
    calc
      Us (X ω) = U ω := hUState ω
      _ = ζ ω := hω hωlive
      _ = Ls (X ω) := (hLState ω).symm
  have hbridge := InteractingSLE.Restart.ae_codeMatch_of_driverCodeMatch_of_generatingTrace
    (Ω := Ω) (C := BoundaryWord) (S := S) (P := P) (M := live) hliveMeas hβ hX
    (K := K) hjoint (w := id) measurable_id (H := Hs) hHs (Γ := Γs) (U := Us)
    hΓsCont (W := Ws) (L := Ls) hWsCont
    (κ := κ) (θ := θ) (F := Fcode) hFcode (G := Gcode) hGcode hgff hdriverState
    hWzero htraceState hUL
  filter_upwards [hbridge] with ω hmatch hωlive
  simpa only [hHsState ω, hΓState ω, hUState ω, id_eq] using hmatch hωlive


/-- Repaired first-contact assembly with cap-dependent means and conditioning.
The countable gluing is proved above; its precise remaining stochastic input is
`FCBoxTraceCompatibility`, rather than a boxwise assertion already using a common sigma algebra. -/
theorem firstContactCanonCondDet_of_active_box_kernels
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓖 : Filtration ℝ≥0 mΩ} {live E : Set Ω}
    (hliveMeas : MeasurableSet live) (hliveG0 : MeasurableSet[𝓖 0] live)
    (β : Ω → BoundaryWord) (hβ : Measurable β)
    (hType : ∀ ω ∈ live, β ω ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    (hE : MeasurableSet E)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ ω ∈ E, Sec7.Lemma71C.IsSegCurve (InteractingSLE.Restart.realPath (Γ ω)))
    (hsegMeas : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω))
        (fcDriverStopTime U q ω))
    (hLiveNatural : MeasurableSet[fcSegmentNaturalFiltration β hβ hE hsegMeas 0] live)
    (hstopCont : FCStoppedDriverContinuous E Γ U)
    (hthreshold : ∀ᵐ ω ∂P, ω ∈ live →
      U ω = fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω)
    (htrace : ∀ᵐ ω ∂P, ω ∈ live →
      IsGeneratingTrace (fun t => fcSegmentProcess E Γ U t ω)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω) (Γ ω))
    (Qc : ℝ≥0 → Ω → ℝ≥0)
    (hQcCont : ∀ ω, Continuous fun t => Qc t ω)
    (hQcMono : ∀ ω, Monotone fun t => Qc t ω)
    (hQc0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (hcapMeas : ∀ q D, MeasurableSet[fcSegmentNaturalFiltration β hβ hE hsegMeas q] D → ∀ t,
      MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ live →
      (q : ℝ≥0∞) < fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω → ∃ t, q ≤ Qc t ω)
    (hSline : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] (lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (tsupport ψ) t))
    (hSball : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] (lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (ballsK Fb) t))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (hHc : Measurable Hc)
    (htransport : ∀ ω, Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) =
      Exist.flowField 0 (θ * chiC κ) (Hc ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) (P.restrict live))
    (hseed : ∀ᵐ ω ∂P, ω ∈ live → ¬ ForceWord.ThresholdCondition ρL ρR 0
      (fcWordLeftPositions κ θ nL nR ρL ρR β ω) (fcWordRightPositions κ θ nL nR ρL ρR β ω))
    {S : Type} [mS : MeasurableSpace S] (X : Ω → S) (hX : Measurable X)
    (Hs : S → DistOn upperHalfPlaneOpens) (hHs : Measurable Hs)
    (Γs : S → ℝ≥0 → ℂ) (Us : S → ℝ≥0∞)
    (hΓsCont : ∀ s, ContinuousOn (Γs s) {t | (t : ℝ≥0∞) ≤ Us s})
    (Ws : ℝ≥0 → S → ℝ) (Ls : S → ℝ≥0∞)
    (hWsCont : ∀ s, ContinuousOn (fun t => Ws t s) {t | (t : ℝ≥0∞) < Ls s})
    (hHsState : ∀ ω, Hs (X ω) = Hc ω)
    (hΓState : ∀ ω, Γs (X ω) = Γ ω)
    (hUState : ∀ ω, Us (X ω) = U ω)
    (hWState : ∀ t ω, Ws t (X ω) = fcSegmentProcess E Γ U t ω)
    (hLState : ∀ ω, Ls (X ω) = fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω)
    (A : ℝ≥0 → Ω → Set ℂ)
    {ℋlocal : Filtration ℝ≥0 mΩ}
    (hGlocal : ∀ t, 𝓖 t ≤ ℋlocal t)
    (hLocal : FCActiveLineLocality (P := P) (F := live) (Qc := Qc) (h := h) (u₀ := u₀)
      (c := c) (W := fcSegmentProcess E Γ U)
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) ℋlocal A)
    {𝒢L : ℝ≥0 → MeasurableSpace Ω}
    (h𝓖L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝓖Lm : ∀ t, 𝒢L t ≤ mΩ)
    (𝒦 : ℝ≥0 → ℕ → MeasurableSpace Ω) (h𝒦 : ∀ t m, 𝒦 t m ≤ mΩ)
    (B : ℝ≥0 → ℕ → Set Ω) (hcover : ∀ t ω, ω ∈ live → ∃ m, ω ∈ B t m)
    (htr : FCBoxTraceCompatibility P 𝒢L 𝒦 B)
    (M : ℝ≥0 → ℕ → Ω → DistOn upperHalfPlaneOpens)
    (hbox : ∀ t m (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ live → ω ∈ B t m → (Qc t ω : ℝ≥0∞) < (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) ω →
      tsupport φ ⊆ (c ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => (fcSegmentProcess E Γ U) s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦 t m] ω =
        Complex.exp (Complex.I * (M t m ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
            ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => (fcSegmentProcess E Γ U) s.toNNReal ω) (Qc t ω)))
              φ φ : ℝ) : ℂ)))
    (hboxMean : ∀ t m (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ live → ω ∈ B t m → ω ∈ lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (tsupport ψ) t →
        Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (M t m ω) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => (fcSegmentProcess E Γ U) s.toNNReal ω) (Qc t ω)
            (bheProc κ ρL ρR (fcSegmentProcess E Γ U)
              (geomLW (fcSegmentProcess E Γ U) (fcWordLeftPositions κ θ nL nR ρL ρR β))
              (geomRW (fcSegmentProcess E Γ U) (fcWordRightPositions κ θ nL nR ρL ρR β))
              ω (Qc t ω)) z * ψ z)
    {Fcode : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFcode : IsCanonicalFlowCode κ θ Fcode)
    {Gcode : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hGcode : IsCanonicalDriverCode κ θ Gcode)
    {K : Kernel BoundaryWord S} [IsMarkovKernel K]
    (hjoint : (P.restrict live).map (fun ω => (β ω, X ω)) = (P.restrict live).map β ⊗ₘ K)
    (hgff : ∀ᵐ b ∂(P.restrict live).map β,
      b.IsSorted ∧ IsGFFWithBoundaryData (K b) Hs b.fn b.jumps) :
    ∀ᵐ ω ∂P, ω ∈ live →
      IsCodeMatch (Fcode ((β ω, 0), Hc ω)) (Γ ω) (U ω) := by
  obtain ⟨Mline, hker, hmean⟩ := exists_common_lineMean_of_box_kernels
    (κ := κ) (a := θ * chiC κ) (ρL := ρL) (ρR := ρR)
    (VL := geomLW (fcSegmentProcess E Γ U) (fcWordLeftPositions κ θ nL nR ρL ρR β))
    (VR := geomRW (fcSegmentProcess E Γ U) (fcWordRightPositions κ θ nL nR ρL ρR β))
    hc hhm 𝒢L h𝓖Lm 𝒦 h𝒦 B hcover htr M hbox hboxMean
  exact firstContactCanonCondDet_of_active_lineMean hκ hliveMeas hliveG0 β hβ hType hE
    hseg hsegMeas hLiveNatural hstopCont hthreshold htrace Qc hQcCont hQcMono hQc0 hQa
    hcapMeas hreach hSline hSball hc hdom hfwd hliftm hliftc hlift hhm hu₀ hh0 Hc hHc
    htransport hint hseed X hX Hs hHs Γs Us hΓsCont Ws Ls hWsCont hHsState hΓState
    hUState hWState hLState A hGlocal hLocal h𝓖L h𝓖Lm Mline (fun _ => live)
    (fun _ _ hω _ => ⟨0, hω⟩) (fun t φ _ => (hker t φ).mono (fun _ hh _ => hh)) hmean hFcode hGcode hjoint hgff

open scoped Classical in
/-- A driver decoded continuously before the coded lifetime. The zero-lifetime
branch retains the code's time-zero value, as required by `IsDriverCodeMatch`. -/
def fcCodeDriver (q : PCode × ℝ≥0∞) : ℝ≥0 → ℝ :=
  let w : ℝ≥0 → ℝ := if q.2 = 0 then fun _ => q.1 0 0 else dec q.1
  if ContinuousOn w {t | (t : ℝ≥0∞) < q.2} then w else fun _ => q.1 0 0

omit mΩ in
theorem continuousOn_fcCodeDriver (q : PCode × ℝ≥0∞) :
    ContinuousOn (fcCodeDriver q) {t | (t : ℝ≥0∞) < q.2} := by
  classical
  let w : ℝ≥0 → ℝ := if q.2 = 0 then fun _ => q.1 0 0 else dec q.1
  change ContinuousOn (if ContinuousOn w {t | (t : ℝ≥0∞) < q.2}
    then w else fun _ => q.1 0 0) {t | (t : ℝ≥0∞) < q.2}
  by_cases hc : ContinuousOn w {t | (t : ℝ≥0∞) < q.2}
  · simpa only [if_pos hc] using hc
  · simp only [if_neg hc]
    exact continuousOn_const

omit mΩ in
/-- On a realized continuous driver code, decoding recovers the driver before the
lifetime and its initial value, including when the lifetime is zero. -/
theorem fcCodeDriver_eq_of_match {q : PCode × ℝ≥0∞} {W : ℝ≥0 → ℝ} {U : ℝ≥0∞}
    (hc : ContinuousOn W {t | (t : ℝ≥0∞) < U}) (hm : IsDriverCodeMatch q W U) :
    fcCodeDriver q 0 = W 0 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → fcCodeDriver q t = W t := by
  classical
  by_cases hU : q.2 = 0
  · have he : fcCodeDriver q = fun _ => q.1 0 0 := by
      simp [fcCodeDriver, hU]
    refine ⟨by rw [he]; exact hm.2.1.symm, ?_⟩
    intro t ht
    rw [hm.1, hU] at ht
    exact False.elim (not_lt_of_ge bot_le ht)
  · have he : ∀ t : ℝ≥0, (t : ℝ≥0∞) < q.2 → dec q.1 t = W t :=
      fun t ht => dec_eq_of_driverCodeMatch hm hc (hm.1.symm ▸ ht)
    have hd : ContinuousOn (dec q.1) {t | (t : ℝ≥0∞) < q.2} := by
      have hc' : ContinuousOn W {t | (t : ℝ≥0∞) < q.2} := hm.1 ▸ hc
      exact hc'.congr he
    have heq : fcCodeDriver q = dec q.1 := by
      simp only [fcCodeDriver, hU, ite_false, hd, ite_true]
    rw [heq]
    exact ⟨he 0 (pos_iff_ne_zero.2 hU), fun t ht => he t (hm.1 ▸ ht)⟩

/-- Conditional word-GFF laws and pathwise driver readings suffice for path determination.
Disintegration is constructed here; no auxiliary path-state or driver-state carrier is an input. -/
theorem ae_codeMatch_of_word_kernel_and_driverReading
    {P : Measure Ω} [IsProbabilityMeasure P] {𝒢 : MeasurableSpace Ω}
    (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M)
    {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable[mΩ] Hc)
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {κ θ : ℝ} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hΓ : ∀ t, Measurable[mΩ] fun ω => Γ ω t) (hU : Measurable[mΩ] U)
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G)
    (hreading : ∀ᵐ ω ∂P, ω ∈ M → ∃ W : ℝ≥0 → ℝ,
      ContinuousOn W {t | (t : ℝ≥0∞) < U ω} ∧ W 0 = 0 ∧
      ContinuousOn (Γ ω) {t | (t : ℝ≥0∞) ≤ U ω} ∧
      IsGeneratingTrace W (U ω) (Γ ω) ∧
      IsDriverCodeMatch (G (β ω, Hc ω)) W (U ω)) :
    ∀ᵐ ω ∂P, ω ∈ M → IsCodeMatch (F ((β ω, 0), Hc ω)) (Γ ω) (U ω) := by
  let _ : MeasurableSpace Ω := mΩ
  let S := DistOn upperHalfPlaneOpens ×
    (((PCode × PCode) × ℝ≥0∞) × (PCode × ℝ≥0∞))
  let X : Ω → S := fun ω => (Hc ω, (encPath (Γ ω) (U ω), G (β ω, Hc ω)))
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  have hXm : Measurable X := hHc.prodMk
    ((measurable_encPath hΓ hU).prodMk (hG.1.comp (hβm.prodMk hHc)))
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word h𝒢 hM hβ
    (w := id) measurable_id hsort hXm (H := fun s : S => s.1) measurable_fst hlaw hcf
  let Γs : S → ℝ≥0 → ℂ := fun s => decPath s.2.1
  let Us : S → ℝ≥0∞ := fun s => s.2.1.2
  let Ws : ℝ≥0 → S → ℝ := fun t s => fcCodeDriver s.2.2 t
  let Ls : S → ℝ≥0∞ := fun s => s.2.2.2
  have hgood : ∀ᵐ ω ∂P, ω ∈ M →
      IsDriverCodeMatch (G (β ω, (X ω).1)) (fun t => Ws t (X ω)) (Ls (X ω)) ∧
      Ws 0 (X ω) = 0 ∧
      IsGeneratingTrace (fun t => Ws t (X ω)) (Ls (X ω)) (Γs (X ω)) ∧
      Us (X ω) = Ls (X ω) := by
    filter_upwards [hreading] with ω hr hω
    obtain ⟨W, hWc, hW0, hΓc, hgen, hdrv⟩ := hr hω
    obtain ⟨hzero, he⟩ := fcCodeDriver_eq_of_match hWc hdrv
    have hmatch : IsDriverCodeMatch (G (β ω, Hc ω))
        (fcCodeDriver (G (β ω, Hc ω))) (G (β ω, Hc ω)).2 := by
      refine ⟨rfl, hzero.trans hdrv.2.1, fun n k ht => ?_⟩
      have ht' : (dyad n k : ℝ≥0∞) < U ω := hdrv.1.symm ▸ ht
      exact (he _ ht').trans (hdrv.2.2 n k ht')
    have htr : IsGeneratingTrace (fcCodeDriver (G (β ω, Hc ω))) (U ω)
        (decPath (encPath (Γ ω) (U ω))) := by
      exact Sec7.IsGeneratingTrace.congr_lt
        (isGeneratingTrace_congr_le hgen fun t ht => decPath_encPath hΓc ht) he
    refine ⟨hmatch, hzero.trans hW0, ?_, hdrv.1⟩
    change IsGeneratingTrace (fcCodeDriver (G (β ω, Hc ω))) (G (β ω, Hc ω)).2
      (decPath (encPath (Γ ω) (U ω)))
    rw [← hdrv.1]
    exact htr
  have hbridge := ae_codeMatch_of_driverCodeMatch_of_generatingTrace
    hMm hβm hXm hlaw (w := id) measurable_id (H := fun s : S => s.1) measurable_fst
    (Γ := Γs) (U := Us) (fun s => continuousOn_decPath s.2.1)
    (W := Ws) (L := Ls) (fun s => continuousOn_fcCodeDriver s.2.2) hF hG hgff
    (hgood.mono fun _ hω hMω => (hω hMω).1)
    (hgood.mono fun _ hω hMω => (hω hMω).2.1)
    (hgood.mono fun _ hω hMω => (hω hMω).2.2.1)
    (hgood.mono fun _ hω hMω => (hω hMω).2.2.2)
  filter_upwards [hbridge, hreading] with ω hb hr hω
  obtain ⟨W, hWc, hW0, hΓc, hgen, hdrv⟩ := hr hω
  have hm := hb hω
  refine ⟨hm.1, fun t ht => ?_⟩
  exact (decPath_encPath hΓc ht).symm.trans (hm.2 t ht)

/-- Full source-facing first-contact determination from the remaining driver realization.
`hDriverReading` is an explicit conditional input, not a claim that physical history
measurability or equality with the force threshold has already been proved. The word,
its mean identification, the conditional GFF law, disintegration and the path bridge
are all supplied by proved results. -/
theorem firstContactCanonCondDetStatement_of_driver_readings
    (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u})
    (hDriverCode : CanonicalDriverCodeStatement)
    (hDriverReading : ∀ (κ : ℝ), 0 < κ → κ < 4 →
      ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
      ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
      ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
        IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) →
      ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
        (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
        IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
      ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
        (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
        Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
      ∀ G₁ G₂ : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞,
        IsCanonicalDriverCode κ θ₁ G₁ → IsCanonicalDriverCode κ θ₂ G₂ →
      ∀ᵐ ω ∂P, ω ∈ meetSet d → ∃ W₁ W₂ : ℝ≥0 → ℝ,
        (ContinuousOn W₁ {t | (t : ℝ≥0∞) < U₁ ω} ∧ W₁ 0 = 0 ∧
          ContinuousOn (γ₁ ω) {t | (t : ℝ≥0∞) ≤ U₁ ω} ∧
          IsGeneratingTrace W₁ (U₁ ω) (γ₁ ω) ∧
          IsDriverCodeMatch (G₁ (β ω, hd.chartField κ h ω)) W₁ (U₁ ω)) ∧
        (ContinuousOn W₂ {t | (t : ℝ≥0∞) < U₂ ω} ∧ W₂ 0 = 0 ∧
          ContinuousOn (γ₂ ω) {t | (t : ℝ≥0∞) ≤ U₂ ω} ∧
          IsGeneratingTrace W₂ (U₂ ω) (γ₂ ω) ∧
          IsDriverCodeMatch (G₂ (β ω, hd.chartField κ h ω)) W₂ (U₂ ω))) :
    FirstContactCanonCondDetStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae Hc hHc γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon u₀ hu₀ F₁ F₂ hF₁ hF₂
  obtain ⟨β, hβ, hsort, hmean⟩ := Sec7.SideHeightBox.exists_isBoxMeanIdentification
    hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
  obtain ⟨G₁, hG₁⟩ := hDriverCode κ θ₁ hκ
  obtain ⟨G₂, hG₂⟩ := hDriverCode κ θ₂ hκ
  have hread := hDriverReading κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon G₁ G₂ hG₁ hG₂
  subst hHc
  have hcf := fun φ => ae_condExp_cexp_chartField_eq_gaussCF_meetSet
    hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hβ hmean φ
  have h₁ := ae_codeMatch_of_word_kernel_and_driverReading (retSigma_le P)
    (hd.measurableSet_meetSet P) hβ hsort (hd.measurable_chartField κ hh.1) hcf hγ₁ hU₁ hF₁ hG₁
    (by
      filter_upwards [hread] with ω hr hω
      obtain ⟨W₁, W₂, h1, -⟩ := hr hω
      exact ⟨W₁, h1⟩)
  have h₂ := ae_codeMatch_of_word_kernel_and_driverReading (retSigma_le P)
    (hd.measurableSet_meetSet P) hβ hsort (hd.measurable_chartField κ hh.1) hcf hγ₂ hU₂ hF₂ hG₂
    (by
      filter_upwards [hread] with ω hr hω
      obtain ⟨W₁, W₂, -, h2⟩ := hr hω
      exact ⟨W₂, h2⟩)
  refine ⟨β, hβ, hsort, hmean, ?_⟩
  filter_upwards [h₁, h₂] with ω h1 h2 hω
  exact ⟨h1 hω, h2 hω⟩

end InteractingSLE.Restart.FCPlumb
