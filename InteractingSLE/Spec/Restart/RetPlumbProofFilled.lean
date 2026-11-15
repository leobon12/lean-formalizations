/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofMeas
import InteractingSLE.Spec.Restart.R1GlueChart
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Measurable fillings and history-marked locality

Packet PROVE-RETPLUMB. A compact random prefix with measurable dyadic hits has
a hitting-measurable filling. A history-measurable enlargement preserves the
marked avoidance criterion. No locality assertion is made for the chart's
empty fallback off its good event.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H)
open LQGMetric (DistOn)
open WholeField
open Supp7 Sec7 Sec7.Lemma76F
open DomainMarkov DomainMarkov.Aux79 K2

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

/-- Intersecting a filling with a compact subset of `ℍ` gives a compact set. -/
theorem isCompact_fillH_inter {A C : Set ℂ} (hA : Bornology.IsBounded A)
    (hC : IsCompact C) (hCH : C ⊆ H) : IsCompact (fillH A ∩ C) := by
  have he : fillH A ∩ C = C \ (H \ fillH A) := by
    ext z
    constructor
    · rintro ⟨hz, hzC⟩
      exact ⟨hzC, fun hn => hn.2 hz⟩
    · rintro ⟨hzC, hz⟩
      exact ⟨by by_contra hn; exact hz ⟨hCH hzC, hn⟩, hzC⟩
  rw [he]
  exact hC.diff (isOpen_H_diff_fillH hA)

/-- Compact intersection commutes with the decreasing dyadic filling limit. -/
theorem fillH_inter_nonempty_iff {A C : Set ℂ} (hA : IsCompact A)
    (hC : IsCompact C) (hCH : C ⊆ H) :
    (fillH A ∩ C).Nonempty ↔ ∀ n : ℕ, (fillH (dyadicCover n A) ∩ C).Nonempty := by
  constructor
  · rintro ⟨z, hz, hzC⟩ n
    exact ⟨z, fillH_subset_fillH_dyadicCover n hz, hzC⟩
  · intro hn
    have hc : ∀ n, IsCompact (fillH (dyadicCover n A) ∩ C) := fun n =>
      isCompact_fillH_inter (isCompact_dyadicCover hA.isBounded n).isBounded hC hCH
    obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => fillH (dyadicCover n A) ∩ C)
      (fun n => inter_subset_inter_left _ (fillH_dyadicCover_antitone (Nat.le_succ n)))
      hn (hc 0) (fun n => (hc n).isClosed)
    have hzn : ∀ n, z ∈ fillH (dyadicCover n A) ∩ C := mem_iInter.1 hz
    refine ⟨z, ?_, (hzn 0).2⟩
    rw [← iInter_fillH_dyadicCover hA]
    exact mem_iInter.2 fun n => (hzn n).1

/-- Filling compact random sets preserves hitting measurability. The input is
dyadic-hit measurability, as used by the existing retained-chart API. -/
theorem measurable_fillH_of_dyadic {K : Ω → Set ℂ}
    (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω)) :
    Measurable[mΩ, hittingSigma] (fun ω => fillH (K ω)) := by
  refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ fun S hS => ?_
  obtain ⟨U, hU, hUH, rfl⟩ := hS
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨C, hCc, hCU⟩ :=
    (isSigmaCompact_iff_sigmaCompactSpace (s := U)).2 inferInstance
  have hCUsub : ∀ n, C n ⊆ U := fun n => hCU ▸ subset_iUnion C n
  have he : (fun ω => fillH (K ω)) ⁻¹' {A | (A ∩ U).Nonempty} =
      ⋃ j : ℕ, ⋂ n : ℕ,
        {ω | (fillH (coverOf n (dyadicIdx n (K ω))) ∩ C j).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, mem_iInter,
      ← dyadicCover_eq_coverOf]
    constructor
    · rintro ⟨z, hzK, hzU⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hCU.symm ▸ hzU)
      exact ⟨j, (fillH_inter_nonempty_iff (hKc ω) (hCc j) ((hCUsub j).trans hUH)).1
        ⟨z, hzK, hj⟩⟩
    · rintro ⟨j, hj⟩
      obtain ⟨z, hzK, hzC⟩ :=
        (fillH_inter_nonempty_iff (hKc ω) (hCc j) ((hCUsub j).trans hUH)).2 hj
      exact ⟨z, hzK, hCUsub j hzC⟩
  rw [he]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iInter fun n =>
    measurableSet_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n
      (fun S => (fillH (coverOf n S) ∩ C j).Nonempty)

/-- A history-measurable enlargement of a marked local set is marked local.
Containment is only needed inside `ℍ`, where avoidance is tested. -/
theorem isHistoryAvoidanceLocal_of_enlargement {ℋ : MeasurableSpace Ω}
    {A B : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens} {P : @Measure Ω mΩ}
    (hloc : @IsHistoryAvoidanceLocal Ω ℋ mΩ A h P)
    (hAB : ∀ ω, A ω ∩ H ⊆ B ω)
    (hBm : Measurable[ℋ, hittingSigma] B) : @IsHistoryAvoidanceLocal Ω ℋ mΩ B h P := by
  let _ : MeasurableSpace Ω := mΩ
  intro U G hUH hG hd F hF
  have hav : MeasurableSet[ℋ] {ω | Disjoint (B ω) U} :=
    hBm (LocalSets.measurableSet_avoid U.isOpen hUH)
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd
    (F ∩ {ω | Disjoint (B ω) U}) (hF.inter hav)
  have he : {ω | Disjoint (A ω) U} ∩ (F ∩ {ω | Disjoint (B ω) U}) =
      {ω | Disjoint (B ω) U} ∩ F := by
    ext ω
    constructor
    · rintro ⟨-, hωF, hωB⟩
      exact ⟨hωB, hωF⟩
    · rintro ⟨hωB, hωF⟩
      refine ⟨Set.disjoint_left.2 (fun z hzA hzU => ?_), hωF, hωB⟩
      exact Set.disjoint_left.1 hωB (hAB ω ⟨hzA, hUH hzU⟩) hzU
  exact ⟨g, hg, by simpa only [he] using hge⟩

/-- The filled stopped prefix is local with the same history mark. The only
extra input over raw-union locality is dyadic-hit measurability in that history. -/
theorem isHistoryAvoidanceLocal_fillH {ℋ : MeasurableSpace Ω}
    {K : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens} {P : @Measure Ω mΩ}
    (hloc : @IsHistoryAvoidanceLocal Ω ℋ mΩ K h P)
    (hK : @IsDyadicHitMeasurable Ω ℋ K) (hKc : ∀ ω, IsCompact (K ω)) :
    @IsHistoryAvoidanceLocal Ω ℋ mΩ (fun ω => fillH (K ω)) h P :=
  @isHistoryAvoidanceLocal_of_enlargement Ω mΩ ℋ K (fun ω => fillH (K ω)) h P hloc
    (fun _ _ hz => mem_fillH_of_mem_closure hz.2 (subset_closure hz.1))
    (@measurable_fillH_of_dyadic Ω ℋ K hK hKc)

/-- A continuous capped version, up to the first retained cutoff, is measurable
in the completed retained information. It is read by `recon` from that history. -/
theorem measurable_capped_left_retSigma76 {P : Measure Ω}
    {η₁ η₂ ηc : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r t : ℝ≥0}
    (hc : ∀ ω, Continuous (ηc ω)) (hm : ∀ s, Measurable fun ω => ηc ω s)
    (ha : ∀ᵐ ω ∂P, ∀ s, ηc ω s = η₁ ω (capTime (capR u r) (ζ₁ ω) s))
    (ht : t ≤ u) : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] (fun ω => ηc ω t) := by
  apply measurable_retSigma76_of_ae_eq (hm t)
    ((measurable_recon t).comp (measurable_fst.comp (measurable_fst.comp
      (comap_measurable (retHist76 η₁ η₂ ζ₁ ζ₂ u r)))))
  filter_upwards [ha] with ω he
  have hp : cappedPath η₁ ζ₁ (capR u r) ω = ηc ω := (funext he).symm
  simp only [Function.comp_apply, retHist76, cstHist, hp, khistOf]
  exact (recon_histOf (T' := ⊤) (hc ω).continuousOn le_top (ENNReal.coe_le_coe.2 ht)).symm

/-- The analogous reader for the second retained cutoff. -/
theorem measurable_capped_right_retSigma76 {P : Measure Ω}
    {η₁ η₂ ηc : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r t : ℝ≥0}
    (hc : ∀ ω, Continuous (ηc ω)) (hm : ∀ s, Measurable fun ω => ηc ω s)
    (ha : ∀ᵐ ω ∂P, ∀ s, ηc ω s = η₂ ω (capTime (capR u r) (ζ₂ ω) s))
    (ht : t ≤ r) : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] (fun ω => ηc ω t) := by
  apply measurable_retSigma76_of_ae_eq (hm t)
    ((measurable_recon t).comp (measurable_fst.comp (measurable_snd.comp
      (comap_measurable (retHist76 η₁ η₂ ζ₁ ζ₂ u r)))))
  filter_upwards [ha] with ω he
  have hp : cappedPath η₂ ζ₂ (capR u r) ω = ηc ω := (funext he).symm
  simp only [Function.comp_apply, retHist76, cstHist, hp, khistOf]
  exact (recon_histOf (T' := ⊤) (hc ω).continuousOn le_top (ENNReal.coe_le_coe.2 ht)).symm

/-- Closed-square hits of a continuous prefix only require measurability at
times before that prefix's cutoff. -/
theorem isDyadicHitMeasurable_prefix {η : Ω → ℝ≥0 → ℂ} {u : ℝ≥0}
    (hc : ∀ ω, Continuous (η ω)) (hm : ∀ t ≤ u, Measurable fun ω => η ω t) :
    IsDyadicHitMeasurable (fun ω => η ω '' Icc 0 u) := by
  intro n k
  have he : {ω | (dyadicSquare n k ∩ η ω '' Icc 0 u).Nonempty} =
      univ ∩ {ω | ∃ s ≤ u, η ω (min s u) ∈ dyadicSquare n k} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_univ, true_and]
    constructor
    · rintro ⟨_, hz, s, hs, rfl⟩
      exact ⟨s, hs.2, by simpa only [min_eq_left hs.2] using hz⟩
    · rintro ⟨s, hs, hz⟩
      exact ⟨_, hz, min s u, ⟨zero_le, min_le_right _ _⟩, rfl⟩
  rw [he]
  exact measurableSet_inter_exists_mem MeasurableSet.univ
    (fun s => hm (min s u) (min_le_right _ _)) measurable_const
    (fun ω _ => ((hc ω).comp (continuous_id.min continuous_const)).continuousOn)
    (isClosed_dyadicSquare n k) (PairData.dyadicSquare_nonempty n k)

/-- Both capped prefixes are dyadic-hit measurable in the actual completed
retained history. Thus no new measurability hypothesis is needed for filling. -/
theorem isDyadicHitMeasurable_capped_union_retSigma76 {P : Measure Ω}
    {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR u r) (ζ₁ ω) s))
    (ha₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR u r) (ζ₂ ω) s)) :
    @IsDyadicHitMeasurable Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r)
      (fun ω => ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r) := by
  have h₁ := @isDyadicHitMeasurable_prefix Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r)
    ηc₁ u hc₁ (fun t ht => measurable_capped_left_retSigma76 hc₁ hm₁ ha₁ ht)
  have h₂ := @isDyadicHitMeasurable_prefix Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r)
    ηc₂ r hc₂ (fun t ht => measurable_capped_right_retSigma76 hc₂ hm₂ ha₂ ht)
  intro n k
  simpa only [inter_union_distrib_left, union_nonempty, ofPred_or] using (h₁ n k).union (h₂ n k)

/-- Fill the actual capped stopped union, keeping the completed physical
history as mark. Raw-union locality is supplied by the preceding module. -/
theorem isHistoryAvoidanceLocal_capped_fill_retSigma76 {P : Measure Ω}
    {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR u r) (ζ₁ ω) s))
    (ha₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR u r) (ζ₂ ω) s))
    (hloc : IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r) (cstUnion ηc₁ ηc₂ u r) h P) :
    IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r)
      (fun ω => fillH (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r)) h P := by
  apply isHistoryAvoidanceLocal_of_enlargement hloc
  · intro ω z hz
    rw [cstUnion_eq] at hz
    exact mem_fillH_of_mem_closure hz.1.2 (subset_closure hz.1.1)
  · exact @measurable_fillH_of_dyadic Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r) _
      (isDyadicHitMeasurable_capped_union_retSigma76 hc₁ hc₂ hm₁ hm₂ ha₁ ha₂)
      (fun ω => (isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω)))

/-- On disjoint original pairs the actual capped filling has exactly the
retained domain as complement, regardless of the chart's fallback elsewhere. -/
theorem ae_capped_fill_domain {P : Measure Ω} {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) s))
    (ha₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) s)) :
    ∀ᵐ ω ∂P, Sec7.Lemma76Exit.IsDisjointPair
      (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      H \ fillH (ηc₁ ω '' Icc 0 d.u ∪ ηc₂ ω '' Icc 0 d.r) = d.D ω := by
  filter_upwards [hag, ha₁, ha₂] with ω hagω e₁ e₂ hp
  obtain ⟨hG, a₁, a₂⟩ := hagω hp.1 hp.2.1
  have hE := mem_E_of_isDisjointPair hd hG a₁ a₂ hp
  have b₁ : EqOn (d.η₁ ω) (ηc₁ ω) (Icc 0 d.u) := by
    intro s hs
    rw [e₁ s, capTime_eq_of_lt hp.1 (lt_capR_left d.u d.r) hs.2]
    exact a₁ s hs.2
  have b₂ : EqOn (d.η₂ ω) (ηc₂ ω) (Icc 0 d.r) := by
    intro t ht
    rw [e₂ t, capTime_eq_of_lt hp.2.1 (lt_capR_right d.u d.r) ht.2]
    exact a₂ t ht.2
  change _ = H \ fillH (d.K ω)
  rw [RetData.K_of_mem hE, prefixSet, b₁.image_eq, b₂.image_eq]

/-- The filled-line input to (L), including history measurability, relative
closedness, locality, and agreement with the retained domain, is available at
every deterministic line. -/
theorem exists_ret_filled_line {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ B : Ω → Set ℂ,
      Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r, hittingSigma] B ∧
      (∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) ∧
      IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) B (centredField h u₀) P ∧
      ∀ᵐ ω ∂P, Sec7.Lemma76Exit.IsDisjointPair
        (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → H \ B ω = d.D ω := by
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, ha₁, ha₂, hloc⟩ :=
    exists_cstUnion_local_retSigma76 hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ d.u d.r
  refine ⟨fun ω => fillH (ηc₁ ω '' Icc 0 d.u ∪ ηc₂ ω '' Icc 0 d.r), ?_, ?_,
    isHistoryAvoidanceLocal_capped_fill_retSigma76 hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hloc,
    ae_capped_fill_domain hd hag ha₁ ha₂⟩
  · exact @measurable_fillH_of_dyadic Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) _
      (isDyadicHitMeasurable_capped_union_retSigma76 hc₁ hc₂ hm₁ hm₂ ha₁ ha₂)
      (fun ω => (isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω)))
  · intro ω
    exact ⟨fillH_subset_H _, isOpen_H_diff_fillH
      ((isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω))).isBounded⟩

/-- K2's (L) with all filled-line inputs discharged. The remaining premises
are physical clock and safe-event measurability, matching the (S) adapter. -/
theorem hasSafeMembers_ret_of_physical_measurability {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0} {F : Set Ω} {c₀ : BoundaryWord}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    (hGsub : G r ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω})
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u
      (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
      (retClock G η₁' η₂' ζ₂ u r t))
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (lineSafe (retClock G η₁' η₂' ζ₂ u r)
          (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
          (retLife G η₁' η₂' ζ₂ u r) (Coupling.ballsK Fb) t)) :
    HasSafeMembers P
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) (retClock G η₁' η₂' ζ₂ u r) hQa)
      F (retLife G η₁' η₂' ζ₂ u r) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
        (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω)) := by
  have hag : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (s : ℝ≥0∞) < ζ₂ ω → ω ∈ G s ∧
        (∀ t ≤ u, η₁' ω t = η₁ ω t) ∧ ∀ t ≤ s, η₂' ω t = η₂ ω t := by
    intro s
    filter_upwards [hG s, ha₁, ha₂] with ω hGω e₁ e₂ hu hs
    exact ⟨hGω hu hs, fun t ht => e₁ t ((ENNReal.coe_le_coe.2 ht).trans hu.le),
      fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hs.le)⟩
  choose B hBm hBc hloc hBD using fun t : ℝ≥0 =>
    exists_ret_filled_line hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (hd (r + t)) (hag (r + t))
  apply hasSafeMembers_ret_of_marked_filling hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG
    hGsub hu₀ hc₀ hF hQa hS B
    (fun t => (hBm t).mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ u (r + t)) le_rfl)
    hBc hloc
  intro t
  filter_upwards [hBD t, ae_retPairAt hκ hκ4 hη₁ hη₂ ha₁ ha₂ (hd r) hF t]
    with ω hBω hp hωF hlt
  exact hBω (hp hωF hlt)

end InteractingSLE.Restart.RetAux79
