/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermPhysChart
import InteractingSLE.Spec.Supplement.AStopSafeFill
import InteractingSLE.Spec.Sec5.GlueCondTopo

/-!
# The line sets of the first path against the completed second path

Packet PROVE-RC-TERM, second run (ruling R124). At the line `(t, N)` (the first path up to `t`, the second up to its
own time `N`), for capped versions `ηc₁`, `ηc₂` of the two flow lines with the cap `capR t N`:

* `fillOf η a ω = fill(η ω ([0, a]))`, `lineSet ηc₁ ηc₂ t N = fillOf ηc₂ N ∪ fillOf ηc₁ t` (the retained set first);
* **`IsLineData`**: the versions (continuous, measurable, from the seeds, almost surely the capped flow lines,
  coordinates almost surely functions of the centred field) with the history-marked locality of their stopped unions
  at `(t, N)` for the retained σ-algebra, and at `(0, N)`, `(t, 0)` for the killed histories of the versions;
  **`exists_isLineData`** (Lemma 7.5 and Aux. lemma 56, as in `exists_cstUnion_local_retSigma76`);
* for line data: the three sets are hitting-measurable for the retained σ-algebra, relatively closed in `ℍ` with
  open complement, half-plane hulls with unbounded lower-union components; **the line set is history-avoidance local
  for `retSigma76 … t N`** (`isHistoryAvoidanceLocal_of_enlargement`); the two filled prefixes and the line set are
  local sets of the centred field; the retained filled prefix is determined by the centred field.

Uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RealContact

namespace Term

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets WholeField

section Sets

variable {Ω : Type u}

/-- The filled prefix `fill(η([0, a]))`. -/
def fillOf (η : Ω → ℝ≥0 → ℂ) (a : ℝ≥0) (ω : Ω) : Set ℂ := fillH (η ω '' Icc 0 a)

/-- **The line set**: the filled second prefix (retained) and the filled first prefix (explored). -/
def lineSet (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (t N : ℝ≥0) (ω : Ω) : Set ℂ := fillOf ηc₂ N ω ∪ fillOf ηc₁ t ω

variable {η : Ω → ℝ≥0 → ℂ} {a : ℝ≥0}

theorem fillOf_subset_H (η : Ω → ℝ≥0 → ℂ) (a : ℝ≥0) (ω : Ω) : fillOf η a ω ⊆ H := fillH_subset_H _

theorem isOpen_H_diff_fillOf (hc : ∀ ω, Continuous (η ω)) (a : ℝ≥0) (ω : Ω) : IsOpen (H \ fillOf η a ω) :=
  isOpen_H_diff_fillH (isCompact_Icc.image (hc ω)).isBounded

theorem isHPHull_fillOf (hc : ∀ ω, Continuous (η ω)) (a : ℝ≥0) {ω : Ω} (h0 : (η ω 0).im ≤ 0) :
    IsHPHull (fillOf η a ω) :=
  isHPHull_fillH_image (hc ω).continuousOn h0

theorem lineSet_subset_H (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (t N : ℝ≥0) (ω : Ω) : lineSet ηc₁ ηc₂ t N ω ⊆ H :=
  union_subset (fillOf_subset_H _ _ _) (fillOf_subset_H _ _ _)

theorem isOpen_H_diff_lineSet {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω))
    (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (t N : ℝ≥0) (ω : Ω) : IsOpen (H \ lineSet ηc₁ ηc₂ t N ω) := by
  have e : H \ lineSet ηc₁ ηc₂ t N ω = (H \ fillOf ηc₂ N ω) ∩ (H \ fillOf ηc₁ t ω) := by
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨⟨hz, fun h => hn (Or.inl h)⟩, ⟨hz, fun h => hn (Or.inr h)⟩⟩
    · rintro ⟨⟨hz, h1⟩, ⟨-, h2⟩⟩
      exact ⟨hz, fun h => h.elim h1 h2⟩
  rw [e]
  exact (isOpen_H_diff_fillOf hc₂ N ω).inter (isOpen_H_diff_fillOf hc₁ t ω)

/-- **A filled prefix is hitting-measurable** for every σ-algebra measuring its coordinates. -/
theorem measurable_fillOf {m : MeasurableSpace Ω} (hc : ∀ ω, Continuous (η ω))
    (hm : ∀ s ≤ a, Measurable[m] fun ω => η ω s) : Measurable[m, hittingSigma] (fillOf η a) :=
  @measurable_fillH_of_dyadic Ω m (fun ω => η ω '' Icc 0 a) (@isDyadicHitMeasurable_prefix Ω m η a hc hm)
    (fun ω => isCompact_Icc.image (hc ω))

/-- The coordinates of the first path are read from the killed pair history. -/
theorem measurable_coord_cstHist_left {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {L₁ L₂ : Ω → ℝ≥0∞} {u r s : ℝ≥0}
    (hc : ∀ ω, Continuous (ηc₁ ω)) (hs : s ≤ u) :
    Measurable[MeasurableSpace.comap (cstHist ηc₁ ηc₂ L₁ L₂ u r) inferInstance] fun ω => ηc₁ ω s := by
  have h1 : Measurable[MeasurableSpace.comap (cstHist ηc₁ ηc₂ L₁ L₂ u r) inferInstance]
      (fun ω => recon (cstHist ηc₁ ηc₂ L₁ L₂ u r ω).1.1 s) :=
    (measurable_recon s).comp (measurable_fst.comp (measurable_fst.comp (comap_measurable _)))
  have e : (fun ω => ηc₁ ω s) = fun ω => recon (cstHist ηc₁ ηc₂ L₁ L₂ u r ω).1.1 s := by
    funext ω
    simp only [cstHist, khistOf]
    exact (recon_histOf (T' := ⊤) (hc ω).continuousOn le_top (ENNReal.coe_le_coe.2 hs)).symm
  rw [e]
  exact h1

/-- The coordinates of the second path are read from the killed pair history. -/
theorem measurable_coord_cstHist_right {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {L₁ L₂ : Ω → ℝ≥0∞} {u r s : ℝ≥0}
    (hc : ∀ ω, Continuous (ηc₂ ω)) (hs : s ≤ r) :
    Measurable[MeasurableSpace.comap (cstHist ηc₁ ηc₂ L₁ L₂ u r) inferInstance] fun ω => ηc₂ ω s := by
  have h1 : Measurable[MeasurableSpace.comap (cstHist ηc₁ ηc₂ L₁ L₂ u r) inferInstance]
      (fun ω => recon (cstHist ηc₁ ηc₂ L₁ L₂ u r ω).2.1 s) :=
    (measurable_recon s).comp (measurable_fst.comp (measurable_snd.comp (comap_measurable _)))
  have e : (fun ω => ηc₂ ω s) = fun ω => recon (cstHist ηc₁ ηc₂ L₁ L₂ u r ω).2.1 s := by
    funext ω
    simp only [cstHist, khistOf]
    exact (recon_histOf (T' := ⊤) (hc ω).continuousOn le_top (ENNReal.coe_le_coe.2 hs)).symm
  rw [e]
  exact h1

end Sets

/-! ### The line data -/

section Data

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The line data at the line `(t, N)`** (see the module docstring). -/
structure IsLineData (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (x₁ x₂ : ℝ) (t N : ℝ≥0) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) : Prop where
  cont₁ : ∀ ω, Continuous (ηc₁ ω)
  cont₂ : ∀ ω, Continuous (ηc₂ ω)
  meas₁ : ∀ s, Measurable fun ω => ηc₁ ω s
  meas₂ : ∀ s, Measurable fun ω => ηc₂ ω s
  zero₁ : ∀ ω, ηc₁ ω 0 = x₁
  zero₂ : ∀ ω, ηc₂ ω 0 = x₂
  ae₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR t N) (ζ₁ ω) s)
  ae₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR t N) (ζ₂ ω) s)
  det₁ : ∀ s : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
    (fun ω => ηc₁ ω s) =ᵐ[P] fun ω => f (centredField h u₀ ω)
  det₂ : ∀ s : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
    (fun ω => ηc₂ ω s) =ᵐ[P] fun ω => f (centredField h u₀ ω)
  loc : IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ t N) (cstUnion ηc₁ ηc₂ t N) (centredField h u₀) P
  locR : IsHistoryAvoidanceLocal
    (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
      (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N) inferInstance) (cstUnion ηc₁ ηc₂ 0 N) (centredField h u₀) P
  locE : IsHistoryAvoidanceLocal
    (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
      (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0) inferInstance) (cstUnion ηc₁ ηc₂ t 0) (centredField h u₀) P

variable {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **Line data exist at every line** (Lemma 7.5 and Aux. lemma 56). -/
theorem exists_isLineData {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ₁ θ₂ : ℝ}
    (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (t N : ℝ≥0) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ, IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ t N ηc₁ ηc₂ := by
  obtain ⟨ηc₁, hc₁, hm₁, h0₁, _, ha₁, hdet₁, hdetζ₁⟩ :=
    exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ (capR t N)
  obtain ⟨ηc₂, hc₂, hm₂, h0₂, _, ha₂, hdet₂, hdetζ₂⟩ :=
    exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ (capR t N)
  have hloc₁ := retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh
    η₁ ζ₁ hη₁ u₀ hu₀ (capR t N) ηc₁ hc₁ hm₁ ha₁
  have hloc₂ := retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh
    η₂ ζ₂ hη₂ u₀ hu₀ (capR t N) ηc₂ hc₂ hm₂ ha₂
  have hmark : ∀ u r : ℝ≥0, IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) u r) inferInstance) (cstUnion ηc₁ ηc₂ u r) (centredField h u₀) P :=
    fun u r => isHistoryAvoidanceLocal_cstUnion
      (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀).measurable
      hc₁ hc₂ h0₁ h0₂ hm₁ hm₂
      ((measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη₁))
      ((measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη₂))
      hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂
  exact ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, h0₁, h0₂, ha₁, ha₂, hdet₁, hdet₂,
    isHistoryAvoidanceLocal_of_le_aeSigma (retSigma76_le_aeSigma_cstHist ha₁ ha₂) (hmark t N), hmark 0 N,
    hmark t 0⟩

namespace IsLineData

variable {t N : ℝ≥0} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ t N ηc₁ ηc₂)
include d

omit [IsProbabilityMeasure P] in
/-- The retained filled prefix is hitting-measurable for the retained σ-algebra. -/
theorem measurable_ret : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N, hittingSigma] (fillOf ηc₂ N) :=
  measurable_fillOf d.cont₂ fun _ hs => measurable_capped_right_retSigma76 d.cont₂ d.meas₂ d.ae₂ hs

omit [IsProbabilityMeasure P] in
/-- The explored filled prefix is hitting-measurable for the retained σ-algebra. -/
theorem measurable_expl : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N, hittingSigma] (fillOf ηc₁ t) :=
  measurable_fillOf d.cont₁ fun _ hs => measurable_capped_left_retSigma76 d.cont₁ d.meas₁ d.ae₁ hs

omit [IsProbabilityMeasure P] in
/-- The line set is hitting-measurable for the retained σ-algebra. -/
theorem measurable_lineSet : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ t N, hittingSigma] (lineSet ηc₁ ηc₂ t N) :=
  @measurable_union_hitting Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ t N) _ _ d.measurable_ret d.measurable_expl

omit [IsProbabilityMeasure P] in
theorem im_zero₁ (ω : Ω) : (ηc₁ ω 0).im ≤ 0 := by rw [d.zero₁ ω, ofReal_im]

omit [IsProbabilityMeasure P] in
theorem im_zero₂ (ω : Ω) : (ηc₂ ω 0).im ≤ 0 := by rw [d.zero₂ ω, ofReal_im]

omit [IsProbabilityMeasure P] in
/-- **The line set is history-avoidance local for the retained σ-algebra at `(t, N)`.** -/
theorem isHistoryAvoidanceLocal_lineSet :
    IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ t N) (lineSet ηc₁ ηc₂ t N) (centredField h u₀) P := by
  refine isHistoryAvoidanceLocal_of_enlargement d.loc (fun ω z hz => ?_) d.measurable_lineSet
  rw [cstUnion_eq] at hz
  rcases hz.1.1 with h1 | h2
  · exact Or.inr (mem_fillH_of_mem_closure hz.2 (subset_closure h1))
  · exact Or.inl (mem_fillH_of_mem_closure hz.2 (subset_closure h2))

omit [IsProbabilityMeasure P] in
/-- The retained filled prefix is history-avoidance local for the killed pair history at `(0, N)`. -/
theorem isHistoryAvoidanceLocal_ret :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N) inferInstance) (fillOf ηc₂ N) (centredField h u₀) P := by
  refine isHistoryAvoidanceLocal_of_enlargement d.locR (fun ω z hz => ?_)
    (measurable_fillOf d.cont₂ fun _ hs => measurable_coord_cstHist_right d.cont₂ hs)
  rw [cstUnion_eq] at hz
  rcases hz.1.1 with ⟨s, hs, rfl⟩ | h2
  · exfalso
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have hH : 0 < (ηc₁ ω s).im := hz.2
    rw [hs0, d.zero₁ ω, ofReal_im] at hH
    exact lt_irrefl _ hH
  · exact mem_fillH_of_mem_closure hz.2 (subset_closure h2)

omit [IsProbabilityMeasure P] in
/-- The explored filled prefix is history-avoidance local for the killed pair history at `(t, 0)`. -/
theorem isHistoryAvoidanceLocal_expl :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0) inferInstance) (fillOf ηc₁ t) (centredField h u₀) P := by
  refine isHistoryAvoidanceLocal_of_enlargement d.locE (fun ω z hz => ?_)
    (measurable_fillOf d.cont₁ fun _ hs => measurable_coord_cstHist_left d.cont₁ hs)
  rw [cstUnion_eq] at hz
  rcases hz.1.1 with h1 | ⟨s, hs, rfl⟩
  · exact mem_fillH_of_mem_closure hz.2 (subset_closure h1)
  · exfalso
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have hH : 0 < (ηc₂ ω s).im := hz.2
    rw [hs0, d.zero₂ ω, ofReal_im] at hH
    exact lt_irrefl _ hH

variable (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
include hh0

/-- The retained filled prefix is a local set of the centred field. -/
theorem isLocalSet_ret : IsLocalSet (fillOf ηc₂ N) (centredField h u₀) P :=
  ((isLocalSet_tfae hh0 (d.measurable_ret.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl)
    (Eventually.of_forall fun ω => ⟨fillOf_subset_H _ _ ω, isOpen_H_diff_fillOf d.cont₂ N ω⟩)).out 1 4).1
    d.isHistoryAvoidanceLocal_ret.isAvoidanceLocal

/-- The explored filled prefix is a local set of the centred field. -/
theorem isLocalSet_expl : IsLocalSet (fillOf ηc₁ t) (centredField h u₀) P :=
  ((isLocalSet_tfae hh0 (d.measurable_expl.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl)
    (Eventually.of_forall fun ω => ⟨fillOf_subset_H _ _ ω, isOpen_H_diff_fillOf d.cont₁ t ω⟩)).out 1 4).1
    d.isHistoryAvoidanceLocal_expl.isAvoidanceLocal

/-- The line set is a local set of the centred field. -/
theorem isLocalSet_lineSet : IsLocalSet (lineSet ηc₁ ηc₂ t N) (centredField h u₀) P :=
  ((isLocalSet_tfae hh0 (d.measurable_lineSet.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl)
    (Eventually.of_forall fun ω =>
      ⟨lineSet_subset_H _ _ _ _ ω, isOpen_H_diff_lineSet d.cont₁ d.cont₂ t N ω⟩)).out 1 4).1
    d.isHistoryAvoidanceLocal_lineSet.isAvoidanceLocal

omit hh0 [IsProbabilityMeasure P] in
/-- **The retained filled prefix is determined by the centred field.** -/
theorem comap_ret_le : MeasurableSpace.comap (fillOf ηc₂ N) hittingSigma ≤
    aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P := by
  refine (measurable_fillOf (m := aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P) d.cont₂
    fun s _ => ?_).comap_le
  obtain ⟨f, hf, hY⟩ := d.det₂ s
  exact Sec6.measurable_aeSigma_of_ae_eq hf hY

omit hh0 [IsProbabilityMeasure P] in
/-- The lower-union components of the retained filled prefix are unbounded. -/
theorem unbounded_ret (ω : Ω) : ∀ z ∈ lowerUnion (fillOf ηc₂ N ω),
    ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fillOf ηc₂ N ω)) z) :=
  Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull (isHPHull_fillOf d.cont₂ N (d.im_zero₂ ω))

omit hh0 [IsProbabilityMeasure P] in
/-- The lower-union components of the explored filled prefix are unbounded. -/
theorem unbounded_expl (ω : Ω) : ∀ z ∈ lowerUnion (fillOf ηc₁ t ω),
    ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fillOf ηc₁ t ω)) z) :=
  Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull (isHPHull_fillOf d.cont₁ t (d.im_zero₁ ω))

end IsLineData

end Data

end Term

end InteractingSLE.RealContact
