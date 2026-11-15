/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentGRule
import InteractingSLE.Spec.Sec5.Aux61SlitWRule

/-!
# Prefix first-hit rules without a cap at the recorded lifetime

The first-hit construction is reused with the lifetime coordinate set to
infinity. Its finite attained hits are determined by the observed prefix,
including on records which do not encode a continuous driving path.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open LawUnique Restart.FlowStopIdentG Aux61ULoc

variable {nL nR : ℕ} {E : Type*} [PseudoEMetricSpace E]

/-- Forget the recorded lifetime; retain all recorded samples. -/
def fullRecord (g : HistorySpace nL nR) : HistorySpace nL nR := (⊤, g.2)

theorem measurable_fullRecord : Measurable (fullRecord (nL := nL) (nR := nR)) :=
  measurable_const.prodMk measurable_snd

/-- The finite attained first-hit construction is invariant under arbitrary
prefix agreement. No continuity of either input record is needed here. -/
theorem hitRule_eq_of_prefix {ψ : HistorySpace nL nR → ℝ≥0 → E}
    (hψ : IsNonAnticipating ψ) (F : Set E) {g g' : HistorySpace nL nR}
    {t : ℝ≥0∞} (ht : t ≤ g.1) (ht' : t ≤ g'.1) (hag : AgreeBefore g g' t)
    (hle : hitRule ψ F g ≤ t) : hitRule ψ F g' = hitRule ψ F g := by
  by_cases hA : hitStart ψ F g < ⊤ ∧ hitGap ψ F g (hitStart ψ F g) = 0
  · have he : hitRule ψ F g = hitStart ψ F g := ite_eq_left hA
    rw [he] at hle
    have hgap : ∀ s, s ≤ t → hitGap ψ F g' s = hitGap ψ F g s := fun s hs =>
      (hitGap_congr (hs.trans ht) (hs.trans ht') fun p hp =>
        hψ.eq_of_agreeBefore hag (hp.trans_le hs)).symm
    have hs : hitStart ψ F g' = hitStart ψ F g := by
      refine le_antisymm (hitStart_le (hle.trans ht') (by rw [hgap _ hle]; exact hA.2)) ?_
      refine le_hitStart fun s _ hs0 => ?_
      by_contra hn
      have hst : s ≤ t := (not_le.1 hn).le.trans hle
      exact hn (hitStart_le (hst.trans ht) (by rw [← hgap s hst]; exact hs0))
    rw [he]
    unfold hitRule
    rw [ite_eq_left ⟨by rw [hs]; exact hA.1, by rw [hs, hgap _ hle]; exact hA.2⟩, hs]
  · have he : hitRule ψ F g = ⊤ := ite_eq_right hA
    rw [he, top_le_iff] at hle
    subst t
    rw [eq_of_agreeBefore_top ht ht' hag]

/-- An uncapped first-hit rule only reads the record up to its value. -/
theorem isGalmarinoRule_firstHit {Y : Type*} [MeasurableSpace Y]
    (ψ : Y → HistorySpace nL nR → ℝ≥0 → E)
    (hψ : ∀ y, IsNonAnticipating (ψ y)) (F : Set E) :
    IsGalmarinoRule stopRec (fun p : Y × HistorySpace nL nR =>
      hitRule (ψ p.1) F (fullRecord p.2)) := by
  intro y g t hle
  have hag : AgreeBefore (fullRecord g) (fullRecord (stopRec t g)) t := by
    intro p hp
    simp only [fullRecord, stopRec, Sec4.stopHistory]
    rw [ite_eq_left (ENNReal.coe_lt_coe.1 hp).le]
  rcases hle with hle | hle
  · exact (hitRule_eq_of_prefix (hψ y) F (le_top) (le_top) hag.symm hle).symm
  · exact hitRule_eq_of_prefix (hψ y) F (le_top) (le_top) hag hle

/-- The uncapped reader equals a genuine positive hit, as soon as its
observations agree with the continuous physical process before that hit. -/
theorem firstHit_eq_of_hit {ψ : HistorySpace nL nR → ℝ≥0 → E}
    (hψ : IsNonAnticipating ψ) {F : Set E} (hF : IsClosed F)
    {g : HistorySpace nL nR} {f : ℝ≥0 → E} {T : ℝ≥0} (hT : 0 < T)
    (hf : ContinuousOn f (Iic T)) (hoff : ∀ s < T, f s ∉ F) (hhit : f T ∈ F)
    (hread : ∀ p, (dyadicTime p : ℝ≥0∞) < T → ψ (fullRecord g) (dyadicTime p) = f (dyadicTime p)) :
    hitRule ψ F (fullRecord g) = T := by
  have hag : AgreeBefore (stopRec T g) (fullRecord g) T := by
    intro p hp
    simp only [stopRec, Sec4.stopHistory, fullRecord]
    rw [ite_eq_left (ENNReal.coe_lt_coe.1 hp).le]
  have he : hitRule ψ F (stopRec T g) = T :=
    hitRule_eq_of_hit hF hT rfl hf hoff hhit
      (fun p hp => (hψ.eq_of_agreeBefore hag hp).trans (hread p hp))
  exact (hitRule_eq_of_prefix hψ F (t := (T : ℝ≥0∞))
    (by exact le_rfl) le_top hag (by rw [he])).trans he

section Meas
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace E] [OpensMeasurableSpace E]
  {g : X → HistorySpace nL nR} {ψ : X → HistorySpace nL nR → ℝ≥0 → E}

/-- Joint measurability of the landed gap construction with a retained parameter. -/
theorem measurable_param_hitGap (hg : Measurable g)
    (hψ : ∀ p, Measurable fun x => ψ x (g x) (dyadicTime p))
    (F : Set E) {τ : X → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable fun x => hitGap (ψ x) F (g x) (τ x) := by
  refine Measurable.iInf fun p => Measurable.ite ?_
    ((Metric.continuous_infEDist (s := F)).measurable.comp (hψ p)) measurable_const
  exact (measurableSet_lt measurable_const hτ).inter
    (measurableSet_lt measurable_const (measurable_fst.comp hg))

/-- The countable description of the first-hit start remains measurable
when the chart is a measurable retained parameter. -/
theorem measurable_param_hitStart (hg : Measurable g)
    (hψ : ∀ p, Measurable fun x => ψ x (g x) (dyadicTime p)) (F : Set E) :
    Measurable fun x => hitStart (ψ x) F (g x) := by
  refine measurable_of_Iio fun c => ?_
  have he : (fun x => hitStart (ψ x) F (g x)) ⁻¹' Iio c =
      (⋃ p : ℕ × ℕ, {x | (dyadicTime p : ℝ≥0∞) < c ∧
        (dyadicTime p : ℝ≥0∞) ≤ (g x).1 ∧ hitGap (ψ x) F (g x) (dyadicTime p) = 0}) ∪
      {x | (g x).1 < c ∧ hitGap (ψ x) F (g x) (g x).1 = 0} := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨t, ⟨ht, h0⟩, htc⟩ : ∃ t, (t ≤ (g x).1 ∧ hitGap (ψ x) F (g x) t = 0) ∧ t < c := by
        simpa only [hitStart, iInf_lt_iff, exists_prop] using h
      by_cases hc : (g x).1 < c
      · exact Or.inr ⟨hc, le_antisymm ((hitGap_anti (g x) ht).trans h0.le) zero_le⟩
      · obtain ⟨p, htp, hpc⟩ := exists_dyadicTime_btwn htc
        exact Or.inl ⟨p, hpc, hpc.le.trans (not_lt.1 hc),
          le_antisymm ((hitGap_anti (g x) htp.le).trans h0.le) zero_le⟩
    · rintro (⟨p, hpc, hp, h0⟩ | ⟨hc, h0⟩)
      · exact (hitStart_le hp h0).trans_lt hpc
      · exact (hitStart_le le_rfl h0).trans_lt hc
  rw [he]
  exact (MeasurableSet.iUnion fun p => (MeasurableSet.const _).inter
    ((measurableSet_le measurable_const (measurable_fst.comp hg)).inter
      (measurableSet_eq_fun (measurable_param_hitGap hg hψ F measurable_const) measurable_const))).union
    ((measurableSet_lt (measurable_fst.comp hg) measurable_const).inter
      (measurableSet_eq_fun (measurable_param_hitGap hg hψ F (measurable_fst.comp hg)) measurable_const))

/-- Joint measurability of the finite attained first-hit rule. -/
theorem measurable_param_hitRule (hg : Measurable g)
    (hψ : ∀ p, Measurable fun x => ψ x (g x) (dyadicTime p)) (F : Set E) :
    Measurable fun x => hitRule (ψ x) F (g x) := by
  have hs := measurable_param_hitStart hg hψ F
  exact Measurable.ite ((measurableSet_lt hs measurable_const).inter
    (measurableSet_eq_fun (measurable_param_hitGap hg hψ F hs) measurable_const)) hs measurable_const

end Meas

end InteractingSLE.Sec5.Aux61SlitW
