/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootZ21Inverse
import InteractingSLE.Spec.Restart.R1Flow

/-!
# Observable relative tips, including real boundary visits

Packet PROVE-T14-GW2ROOT2. Read the extended forward chart by its vertical
limits and evaluate a stopped physical trace by the existing dyadic endpoint
reader. Both maps are Borel on the entire record space.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- The boundary chart read as a limit of its censored interior evaluations. -/
def boundaryRead (s : ℝ≥0) (p : RecData × ℂ) : ℂ :=
  limUnder atTop fun n : ℕ =>
    {x : RecData × ℂ | vert n x.2 ∈ relDomain (rdrv x.1) s}.indicator
      (fun x => relMap (rdrv x.1) s (vert n x.2)) p

theorem measurable_boundaryRead (s : ℝ≥0) : Measurable (boundaryRead s) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  apply Measurable.stronglyMeasurable
  exact RootY20.measurable_indicator_record_chart s measurable_fst
    (measurable_snd.add measurable_const)

/-- At every safe point the total reader is the actual boundary extension. -/
theorem boundaryRead_eq_relBdry (s : ℝ≥0) (r : RecData) {z : ℂ}
    (hz : z ∈ relSafe (rdrv r) s) :
    boundaryRead s (r, z) = relBdry (rdrv r) s z := by
  have he : ∀ᶠ n : ℕ in atTop, vert n z ∈ relDomain (rdrv r) s :=
    tendsto_principal.mp ((tendsto_vert_relDomain hz).mono_right inf_le_right)
  apply Tendsto.limUnder_eq
  apply (tendsto_relMap_vert (continuous_rdrv r) (rdrv_zero r) s.coe_nonneg hz).congr'
  filter_upwards [he] with n hn
  exact (indicator_of_mem (show (r, z) ∈
    {x : RecData × ℂ | vert n x.2 ∈ relDomain (rdrv x.1) s} from hn)
      (fun x : RecData × ℂ => relMap (rdrv x.1) s (vert n x.2))).symm

/-- Evaluation of the recorded physical trace at a time read from the record. -/
def physicalTipRead (p : RecData × ℝ≥0) : ℂ :=
  endVal ((p.2 : ℝ≥0∞), RootU19.recordTrace p.1)

theorem measurable_physicalTipRead : Measurable physicalTipRead :=
  measurable_endVal.comp
    ((measurable_coe_nnreal_ennreal.comp measurable_snd).prodMk
      (RootU19.measurable_recordTrace.comp measurable_fst))

/-- Dyadic endpoint evaluation returns the actual tip at every time through
a strictly live physical cutoff, including the cutoff itself. -/
theorem physicalTipRead_recOf_eq {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ)
    {v t : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2) (htv : t ≤ v) :
    physicalTipRead (recOf (v : ℝ≥0∞) e, t) = γ t := by
  have hc : ContinuousOn e.1 {q | (q : ℝ≥0∞) ≤ min (v : ℝ≥0∞) e.2} :=
    he.1.mono fun q hq => (hq.trans (min_le_left _ _)).trans_lt hv
  have hg := LP.isGeneratingTrace_mono hγ (min_le_right (v : ℝ≥0∞) e.2)
  have hval : ∀ q ≤ t, RootU19.recordTrace (recOf (v : ℝ≥0∞) e) q = γ q := by
    intro q hq
    exact RootU19.recordTrace_recOf_eq he
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)) hc hg
      (le_min (ENNReal.coe_le_coe.mpr (hq.trans htv))
        ((ENNReal.coe_le_coe.mpr (hq.trans htv)).trans hv.le))
  change endVal ((t : ℝ≥0∞), _) = γ t
  unfold endVal
  split_ifs with ht0
  · have ht : t = 0 := ENNReal.coe_eq_zero.mp ht0
    subst t
    exact hval 0 le_rfl
  · simp only [ENNReal.toNNReal_coe]
    have ht : (t : ℝ≥0∞) ≤ e.2 := (ENNReal.coe_le_coe.mpr htv).trans hv.le
    have hl := (hγ.2.1 t ht).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨LP.tendsto_dyadicBelow t,
        Eventually.of_forall fun n =>
          (ENNReal.coe_le_coe.mpr (dyadicBelow_le n t)).trans ht⟩)
    exact (hl.congr fun n => (hval _ (dyadicBelow_le n t)).symm).limUnder_eq

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
