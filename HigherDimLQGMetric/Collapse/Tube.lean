import HigherDimLQGMetric.Collapse.Recovery
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

/-!
# Last contacts with a metric tube

These elementary facts replace the arclength-measure argument in the source's Lemma 3.1.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- A continuous function that rises above a level has a last contact with that level. -/
theorem exists_last_level {f : ℝ → ℝ} (hf : Continuous f) {t η : ℝ}
    (ht : 0 ≤ t) (hf0 : f 0 ≤ η) (hft : η < f t) :
    ∃ s ∈ Icc 0 t, f s = η ∧ ∀ r ∈ Icc s t, η ≤ f r := by
  let S : Set ℝ := Icc 0 t ∩ {r | f r ≤ η}
  have hScompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_Iic.preimage hf)
  have hSnonempty : S.Nonempty := ⟨0, ⟨⟨le_rfl, ht⟩, hf0⟩⟩
  obtain ⟨s, hsS, hsmax⟩ := hScompact.exists_isMaxOn hSnonempty continuousOn_id
  have hs : s ∈ Icc 0 t := hsS.1
  have hfs : f s ≤ η := hsS.2
  have hsf : f s = η := by
    by_contra hne
    have hfst : f s < η := lt_of_le_of_ne hfs hne
    obtain ⟨r, hr, hfr⟩ : ∃ r ∈ Icc s t, f r = η :=
      (intermediate_value_Icc hs.2 hf.continuousOn)
        ⟨hfst.le, hft.le⟩
    have hsr : s < r := lt_of_le_of_ne hr.1 (by
      intro hrs
      have : f s = η := hrs ▸ hfr
      exact hne this)
    exact (not_lt_of_ge (hsmax ⟨⟨hs.1.trans hr.1, hr.2⟩, hfr.le⟩)) hsr
  refine ⟨s, hs, hsf, ?_⟩
  intro r hr
  by_contra hnot
  have hfr : f r ≤ η := le_of_lt (lt_of_not_ge hnot)
  have hrS : r ∈ S := ⟨⟨hs.1.trans hr.1, hr.2⟩, hfr⟩
  have hrs : r ≤ s := hsmax hrS
  have hsr : r = s := le_antisymm hrs hr.1
  have habsurd : η < η := by simpa only [hsr, hsf] using (lt_of_not_ge hnot)
  exact (lt_irrefl η) habsurd

/-- A curve that reaches beyond the closed `η`-tube pays for the distance it spends outside.
The bound uses only lower Darboux sums and a last contact with the tube. -/
theorem weightedLength_ge_of_far_from_set_on {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {w : X → ℝ} {η a₀ T : ℝ} {t : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (ht : t ∈ Icc (0 : ℝ) T)
    (hstart : Metric.infDist (P 0) K ≤ η)
    (hfar : η < Metric.infDist (P t) K)
    (hwoff : ∀ z, η ≤ Metric.infDist z K → a₀ ≤ w z) :
    ENNReal.ofReal a₀ * ENNReal.ofReal (Metric.infDist (P t) K - η) ≤
      weightedLength w P 0 T := by
  let Q : ℝ → X := Set.IccExtend hT
    (fun s : Icc (0 : ℝ) T => P s)
  have hQcont : Continuous Q := continuous_IccExtend_iff.mpr hP.domRestrict
  have hQeq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) : Q s = P s := by
    exact Set.IccExtend_of_mem (h := hT) _ hs
  let f : ℝ → ℝ := fun s => Metric.infDist (Q s) K
  have hfcont : Continuous f := (Metric.continuous_infDist_pt K).comp hQcont
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hf0 : f 0 ≤ η := by simpa only [f, hQeq h0] using hstart
  have hft : η < f t := by simpa only [f, hQeq ht] using hfar
  obtain ⟨s, hs, hfs, hlevel⟩ := exists_last_level hfcont ht.1 hf0 hft
  have hs1 : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  have hfs' : Metric.infDist (P s) K = η := by simpa only [f, hQeq hs1] using hfs
  have hw : ∀ r ∈ Icc s t, a₀ ≤ w (P r) := by
    intro r hr
    have hr1 : r ∈ Icc (0 : ℝ) T := ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    apply hwoff
    simpa only [f, hQeq hr1] using hlevel r hr
  have hsub : Metric.infDist (P t) K - η ≤ dist (P s) (P t) := by
    have htri := Metric.infDist_le_infDist_add_dist (x := P t) (y := P s) (s := K)
    rw [hfs'] at htri
    rw [dist_comm] at htri
    linarith
  calc ENNReal.ofReal a₀ * ENNReal.ofReal (Metric.infDist (P t) K - η)
      ≤ ENNReal.ofReal a₀ * edist (P s) (P t) := by
        rw [edist_dist]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hsub)
    _ ≤ ENNReal.ofReal a₀ * curveLength P s t :=
      mul_le_mul' le_rfl (edist_le_curveLength P hs.2)
    _ ≤ weightedLength w P s t := ofReal_mul_curveLength_le_weightedLength hs.2 hw
    _ ≤ weightedLength w P 0 T := weightedLength_mono_interval hs.1 hs.2 ht.2

/-- Unit-interval version of the last-contact tube barrier. -/
theorem weightedLength_ge_of_far_from_set {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {w : X → ℝ} {η a₀ : ℝ} {t : ℝ}
    (hP : ContinuousOn P (Icc 0 1)) (ht : t ∈ Icc (0 : ℝ) 1)
    (hstart : Metric.infDist (P 0) K ≤ η)
    (hfar : η < Metric.infDist (P t) K)
    (hwoff : ∀ z, η ≤ Metric.infDist z K → a₀ ≤ w z) :
    ENNReal.ofReal a₀ * ENNReal.ofReal (Metric.infDist (P t) K - η) ≤
      weightedLength w P 0 1 :=
  weightedLength_ge_of_far_from_set_on zero_le_one hP ht hstart hfar hwoff

/-- A path whose weighted cost is below the exit cost stays in the open `ε`-tube. -/
theorem path_stays_in_tube_of_cost_lt {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {w : X → ℝ} {η a₀ ε : ℝ}
    (hP : ContinuousOn P (Icc 0 1))
    (hstart : Metric.infDist (P 0) K ≤ η)
    (hηε : η < ε)
    (hwoff : ∀ z, η ≤ Metric.infDist z K → a₀ ≤ w z)
    (hcost : weightedLength w P 0 1 <
      ENNReal.ofReal a₀ * ENNReal.ofReal (ε - η)) :
    ∀ t ∈ Icc (0 : ℝ) 1, Metric.infDist (P t) K < ε := by
  intro t ht
  by_contra hnot
  have hε : ε ≤ Metric.infDist (P t) K := le_of_not_gt hnot
  have hfar : η < Metric.infDist (P t) K := hηε.trans_le hε
  have hbound := weightedLength_ge_of_far_from_set hP ht hstart hfar hwoff
  have hmono : ENNReal.ofReal a₀ * ENNReal.ofReal (ε - η) ≤
      ENNReal.ofReal a₀ * ENNReal.ofReal (Metric.infDist (P t) K - η) :=
    mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (sub_le_sub_right hε _))
  exact (not_lt_of_ge (hmono.trans hbound)) hcost

/-- A quantitative tube bound for every point on a low-cost path. -/
theorem infDist_le_eta_add_cost_div_on {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {w : X → ℝ} {η a₀ c T : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (ha₀ : 0 < a₀) (hc : 0 ≤ c)
    (hstart : Metric.infDist (P 0) K ≤ η)
    (hwoff : ∀ z, η ≤ Metric.infDist z K → a₀ ≤ w z)
    (hcost : weightedLength w P 0 T ≤ ENNReal.ofReal c) :
    ∀ t ∈ Icc (0 : ℝ) T, Metric.infDist (P t) K ≤ η + c / a₀ := by
  intro t ht
  by_cases hfar : η < Metric.infDist (P t) K
  · have hb := weightedLength_ge_of_far_from_set_on hT hP ht hstart hfar hwoff
    have hprod : a₀ * (Metric.infDist (P t) K - η) ≤ c := by
      have h := hb.trans hcost
      rw [← ENNReal.ofReal_mul ha₀.le] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have hdiv : Metric.infDist (P t) K - η ≤ c / a₀ :=
      (le_div_iff₀ ha₀).2 (by nlinarith [hprod])
    linarith
  · have hsmall : Metric.infDist (P t) K ≤ η := le_of_not_gt hfar
    have hdiv : 0 ≤ c / a₀ := div_nonneg hc ha₀.le
    linarith

/-- Unit-interval version of the quantitative tube bound. -/
theorem infDist_le_eta_add_cost_div {X : Type*} [MetricSpace X]
    {K : Set X} {P : ℝ → X} {w : X → ℝ} {η a₀ c : ℝ}
    (hP : ContinuousOn P (Icc 0 1)) (ha₀ : 0 < a₀) (hc : 0 ≤ c)
    (hstart : Metric.infDist (P 0) K ≤ η)
    (hwoff : ∀ z, η ≤ Metric.infDist z K → a₀ ≤ w z)
    (hcost : weightedLength w P 0 1 ≤ ENNReal.ofReal c) :
    ∀ t ∈ Icc (0 : ℝ) 1, Metric.infDist (P t) K ≤ η + c / a₀ :=
  infDist_le_eta_add_cost_div_on zero_le_one hP ha₀ hc hstart hwoff hcost

end HigherDimLQGMetric
