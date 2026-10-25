import SupercriticalLQGUniqueness.B2.Iface.Statements
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem euclidean_limit_eq_metric_limit (D : LSCMetric) (s : ℕ → ℂ) (z z' : ℂ)
    (heuc : Tendsto s atTop (𝓝 z))
    (hmetric : Tendsto (fun n => D.1 (z', s n)) atTop (𝓝 0)) : z' = z := by
  have hpair : Tendsto (fun n => (z', s n)) atTop (𝓝 (z', z)) :=
    tendsto_const_nhds.prodMk_nhds heuc
  have hzero : D.1 (z', z) = 0 := by
    by_contra hne
    have hpos : 0 < D.1 (z', z) := lt_of_le_of_ne zero_le (Ne.symm hne)
    obtain ⟨a, -, ha0, ha⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
    have hevent : ∀ᶠ n in atTop, D.1 (z', s n) ≤ ENNReal.ofReal a :=
      (hmetric.eventually (isOpen_Iio.mem_nhds ha0)).mono fun n hn => hn.le
    have hclosed : IsClosed {p : ℂ × ℂ | D.1 p ≤ ENNReal.ofReal a} :=
      D.2.2.isClosed_preimage (ENNReal.ofReal a)
    have hlim : D.1 (z', z) ≤ ENNReal.ofReal a :=
      hclosed.mem_of_tendsto hpair hevent
    exact (not_le_of_gt ha) hlim
  exact D.isExtMetric.2.1 z' z hzero

 


theorem continuousOn_euclidean_of_bounded (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hbounded : Bornology.IsBounded (P '' Icc a b)) :
    ContinuousOn P (Icc a b) := by
  obtain ⟨R, hR⟩ := hbounded.subset_ball 0
  intro t ht
  change Tendsto P (𝓝[Icc a b] t) (𝓝 (P t))
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hseq : ∀ᶠ n in atTop, P (ns n) ∈ Metric.closedBall 0 R := by
    filter_upwards [hns.eventually self_mem_nhdsWithin] with n hn
    exact Metric.ball_subset_closedBall (hR ⟨ns n, hn, rfl⟩)
  obtain ⟨w, _, φ, hφ, hw⟩ :=
    (isCompact_closedBall (0 : ℂ) R).tendsto_subseq' hseq.frequently
  refine ⟨φ, ?_⟩
  have hnsφ : Tendsto (ns ∘ φ) atTop (𝓝[Icc a b] t) :=
    hns.comp hφ.tendsto_atTop
  have hD : Tendsto (fun n => D.pt (P (ns (φ n)))) atTop
      (𝓝 (D.pt (P t))) := by
    have hDwithin : Tendsto (D.pt ∘ P) (𝓝[Icc a b] t)
        (𝓝 (D.pt (P t))) := hP.2 t ht
    exact hDwithin.comp hnsφ
  have hd0 : Tendsto (fun n => D.1 (P (ns (φ n)), P t)) atTop (𝓝 0) :=
    (tendsto_iff_edist_tendsto_0).mp hD
  have hd0' : Tendsto (fun n => D.1 (P t, P (ns (φ n)))) atTop (𝓝 0) := by
    simpa only [D.isExtMetric.2.2.1] using hd0
  have hweq : P t = w :=
    euclidean_limit_eq_metric_limit D (fun n => P (ns (φ n))) w (P t) hw hd0'
  change Tendsto (fun n => P (ns (φ n))) atTop (𝓝 w) at hw
  simpa only [hweq] using hw

 


theorem compact_separated_pairs_pos (D : LSCMetric) {K : Set ℂ}
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hne : ({p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}).Nonempty) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ p : ℂ × ℂ,
      p.1 ∈ K → p.2 ∈ K → δ ≤ dist p.1 p.2 → c ≤ D.1 p := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ dist p.1 p.2}
  have hS : IsCompact S := by
    have hclosed : IsClosed {p : ℂ × ℂ | δ ≤ dist p.1 p.2} :=
      isClosed_le continuous_const continuous_dist
    have hSeq : S = (K ×ˢ K) ∩ {p : ℂ × ℂ | δ ≤ dist p.1 p.2} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hSeq]
    exact (hK.prod hK).inter_right hclosed
  obtain ⟨p, hp, hmin⟩ :=
    (D.2.2.lowerSemicontinuousOn S).exists_isMinOn hne hS
  have hpne : p.1 ≠ p.2 := by
    intro heq
    have hsep : δ ≤ dist p.1 p.2 := hp.2.2
    rw [heq, dist_self] at hsep
    linarith
  have hDp : D.1 p ≠ 0 := by
    intro hz
    exact hpne (D.isExtMetric.2.1 p.1 p.2 hz)
  refine ⟨D.1 p, pos_iff_ne_zero.mpr hDp, ?_⟩
  intro q hq1 hq2 hqδ
  exact isMinOn_iff.mp hmin q ⟨hq1, hq2, hqδ⟩

end SupercriticalLQGUniqueness.B2.PfeLocal
