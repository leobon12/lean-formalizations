import SupercriticalLQGUniqueness.B2.LscTop.Metrizable
import SLUMetricAPI2
import LQGMetric.Metric.Internal

 










set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open LQGMetric.MetricGeometry

 


theorem internal_eq_of_metric_ball (D : LSCMetric) (hD : D.IsLengthSpace)
    {Y : Set ℂ} {x y : ℂ} {r : ℝ≥0∞} (hr : r < ∞)
    (hball : Metric.eball (D.pt x) r ⊆ D.pt '' Y)
    (hxy : D (x, y) < r) (hx : x ∈ Y) (hy : y ∈ Y) :
    D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) = D (x, y) := by
  have hxyfin : D (x, y) < ∞ := hxy.trans hr
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
    obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hD x y hxyfin (min ε δ)
      (by exact_mod_cast lt_min hε hδ)
    have hminδ : ENNReal.ofReal (min (ε : ℝ) (δ : ℝ)) ≤ (δ : ℝ≥0∞) := by
      calc
        ENNReal.ofReal (min (ε : ℝ) (δ : ℝ)) ≤ ENNReal.ofReal (δ : ℝ) :=
          ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ = δ := ENNReal.ofReal_coe_nnreal
    have hminε : ENNReal.ofReal (min (ε : ℝ) (δ : ℝ)) ≤ (ε : ℝ≥0∞) := by
      calc
        ENNReal.ofReal (min (ε : ℝ) (δ : ℝ)) ≤ ENNReal.ofReal (ε : ℝ) :=
          ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ε := ENNReal.ofReal_coe_nnreal
    have hlenr : D.len P a b < r :=
      hlen.trans_lt (lt_of_le_of_lt (add_le_add le_rfl hminδ) hδr)
    have hY : ∀ t ∈ Icc a b, P t ∈ Y := by
      intro t ht
      have hxt : D (x, P t) ≤ D.len P a b := by
        rw [← ha, ← D.edist_pt]
        exact (edist_le_curveLength (D.pt ∘ P) ht.1).trans
          (curveLength_mono (D.pt ∘ P) le_rfl ht.2)
      have hm : D.pt (P t) ∈ Metric.eball (D.pt x) r := by
        rw [Metric.mem_eball, edist_comm, D.edist_pt]
        exact hxt.trans_lt hlenr
      rcases hball hm with ⟨w, hw, hweq⟩
      change w = P t at hweq
      exact hweq ▸ hw
    calc
      D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ D.len P a b := by
        unfold LSCMetric.internal
        exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
          iInf_le_of_le hP <| iInf_le_of_le hY <|
            iInf_le_of_le ha <| iInf_le_of_le hb le_rfl
      _ ≤ D (x, y) + ε := hlen.trans (add_le_add le_rfl hminε)
  · rw [D.internal_eq_internalEDist, ← D.edist_pt]
    exact edist_le_internalEDist (D.pt '' Y) (D.pt x) (D.pt y)

end SupercriticalLQGUniqueness.B2.PfeAxioms
