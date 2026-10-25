import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.CompactAttain




 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

 

theorem exists_shield_loop (D : LSCMetric) (z : ℂ) (t : ℝ)
    (hcheap : Objects.CorrectedEvent.around D z t (2 * t) < Objects.CorrectedEvent.acr D z (2 * t) (3 * t)) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
      P '' Icc a b ⊆ Objects.CorrectedEvent.ann z t (2 * t) ∧
      LQGMetric.Disconnects (P '' Icc a b) (Metric.sphere z t)
        (Metric.sphere z (2 * t)) ∧
      D.len P a b < Objects.CorrectedEvent.acr D z (2 * t) (3 * t) := by
  unfold Objects.CorrectedEvent.around at hcheap
  obtain ⟨P, a, b, hP, htrace, hdis, hlen⟩ :=
    (by simpa only [iInf_lt_iff] using hcheap)
  exact ⟨P, a, b, hP, htrace, hdis, hlen⟩

 

theorem acr_le_crossing (D : LSCMetric) (z : ℂ) (t : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (htrace : P '' Icc a b ⊆ Objects.CorrectedEvent.cann z (2 * t) (3 * t))
    (ha : P a ∈ Metric.sphere z (2 * t))
    (hb : P b ∈ Metric.sphere z (3 * t)) :
    Objects.CorrectedEvent.acr D z (2 * t) (3 * t) ≤ D.len P a b := by
  unfold Objects.CorrectedEvent.acr
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le htrace <|
    iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

 


theorem strict_surgery_sum {pre loop cross post total acr : ENNReal}
    (hfinite : total < ⊤)
    (hcheap : loop < acr) (hcross : acr ≤ cross)
    (hpaid : pre + cross + post ≤ total) :
    pre + loop + post < total := by
  have hpre : pre ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite.ne
      (le_trans (le_add_right le_rfl) (le_trans (le_add_right le_rfl) hpaid))
  have hpost : post ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite.ne
      (le_trans (le_add_left le_rfl) hpaid)
  have hlt : pre + loop + post < pre + cross + post := by
    have hmid : pre + loop < pre + cross :=
      ENNReal.add_lt_add_left hpre (hcheap.trans_le hcross)
    exact ENNReal.add_lt_add_right hpost hmid
  exact hlt.trans_le hpaid

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
