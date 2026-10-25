import SupercriticalLQGUniqueness.B2.PfeWeyl.CompactOscillation
import SLUMetricAPI2

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem eventually_lower_on_compact {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    {r : ℝ≥0∞} (hr : r < ⨅ p ∈ K, D p) :
    ∀ᶠ n in atTop, ∀ p ∈ K, r ≤ G n p := by
  by_contra hbad
  rw [not_eventually] at hbad
  obtain ⟨φ, hφ, hbadφ⟩ := extraction_of_frequently_atTop hbad
  have hpts : ∀ n, ∃ p ∈ K, G (φ n) p < r := by
    intro n
    simp only [not_forall, not_le] at hbadφ
    obtain ⟨p, hp, hpr⟩ := hbadφ n
    exact ⟨p, hp, hpr⟩
  choose p hpK hpbad using hpts
  obtain ⟨q, hqK, ψ, hψ, hpψ⟩ := hK.tendsto_subseq (x := p) hpK
  have hGψ : Tendsto (fun n => G (φ (ψ n))) atTop (𝓝 D) :=
    hG.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hlim : D q ≤ liminf (fun n => G (φ (ψ n)) (p (ψ n))) atTop :=
    (LSCMetric.tendsto_iff.mp hGψ).1 (p ∘ ψ) q hpψ
  have hbound : liminf (fun n => G (φ (ψ n)) (p (ψ n))) atTop ≤ r :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n => (hpbad (ψ n)).le)
  exact (not_lt_of_ge (hlim.trans hbound)) (hr.trans_le (iInf₂_le q hqK))

 

theorem compact_iInf_liminf {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) {K : Set (ℂ × ℂ)} (hK : IsCompact K) :
    (⨅ p ∈ K, D p) ≤ liminf (fun n => ⨅ p ∈ K, G n p) atTop := by
  refine le_of_forall_lt fun r hr => ?_
  obtain ⟨w, hrw, hw⟩ := exists_between hr
  have htail : ∀ᶠ n in atTop, w ≤ ⨅ p ∈ K, G n p := by
    filter_upwards [eventually_lower_on_compact hG hK hw] with n hn
    exact le_iInf fun p => le_iInf fun hp => hn p hp
  exact hrw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)

end SupercriticalLQGUniqueness.B2.PfeWeyl
