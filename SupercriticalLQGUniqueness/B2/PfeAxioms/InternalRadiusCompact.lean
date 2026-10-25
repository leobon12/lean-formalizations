import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalRadius
import SupercriticalLQGUniqueness.B2.LscTop.Compact
import SupercriticalLQGUniqueness.B2.PfeWeyl.GammaCompact

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem compact_setDistance_pos (D : LSCMetric) {K L : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L) (hneK : K.Nonempty)
    (hneL : L.Nonempty) (hKL : Disjoint K L) :
    0 < ⨅ p ∈ K ×ˢ L, D p := by
  let S : Set (ℂ × ℂ) := K ×ˢ L
  have hS : IsCompact S := hK.prod hL
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hneK
    obtain ⟨y, hy⟩ := hneL
    exact ⟨(x, y), hx, hy⟩
  obtain ⟨p, hp, hmin⟩ :=
    (D.lowerSemicontinuous.lowerSemicontinuousOn S).exists_isMinOn hne hS
  have hpne : p.1 ≠ p.2 := by
    intro heq
    exact Set.disjoint_left.mp hKL hp.1 (heq ▸ hp.2)
  have hp0 : 0 < D p := pos_iff_ne_zero.mpr (fun hz => hpne (D.isExtMetric.2.1 p.1 p.2 hz))
  apply lt_of_lt_of_le hp0
  exact le_iInf fun q => le_iInf fun hq => hmin hq

 

theorem eventually_compact_setDistance_pos {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) {K L : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L) (hneK : K.Nonempty)
    (hneL : L.Nonempty) (hKL : Disjoint K L) :
    ∃ r : ℝ≥0∞, 0 < r ∧ ∀ᶠ n in atTop, ∀ p ∈ K ×ˢ L, r ≤ G n p := by
  have hpos := compact_setDistance_pos D hK hL hneK hneL hKL
  obtain ⟨r, hr0, hr⟩ := exists_between hpos
  exact ⟨r, hr0, B2.PfeWeyl.eventually_lower_on_compact hG (hK.prod hL) hr⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
