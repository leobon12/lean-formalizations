import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaInnerUpper

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem buffered_inner_internal_upper_of_compact_collar
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {W V K : Set ℂ} (hWV : W ⊆ V)
    (hWK : W ⊆ interior K)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hneFront : (frontier V).Nonempty)
    (hdisj : Disjoint K (frontier V))
    (hsmall : SmallAnnulusCosts G D K V)
    (x y : W) {C : ℝ} (hC : 0 < C)
    (hxy : D.internal W (x, y) < ENNReal.ofReal C) :
    ∃ x' y' : ℕ → V,
      Tendsto x' atTop (𝓝 ⟨(x : ℂ), hWV x.property⟩) ∧
      Tendsto y' atTop (𝓝 ⟨(y : ℂ), hWV y.property⟩) ∧
      ∀ᶠ n in atTop, (G n).internal V (x' n, y' n) < ENNReal.ofReal C := by
  have hneK : K.Nonempty := ⟨(x : ℂ), interior_subset (hWK x.property)⟩
  have hsep : 0 < ⨅ p ∈ K ×ˢ frontier V, D p :=
    compact_setDistance_pos D hK hfront hneK hneFront hdisj
  have hone : (0 : ℝ≥0∞) < 1 := by norm_num
  have hmin : 0 < min (⨅ p ∈ K ×ˢ frontier V, D p) 1 :=
    lt_min hsep hone
  obtain ⟨R, hRpos, hRmin⟩ := exists_between hmin
  obtain ⟨r, hrpos, hrR⟩ := exists_between hRpos
  have hR : R < ⨅ p ∈ K ×ˢ frontier V, D p :=
    hRmin.trans_le (min_le_left _ _)
  have hrfin : r < ∞ := by
    have hrone : r < (1 : ℝ≥0∞) :=
      (hrR.trans hRmin).trans_le (min_le_right _ _)
    exact hrone.trans (by norm_num)
  exact buffered_inner_internal_upper_real hG hLen hPath hforget hWV hWK
    hV hK hfront hsmall hrR hR hrpos hrfin x y hC hxy

end SupercriticalLQGUniqueness.B2.PfeAxioms
