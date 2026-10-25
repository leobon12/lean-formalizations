import SupercriticalLQGUniqueness.B2.PfeWeyl.GammaCompact

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem eventual_compact_oscillation {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {K : Set ℂ} (hK : IsCompact K)
    (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ u ∈ K, ∀ v ∈ K, D (u, v) ≤ ENNReal.ofReal δ →
        |f u - f v| < θ) ∧
      (∀ᶠ n in atTop, ∀ u ∈ K, ∀ v ∈ K,
        G n (u, v) ≤ ENNReal.ofReal δ → |fn n u - fn n v| < θ) := by
  have hhalf : 0 < θ / 2 := half_pos hθ
  obtain ⟨ε, hε, hmod⟩ := compact_oscillation D f hK hhalf
  let S : Set (ℂ × ℂ) := (K ×ˢ K) ∩ {p | θ / 2 ≤ |f p.1 - f p.2|}
  have hc : Continuous (fun p : ℂ × ℂ => |f p.1 - f p.2|) :=
    ((f.continuous.comp continuous_fst).sub
      (f.continuous.comp continuous_snd)).abs
  have hSc : IsCompact S :=
    (hK.prod hK).inter_right (isClosed_le continuous_const hc)
  have hεinf : ENNReal.ofReal ε ≤ ⨅ p ∈ S, D p := by
    apply le_iInf
    intro p
    apply le_iInf
    intro hp
    by_contra hnot
    have hpD : D p ≤ ENNReal.ofReal ε := le_of_not_ge hnot
    exact (not_lt_of_ge hp.2) (hmod p.1 hp.1.1 p.2 hp.1.2 hpD)
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδinf : ENNReal.ofReal δ < ⨅ p ∈ S, D p :=
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)).trans_le hεinf
  have hγ := compact_iInf_liminf hG hSc
  have htail : ∀ᶠ n in atTop,
      ENNReal.ofReal δ < ⨅ p ∈ S, G n p :=
    eventually_lt_of_lt_liminf (hδinf.trans_le hγ)
  have hclose := hfn (θ / 4) (by linarith)
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro u hu v hv hD
    have hεbound : D (u, v) ≤ ENNReal.ofReal ε :=
      hD.trans (ENNReal.ofReal_le_ofReal (by dsimp [δ]; linarith))
    exact (hmod u hu v hv hεbound).trans (half_lt_self hθ)
  · filter_upwards [htail, hclose] with n hlow hfnn u hu v hv hDn
    have hlimosc : |f u - f v| < θ / 2 := by
      by_contra hnot
      have hp : (u, v) ∈ S := ⟨⟨hu, hv⟩, le_of_not_gt hnot⟩
      have hchain : ENNReal.ofReal δ < G n (u, v) :=
        hlow.trans_le (iInf₂_le (u, v) hp)
      exact (not_lt_of_ge hDn) hchain
    have htri : |fn n u - fn n v| ≤
        |fn n u - f u| + |f u - f v| + |f v - fn n v| := by
      calc
        |fn n u - fn n v| = |(fn n u - f u) + (f u - f v) + (f v - fn n v)| := by
          congr 1
          ring
        _ ≤ |(fn n u - f u) + (f u - f v)| + |f v - fn n v| := abs_add_le _ _
        _ ≤ |fn n u - f u| + |f u - f v| + |f v - fn n v| := by
          gcongr
          exact abs_add_le _ _
    have hvclose : |f v - fn n v| < θ / 4 := by
      simpa only [abs_sub_comm] using hfnn v hv
    linarith [hfnn u hu]

end SupercriticalLQGUniqueness.B2.PfeWeyl
