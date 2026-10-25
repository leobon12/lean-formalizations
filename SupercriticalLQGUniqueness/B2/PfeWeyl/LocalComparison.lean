import SupercriticalLQGUniqueness.B2.PfeWeyl.OrdinarySampling

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 


theorem weylScale_le_exp_mul_of_short_dist
    (D : LSCMetric) (hD : D.IsLengthSpace)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (δ θ : ℝ)
    {K K' : Set ℂ} (hloc : LocalizedNearMinPaths D ξ f K K')
    (hosc : ∀ u ∈ K', ∀ v ∈ K',
      D (u, v) ≤ ENNReal.ofReal δ → |f u - f v| < θ)
    (z : ℂ) (hz : z ∈ K) (w : ℂ) (hw : w ∈ K)
    (_hδ : 0 < δ) (_hθ : 0 ≤ θ)
    (hzw : D (z, w) < ENNReal.ofReal (δ / 2))
    {η : ℝ} (hη : 0 < η) (hηδ : η < δ / 2) (hη1 : η ≤ 1) :
    weylScale ξ f D (z, w) ≤
      ENNReal.ofReal (Real.exp (ξ * (f z + θ))) *
        (D (z, w) + ENNReal.ofReal η) := by
  have hfin : D (z, w) < ⊤ := hzw.trans ENNReal.ofReal_lt_top
  obtain ⟨P, L, hP, hu, hP0, hPL, hPK, hlen⟩ :=
    exists_localized_near_min_ordinary_curve D hD ξ f hloc z hz w hw hfin hη hη1
  have hzK' : z ∈ K' := by
    apply hPK
    exact ⟨0, ⟨le_rfl, hP.1⟩, hP0⟩
  have hseg : ∀ t ∈ Icc 0 L, D (z, P t) ≤ ENNReal.ofReal δ := by
    intro t ht
    have hdist : D (z, P t) ≤ D.len P 0 L := by
      rw [← hP0]
      exact eVariationOn.edist_le (D.pt ∘ P) ⟨le_rfl, hP.1⟩ ht
    have hsum : D (z, w) + ENNReal.ofReal η < ENNReal.ofReal δ := by
      have hhalf : 0 ≤ δ / 2 := by linarith
      calc
        D (z, w) + ENNReal.ofReal η <
            ENNReal.ofReal (δ / 2) + ENNReal.ofReal η :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hzw
        _ = ENNReal.ofReal (δ / 2 + η) :=
          (ENNReal.ofReal_add hhalf hη.le).symm
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)
    exact (hdist.trans_lt hlen).le.trans hsum.le
  have hfield : ∀ t ∈ Icc 0 L, f (P t) ≤ f z + θ := by
    intro t ht
    have h := hosc z hzK' (P t) (hPK ⟨t, ht, rfl⟩) (hseg t ht)
    exact le_of_lt (by linarith [(abs_lt.mp h).1])
  have hfieldlo : ∀ t ∈ Icc 0 L, f z - θ ≤ f (P t) := by
    intro t ht
    have h := hosc z hzK' (P t) (hPK ⟨t, ht, rfl⟩) (hseg t ht)
    exact le_of_lt (by linarith [(abs_lt.mp h).2])
  have hcost := (unitSpeed_weyl_cost_bounds D ξ hξ f hforget hP hu
    (f z - θ) (f z + θ) hfieldlo hfield).2
  have hw : weylScale ξ f D (z, w) ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
    unfold weylScale
    exact iInf_le_of_le P (iInf_le_of_le L (iInf_le_of_le hP
      (iInf_le_of_le hu (iInf_le_of_le hP0 (iInf_le_of_le hPL le_rfl)))))
  exact hw.trans (hcost.trans (mul_le_mul' le_rfl hlen.le))

 

theorem exp_mul_dist_le_weylScale_add_of_short_cost
    (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (δ θ m M : ℝ)
    {K K' : Set ℂ} (hloc : LocalizedNearMinPaths D ξ f K K')
    (hosc : ∀ u ∈ K', ∀ v ∈ K',
      D (u, v) ≤ ENNReal.ofReal δ → |f u - f v| < θ)
    (hbound : ∀ z ∈ K', m ≤ f z ∧ f z ≤ M)
    (z : ℂ) (hz : z ∈ K) (w : ℂ) (hw : w ∈ K)
    (hfin : weylScale ξ f D (z, w) ≠ ⊤)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsmall : weylScale ξ f D (z, w) + ENNReal.ofReal η <
      ENNReal.ofReal (Real.exp (ξ * m)) * ENNReal.ofReal δ) :
    ENNReal.ofReal (Real.exp (ξ * (f z - θ))) * D (z, w) <
      weylScale ξ f D (z, w) + ENNReal.ofReal η := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hPK, hcost⟩ :=
    exists_localized_near_min_weyl_curve D ξ f hloc z hz w hw hfin hη hη1
  have hzK' : z ∈ K' := hPK ⟨0, ⟨le_rfl, hP.1⟩, hP0⟩
  have hpathbound : ∀ t ∈ Icc 0 L, m ≤ f (P t) ∧ f (P t) ≤ M := by
    intro t ht
    exact hbound (P t) (hPK ⟨t, ht, rfl⟩)
  have hlenfactor := (unitSpeed_weyl_cost_bounds D ξ hξ f hforget hP hu m M
    (fun t ht => (hpathbound t ht).1) (fun t ht => (hpathbound t ht).2)).1
  have hmul : ENNReal.ofReal (Real.exp (ξ * m)) * D.len P 0 L <
      ENNReal.ofReal (Real.exp (ξ * m)) * ENNReal.ofReal δ :=
    (hlenfactor.trans_lt hcost).trans hsmall
  have hlenδ : D.len P 0 L < ENNReal.ofReal δ := by
    exact (ENNReal.mul_lt_mul_iff_left
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top).mp
        (by simpa only [mul_comm] using hmul)
  have hseg : ∀ t ∈ Icc 0 L, D (z, P t) ≤ ENNReal.ofReal δ := by
    intro t ht
    have hd : D (z, P t) ≤ D.len P 0 L := by
      rw [← hP0]
      exact eVariationOn.edist_le (D.pt ∘ P) ⟨le_rfl, hP.1⟩ ht
    exact hd.trans hlenδ.le
  have hfieldlo : ∀ t ∈ Icc 0 L, f z - θ ≤ f (P t) := by
    intro t ht
    have h := hosc z hzK' (P t) (hPK ⟨t, ht, rfl⟩) (hseg t ht)
    exact le_of_lt (by linarith [(abs_lt.mp h).2])
  have hcostlo := (unitSpeed_weyl_cost_bounds D ξ hξ f hforget hP hu
    (f z - θ) M hfieldlo (fun t ht => (hpathbound t ht).2)).1
  have hdist : D (z, w) ≤ D.len P 0 L := by
    rw [← hP0, ← hPL]
    exact eVariationOn.edist_le (D.pt ∘ P) ⟨le_rfl, hP.1⟩ ⟨hP.1, le_rfl⟩
  exact (mul_le_mul' le_rfl hdist).trans_lt (hcostlo.trans_lt hcost)

end SupercriticalLQGUniqueness.B2.PfeWeyl
