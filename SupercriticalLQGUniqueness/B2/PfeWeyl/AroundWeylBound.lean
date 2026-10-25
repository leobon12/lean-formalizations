import SupercriticalLQGUniqueness.B2.PfeWeyl.Inputs
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.WeylBump

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open LQGMetric.MetricGeometry

private theorem weylScale_le_of_bound_on (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (d : LSCMetric) {P : ℝ → ℂ} {L M : ℝ}
    (hc : ContinuousOn (d.pt ∘ P) (Icc 0 L))
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hf : ∀ t ∈ Icc 0 L, f (P t) ≤ M)
    {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') (ht' : t' ≤ L) :
    weylScale ξ f d (P t, P t') ≤
      ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal (t' - t) := by
  let Q : ℝ → ℂ := fun τ => P (t + τ)
  have hQc : d.IsCurve Q 0 (t' - t) := by
    refine ⟨by linarith, ?_⟩
    have hmaps : MapsTo (fun τ : ℝ => t + τ) (Icc 0 (t' - t)) (Icc 0 L) :=
      fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact hc.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hQu : HasUnitSpeedOn (d.pt ∘ Q) (Icc 0 (t' - t)) :=
    Uniqueness.TwoScale.S36.hasUnitSpeedOn_shift hu ht ht'
  have hcost : weylScale ξ f d (P t, P t') ≤
      ∫⁻ τ in Icc 0 (t' - t), ENNReal.ofReal (Real.exp (ξ * f (Q τ))) := by
    unfold weylScale
    exact iInf_le_of_le Q (iInf_le_of_le (t' - t) (iInf_le_of_le hQc
      (iInf_le_of_le hQu (iInf_le_of_le (by simp [Q])
        (iInf_le_of_le (by simp [Q]) le_rfl)))))
  refine hcost.trans ?_
  calc
    (∫⁻ τ in Icc 0 (t' - t), ENNReal.ofReal (Real.exp (ξ * f (Q τ)))) ≤
        ∫⁻ τ in Icc 0 (t' - t), ENNReal.ofReal (Real.exp (ξ * M)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hf (t + τ)
          ⟨by linarith [hτ.1], by linarith [hτ.2]⟩) hξ))
    _ = ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal (t' - t) := by
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]

private theorem isCurve_len_le_of_weyl_bound (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y))
    {P : ℝ → ℂ} {L M : ℝ} (hL : 0 ≤ L)
    (hc : ContinuousOn (d.pt ∘ P) (Icc 0 L))
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hf : ∀ t ∈ Icc 0 L, f (P t) ≤ M) :
    e.IsCurve P 0 L ∧
      e.len P 0 L ≤ ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal L := by
  set k : ℝ≥0 := (Real.exp (ξ * M)).toNNReal with hkdef
  have hk : (k : ℝ≥0∞) = ENNReal.ofReal (Real.exp (ξ * M)) := rfl
  have hlip : LipschitzOnWith k (e.pt ∘ P) (Icc 0 L) := by
    have key : ∀ t ∈ Icc 0 L, ∀ t' ∈ Icc 0 L, t ≤ t' →
        edist ((e.pt ∘ P) t) ((e.pt ∘ P) t') ≤ k * edist t t' := by
      intro t ht t' ht' htt'
      change e (P t, P t') ≤ _
      rw [he, hk, edist_dist, Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (by linarith)]
      exact weylScale_le_of_bound_on ξ hξ f d hc hu hf ht.1 htt' ht'.2
    intro t ht t' ht'
    rcases le_total t t' with h | h
    · exact key t ht t' ht' h
    · rw [edist_comm, edist_comm t t']
      exact key t' ht' t ht h
  refine ⟨⟨hL, hlip.continuousOn⟩, ?_⟩
  have h1 := hlip.comp_eVariationOn_le (g := id) (s := Icc 0 L) (mapsTo_id _)
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc 0 L) ≤ ENNReal.ofReal L := by
    have := ((monotone_id (α := ℝ)).monotoneOn (Icc 0 L)).eVariationOn_eq
      (left_mem_Icc.mpr hL) (right_mem_Icc.mpr hL)
    rw [inter_self] at this
    rw [this]
    simp
  calc e.len P 0 L = eVariationOn ((e.pt ∘ P) ∘ id) (Icc 0 L) := rfl
    _ ≤ k * eVariationOn (id : ℝ → ℝ) (Icc 0 L) := h1
    _ ≤ k * ENNReal.ofReal L := mul_le_mul' le_rfl h2
    _ = _ := by rw [hk]

 

theorem aroundDist_le_mul_of_weyl_bound
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y))
    (A : EuclideanAnnulus) (M : ℝ)
    (hfA : ∀ y ∈ A.toSet, f y ≤ M) :
    aroundDist e A ≤ ENNReal.ofReal (Real.exp (ξ * M)) * aroundDist d A := by
  have hk0 : ENNReal.ofReal (Real.exp (ξ * M)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  conv_rhs => unfold aroundDist
  simp only [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]
  refine le_iInf fun π => le_iInf fun a => le_iInf fun b => le_iInf fun hπ =>
    le_iInf fun htr => le_iInf fun hsep => ?_
  by_cases hfin : d.len π a b = ⊤
  · rw [hfin, ENNReal.mul_top hk0]
    exact le_top
  obtain ⟨Q, T, hlen, hT, hQc, hQu, himg⟩ :=
    Uniqueness.TwoScale.S36.exists_unit_reparam d hπ hfin
  have hQA : ∀ t ∈ Icc 0 T, Q t ∈ A.toSet := by
    intro t ht
    have : Q t ∈ π '' Icc a b := himg ▸ ⟨t, ht, rfl⟩
    obtain ⟨w, hw, hwt⟩ := this
    rw [← hwt]
    exact htr w hw
  obtain ⟨hQe, hlenQ⟩ := isCurve_len_le_of_weyl_bound ξ hξ f d e he
    hT hQc hQu (fun t ht => hfA _ (hQA t ht))
  have hsepQ : Disconnects (Q '' Icc 0 T) A.innerBoundary A.outerBoundary := by
    rw [himg]
    exact hsep
  calc aroundDist e A ≤ e.len Q 0 T := by
        unfold aroundDist
        exact iInf_le_of_le Q (iInf_le_of_le 0 (iInf_le_of_le T
          (iInf_le_of_le hQe (iInf_le_of_le hQA
            (iInf_le_of_le hsepQ le_rfl)))))
    _ ≤ ENNReal.ofReal (Real.exp (ξ * M)) * ENNReal.ofReal T := hlenQ
    _ = ENNReal.ofReal (Real.exp (ξ * M)) * d.len π a b := by rw [hlen]

 

theorem smallAnnulusCosts_weyl
    {G W : ℕ → LSCMetric} {D : LSCMetric}
    (ξ : ℝ) (hξ : 0 ≤ ξ) (fn : ℕ → C(ℂ, ℝ))
    {K' K'' : Set ℂ} (hsmall : SmallAnnulusCosts G D K' K'')
    (hW : ∀ n p, W n p = weylScale ξ (fn n) (G n) p)
    (M : ℝ) (hM : ∀ n, ∀ z ∈ K'', fn n z ≤ M) :
    ∀ z ∈ K', IsNonsingular D z →
      ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ →
        ∃ A : EuclideanAnnulus,
          IsRationalDoubleAnnulus A ∧
          dist z A.center < A.innerRadius ∧
          A.outerRadius < ρ ∧ A.toSet ⊆ K'' ∧
          ∀ᶠ n in atTop, aroundDist (W n) A < ENNReal.ofReal δ := by
  intro z hz hns δ hδ ρ hρ
  let c := Real.exp (ξ * M)
  have hc : 0 < c := Real.exp_pos _
  let η := δ / (2 * c)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hrat, hzA, hρA, hAK, hGn⟩ := hsmall z hz hns η hη ρ hρ
  refine ⟨A, hrat, hzA, hρA, hAK, ?_⟩
  have hcENN : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hsmallScalar : ENNReal.ofReal c * ENNReal.ofReal η < ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_mul hc.le]
    apply (ENNReal.ofReal_lt_ofReal_iff hδ).2
    dsimp [η]
    have : c * (δ / (2 * c)) = δ / 2 := by field_simp
    linarith
  filter_upwards [hGn] with n hn
  have hbound := aroundDist_le_mul_of_weyl_bound ξ hξ (fn n) (G n) (W n)
    (fun x y => hW n (x, y)) A M (fun y hy => hM n y (hAK hy))
  calc
    aroundDist (W n) A ≤ ENNReal.ofReal c * aroundDist (G n) A := hbound
    _ < ENNReal.ofReal c * ENNReal.ofReal η := by
      simpa only [mul_comm] using
        (ENNReal.mul_lt_mul_left hcENN ENNReal.ofReal_ne_top hn)
    _ < ENNReal.ofReal δ := hsmallScalar

end SupercriticalLQGUniqueness.B2.PfeWeyl
