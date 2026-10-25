import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.B2.PfeWeyl.OrdinarySampling
import SupercriticalLQGUniqueness.B2.PfeWeyl.GammaCompact
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.WeylBump

 
















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem len_eq_ofReal_of_unitSpeed (E : LSCMetric) {P : ℝ → ℂ} {L : ℝ}
    (hL : 0 ≤ L) (hu : HasUnitSpeedOn (E.pt ∘ P) (Icc 0 L)) :
    E.len P 0 L = ENNReal.ofReal L := by
  have h := (hasUnitSpeedOn_iff E P L).1 hu 0 ⟨le_rfl, hL⟩ L ⟨hL, le_rfl⟩ hL
  simpa only [sub_zero] using h

 

theorem weylScale_le_of_unitSpeed_bound (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (E : LSCMetric) {P : ℝ → ℂ} {L M' : ℝ}
    (hP : E.IsCurve P 0 L) (hu : HasUnitSpeedOn (E.pt ∘ P) (Icc 0 L))
    (hg : ∀ t ∈ Icc 0 L, g (P t) ≤ M') :
    weylScale ξ g E (P 0, P L) ≤
      ENNReal.ofReal (Real.exp (ξ * M')) * ENNReal.ofReal L := by
  have hcost : weylScale ξ g E (P 0, P L) ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t))) := by
    unfold weylScale
    exact iInf_le_of_le P (iInf_le_of_le L (iInf_le_of_le hP
      (iInf_le_of_le hu (iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl)))))
  refine hcost.trans ?_
  calc
    (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))) ≤
        ∫⁻ _t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * M')) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hg t ht) hξ))
    _ = ENNReal.ofReal (Real.exp (ξ * M')) * ENNReal.ofReal L := by
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]

 



theorem weylScale_le_exp_mul_of_local (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (E : LSCMetric) (hE : E.IsLengthSpace) {u v : ℂ} (huv : E (u, v) < ⊤)
    {η : ℝ} (hη : 0 < η) {M' : ℝ}
    (hloc : ∀ x, E (u, x) < E (u, v) + ENNReal.ofReal η → g x ≤ M') :
    weylScale ξ g E (u, v) ≤
      ENNReal.ofReal (Real.exp (ξ * M')) * (E (u, v) + ENNReal.ofReal η) := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hlen⟩ :=
    exists_near_min_ordinary_curve E hE u v huv hη
  have hg : ∀ t ∈ Icc 0 L, g (P t) ≤ M' := by
    intro t ht
    apply hloc
    have h1 : E (P 0, P t) ≤ E.len P 0 t := LSCMetric.apply_le_len E P ht.1
    have h2 : E.len P 0 t ≤ E.len P 0 L := len_mono_Icc E P le_rfl ht.2
    rw [hP0] at h1
    exact (h1.trans h2).trans_lt hlen
  have hb := weylScale_le_of_unitSpeed_bound ξ hξ g E hP hu hg
  rw [hP0, hPL] at hb
  refine hb.trans ?_
  rw [← len_eq_ofReal_of_unitSpeed E hP.1 hu]
  gcongr

 


theorem weylScale_le_of_bound_on_sub (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (d : LSCMetric) {P : ℝ → ℂ} {L M' : ℝ}
    (hc : ContinuousOn (d.pt ∘ P) (Icc 0 L))
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hg : ∀ t ∈ Icc 0 L, g (P t) ≤ M')
    {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') (ht' : t' ≤ L) :
    weylScale ξ g d (P t, P t') ≤
      ENNReal.ofReal (Real.exp (ξ * M')) * ENNReal.ofReal (t' - t) := by
  let Q : ℝ → ℂ := fun τ => P (t + τ)
  have hQc : d.IsCurve Q 0 (t' - t) := by
    refine ⟨by linarith, ?_⟩
    have hmaps : MapsTo (fun τ : ℝ => t + τ) (Icc 0 (t' - t)) (Icc 0 L) :=
      fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact hc.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hQu : HasUnitSpeedOn (d.pt ∘ Q) (Icc 0 (t' - t)) :=
    Uniqueness.TwoScale.S36.hasUnitSpeedOn_shift hu ht ht'
  have hQg : ∀ τ ∈ Icc 0 (t' - t), g (Q τ) ≤ M' := fun τ hτ =>
    hg (t + τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have h := weylScale_le_of_unitSpeed_bound ξ hξ g d hQc hQu hQg
  simpa only [Q, add_zero, add_sub_cancel] using h

 




theorem weyl_isCurve_len_le (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ g d (x, y))
    {P : ℝ → ℂ} {L M' : ℝ} (hL : 0 ≤ L)
    (hc : ContinuousOn (d.pt ∘ P) (Icc 0 L))
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hg : ∀ t ∈ Icc 0 L, g (P t) ≤ M') :
    e.IsCurve P 0 L ∧
      e.len P 0 L ≤ ENNReal.ofReal (Real.exp (ξ * M')) * ENNReal.ofReal L := by
  set k : ℝ≥0 := (Real.exp (ξ * M')).toNNReal with hkdef
  have hk : (k : ℝ≥0∞) = ENNReal.ofReal (Real.exp (ξ * M')) := rfl
  have hlip : LipschitzOnWith k (e.pt ∘ P) (Icc 0 L) := by
    have key : ∀ t ∈ Icc 0 L, ∀ t' ∈ Icc 0 L, t ≤ t' →
        edist ((e.pt ∘ P) t) ((e.pt ∘ P) t') ≤ k * edist t t' := by
      intro t ht t' ht' htt'
      change e (P t, P t') ≤ _
      rw [he, hk, edist_dist, Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (by linarith)]
      exact weylScale_le_of_bound_on_sub ξ hξ g d hc hu hg ht.1 htt' ht'.2
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

 



theorem compact_offDiag_pos (D : LSCMetric) {S : Set (ℂ × ℂ)}
    (hS : IsCompact S) (hoff : ∀ p ∈ S, p.1 ≠ p.2) :
    0 < ⨅ p ∈ S, D p := by
  rcases S.eq_empty_or_nonempty with hemp | hne
  · simp [hemp]
  obtain ⟨p, hp, hmin⟩ :=
    (D.lowerSemicontinuous.lowerSemicontinuousOn S).exists_isMinOn hne hS
  have hp0 : 0 < D p := pos_iff_ne_zero.mpr
    (fun hz => hoff p hp (D.isExtMetric.2.1 p.1 p.2 hz))
  exact lt_of_lt_of_le hp0 (le_iInf fun q => le_iInf fun hq => hmin hq)

 



theorem exists_uniform_euclidean_control (D : LSCMetric) (hD : D.IsLengthSpace)
    (hforget : Continuous (euclidForget D)) {K : Set ℂ} (hK : IsCompact K)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ u ∈ K, ∀ v : ℂ, D (u, v) < c → dist u v < τ := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ K ∧ dist p.1 p.2 = τ / 2}
  have hSsub : S ⊆ K ×ˢ Metric.cthickening (τ / 2) K := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    exact Metric.mem_cthickening_of_dist_le p.2 p.1 (τ / 2) K hp.1
      (by rw [dist_comm]; exact hp.2.le)
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {p : ℂ × ℂ | p.1 ∈ K} :=
      hK.isClosed.preimage continuous_fst
    have h2 : IsClosed {p : ℂ × ℂ | dist p.1 p.2 = τ / 2} :=
      isClosed_eq (continuous_fst.dist continuous_snd) continuous_const
    exact h1.inter h2
  have hS : IsCompact S :=
    (hK.prod (hK.cthickening)).of_isClosed_subset hSclosed hSsub
  have hoff : ∀ p ∈ S, p.1 ≠ p.2 := by
    intro p hp heq
    have := hp.2
    rw [heq, dist_self] at this
    linarith
  refine ⟨⨅ p ∈ S, D p, compact_offDiag_pos D hS hoff, ?_⟩
  intro u hu v hv
  by_contra hfar
  push Not at hfar
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hv
  have hfin : D (u, v) < ⊤ := hv.trans_le le_top
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ :=
    hD u v hfin (r : ℝ) (by exact_mod_cast hr0)
  have hPc := continuousOn_of_isCurve_of_forget D hforget hP
  have hdc : ContinuousOn (fun t => dist u (P t)) (Icc a b) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hPc)
  have hivt := intermediate_value_Icc hP.1 hdc
  have hmem : τ / 2 ∈ Icc (dist u (P a)) (dist u (P b)) := by
    rw [hPa, hPb, dist_self]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨t, ht, hdt⟩ := hivt hmem
  have hpS : (u, P t) ∈ S := ⟨hu, hdt⟩
  have hlow : (⨅ p ∈ S, D p) ≤ D (u, P t) := iInf₂_le _ hpS
  have hup : D (u, P t) ≤ D (u, v) + (r : ℝ≥0∞) := by
    have h1 : D (P a, P t) ≤ D.len P a t := LSCMetric.apply_le_len D P ht.1
    have h2 : D.len P a t ≤ D.len P a b := len_mono_Icc D P le_rfl ht.2
    rw [← hPa]
    refine (h1.trans h2).trans ?_
    rw [hPa]
    simpa only [ENNReal.ofReal_coe_nnreal] using hlen
  exact (not_lt_of_ge (hlow.trans hup)) hr

 

theorem eventually_lt_acrossDist {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) (A : EuclideanAnnulus) {T : ℝ≥0∞}
    (hT : T < acrossDist D A) :
    ∀ᶠ n in atTop, T < acrossDist (G n) A := by
  obtain ⟨r, hTr, hr⟩ := exists_between hT
  have hK : IsCompact (A.innerBoundary ×ˢ A.outerBoundary) :=
    (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  rw [acrossDist_eq_iInf_prod] at hr
  filter_upwards [eventually_lower_on_compact hG hK hr] with n hn
  rw [acrossDist_eq_iInf_prod]
  exact hTr.trans_le (le_iInf₂ hn)

 
theorem acrossDist_pos (D : LSCMetric) (A : EuclideanAnnulus) :
    0 < acrossDist D A := by
  rw [acrossDist_eq_iInf_prod]
  refine compact_offDiag_pos D ((isCompact_sphere _ _).prod (isCompact_sphere _ _)) ?_
  intro p hp heq
  have h1 : dist p.1 A.center = A.innerRadius := hp.1
  have h2 : dist p.2 A.center = A.outerRadius := hp.2
  rw [heq] at h1
  linarith [A.innerRadius_lt_outerRadius]

end SupercriticalLQGUniqueness.B2.PfeWeyl
