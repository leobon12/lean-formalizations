import SLUMetricAPI2
import LQGMetric.Metric.CurveNatural
import LQGMetric.Topo.RectCross




 
















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
open LQGMetric.MetricGeometry

 
theorem hasUnitSpeedOn_shift {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {L t t' : ℝ}
    (hγ : HasUnitSpeedOn γ (Icc 0 L)) (ht : 0 ≤ t) (ht' : t' ≤ L) :
    HasUnitSpeedOn (fun τ => γ (t + τ)) (Icc 0 (t' - t)) := by
  intro x hx y hy
  rcases le_or_gt x y with hxy | hxy
  · have hint : Icc 0 (t' - t) ∩ Icc x y = Icc x y := inter_eq_right.mpr
      (Icc_subset_Icc hx.1 hy.2)
    have hcomp : (fun τ => γ (t + τ)) = γ ∘ (fun τ => t + τ) := rfl
    rw [hint, hcomp, eVariationOn.comp_eq_of_monotoneOn γ (fun τ => t + τ)
      (fun a _ b _ hab => by linarith), image_const_add_Icc]
    have hxL : t + x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hyL : t + y ∈ Icc 0 L := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h := hγ hxL hyL
    rw [inter_eq_right.mpr (Icc_subset_Icc hxL.1 hyL.2)] at h
    rw [h]
    congr 1
    ring
  · rw [Icc_eq_empty (not_le.mpr hxy), inter_empty, eVariationOn.subsingleton _
      subsingleton_empty]
    rw [ENNReal.ofReal_eq_zero.mpr]
    simp only [NNReal.coe_one, one_mul]
    linarith

 
theorem weylScale_le_of_const_on (ξ : ℝ) (f : C(ℂ, ℝ)) (d : LSCMetric) {P : ℝ → ℂ} {L c : ℝ}
    (hc : ContinuousOn (d.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hf : ∀ t ∈ Icc 0 L, f (P t) = c) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t')
    (ht' : t' ≤ L) :
    weylScale ξ f d (P t, P t') ≤
      ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (t' - t) := by
  let Q : ℝ → ℂ := fun τ => P (t + τ)
  have hQc : d.IsCurve Q 0 (t' - t) := by
    refine ⟨by linarith, ?_⟩
    have hmaps : MapsTo (fun τ : ℝ => t + τ) (Icc 0 (t' - t)) (Icc 0 L) := fun τ hτ =>
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact hc.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hQu : HasUnitSpeedOn (d.pt ∘ Q) (Icc 0 (t' - t)) :=
    hasUnitSpeedOn_shift (γ := d.pt ∘ P) hu ht ht'
  unfold weylScale
  refine iInf_le_of_le Q (iInf_le_of_le (t' - t) (iInf_le_of_le hQc (iInf_le_of_le hQu
    (iInf_le_of_le (by simp [Q]) (iInf_le_of_le (by simp [Q]) ?_)))))
  have hconst : EqOn (fun τ => ENNReal.ofReal (Real.exp (ξ * f (Q τ))))
      (fun _ => ENNReal.ofReal (Real.exp (ξ * c))) (Icc 0 (t' - t)) := by
    intro τ hτ
    have hτL : t + τ ∈ Icc 0 L := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    simp only [Q, hf (t + τ) hτL]
  rw [setLIntegral_congr_fun measurableSet_Icc hconst, setLIntegral_const, Real.volume_Icc,
    sub_zero]

 
theorem isCurve_len_le_of_weyl (ξ : ℝ) (f : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y)) {P : ℝ → ℂ} {L c : ℝ} (hL : 0 ≤ L)
    (hc : ContinuousOn (d.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 L))
    (hf : ∀ t ∈ Icc 0 L, f (P t) = c) :
    e.IsCurve P 0 L ∧ e.len P 0 L ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal L := by
  set k : ℝ≥0 := (Real.exp (ξ * c)).toNNReal with hkdef
  have hk : (k : ℝ≥0∞) = ENNReal.ofReal (Real.exp (ξ * c)) := rfl
  have hlip : LipschitzOnWith k (e.pt ∘ P) (Icc 0 L) := by
    have key : ∀ t ∈ Icc 0 L, ∀ t' ∈ Icc 0 L, t ≤ t' →
        edist ((e.pt ∘ P) t) ((e.pt ∘ P) t') ≤ k * edist t t' := by
      intro t ht t' ht' htt'
      change e (P t, P t') ≤ _
      rw [he, hk, edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
      exact weylScale_le_of_const_on ξ f d hc hu hf ht.1 htt' ht'.2
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

 
theorem exists_unit_reparam (d : LSCMetric) {π : ℝ → ℂ} {a b : ℝ} (hπ : d.IsCurve π a b)
    (hfin : d.len π a b ≠ ⊤) :
    ∃ (Q : ℝ → ℂ) (T : ℝ), d.len π a b = ENNReal.ofReal T ∧ 0 ≤ T ∧
      ContinuousOn (d.pt ∘ Q) (Icc 0 T) ∧ HasUnitSpeedOn (d.pt ∘ Q) (Icc 0 T) ∧
      Q '' Icc 0 T = π '' Icc a b := by
  have hab : a ≤ b := hπ.1
  have hcont : ContinuousOn (d.pt ∘ π) (Icc a b) := hπ.2
  have hL : curveLength (d.pt ∘ π) a b ≠ ⊤ := hfin
  set T := (curveLength (d.pt ∘ π) a b).toReal with hTdef
  let Q : ℝ → ℂ := fun τ => @lengthParam d.Space _ (d.pt ∘ π) a b τ
  have hQD : d.pt ∘ Q = lengthParam (d.pt ∘ π) a b := by
    funext τ
    rfl
  have himage := variationOnFromTo_image_Icc hab hcont hL
  refine ⟨Q, T, ?_, ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · rw [hTdef, ENNReal.ofReal_toReal hL]
    rfl
  · rw [hQD]
    exact (lipschitzOnWith_lengthParam hab hcont hL).continuousOn
  · rw [hQD]
    exact hasUnitSpeedOn_lengthParam hab hcont hL
  · ext y
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      have hτ' : τ ∈ variationOnFromTo (d.pt ∘ π) (Icc a b) a '' Icc a b := by
        rw [himage]
        exact hτ
      obtain ⟨w, hw, hwτ⟩ := hτ'
      refine ⟨w, hw, ?_⟩
      have h2 := lengthParam_variationOnFromTo hL hw
      rw [hwτ] at h2
      exact h2.symm
    · rintro ⟨w, hw, rfl⟩
      refine ⟨variationOnFromTo (d.pt ∘ π) (Icc a b) a w, ?_,
        lengthParam_variationOnFromTo hL hw⟩
      rw [← himage]
      exact ⟨w, hw, rfl⟩

 

theorem aroundDist_le_weyl (ξ : ℝ) (f : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y)) (A : EuclideanAnnulus) (c : ℝ)
    (hfA : ∀ y ∈ A.toSet, f y = c) :
    aroundDist e A ≤ ENNReal.ofReal (Real.exp (ξ * c)) * aroundDist d A := by
  have hk0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  conv_rhs => unfold aroundDist
  simp only [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]
  refine le_iInf fun π => le_iInf fun a => le_iInf fun b => le_iInf fun hπ =>
    le_iInf fun htr => le_iInf fun hsep => ?_
  by_cases hfin : d.len π a b = ⊤
  · rw [hfin, ENNReal.mul_top hk0]
    exact le_top
  obtain ⟨Q, T, hlen, hT, hQc, hQu, himg⟩ := exists_unit_reparam d hπ hfin
  have hQA : ∀ t ∈ Icc 0 T, Q t ∈ A.toSet := by
    intro t ht
    have : Q t ∈ π '' Icc a b := himg ▸ ⟨t, ht, rfl⟩
    obtain ⟨w, hw, hwt⟩ := this
    rw [← hwt]
    exact htr w hw
  obtain ⟨hQe, hlenQ⟩ := isCurve_len_le_of_weyl ξ f d e he hT hQc hQu
    (fun t ht => hfA _ (hQA t ht))
  have hsepQ : Disconnects (Q '' Icc 0 T) A.innerBoundary A.outerBoundary := by
    rw [himg]
    exact hsep
  calc aroundDist e A ≤ e.len Q 0 T := by
        unfold aroundDist
        exact iInf_le_of_le Q (iInf_le_of_le 0 (iInf_le_of_le T (iInf_le_of_le hQe
          (iInf_le_of_le hQA (iInf_le_of_le hsepQ le_rfl)))))
    _ ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal T := hlenQ
    _ = ENNReal.ofReal (Real.exp (ξ * c)) * d.len π a b := by rw [hlen]

 

theorem acrossDist_le_weyl (ξ : ℝ) (f : C(ℂ, ℝ)) (d e : LSCMetric)
    (he : ∀ x y : ℂ, e (x, y) = weylScale ξ f d (x, y))
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (A : EuclideanAnnulus)
    (hfA : ∀ y : ℂ, A.innerRadius ≤ dist y A.center → dist y A.center ≤ A.outerRadius →
      f y = 0) :
    acrossDist d A ≤ acrossDist e A := by
  have hA : A.innerRadius ≤ A.outerRadius := A.2.2.le
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  rw [he]
  unfold weylScale
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
    le_iInf fun h0 => le_iInf fun h1 => ?_
  have hPc : ContinuousOn P (Icc 0 L) := hcont P 0 L hP
  have hfc : ContinuousOn (fun t => dist (P t) A.center) (Icc 0 L) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hx' : dist (P 0) A.center = A.innerRadius := by
    rw [h0]
    exact Metric.mem_sphere.mp hx
  have hy' : dist (P L) A.center = A.outerRadius := by
    rw [h1]
    exact Metric.mem_sphere.mp hy
  obtain ⟨σ, τ, h0σ, hστ, hτL, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hfc hA hx'.le hy'.ge
  have hσL : σ ∈ Icc 0 L := ⟨h0σ, hστ.trans hτL⟩
  have hτL' : τ ∈ Icc 0 L := ⟨h0σ.trans hστ, hτL⟩
  
  have hcross : acrossDist d A ≤ d (P σ, P τ) := by
    refine iInf₂_le_of_le (P σ) ?_ (iInf₂_le (P τ) ?_)
    · exact Metric.mem_sphere.mpr hσ
    · exact Metric.mem_sphere.mpr hτ
  have hdist : d (P σ, P τ) ≤ ENNReal.ofReal (τ - σ) := by
    have h := hu hσL hτL'
    rw [inter_eq_right.mpr (Icc_subset_Icc hσL.1 hτL'.2), NNReal.coe_one, one_mul] at h
    calc d (P σ, P τ) = edist ((d.pt ∘ P) σ) ((d.pt ∘ P) τ) := rfl
      _ ≤ eVariationOn (d.pt ∘ P) (Icc σ τ) :=
          eVariationOn.edist_le _ (left_mem_Icc.mpr hστ) (right_mem_Icc.mpr hστ)
      _ = ENNReal.ofReal (τ - σ) := h
  
  have hone : EqOn (fun t => ENNReal.ofReal (Real.exp (ξ * f (P t)))) (fun _ => 1) (Icc σ τ) := by
    intro t ht
    have hb := hbetween t ht
    simp only [hfA (P t) hb.1 hb.2, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  have hint : ENNReal.ofReal (τ - σ) ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
    calc ENNReal.ofReal (τ - σ) = ∫⁻ t in Icc σ τ, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
          rw [setLIntegral_congr_fun measurableSet_Icc hone, setLIntegral_const, Real.volume_Icc,
            one_mul]
      _ ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
          lintegral_mono_set (Icc_subset_Icc h0σ hτL)
  exact hcross.trans (hdist.trans hint)



end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
