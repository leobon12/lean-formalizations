import SupercriticalLQGUniqueness.B2.PfeAxioms.S2SampleIdentify
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1LocalBounds
import HigherDimLQGMetric.Metric.Reparam

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.MetricGeometry

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem exists_unitSpeed_of_weylScale_lt (Φ : LSCMetric) (ξ : ℝ) (g : C(ℂ, ℝ))
    {x y : ℂ} {T : ℝ≥0∞} (h : weylScale ξ g Φ (x, y) < T) :
    ∃ (P : ℝ → ℂ) (L : ℝ), Φ.IsCurve P 0 L ∧ HasUnitSpeedOn (Φ.pt ∘ P) (Icc 0 L) ∧
      P 0 = x ∧ P L = y ∧ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t))) < T := by
  unfold weylScale at h
  simp only [iInf_lt_iff] at h
  obtain ⟨P, L, hP, hu, h0, h1, hint⟩ := h
  exact ⟨P, L, hP, hu, h0, h1, hint⟩

 
theorem exists_bound_along (Φ : LSCMetric) (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (g : C(ℂ, ℝ)) {P : ℝ → ℂ} {a b : ℝ} (hP : Φ.IsCurve P a b) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, g (P t) ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn
    (g.continuous.comp_continuousOn (continuousOn_of_isCurve_forget Φ hforget hP))).bddAbove
  exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩

 
theorem isLengthSpace_weylScale (Φ : LSCMetric) (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ)) (E : LSCMetric)
    (hE : ∀ p, E p = weylScale ξ g Φ p) : E.IsLengthSpace := by
  intro x y hxy ε hε
  have hlt : weylScale ξ g Φ (x, y) < E (x, y) + ENNReal.ofReal ε := by
    rw [← hE]; exact ENNReal.lt_add_right hxy.ne (ENNReal.ofReal_pos.2 hε).ne'
  obtain ⟨P, L, hP, hu, h0, h1, hint⟩ := exists_unitSpeed_of_weylScale_lt Φ ξ g hlt
  obtain ⟨M, hM⟩ := exists_bound_along Φ hforget g hP
  obtain ⟨hEc, -⟩ := PfeWeyl.weyl_isCurve_len_le ξ hξ g Φ E (fun u v => hE (u, v)) hP.1 hP.2
    hu hM
  refine ⟨P, 0, L, hEc, h0, h1, ?_⟩
  have hwc : ContinuousOn (fun t => Real.exp (ξ * g (P t))) (Icc 0 L) :=
    (Real.continuous_exp.comp (continuous_const.mul g.continuous)).comp_continuousOn
      (continuousOn_of_isCurve_forget Φ hforget hP)
  rw [len_eq_weylWL_of_eqOn Φ E ξ g g hforget hE hP (fun _ _ => rfl)]
  unfold weylWL
  rw [HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn (w := weylWt Φ ξ g) hP.1 hu hwc]
  exact hint.le

 
theorem weylWL_chain (Φ E : LSCMetric) (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (g f : C(ℂ, ℝ)) (hE : ∀ p, E p = weylScale ξ g Φ p)
    {P : ℝ → ℂ} {a b : ℝ} (hPΦ : Φ.IsCurve P a b) :
    weylWL E ξ f P a b = weylWL Φ ξ (f + g) P a b := by
  have hab := hPΦ.1
  set Q : ℝ → Φ.Space := Φ.pt ∘ P with hQ
  have hQc : ContinuousOn Q (Icc a b) := hPΦ.2
  have hlowb : ∀ h : C(ℂ, ℝ), ∃ m : ℝ, 0 < m ∧
      ∀ s ∈ Icc a b, m ≤ Real.exp (ξ * h (P s)) := by
    intro h
    obtain ⟨M, hM⟩ := exists_bound_along Φ hforget (-h) hPΦ
    refine ⟨Real.exp (ξ * -M), Real.exp_pos _, fun s hs => Real.exp_le_exp.2 ?_⟩
    have h1 := hM s hs
    simp only [ContinuousMap.neg_apply] at h1
    nlinarith
  by_cases hL : curveLength Q a b = ⊤
  · obtain ⟨m1, hm1, hb1⟩ := hlowb (f + g)
    obtain ⟨m2, hm2, hb2⟩ := hlowb g
    obtain ⟨m3, hm3, hb3⟩ := hlowb f
    have hR : weylWL Φ ξ (f + g) P a b = ⊤ :=
      HigherDimLQGMetric.weightedLength_eq_top hm1 hab (fun s hs => hb1 s hs) hL
    have hEL : curveLength (E.pt ∘ P) a b = ⊤ := by
      have h1 : E.len P a b = weylWL Φ ξ g P a b :=
        len_eq_weylWL_of_eqOn Φ E ξ g g hforget hE hPΦ (fun _ _ => rfl)
      have h2 : weylWL Φ ξ g P a b = ⊤ :=
        HigherDimLQGMetric.weightedLength_eq_top hm2 hab (fun s hs => hb2 s hs) hL
      rw [← E.len_eq_curveLength, h1, h2]
    have hLft : weylWL E ξ f P a b = ⊤ :=
      HigherDimLQGMetric.weightedLength_eq_top hm3 hab (fun s hs => hb3 s hs) hEL
    rw [hLft, hR]
  · obtain ⟨hu, hcP, -, -, -⟩ :=
      HigherDimLQGMetric.lengthParam_props hab hQc hL (mapsTo_univ Q _)
    have hRHS0 := HigherDimLQGMetric.weightedLength_eq_lengthParam (w := weylWt Φ ξ (f + g))
      hab hQc hL
    have hσc : ContinuousOn (variationOnFromTo Q (Icc a b) a) (Icc a b) :=
      HigherDimLQGMetric.continuousOn_variationOnFromTo hab hQc hL
    have hbv : BoundedVariationOn Q (Icc a b) := hL
    have hσm : MonotoneOn (variationOnFromTo Q (Icc a b) a) (Icc a b) :=
      variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn ⟨le_rfl, hab⟩
    have hσa : variationOnFromTo Q (Icc a b) a a = 0 := variationOnFromTo.self _ _ _
    have hσb : variationOnFromTo Q (Icc a b) a b = (curveLength Q a b).toReal := by
      rw [variationOnFromTo.eq_of_le _ _ hab, inter_self]; rfl
    have hrep : ∀ t ∈ Icc a b,
        lengthParam Q a b (variationOnFromTo Q (Icc a b) a t) = Q t :=
      fun t ht => lengthParam_variationOnFromTo hL ht
    have hlenL := curveLength_lengthParam hab hQc hL
    generalize hRdef : lengthParam Q a b = Rs at hu hcP hRHS0 hrep hlenL
    generalize hℓdef : (curveLength Q a b).toReal = ℓ at hu hcP hRHS0 hσb hlenL
    have hℓ0 : 0 ≤ ℓ := by rw [← hℓdef]; exact ENNReal.toReal_nonneg
    obtain ⟨R, rfl⟩ : ∃ R : ℝ → ℂ, Φ.pt ∘ R = Rs := ⟨Rs, rfl⟩
    have hRΦ : Φ.IsCurve R 0 ℓ := ⟨hℓ0, hcP⟩
    have hRc : ContinuousOn R (Icc 0 ℓ) :=
      continuousOn_of_isCurve_forget Φ hforget hRΦ
    have hexpc : ∀ h : C(ℂ, ℝ),
        ContinuousOn (fun t => Real.exp (ξ * h (R t))) (Icc 0 ℓ) :=
      fun h => (Real.continuous_exp.comp (continuous_const.mul h.continuous)).comp_continuousOn hRc
    have hRHS : weylWL Φ ξ (f + g) P a b =
        ∫⁻ τ in Icc 0 ℓ, ENNReal.ofReal (Real.exp (ξ * (f + g) (R τ))) := by
      unfold weylWL
      rw [hRHS0, HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hℓ0 hu (hexpc (f + g))]
      rfl
    have hLHS : weylWL E ξ f P a b =
        HigherDimLQGMetric.weightedLength (weylWt E ξ f) (E.pt ∘ R) 0 ℓ := by
      have hcomp := HigherDimLQGMetric.weightedLength_comp_monotoneOn
        (w := weylWt E ξ f) (P := E.pt ∘ R) hab hσc hσm
      rw [hσa, hσb] at hcomp
      rw [← hcomp]
      unfold weylWL
      refine HigherDimLQGMetric.weightedLength_congr fun t ht => ?_
      exact (congrArg (fun z : ℂ => E.pt z) (hrep t ht)).symm
    have hlen : ∀ u t, 0 ≤ u → u ≤ t → t ≤ ℓ → curveLength (E.pt ∘ R) u t =
        ∫⁻ τ in Icc u t, ENNReal.ofReal (Real.exp (ξ * g (R τ))) := by
      intro u t hu0 hut htℓ
      have hsub : Φ.IsCurve R u t := isCurve_sub hRΦ hu0 hut htℓ
      rw [← E.len_eq_curveLength, len_eq_weylWL_of_eqOn Φ E ξ g g hforget hE hsub
        (fun _ _ => rfl)]
      unfold weylWL
      exact HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hut
        (hasUnitSpeedOn_mono_Icc hu hu0 htℓ)
        ((hexpc g).mono (Icc_subset_Icc hu0 htℓ))
    have hfin : curveLength (E.pt ∘ R) 0 ℓ ≠ ⊤ := by
      rw [← E.len_eq_curveLength, len_eq_weylWL_of_eqOn Φ E ξ g g hforget hE hRΦ
        (fun _ _ => rfl)]
      obtain ⟨M, hM⟩ := exists_bound_along Φ hforget g hRΦ
      refine HigherDimLQGMetric.weightedLength_ne_top (M := Real.exp (ξ * M))
        (fun s hs => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hM s hs) hξ)) ?_
      rw [hlenL]
      exact hL
    rw [hLHS, HigherDimLQGMetric.weightedLength_eq_lintegral_of_curveLength hℓ0 hlen hfin
      (hexpc f), hRHS]
    refine setLIntegral_congr_fun measurableSet_Icc fun τ _ => ?_
    show ENNReal.ofReal (Real.exp (ξ * f (R τ))) * ENNReal.ofReal (Real.exp (ξ * g (R τ))) =
      ENNReal.ofReal (Real.exp (ξ * (f + g) (R τ)))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ContinuousMap.add_apply,
      mul_add]

theorem weylScale_le_of_unitSpeed (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ)) {P : ℝ → ℂ} {L : ℝ}
    (hP : D.IsCurve P 0 L) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) :
    weylScale ξ f D (P 0, P L) ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  unfold weylScale
  exact iInf_le_of_le P <| iInf_le_of_le L <| iInf_le_of_le hP <| iInf_le_of_le hu <|
    iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl

theorem le_weylScale_of_forall (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ)) (p : ℂ × ℂ) {c : ℝ≥0∞}
    (h : ∀ (P : ℝ → ℂ) (L : ℝ), D.IsCurve P 0 L → HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) →
      P 0 = p.1 → P L = p.2 → c ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) :
    c ≤ weylScale ξ f D p := by
  unfold weylScale
  exact le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
    le_iInf fun h0 => le_iInf fun h1 => h P L hP hu h0 h1

 

theorem weylScale_comp (Φ E : LSCMetric) (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ)) (hE : ∀ p, E p = weylScale ξ g Φ p)
    (f : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    weylScale ξ f E p = weylScale ξ (f + g) Φ p := by
  have hEforget : Continuous (PfeWeyl.euclidForget E) :=
    Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl Φ E ξ hξ g hforget hE
  apply le_antisymm
  · apply le_weylScale_of_forall
    intro R L hR hu h0 h1
    obtain ⟨M, hM⟩ := exists_bound_along Φ hforget g hR
    obtain ⟨hRE, -⟩ := PfeWeyl.weyl_isCurve_len_le ξ hξ g Φ E (fun u v => hE (u, v)) hR.1 hR.2
      hu hM
    have h2 := weylScale_le_weylWL E ξ f hEforget hRE
    rw [h0, h1] at h2
    have hp : p = (p.1, p.2) := rfl
    rw [hp]
    refine h2.trans (le_of_eq ?_)
    have hwc : ContinuousOn (fun t => Real.exp (ξ * (f + g) (R t))) (Icc 0 L) :=
      (Real.continuous_exp.comp (continuous_const.mul (f + g).continuous)).comp_continuousOn
        (continuousOn_of_isCurve_forget Φ hforget hR)
    rw [weylWL_chain Φ E hforget ξ hξ g f hE hR]
    unfold weylWL
    exact HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn (w := weylWt Φ ξ (f + g)) hR.1 hu
      hwc
  · apply le_weylScale_of_forall
    intro Q L hQ hu h0 h1
    have hQΦ : Φ.IsCurve Q 0 L :=
      Uniqueness.Toolkit.WeylShift.curve_back_all_continuous Φ E ξ hξ g hforget hE hQ
    have h2 := weylScale_le_weylWL Φ ξ (f + g) hforget hQΦ
    rw [h0, h1] at h2
    have hp : p = (p.1, p.2) := rfl
    rw [hp]
    refine h2.trans (le_of_eq ?_)
    have hwc : ContinuousOn (fun t => Real.exp (ξ * f (Q t))) (Icc 0 L) :=
      (Real.continuous_exp.comp (continuous_const.mul f.continuous)).comp_continuousOn
        (continuousOn_of_isCurve_forget Φ hforget hQΦ)
    rw [← weylWL_chain Φ E hforget ξ hξ g f hE hQΦ]
    unfold weylWL
    exact HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn (w := weylWt E ξ f) hQ.1 hu hwc

end SupercriticalLQGUniqueness.B2.PfeAxioms
