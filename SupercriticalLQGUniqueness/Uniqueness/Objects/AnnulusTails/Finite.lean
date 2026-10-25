import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tail
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 

theorem acr_le_curve_of_endpoint_order (D : LSCMetric) {P : ℝ → ℂ} {s t c d : ℝ} {v : ℂ}
    (hP : D.IsCurve P s t) (hcont : ContinuousOn P (Icc s t)) (hcd : c ≤ d)
    (hs : dist (P s) v ≤ c) (ht : d ≤ dist (P t) v) :
    Objects.CorrectedEvent.acr D v c d ≤ D.len P s t := by
  have hrad : ContinuousOn (fun u => dist (P u) v) (Icc s t) :=
    Continuous.comp_continuousOn (g := fun x : ℂ => dist x v) (by fun_prop) hcont
  obtain ⟨s', t', hss', hs't', ht't, hsc, htd, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hrad hcd hs ht
  have hP' : D.IsCurve P s' t' := ⟨hs't', hP.2.mono (Icc_subset_Icc hss' ht't)⟩
  have htrace' : P '' Icc s' t' ⊆ Objects.CorrectedEvent.cann v c d := by
    rintro x ⟨u, hu, rfl⟩
    exact hbetween u hu
  have hcost : Objects.CorrectedEvent.acr D v c d ≤ D.len P s' t' :=
    iInf_le_of_le P <| iInf_le_of_le s' <| iInf_le_of_le t' <|
      iInf_le_of_le hP' <| iInf_le_of_le htrace' <|
        iInf_le_of_le (mem_sphere.mpr hsc) <| iInf_le_of_le (mem_sphere.mpr htd) le_rfl
  exact hcost.trans (LQGMetric.MetricGeometry.curveLength_mono _ hss' ht't)

 


theorem acr_lt_top_of_across (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {y : ℂ} {a b : ℝ} (A : EuclideanAnnulus) (hc : A.center = y) (h1 : A.innerRadius ≤ a)
    (h2 : a ≤ b) (h3 : b ≤ A.outerRadius) (hX : acrossDist D A < ⊤) :
    Objects.CorrectedEvent.acr D y a b < ⊤ := by
  unfold acrossDist at hX
  simp only [iInf_lt_iff] at hX
  obtain ⟨x, hx, x', hx', hxx'⟩ := hX
  have hforget := BiLipschitz.Barrier.continuous_forget_of_barrier D hB hL
  obtain ⟨P, u, v, hP, hPu, hPv, hlen⟩ := hL x x' hxx' 1 one_pos
  have hcont : ContinuousOn P (Icc u v) := hforget.comp_continuousOn hP.2
  have hdu : dist (P u) y ≤ a := by
    rw [hPu, ← hc]
    have : dist x A.center = A.innerRadius := hx
    linarith
  have hdv : b ≤ dist (P v) y := by
    rw [hPv, ← hc]
    have : dist x' A.center = A.outerRadius := hx'
    linarith
  calc Objects.CorrectedEvent.acr D y a b ≤ D.len P u v := acr_le_curve_of_endpoint_order D hP hcont h2 hdu hdv
    _ ≤ D (x, x') + ENNReal.ofReal 1 := hlen
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hxx', ENNReal.ofReal_lt_top⟩

 
theorem ae_acrossDist_translate_lt_top (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (A : EuclideanAnnulus) (s : Ioi (0 : ℝ)) (y : ℂ) :
    ∀ᵐ ω ∂P, acrossDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate s s.2) y) < ⊤ := by
  have hnz := normalized_translate_sub_circleAvg hh y
  filter_upwards [TwoScale.S36.ae_acrossDist_dilate_lt_top ξ Q D hD P _ hnz A s,
    Positivity.Witnesses.ae_normalized_across_translate P h hh ξ Q D hD A y s] with ω hfin heq
  have hs : (0 : ℝ) < s := s.2
  set c₂ : ℝ := (s : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s y)) with hc₂
  have hc₂0 : 0 < c₂ := mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _)
  have hlhs : ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg
        (LQGMetric.addConst (translateDist y (h ω)) (-LQGMetric.circleAvg (h ω) 1 y)) s 0))) *
      acrossDist (D (LQGMetric.addConst (translateDist y (h ω))
        (-LQGMetric.circleAvg (h ω) 1 y))) (A.dilate s s.2) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  rw [heq] at hlhs
  by_contra hn
  rw [not_lt, top_le_iff] at hn
  rw [hn, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc₂0).ne'] at hlhs
  exact lt_irrefl _ hlhs

 

theorem ae_acr_lt_top (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : Ioi (0 : ℝ)) (y : ℂ) :
    ∀ᵐ ω ∂P, Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) < ⊤ := by
  have hs : (0 : ℝ) < s := s.2
  let A : EuclideanAnnulus := ⟨(0, (a / 2, 2 * b)), by positivity, by linarith⟩
  have hcp : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh.1
  filter_upwards [ae_acrossDist_translate_lt_top ξ Q D hD P h hh A s y,
    BiLipschitz.Barrier.ae_barrier hD hQ P h hh, hD.length P h hcp] with ω hfin hB hL
  refine acr_lt_top_of_across (D (h ω)) hB hL (Positivity.Witnesses.annulusTranslate (A.dilate s s.2) y)
    ?_ ?_ (by nlinarith) ?_ hfin
  · change (s : ℝ) • (0 : ℂ) + y = y
    simp
  · change (s : ℝ) * (a / 2) ≤ a * s
    nlinarith
  · change b * s ≤ (s : ℝ) * (2 * b)
    nlinarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
