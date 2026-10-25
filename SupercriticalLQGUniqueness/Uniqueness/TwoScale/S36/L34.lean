import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.HTranslate
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal.OneAnnulus




 










set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC addConst restrictTo)

 
theorem attainedEvent_eq_inter (D D' : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ)) (Cm Cp : ℝ) :
    TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cm Cp =
      {g : DistC | ∃ c : ℝ, IsCircleAverage g r z c} ∩
        {g : DistC | TwoScale.S36Events.EventClause1 (D g) z r q θ} ∩
        {g : DistC | TwoScale.S36Events.EventClause3 (D g) z r q a} ∩
        {g : DistC | E4Prop (D g) z r a K} ∩
        {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
          E2Prop (D g) ξ Q z r q a θ Cm Cp c} ∩
        {g : DistC | ∀ c : ℝ, IsCircleAverage g r z c →
          E5Lit (D g) (D' g) ξ Q z r q a C θ Cm Cp c} := by
  ext g
  constructor
  · rintro ⟨c, hc, hA⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := (attained_iff (D g) (D' g) ξ Q z r q a K C θ Cm Cp c).mp hA
    refine ⟨⟨⟨⟨⟨⟨c, hc⟩, h1⟩, h3⟩, h4⟩, fun c' hc' => ?_⟩, fun c' hc' => ?_⟩
    · rw [← isCircleAverage_unique hc hc']
      exact h2
    · rw [← isCircleAverage_unique hc hc']
      exact h5
  · rintro ⟨⟨⟨⟨⟨⟨c, hc⟩, h1⟩, h3⟩, h4⟩, h2⟩, h5⟩
    exact ⟨c, hc, (attained_iff (D g) (D' g) ξ Q z r q a K C θ Cm Cp c).mpr
      ⟨h1, h2 c hc, h3, h4, h5 c hc⟩⟩

 
theorem hAt_of_not_E5 (d e : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ))
    (Cm Cp c : ℝ) (h : ¬ E5Lit d e ξ Q z r q a C θ Cm Cp c) :
    HAt d e ξ Q z r (aWin a) C θ c := by
  unfold E5Lit at h
  push Not at h
  obtain ⟨u, v, hu, hv, -, -, ⟨P, s, t, hgeo, htr, hdiam, hN, hLu, hLv⟩, hlt⟩ := h
  exact ⟨u, v, hu, hv, hlt.le, P, s, t, hgeo, htr, hdiam, hN,
    (endpointLoopAt_iff d r a θ u v u).mp hLu, (endpointLoopAt_iff d r a θ u v v).mp hLv⟩

 


theorem attained_prob_of_clauses {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D') (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (Cm Cp p : ℝ)
    (hp : 0 ≤ p)
    (hE1 : P {ω | ¬ TwoScale.S36Events.EventClause1 (D (h ω)) z r q θ} ≤ ENNReal.ofReal (p / 4))
    (hE2 : P {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
      E2Prop (D (h ω)) (ξ : ℝ) Q z r q a θ Cm Cp c} ≤ ENNReal.ofReal (p / 4))
    (hE3 : P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a} ≤ ENNReal.ofReal (p / 4))
    (hE4 : P {ω | ¬ E4Prop (D (h ω)) z r a K} ≤ ENNReal.ofReal (p / 4))
    (hH : P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q r (aWin a) C θ (h ω)} ≤ ENNReal.ofReal p) :
    ENNReal.ofReal (1 - 2 * p) ≤
      P (h ⁻¹' TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q z r q a K C θ Cm Cp) := by
  set E := TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q z r q a K C θ Cm Cp with hEdef
  have hCA : P {ω | ¬ ∃ c : ℝ, IsCircleAverage (h ω) r z c} = 0 := by
    have := ae_exists_circleAverage hh.1 r z
    rwa [ae_iff] at this
  have hE5 : P {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
      E5Lit (D (h ω)) (D' (h ω)) (ξ : ℝ) Q z r q a C θ Cm Cp c} ≤ ENNReal.ofReal p := by
    refine (measure_mono ?_).trans ((prob_hAt_le P h hh ξ Q D D' hD hD' z r (aWin a) C θ).trans hH)
    intro ω hω
    have hω' : ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
        E5Lit (D (h ω)) (D' (h ω)) (ξ : ℝ) Q z r q a C θ Cm Cp c := hω
    push Not at hω'
    obtain ⟨c, hc, hn⟩ := hω'
    exact ⟨c, hc, hAt_of_not_E5 _ _ _ _ _ _ _ _ _ _ _ _ c hn⟩
  
  have hcover : h ⁻¹' Eᶜ ⊆ {ω | ¬ ∃ c : ℝ, IsCircleAverage (h ω) r z c} ∪
      {ω | ¬ TwoScale.S36Events.EventClause1 (D (h ω)) z r q θ} ∪
      {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a} ∪
      {ω | ¬ E4Prop (D (h ω)) z r a K} ∪
      {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
        E2Prop (D (h ω)) (ξ : ℝ) Q z r q a θ Cm Cp c} ∪
      {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
        E5Lit (D (h ω)) (D' (h ω)) (ξ : ℝ) Q z r q a C θ Cm Cp c} := by
    intro ω hω
    have hω' : h ω ∉ E := hω
    rw [hEdef, attainedEvent_eq_inter] at hω'
    simp only [mem_inter_iff, mem_ofPred_eq, not_and_or] at hω'
    simp only [mem_union, mem_ofPred_eq]
    tauto
  have hcompl : P (h ⁻¹' Eᶜ) ≤ ENNReal.ofReal (2 * p) := by
    refine (measure_mono hcover).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) hE5).trans ?_
    refine (add_le_add (add_le_add (measure_union_le _ _) hE2) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (measure_union_le _ _) hE4) le_rfl)
      le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add (measure_union_le _ _) hE3) le_rfl)
      le_rfl) le_rfl).trans ?_
    rw [hCA, zero_add]
    have hp4 : 0 ≤ p / 4 := by positivity
    refine (add_le_add (add_le_add (add_le_add (add_le_add hE1 le_rfl) le_rfl) le_rfl)
      le_rfl).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add hp4 hp4, ← ENNReal.ofReal_add (by positivity) hp4,
      ← ENNReal.ofReal_add (by positivity) hp4, ← ENNReal.ofReal_add (by positivity) hp]
    congr 1
    ring
  have hnull : NullMeasurableSet (h ⁻¹' E) P :=
    (AttainedEvent_um D D' hD.measurable hD'.measurable (ξ : ℝ) Q z r q a K C θ Cm Cp)
      |>.nullMeasurableSet_preimage hh.1.measurable.aemeasurable
  have hsum : P (h ⁻¹' E) + P (h ⁻¹' E)ᶜ = 1 := by
    rw [measure_add_measure_compl₀ hnull, measure_univ]
  have hpre : (h ⁻¹' E)ᶜ = h ⁻¹' Eᶜ := rfl
  rw [hpre] at hsum
  calc
    ENNReal.ofReal (1 - 2 * p) ≤ 1 - ENNReal.ofReal (2 * p) := by
      rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    _ ≤ 1 - P (h ⁻¹' Eᶜ) := tsub_le_tsub_left hcompl 1
    _ = P (h ⁻¹' E) := by
      rw [← hsum, ENNReal.add_sub_cancel_right (measure_ne_top P _)]

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
