import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleTools
import SupercriticalLQGUniqueness.B2.PfeWeyl.CircleLiminf

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open PfeAxioms

 
theorem weyl_circle_segment
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (W : ℕ → LSCMetric)
    (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    {θ : ℝ} (hθ : 0 < θ) {v : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (M' : ℝ)
    (hfv : ∀ x ∈ Metric.closedBall v ρ, f x ≤ M')
    {C C' : Set ℂ}
    (hcirc : Tendsto (fun n => B2.Iface.setDistance (G n) C C') atTop
      (𝓝 (B2.Iface.setDistance D C C')))
    {B : ℝ≥0∞} (hCB : B2.Iface.setDistance D C C' < B)
    (hBA : B < acrossDist D (halfAnnulus v ρ hρ))
    (hanchor : C ⊆ Metric.closedBall v (ρ / 2) ∨ C' ⊆ Metric.closedBall v (ρ / 2)) :
    ∀ᶠ n in atTop, ∃ T : BufferedMetricTrace (W n) (univ : Set ℂ),
      T.path T.start ∈ C ∧ T.path T.stop ∈ C' ∧
      T.cost ≤ ENNReal.ofReal (Real.exp (ξ * (M' + θ))) * B := by
  set A := halfAnnulus v ρ hρ with hAdef
  have hAc : A.center = v := rfl
  have hAin : A.innerRadius = ρ / 2 := rfl
  have hAout : A.outerRadius = ρ := rfl
  obtain ⟨B₁, hB₁a, hB₁b⟩ := exists_between hCB
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hB₁b
  have hη : (0 : ℝ) < r := by exact_mod_cast hr0
  have h1 : ∀ᶠ n in atTop, B2.Iface.setDistance (G n) C C' < B₁ :=
    (tendsto_order.1 hcirc).2 B₁ hB₁a
  have h2 := eventually_lt_acrossDist hG A hBA
  have h3 := hfn (Metric.closedBall v ρ) (isCompact_closedBall v ρ) θ hθ
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  simp only [B2.Iface.setDistance, iInf_lt_iff] at hn1
  obtain ⟨a, ha, b, hb, hab⟩ := hn1
  obtain ⟨Q, L, hQ, hu, hQ0, hQL, hlen⟩ :=
    exists_near_min_ordinary_curve (G n) (hGlen n) a b (hab.trans_le le_top) hη
  have hlenB : (G n).len Q 0 L < B := by
    refine hlen.trans ?_
    rw [ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.add_lt_add_right ENNReal.coe_ne_top hab).trans hr
  have hQc := continuousOn_of_isCurve_of_forget _ (hGforget n) hQ
  have hball : ∀ t ∈ Icc 0 L, Q t ∈ Metric.ball v ρ := by
    rcases hanchor with hC | hC'
    · have hQa : dist (Q 0) A.center ≤ A.innerRadius := by
        rw [hQ0, hAc, hAin]
        exact Metric.mem_closedBall.1 (hC ha)
      have := curve_mem_ball_of_len_lt_acrossDist (G n) A hQc hQa (hlenB.trans hn2)
      rwa [hAc, hAout] at this
    · have hQb : dist (Q L) A.center ≤ A.innerRadius := by
        rw [hQL, hAc, hAin]
        exact Metric.mem_closedBall.1 (hC' hb)
      have := curve_mem_ball_of_len_lt_acrossDist_rev (G n) A hQc hQb (hlenB.trans hn2)
      rwa [hAc, hAout] at this
  have hfield : ∀ t ∈ Icc 0 L, fn n (Q t) ≤ M' + θ := by
    intro t ht
    have hQt : Q t ∈ Metric.closedBall v ρ := Metric.ball_subset_closedBall (hball t ht)
    have := (abs_sub_lt_iff.1 (hn3 (Q t) hQt)).1
    linarith [hfv (Q t) hQt]
  obtain ⟨hWc, hWlen⟩ :=
    weyl_isCurve_len_le ξ hξ (fn n) (G n) (W n) (hW n) hQ.1 hQ.2 hu hfield
  refine ⟨⟨Q, 0, L, hWc, fun _ _ => mem_univ _⟩, ?_, ?_, ?_⟩
  · change Q 0 ∈ C
    rw [hQ0]
    exact ha
  · change Q L ∈ C'
    rw [hQL]
    exact hb
  · change (W n).len Q 0 L ≤ _
    refine hWlen.trans ?_
    rw [← len_eq_ofReal_of_unitSpeed (G n) hQ.1 hu]
    gcongr

end SupercriticalLQGUniqueness.B2.PfeWeyl
