import SupercriticalLQGUniqueness.B2.PfeWeyl.W1LocalBounds
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaChain

 


















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
def halfAnnulus (a : ℂ) (ρ : ℝ) (hρ : 0 < ρ) : EuclideanAnnulus :=
  ⟨(a, (ρ / 2, ρ)), half_pos hρ, half_lt_self hρ⟩

 
theorem weyl_segment_recovery
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (W : ℕ → LSCMetric)
    (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    {θ : ℝ} (hθ : 0 < θ) {a b : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (M' : ℝ)
    (hfa : ∀ x ∈ Metric.closedBall a ρ, f x ≤ M')
    {η : ℝ} (hη : 0 < η)
    (hab : D (a, b) + ENNReal.ofReal η < acrossDist D (halfAnnulus a ρ hρ)) :
    ∃ x y : ℕ → ℂ, Tendsto x atTop (𝓝 a) ∧ Tendsto y atTop (𝓝 b) ∧
      ∀ᶠ n in atTop, ∃ T : PfeAxioms.BufferedMetricTrace (W n) (univ : Set ℂ),
        T.path T.start = x n ∧ T.path T.stop = y n ∧
        T.cost ≤ ENNReal.ofReal (Real.exp (ξ * (M' + θ))) *
          (D (a, b) + ENNReal.ofReal η) := by
  set A := halfAnnulus a ρ hρ with hAdef
  have hAc : A.center = a := rfl
  have hAin : A.innerRadius = ρ / 2 := rfl
  have hAout : A.outerRadius = ρ := rfl
  have hDfin : D (a, b) < ⊤ :=
    lt_of_le_of_lt le_self_add (hab.trans_le le_top)
  obtain ⟨p, hp, hGp⟩ := (LSCMetric.tendsto_iff.1 hG).2 (a, b)
  have hx : Tendsto (fun n => (p n).1) atTop (𝓝 a) := (continuous_fst.tendsto _).comp hp
  have hy : Tendsto (fun n => (p n).2) atTop (𝓝 b) := (continuous_snd.tendsto _).comp hp
  refine ⟨fun n => (p n).1, fun n => (p n).2, hx, hy, ?_⟩
  have hη2 : 0 < η / 2 := half_pos hη
  have hhalf : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hη2.le hη2.le]
    ring_nf
  have h1 : ∀ᶠ n in atTop, G n (p n) < D (a, b) + ENNReal.ofReal (η / 2) :=
    (tendsto_order.1 hGp).2 _
      (ENNReal.lt_add_right hDfin.ne (ENNReal.ofReal_pos.2 hη2).ne')
  have h2 := eventually_lt_acrossDist hG A hab
  have h3 : ∀ᶠ n in atTop, (p n).1 ∈ Metric.ball a (ρ / 2) :=
    hx.eventually (Metric.ball_mem_nhds a (half_pos hρ))
  have h4 := hfn (Metric.closedBall a ρ) (isCompact_closedBall a ρ) θ hθ
  filter_upwards [h1, h2, h3, h4] with n hn1 hn2 hn3 hn4
  have hfin : G n ((p n).1, (p n).2) < ⊤ := by
    rw [Prod.mk.eta]
    exact hn1.trans_le le_top
  obtain ⟨Q, L, hQ, hu, hQ0, hQL, hlen⟩ :=
    exists_near_min_ordinary_curve (G n) (hGlen n) (p n).1 (p n).2 hfin hη2
  rw [Prod.mk.eta] at hlen
  have hlenη : (G n).len Q 0 L < D (a, b) + ENNReal.ofReal η := by
    refine hlen.trans ?_
    calc G n (p n) + ENNReal.ofReal (η / 2)
        < D (a, b) + ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hn1
      _ = D (a, b) + ENNReal.ofReal η := by rw [add_assoc, hhalf]
  have hQc := continuousOn_of_isCurve_of_forget _ (hGforget n) hQ
  have hQa : dist (Q 0) A.center ≤ A.innerRadius := by
    rw [hQ0, hAc, hAin]
    exact (Metric.mem_ball.1 hn3).le
  have hball := curve_mem_ball_of_len_lt_acrossDist (G n) A hQc hQa (hlenη.trans hn2)
  have hfield : ∀ t ∈ Icc 0 L, fn n (Q t) ≤ M' + θ := by
    intro t ht
    have hQt : Q t ∈ Metric.closedBall a ρ := by
      have := hball t ht
      rw [hAc, hAout] at this
      exact Metric.ball_subset_closedBall this
    have := (abs_sub_lt_iff.1 (hn4 (Q t) hQt)).1
    linarith [hfa (Q t) hQt]
  obtain ⟨hWc, hWlen⟩ :=
    weyl_isCurve_len_le ξ hξ (fn n) (G n) (W n) (hW n) hQ.1 hQ.2 hu hfield
  refine ⟨⟨Q, 0, L, hWc, fun _ _ => mem_univ _⟩, hQ0, hQL, ?_⟩
  change (W n).len Q 0 L ≤ _
  refine hWlen.trans ?_
  rw [← len_eq_ofReal_of_unitSpeed (G n) hQ.1 hu]
  gcongr

end SupercriticalLQGUniqueness.B2.PfeWeyl
