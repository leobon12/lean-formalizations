import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.UnitParam
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.CarrierHighProb




 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)
open LQGMetric.MetricGeometry

 

theorem lt_dist_of_boundary_middle {z x y : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : δ < 1 / 4)
    (hx : x ∈ TwoScale.S36Events.eventMiddle z r) (hy : y ∈ TwoScale.S36Events.eventBoundary z r) :
    δ * r < dist y x := by
  have hx1 : dist x z < 3 * r / 2 := Metric.mem_ball.mp hx.1
  have hx2 : 3 * r / 4 < dist x z := lt_of_not_ge fun h => hx.2 (Metric.mem_closedBall.mpr h)
  have hδr : δ * r < r / 4 := by nlinarith
  rcases hy with hy | hy
  · have hyz : dist y z = r / 2 := Metric.mem_sphere.mp hy
    have htri := dist_triangle x y z
    rw [dist_comm x y] at htri
    linarith
  · have hyz : dist y z = 2 * r := Metric.mem_sphere.mp hy
    have htri := dist_triangle y x z
    linarith

 

theorem eventClause1_of_carrierRatio {Ω : Type} (h : Ω → DistC) (ω : Ω)
    (D : DistC → LSCMetric) (θ q₀ : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (hCR : TwoScale.Carrier.carrierRatioProperty h ω D θ q₀ r z)
    (q : Ioo (0 : ℝ) (1 / 100)) (hq : (q : ℝ) ≤ q₀) :
    TwoScale.S36Events.EventClause1 (D (h ω)) z r q θ := by
  intro P s t hP δ hδ hδq x hx hhit
  have hr : 0 < (r : ℝ) := r.2
  have hδ1 : δ < 1 / 100 := lt_of_le_of_lt hδq q.2.2
  obtain ⟨Pth, T, hT0, hcurve, hmaps, hgeo, hP0, hPT, hpre⟩ :=
    exists_unit_internal_param (D (h ω)) z r hP
  obtain ⟨-, -, -, -, hbs, hbt, -, -⟩ := hP
  obtain ⟨w, hw, hwx⟩ := hhit
  obtain ⟨σ, hσ, hσw⟩ := hpre w hw
  have hwx' : dist (P w) x < δ * r := Metric.mem_ball.mp hwx
  have hx1 : dist x z < 3 * r / 2 := Metric.mem_ball.mp hx.1
  have hx2 : 3 * r / 4 < dist x z := lt_of_not_ge fun h' => hx.2 (Metric.mem_closedBall.mpr h')
  have hσ0 : 0 < σ := by
    rcases eq_or_lt_of_le hσ.1 with h0 | h0
    · exfalso
      rw [← h0, hP0] at hσw
      have hfar := lt_dist_of_boundary_middle (δ := δ) hr (by linarith) hx hbs
      rw [hσw] at hfar
      linarith
    · exact h0
  have hσT : σ < T := by
    rcases eq_or_lt_of_le hσ.2 with h0 | h0
    · exfalso
      rw [h0, hPT] at hσw
      have hfar := lt_dist_of_boundary_middle (δ := δ) hr (by linarith) hx hbt
      rw [hσw] at hfar
      linarith
    · exact h0
  have hend0 : dist (Pth 0) z = r / 2 ∨ dist (Pth 0) z = 2 * r := by
    rw [hP0]
    rcases hbs with hb | hb
    · exact Or.inl (Metric.mem_sphere.mp hb)
    · exact Or.inr (Metric.mem_sphere.mp hb)
  have hendT : dist (Pth T) z = r / 2 ∨ dist (Pth T) z = 2 * r := by
    rw [hPT]
    rcases hbt with hb | hb
    · exact Or.inl (Metric.mem_sphere.mp hb)
    · exact Or.inr (Metric.mem_sphere.mp hb)
  have hhit' : dist (Pth σ) x ≤ δ * r := by
    rw [hσw]
    exact hwx'.le
  have hratio := hCR δ hδ (hδq.trans hq) x hx2.le hx1.le hσ0 hσT hcurve hmaps hgeo hend0 hendT
    hhit'
  have hsqrt : δ < Real.sqrt δ := by
    rw [Real.lt_sqrt hδ.le]
    nlinarith
  refine ⟨⟨(x, (δ * r, Real.sqrt δ * r)), mul_pos hδ hr, mul_lt_mul_of_pos_right hsqrt hr⟩,
    rfl, rfl, rfl, ?_⟩
  exact hratio _ rfl rfl (by
    change Real.sqrt δ * r = δ ^ ((1 : ℝ) / 2) * r
    rw [Real.sqrt_eq_rpow])

 


theorem E1_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) :
    ∃ (θ : Ioi (0 : ℝ)) (q₀ : ℝ), 0 < q₀ ∧
      ∀ (q : Ioo (0 : ℝ) (1 / 100)), (q : ℝ) ≤ q₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        P {ω | ¬ TwoScale.S36Events.EventClause1 (D (h ω)) z r q θ} ≤ ENNReal.ofReal (p / 4) := by
  obtain ⟨M, C, θ, q₀, -, -, hθ, hq₀, -, hmain⟩ :=
    TwoScale.Carrier.exists_carrier_high_probability_ratio_f0 ξ Q D hD p hp
  refine ⟨⟨θ, hθ⟩, q₀, hq₀, ?_⟩
  intro q hq Ω _ P _ h hh z r
  obtain ⟨hbad, hgood⟩ := hmain P h hh hq₀ r r.2 z
  refine (measure_mono ?_).trans hbad
  intro ω hω hgω
  exact hω (eventClause1_of_carrierRatio h ω D θ q₀ z r (hgood ω hgω) q hq)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
