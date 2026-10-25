import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Bad
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.CoverB
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeoCompactB




 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 
theorem not_G_of_coverB (d e : LSCMetric) (hB : BiLipschitz.Barrier.Barrier d) (hL : d.IsLengthSpace)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ)) (Cm Cp : ℝ) (C' κ : Ioi (0 : ℝ))
    (hCC : (C : ℝ) ≤ Cp)
    (hgap : (C : ℝ) + (K : ℝ) / ((K : ℝ) + 1) * (Cp - (C : ℝ)) < C')
    (hbilip : ∀ x y : ℂ, e (x, y) ≤ ENNReal.ofReal Cp * d (x, y))
    (b : Ioi (0 : ℝ)) {ε : ℝ} (hε0 : 0 < ε) (hεκ : ε ≤ (κ : ℝ) / 32)
    {J : ℕ} (hJ : 2 ≤ J) (hgc : GeoCompactEventB d J b)
    (hcov : ∀ x ∈ Metric.closedBall (0 : ℂ) (2 ^ (J + 1) * b), ∃ (c' : ℂ) (r : ℝ),
      (∃ (hr : 0 < r) (hCircle : ℝ), TwoScale.S36Events.Attained d e ξ Q c' ⟨r, hr⟩ q a K C θ Cm Cp hCircle) ∧
      ε ^ 2 * b ≤ r ∧ r ≤ ε * b ∧ x ∈ Metric.ball c' (r / 2)) :
    ¬ OptimalConstants.Ratios.G d e b κ C' := by
  rintro ⟨z, w, hz, hw, hRP, hG⟩
  obtain ⟨-, -, -, hpos, hfin⟩ := hRP
  have hb : 0 < (b : ℝ) := b.2
  have hκ0 : 0 < (κ : ℝ) := κ.2
  have hC'0 : 0 < (C' : ℝ) := C'.2
  have hlhs : 0 < ENNReal.ofReal (C' : ℝ) * d (z, w) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hC'0).ne' hpos.ne'
  
  have hsep : (κ : ℝ) * b ≤ dist z w := by
    by_contra hlt
    push Not at hlt
    have h0 : OptimalConstants.Ratios.setDist e (Metric.ball z ((κ : ℝ) * b)) (Metric.ball w ((κ : ℝ) * b)) = 0 := by
      refine le_antisymm ?_ bot_le
      calc OptimalConstants.Ratios.setDist e (Metric.ball z ((κ : ℝ) * b)) (Metric.ball w ((κ : ℝ) * b))
          ≤ e (z, z) := iInf₂_le_of_le z (Metric.mem_ball_self (by positivity))
            (iInf₂_le z (Metric.mem_ball.mpr hlt))
        _ = 0 := edist_self (e.pt z)
    rw [h0] at hG
    exact absurd hG (not_le.mpr hlhs)
  
  obtain ⟨P, hP, hgeo, hunit, hP0, hPT⟩ := exists_unit_geodesic d hB hL hfin
  set T := (d (z, w)).toReal with hTdef
  have hT : 0 < T := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hzb : ‖P 0‖ ≤ b := by rw [hP0]; simpa using hz
  have hwb : ‖P T‖ ≤ b := by rw [hPT]; simpa using hw
  have hstay := geodesic_stays_of_geoCompactEventB d hJ b hgc hP hgeo hunit hzb hwb
  have htrace : ∀ u ∈ Icc (0 : ℝ) T, P u ∈ Metric.closedBall (0 : ℂ) (2 ^ (J + 1) * b) :=
    fun u hu => mem_closedBall_zero_iff.mpr (hstay u hu).le
  have hα : 1 / 2 < (a : ℝ) := by linarith [a.2.1, q.2.2]
  obtain ⟨t₀, τ, steps, ht₀, ht₀τ, hτT, hne, hfrom, hend, hlast, hstart, hfinish⟩ :=
    TwoScale.Stopping.stopping_construction
      (Good := fun c r => ∃ (hr : 0 < r) (hCircle : ℝ),
        TwoScale.S36Events.Attained d e ξ Q c ⟨r, hr⟩ q a K C θ Cm Cp hCircle)
      (Metric.closedBall (0 : ℂ) (2 ^ (J + 1) * b)) hε0 hb hεκ hα a.2.2 hP hT hP0 hPT hsep
      htrace hcov
  have htel := TwoScale.S36Events.strict_metric_telescope_from_attained d e steps ξ Q q a K C θ Cm rfl hε0
    hb hCC hgap hP hgeo hunit hP0 hPT hT ht₀ hne hfrom hlast hbilip
    (fun st _ => st.good)
  
  have h7 : 7 * ε * b ≤ (κ : ℝ) * b := by nlinarith
  have hball : ∀ x y : ℂ, x ∈ Metric.ball y (7 * ε * b) → x ∈ Metric.ball y ((κ : ℝ) * b) :=
    fun x y hx => Metric.ball_subset_ball h7 hx
  have hset : OptimalConstants.Ratios.setDist e (Metric.ball z ((κ : ℝ) * b)) (Metric.ball w ((κ : ℝ) * b)) ≤
      e (P t₀, P (TwoScale.Stopping.StepsEnd t₀ steps)) :=
    iInf₂_le_of_le (P t₀) (hball _ _ hstart) (iInf₂_le (P (TwoScale.Stopping.StepsEnd t₀ steps))
      (hball _ _ hfinish))
  have hrhs : ENNReal.ofReal ((C' : ℝ) * T) = ENNReal.ofReal (C' : ℝ) * d (z, w) := by
    rw [ENNReal.ofReal_mul hC'0.le, hTdef, ENNReal.ofReal_toReal hfin.ne]
  have hcontra := hG.trans_lt (hset.trans_lt (htel.trans_eq hrhs))
  exact lt_irrefl _ hcontra

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
