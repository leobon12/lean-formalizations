import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.SaturationE
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LQGMetric.Papers.CONF.S3D112M4
import LQGMetric.Papers.DFGPS.L2_17CoreB




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC addConst restrictTo)

 

theorem isCircleAverage_addConst (g : DistC) (t : ℝ) (r : Ioi (0 : ℝ)) (z : ℂ) (c : ℝ) :
    IsCircleAverage (addConst g t) r z (c + t) ↔ IsCircleAverage g r z c := by
  unfold IsCircleAverage
  have h : (fun n : ℕ => Real.circleAverage (fun x => (addConst g t)
      (LQGMetric.bumpTest n x)) z (r : ℝ)) =
      fun n : ℕ => Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z (r : ℝ) + t := by
    funext n
    exact LQGMetric.CircleAvg.mollAvg_addConst g t n z r
  rw [h]
  exact tendsto_add_const_iff t

 

theorem isCircleAverage_congr_restrict {U : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (he : restrictTo U g₁ = restrictTo U g₂) (r : Ioi (0 : ℝ)) (z : ℂ)
    (hsU : Metric.sphere z r ⊆ U) (c : ℝ) :
    IsCircleAverage g₁ r z c ↔ IsCircleAverage g₂ r z c := by
  obtain ⟨ε, hε, hthick⟩ := (isCompact_sphere z (r : ℝ)).exists_thickening_subset_open
    U.isOpen hsU
  obtain ⟨N, hN⟩ := LQGMetric.CONF.exists_circBump_supp r.2 z (subset_refl _) hε
  rw [isCircleAverage_iff_circBump, isCircleAverage_iff_circBump]
  have heq : ∀ᶠ n : ℕ in atTop, g₁ (LQGMetric.CircleAvg.circBump n z (r : ℝ)) =
      g₂ (LQGMetric.CircleAvg.circBump n z (r : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _ ((hN n hn).trans hthick)
  exact ⟨fun h => h.congr' heq, fun h => h.congr' (heq.mono fun _ h => h.symm)⟩

 

section Scaling

variable {d₁ d₂ : LSCMetric} {k : ℝ≥0∞}

theorem setDist_eq_mul_of_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y)) (A B : Set ℂ) :
    OptimalConstants.Ratios.setDist d₂ A B = k * OptimalConstants.Ratios.setDist d₁ A B := by
  unfold OptimalConstants.Ratios.setDist
  simp only [hd, ENNReal.mul_iInf_of_ne hk0 hkt]

theorem scale_le_scale_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (a b c : ℝ≥0∞) :
    k * a ≤ c * (k * b) ↔ a ≤ c * b := by
  rw [mul_left_comm c k b]
  exact ENNReal.mul_le_mul_iff_right hk0 hkt

theorem scale_le_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (a b : ℝ≥0∞) :
    k * a ≤ k * b ↔ a ≤ b :=
  ENNReal.mul_le_mul_iff_right hk0 hkt

theorem mul_lt_top_iff_of_ne (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (a : ℝ≥0∞) :
    k * a < ⊤ ↔ a < ⊤ := by
  constructor
  · intro h
    by_contra ha
    rw [not_lt, top_le_iff] at ha
    rw [ha, ENNReal.mul_top hk0] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hkt) h

theorem ibg_scale_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y))
    (z : ℂ) (r : ℝ) (P : ℝ → ℂ) (s t : ℝ) :
    TwoScale.S36Events.InternalBoundaryGeodesic d₂ z r P s t ↔ TwoScale.S36Events.InternalBoundaryGeodesic d₁ z r P s t := by
  unfold TwoScale.S36Events.InternalBoundaryGeodesic
  simp only [Positivity.Witnesses.isCurve_iff_of_dist_scale d₁ d₂ k hk0 hkt hd,
    Positivity.Witnesses.len_eq_mul_of_dist_scale d₁ d₂ k hd,
    Positivity.Witnesses.internal_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hd,
    ENNReal.mul_right_inj hk0 hkt, mul_lt_top_iff_of_ne hk0 hkt]

end Scaling

 

theorem ofReal_N_shift (ξ Q a r c t : ℝ) :
    ENNReal.ofReal ((1 - a)⁻¹ * r ^ (ξ * Q) * Real.exp (ξ * (c + t))) =
      ENNReal.ofReal (Real.exp (ξ * t)) *
        ENNReal.ofReal ((1 - a)⁻¹ * r ^ (ξ * Q) * Real.exp (ξ * c)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
  ring_nf

 

theorem attained_scale_iff {d₁ e₁ d₂ e₂ : LSCMetric} {ξ : ℝ} (t : ℝ)
    (hd : ∀ x y, d₂ (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * d₁ (x, y))
    (he : ∀ x y, e₂ (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * e₁ (x, y))
    (Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (Cm Cp c : ℝ) :
    TwoScale.S36Events.Attained d₂ e₂ ξ Q z r q a K C θ Cm Cp (c + t) ↔
      TwoScale.S36Events.Attained d₁ e₁ ξ Q z r q a K C θ Cm Cp c := by
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * t)) with hkdef
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have harnd := Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hd
  have hacr := Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hd
  have hset := setDist_eq_mul_of_scale hk0 hkt hd
  rw [attained_iff, attained_iff]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · 
    unfold TwoScale.S36Events.EventClause1
    simp only [ibg_scale_iff hk0 hkt hd, harnd, hacr, scale_le_scale_iff hk0 hkt]
  · 
    unfold E2Prop
    rw [harnd, hset, ofReal_N_shift, mul_left_comm _ k, min_mul_mul_left]
    exact scale_le_iff hk0 hkt _ _
  · 
    unfold TwoScale.S36Events.EventClause3
    simp only [ibg_scale_iff hk0 hkt hd]
  · 
    unfold E4Prop
    rw [harnd, hacr]
    exact scale_le_scale_iff hk0 hkt _ _ _
  · 
    unfold E5Lit OptimalConstants.Ratios.Geodesic TwoScale.S36Events.EndpointLoopAt
    simp only [harnd, hset, hd, he, Positivity.Witnesses.isCurve_iff_of_dist_scale d₁ d₂ k hk0 hkt hd,
      Positivity.Witnesses.len_eq_mul_of_dist_scale d₁ d₂ k hd, ENNReal.mul_right_inj hk0 hkt,
      mul_lt_top_iff_of_ne hk0 hkt, ofReal_N_shift, ← hkdef]
    simp only [scale_le_scale_iff hk0 hkt, scale_le_iff hk0 hkt, max_mul_mul_left]

 
theorem attainedEvent_addConst_iff (D D' : DistC → LSCMetric) (ξ Q : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ)) (Cm Cp : ℝ) (g : DistC) (t : ℝ)
    (hd : ∀ x y, D (addConst g t) (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * D g (x, y))
    (he : ∀ x y, D' (addConst g t) (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * D' g (x, y)) :
    addConst g t ∈ TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cm Cp ↔
      g ∈ TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cm Cp := by
  constructor
  · rintro ⟨c', hc', hA⟩
    refine ⟨c' - t, ?_, ?_⟩
    · have h := (isCircleAverage_addConst g t r z (c' - t))
      rw [sub_add_cancel] at h
      exact h.mp hc'
    · have h := attained_scale_iff (d₁ := D g) (e₁ := D' g) (d₂ := D (addConst g t))
        (e₂ := D' (addConst g t)) t hd he Q z r q a K C θ Cm Cp (c' - t)
      rw [sub_add_cancel] at h
      exact h.mp hA
  · rintro ⟨c, hc, hA⟩
    exact ⟨c + t, (isCircleAverage_addConst g t r z c).mpr hc,
      (attained_scale_iff (d₁ := D g) (e₁ := D' g) (d₂ := D (addConst g t))
        (e₂ := D' (addConst g t)) t hd he Q z r q a K C θ Cm Cp c).mpr hA⟩

 
theorem ae_attainedEvent_addConst_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D') (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (Cm Cp : ℝ)
    (t : Ω → ℝ) :
    ∀ᵐ ω ∂P, (addConst (h ω) (t ω) ∈ TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cm Cp ↔
      h ω ∈ TwoScale.S36Events.AttainedEvent D D' ξ Q z r q a K C θ Cm Cp) := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul P h hh ξ Q D hD t,
    Positivity.Witnesses.ae_addConst_eq_mul P h hh ξ Q D' hD' t] with ω hw hw'
  exact attainedEvent_addConst_iff D D' ξ Q z r q a K C θ Cm Cp (h ω) (t ω)
    (fun x y => hw (x, y)) (fun x y => hw' (x, y))

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
