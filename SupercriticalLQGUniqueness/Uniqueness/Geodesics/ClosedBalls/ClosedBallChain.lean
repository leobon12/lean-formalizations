import SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls.FiniteAnnularNetwork




 


set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

open LQGMetric (DistC)

 

theorem exists_annular_chain_geometry
    (z₁ z₂ : ℂ) (hneq : z₁ ≠ z₂)
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    ∃ (n : ℕ) (c : ℕ → ℂ) (ρ : ℝ) (u : ℂ),
      0 < ρ ∧ ‖u‖ = 1 ∧
      (∀ i < n, c (i + 1) = c i + (3 / 2 * ρ) • u) ∧
      c 0 = z₁ ∧ c n = z₂ ∧ 2 * ρ < r₁ ∧ 2 * ρ < r₂ := by
  let v : ℂ := z₂ - z₁
  let d : ℝ := ‖v‖
  have hd : 0 < d := by
    dsimp [d, v]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hneq))
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * d / (3 * r) + 1)
  have hn0 : 0 < (n : ℝ) := by
    have hp : 0 < 4 * d / (3 * r) := div_pos (by positivity) (by positivity)
    linarith
  let ρ : ℝ := 2 * d / (3 * n)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (by positivity) (by positivity)
  let u : ℂ := (d⁻¹ : ℝ) • v
  have hu : ‖u‖ = 1 := by
    change ‖(d⁻¹ : ℝ) • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    change d⁻¹ * d = 1
    exact inv_mul_cancel₀ hd.ne'
  let c : ℕ → ℂ := fun i => z₁ + ((i : ℝ) * (3 / 2 * ρ)) • u
  have hstep : ∀ i < n, c (i + 1) = c i + (3 / 2 * ρ) • u := by
    intro i _
    dsimp [c]
    simp only [Nat.cast_add, Nat.cast_one]
    push_cast
    ring
  have hc0 : c 0 = z₁ := by simp [c]
  have hscalar : (n : ℝ) * (3 / 2 * ρ) = d := by
    dsimp [ρ]
    field_simp
  have hcn : c n = z₂ := by
    dsimp [c]
    rw [hscalar]
    have hdu : d • u = v := by
      change (d : ℂ) * ((d⁻¹ : ℝ) • v) = v
      simp [Complex.real_smul, hd.ne']
    calc
      z₁ + d • u = z₁ + v := congrArg (fun w : ℂ => z₁ + w) hdu
      _ = z₂ := by simp [v]
  have hsmall : 2 * ρ < r := by
    have hden : 0 < 3 * (n : ℝ) := by positivity
    have hbound : 4 * d < 3 * (n : ℝ) * r := by
      have hraw : 4 * d / (3 * r) < (n : ℝ) := by linarith
      have hden' : 0 < 3 * r := by positivity
      have := (div_lt_iff₀ hden').mp hraw
      nlinarith
    calc
      2 * ρ = 4 * d / (3 * (n : ℝ)) := by dsimp [ρ]; ring
      _ < r := (div_lt_iff₀ hden).2 (by nlinarith)
  refine ⟨n, c, ρ, u, hρ, hu, hstep, hc0, hcn, ?_, ?_⟩
  · exact hsmall.trans_le (min_le_left r₁ r₂)
  · exact hsmall.trans_le (min_le_right r₁ r₂)

 

theorem ae_setDist_closedBalls_lt_top
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (z₁ z₂ : ℂ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall z₁ r₁)
      (Metric.closedBall z₂ r₂)) :
    ∀ᵐ ω ∂μ, OptimalConstants.Ratios.setDist (D (h ω))
      (Metric.closedBall z₁ r₁) (Metric.closedBall z₂ r₂) < ⊤ := by
  have hneq : z₁ ≠ z₂ := by
    intro heq
    have hz₁ : z₁ ∈ Metric.closedBall z₁ r₁ := by
      exact Metric.mem_closedBall_self hr₁.le
    have hz₂ : z₁ ∈ Metric.closedBall z₂ r₂ := by
      simpa [← heq] using (Metric.mem_closedBall_self hr₂.le :
        z₂ ∈ Metric.closedBall z₂ r₂)
    exact Set.disjoint_left.mp hdisj hz₁ hz₂
  obtain ⟨n, c, ρ, u, hρ, hu, hstep, hc0, hcn, hsmall₁, hsmall₂⟩ :=
    exists_annular_chain_geometry z₁ z₂ hneq r₁ r₂ hr₁ hr₂
  filter_upwards [ae_finite_around_chain hD μ h hh c ρ hρ] with ω hfinite
  have hnet := setDist_closedBalls_lt_top_of_annular_chain
    (D (h ω)) n c ρ hρ u hu hstep r₁ r₂ hsmall₁ hsmall₂ hfinite
  simpa only [hc0, hcn] using hnet

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls
