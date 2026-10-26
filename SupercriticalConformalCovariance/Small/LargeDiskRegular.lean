import SupercriticalConformalCovariance.Small.RegularConfinement

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

/-- The dyadic regular-pair conditions persist under every radius at least two. -/
theorem sourceRegularPair_conf_ge_two
    (D : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (R α θ m : ℝ) (hR : 2 ≤ R) (u v : ℂ)
    (hα : (3 / 4 : ℝ) < α ∧ α < 1)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair D 0 u v 1 α θ m) :
    SupercriticalConformalCovariance.Regular.SourceRegularPair (conf D 0 R) 0 u v 1 α θ m := by
  have hu : u ∈ closedBall 0 1 := by
    change dist u 0 ≤ 1
    have hs : dist u 0 = α := by
      simpa only [Metric.mem_sphere, mul_one] using hreg.2.1
    exact hs.trans_le hα.2.le
  have hv : v ∈ closedBall 0 1 := by
    change dist v 0 ≤ 1
    exact (show dist v 0 = 1 by simpa only [Metric.mem_sphere] using hreg.2.2.1).le
  have hsquare : (1 - α) ^ 2 < 1 := by nlinarith [sq_nonneg α]
  have hsmall : ∀ j : ℕ, 0 < SupercriticalConformalCovariance.Regular.dyadic j →
      SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - α) ^ 2 → SupercriticalConformalCovariance.Regular.dyadic j < 1 :=
    fun j _ hj => hj.trans_lt hsquare
  have hunit : ∀ x : ℂ, x = u ∨ x = v → closedBall x 1 ⊆ closedBall 0 R := by
    intro x hx y hy
    have hx1 : dist x 0 ≤ 1 := by
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    change dist y 0 ≤ R
    calc
      dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
      _ ≤ 1 + 1 := add_le_add hy hx1
      _ ≤ R := by linarith
  apply sourceRegularPair_conf_of_geometry D hL hC R α θ m u v
  · intro x hx
    exact (closedBall_subset_closedBall (by linarith : (1 : ℝ) ≤ R)) hx.1
  · exact hsmall
  · intro x hx j hj hjα
    exact (closedBall_subset_closedBall (le_of_lt (hsmall j hj hjα))).trans
      (hunit x hx)
  · intro x hx j hj hj1 hjα y hy
    apply hunit x hx
    change dist y x ≤ 1
    have hy' : dist y x < Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) := hy.1
    exact le_of_lt (lt_trans hy' (by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hj.le hj1))
  · exact hreg

/-- Failure persists under an expanding source confinement and a larger target cost. -/
theorem sourceFailure_conf_ge_two_of_target_mono
    (D F : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (R α θ m T η : ℝ) (hR : 2 ≤ R) (u v : ℂ) (eCost : ℝ≥0∞)
    (hα : (3 / 4 : ℝ) < α ∧ α < 1) (hmT : m ≤ T)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair D 0 u v 1 α θ m)
    (hfail : ENNReal.ofReal (1 + η) * D (u,v) ≤ eCost)
    (hmono : eCost ≤ F (u,v)) :
    SupercriticalConformalCovariance.Regular.SourceFailure (conf D 0 R) F 0 u v 1 α θ T
      ((1 - α)⁻¹ * T) (1 - α) η := by
  have hregC := sourceRegularPair_conf_ge_two D hL hC R α θ m hR u v hα hreg
  obtain ⟨⟨P,a,b,hgeo,htrace⟩,_,_,_,_,_⟩ := hreg
  have hK : ∀ t ∈ Icc a b, P t ∈ closedBall 0 R := by
    intro t ht
    have hA := htrace ⟨t,ht,rfl⟩
    exact (closedBall_subset_closedBall (by linarith : (1 : ℝ) ≤ R)) hA.1
  have heq := conf_cost_eq_of_geodesic_trace D 0 R u v P a b hgeo hK
  apply sourceFailure_of_regular_and_bound (conf D 0 R) F 0 u v α θ m T η
    hα.2 hmT hregC
  rw [heq]
  exact hfail.trans hmono

end SupercriticalConformalCovariance.Small
