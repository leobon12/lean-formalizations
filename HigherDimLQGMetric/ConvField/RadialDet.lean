import HigherDimLQGMetric.ConvField.Polar

/-! Deterministic radial pairing for a distribution regularized by `bumpTest`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem l2b_continuous_sphereAvgSeq_radius (T : DistRd d) (n : ℕ) (z : Rd d) :
    Continuous fun r : ℝ => sphereAvgSeq T r z n := by
  change Continuous ((fun p : ℝ × Rd d => sphereAvgSeq T p.1 p.2 n) ∘
    (fun r : ℝ => (r, z)))
  exact (continuous_sphereAvgSeq T n).comp
    (continuous_id.prodMk continuous_const)

theorem l2b_integral_mul_eq_polar (hd : 2 ≤ d) (φ : TestRd d) (z : Rd d)
    (hφ : ∀ w : Rd d, φ w = φ (z + ‖w - z‖ • e₁ d))
    {m : Rd d → ℝ} (hm : Continuous m) :
    (∫ y : Rd d, φ y * m y) =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * φ (z + r • e₁ d) *
          (∫ u : sphere (0 : Rd d) 1, m (z + r • (u : Rd d)) ∂sphereMeasure d) := by
  let f : Rd d → ℝ := fun x => φ (z + x) * m (z + x)
  have hfc : Continuous f :=
    (φ.continuous.comp (continuous_const.add continuous_id)).mul
      (hm.comp (continuous_const.add continuous_id))
  have hfs : HasCompactSupport f := by
    exact (φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft z)).mul_right
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfs
  have hmove : (∫ y : Rd d, φ y * m y) = ∫ x : Rd d, f x :=
    (integral_add_left_eq_self (fun y : Rd d => φ y * m y) z).symm
  rw [hmove, l2b_integral_polar_sphere hd hfi]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := hr
  have hφr (u : sphere (0 : Rd d) 1) :
      φ (z + r • (u : Rd d)) = φ (z + r • e₁ d) := by
    rw [hφ, add_sub_cancel_left, norm_smul,
      mem_sphere_zero_iff_norm.mp u.2, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
  simp only [f, hφr]
  simp only [mul_assoc, integral_const_mul]

theorem l2b_tendsto_polar_sphBump (hd : 2 ≤ d) (T : DistRd d)
    (φ : TestRd d) (z : Rd d)
    (hφ : ∀ w : Rd d, φ w = φ (z + ‖w - z‖ • e₁ d)) :
    Tendsto (fun n : ℕ =>
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * φ (z + r • e₁ d) *
          sphereAvgSeq T r z n) atTop (𝓝 (T φ)) := by
  refine (l2b_tendsto_integral_mul_pair_bumpTest T φ).congr fun n => ?_
  have h := l2b_integral_mul_eq_polar hd φ z hφ
    (m := fun y => T (bumpTest n y))
    (T.continuous.comp (continuous_bumpTest n))
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [sphereAvgSeq]
  rw [integral_unitSphereProb_eq_sphereMeasure
    (continuous_apply_bumpTest_affine T n r z)]

end HigherDimLQGMetric
