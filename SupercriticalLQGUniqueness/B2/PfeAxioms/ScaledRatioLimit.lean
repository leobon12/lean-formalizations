import SupercriticalLQGUniqueness.B2.LscTop.Dilate

 


set_option autoImplicit false
noncomputable section

open Filter Topology Set

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem tendsto_inverse_ratio_coefficient
    (a b : ℕ → ℝ) (r c t : ℝ)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hr : 0 < r) (hc : 0 < c)
    (h : Tendsto (fun n => r * b n / a n) atTop (𝓝 c)) :
    Tendsto (fun n => a n / (r * b n) * Real.exp t) atTop
      (𝓝 (c⁻¹ * Real.exp t)) := by
  have hInv := h.inv₀ hc.ne'
  have heq (n : ℕ) : a n / (r * b n) = (r * b n / a n)⁻¹ := by
    field_simp [ne_of_gt (ha n), ne_of_gt (hb n), ne_of_gt hr]
  simpa only [heq] using hInv.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.exp t) atTop (𝓝 (Real.exp t)))

theorem tendsto_scaled_metric_of_normalizer_ratio
    (G H : ℕ → LSCMetric) (D : LSCMetric)
    (a b : ℕ → ℝ) (r c t : ℝ)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hr : 0 < r) (hc : 0 < c)
    (h : Tendsto (fun n => r * b n / a n) atTop (𝓝 c))
    (hG : Tendsto G atTop (𝓝 D))
    (hH : ∀ n, H n = B2.LscTop.smulMetric
      ⟨a n / (r * b n) * Real.exp t,
        Set.mem_Ioi.mpr (mul_pos (div_pos (ha n) (mul_pos hr (hb n))) (Real.exp_pos _))⟩
      (B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩ (G n))) :
    Tendsto H atTop
      (𝓝 (B2.LscTop.smulMetric
        ⟨c⁻¹ * Real.exp t,
          Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr hc) (Real.exp_pos _))⟩
        (B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩ D))) := by
  have hcoef := tendsto_inverse_ratio_coefficient a b r c t ha hb hr hc h
  have hcoef' : Tendsto
      (fun n : ℕ => (⟨a n / (r * b n) * Real.exp t,
        Set.mem_Ioi.mpr (mul_pos (div_pos (ha n) (mul_pos hr (hb n)))
          (Real.exp_pos _))⟩ : Ioi (0 : ℝ))) atTop
      (𝓝 (⟨c⁻¹ * Real.exp t,
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr hc) (Real.exp_pos _))⟩ : Ioi (0 : ℝ))) :=
    tendsto_subtype_rng.mpr hcoef
  have hDil : Tendsto
      (fun n => B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩ (G n)) atTop
      (𝓝 (B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩ D)) :=
    B2.LscTop.tendsto_dilate tendsto_const_nhds hG
  have hSmul := B2.LscTop.tendsto_smulMetric hcoef' hDil
  have hFun : H = fun n => B2.LscTop.smulMetric
      ⟨a n / (r * b n) * Real.exp t,
        Set.mem_Ioi.mpr (mul_pos (div_pos (ha n) (mul_pos hr (hb n)))
          (Real.exp_pos _))⟩
      (B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩ (G n)) := funext hH
  rw [hFun]
  exact hSmul

end SupercriticalLQGUniqueness.B2.PfeAxioms
