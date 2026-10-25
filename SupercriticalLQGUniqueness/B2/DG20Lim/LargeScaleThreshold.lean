import SupercriticalLQGUniqueness.B2.DG20Lim.LargeScaleFieldPower

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_scale_field_threshold_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    (T M : ℝ) (hT : 0 < T) (hM : 0 < M) :
    ∃ R₀ : ℝ, 1 < R₀ ∧
      ∀ (r : Ioi (1 : ℝ)) (e : Ioo (0 : ℝ) 1)
        (hr : R₀ ≤ (r : ℝ)) (c : ℝ)
        (hc : -(Q / 4 * Real.log (r : ℝ)) ≤ c),
        T * M ≤
          ((r : ℝ) *
            (m ⟨(e : ℝ) / (r : ℝ),
              div_pos e.property.1 (lt_trans one_pos r.property)⟩ : ℝ) /
            (m ⟨(e : ℝ), e.property.1⟩ : ℝ)) * Real.exp ((ξ : ℝ) * c) := by
  have hQpos : 0 < Q := hPos ξ Q hQ
  have hp : 0 < (ξ : ℝ) * Q / 4 := by
    exact div_pos (mul_pos ξ.property hQpos) (by norm_num)
  obtain ⟨C, hC, hscale⟩ :=
    exists_large_scale_power_lower_of_inputs hS4 hPos ξ Q hQ m hm
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hC
  obtain ⟨R, hR⟩ := tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop hp) (T * M / C⁻¹)
  refine ⟨max R 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro r e hr c hc
  have hrR : R ≤ (r : ℝ) := (le_max_left _ _).trans hr
  have hpow : T * M ≤ C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q / 4) := by
    have hh := mul_le_mul_of_nonneg_left (hR _ hrR) hCinv.le
    calc
      T * M = C⁻¹ * (T * M / C⁻¹) := by field_simp [hCinv.ne']
      _ ≤ C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q / 4) := hh
  have hbase := hscale r e
  have hexp : (ξ : ℝ) * Q / 4 + (ξ : ℝ) * (Q / 4) =
      (ξ : ℝ) * Q / 2 := by ring
  have hfield := large_scale_field_power_bound
    (r := (r : ℝ)) (ξ := (ξ : ℝ)) (β := Q / 4)
    (p := (ξ : ℝ) * Q / 4) (C := C⁻¹)
    (a := (r : ℝ) *
      (m ⟨(e : ℝ) / (r : ℝ),
        div_pos e.property.1 (lt_trans one_pos r.property)⟩ : ℝ) /
      (m ⟨(e : ℝ), e.property.1⟩ : ℝ)) (c := c)
    (lt_trans one_pos r.property) ξ.property hCinv.le
    (by simpa only [hexp] using hbase) hc
  exact hpow.trans hfield

end SupercriticalLQGUniqueness.B2.DG20Lim
