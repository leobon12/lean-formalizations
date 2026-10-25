import SupercriticalLQGUniqueness.B2.DG20Lim.PointScalePower

 


set_option autoImplicit false
noncomputable section

open Set
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_point_scale_power_of_section4
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r δ : Ioo (0 : ℝ) 1) (c : ℝ),
        c ≤ Q / 4 * Real.log ((r : ℝ)⁻¹) →
          ((r : ℝ) * (m ⟨(δ : ℝ), δ.property.1⟩ : ℝ) /
            (m ⟨(r : ℝ) * (δ : ℝ),
              mul_pos r.property.1 δ.property.1⟩ : ℝ)) *
            Real.exp ((ξ : ℝ) * c) ≤
              C * (r : ℝ) ^ ((ξ : ℝ) * Q / 2) := by
  have hQpos : 0 < Q := hPos ξ Q hQ
  let ζ : ℝ := (ξ : ℝ) * Q / 4
  have hζ : 0 < ζ := by
    dsimp [ζ]
    exact div_pos (mul_pos ξ.property hQpos) (by norm_num)
  obtain ⟨C, hC, hratio⟩ := (hS4 ξ Q hQ m hm).2.1 ζ hζ
  refine ⟨C, hC, ?_⟩
  intro r δ c hc
  let e : Ioo (0 : ℝ) (r : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1,
      by simpa using (mul_lt_mul_of_pos_left δ.property.2 r.property.1)⟩
  have heq : (⟨(e : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos e.property.1 r.property.1)⟩ : Ioi (0 : ℝ)) =
      ⟨(δ : ℝ), δ.property.1⟩ := by
    apply Subtype.ext
    dsimp [e]
    field_simp [r.property.1.ne']
  have hb := (hratio r e).2
  rw [heq] at hb
  have hbase :
      (r : ℝ) * (m ⟨(δ : ℝ), δ.property.1⟩ : ℝ) /
        (m ⟨(r : ℝ) * (δ : ℝ),
          mul_pos r.property.1 δ.property.1⟩ : ℝ) ≤
        C * (r : ℝ) ^ (((ξ : ℝ) * Q / 2) +
          (ξ : ℝ) * (Q / 4)) := by
    have heexp : (ξ : ℝ) * Q / 2 + (ξ : ℝ) * (Q / 4) =
        (ξ : ℝ) * Q - ζ := by dsimp [ζ]; ring
    rw [heexp]
    simpa only [e] using hb
  exact point_scale_power_bound r.property.1 ξ.property hC.le
    hbase hc

end SupercriticalLQGUniqueness.B2.DG20Lim
