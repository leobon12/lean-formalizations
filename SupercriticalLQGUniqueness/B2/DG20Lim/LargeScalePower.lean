import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleAverageDecay
import SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
noncomputable section

open Set LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_scale_power_lower_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : Ioi (1 : ℝ), ∀ e : Ioo (0 : ℝ) 1,
        C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q / 2) ≤
          (r : ℝ) *
            (m ⟨(e : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr
                (div_pos e.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
            (m ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩ : ℝ) := by
  have hQpos : 0 < Q := hPos ξ Q hQ
  have hζ : 0 < (ξ : ℝ) * Q / 2 := div_pos (mul_pos (Set.mem_Ioi.mp ξ.property) hQpos) (by norm_num)
  obtain ⟨C, hC, hscale⟩ := (hS4 ξ Q hQ m hm).2.2
    ((ξ : ℝ) * Q / 2) hζ
  refine ⟨C, hC, ?_⟩
  intro r e
  have h := (hscale r e).1
  have hexp : (ξ : ℝ) * Q - (ξ : ℝ) * Q / 2 =
      (ξ : ℝ) * Q / 2 := by ring
  simpa only [hexp] using h

end SupercriticalLQGUniqueness.B2.DG20Lim
