import SupercriticalLQGUniqueness.Support.LSCMetricLowerSemicontinuous
import Mathlib.Topology.Semicontinuity.Basic

 




set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem compact_oscillation (D : LSCMetric) (f : C(ℂ, ℝ))
    {K : Set ℂ} (hK : IsCompact K) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ K, ∀ v ∈ K,
      D (u, v) ≤ ENNReal.ofReal δ → |f u - f v| < θ := by
  let S : Set (ℂ × ℂ) := (K ×ˢ K) ∩ {p | θ ≤ |f p.1 - f p.2|}
  have hc : Continuous (fun p : ℂ × ℂ => |f p.1 - f p.2|) :=
    ((f.continuous.comp continuous_fst).sub
      (f.continuous.comp continuous_snd)).abs
  have hSc : IsCompact S :=
    (hK.prod hK).inter_right (isClosed_le continuous_const hc)
  by_cases hSne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ :=
      (D.lowerSemicontinuous.lowerSemicontinuousOn S).exists_isMinOn hSne hSc
    have hpne : p.1 ≠ p.2 := by
      intro heq
      have hθp : θ ≤ |f p.1 - f p.2| := hp.2
      rw [heq, sub_self, abs_zero] at hθp
      exact (not_le_of_gt hθ) hθp
    have hpD : 0 < D p := by
      apply bot_lt_iff_ne_bot.mpr
      intro hz
      exact hpne (D.isExtMetric.2.1 p.1 p.2 hz)
    obtain ⟨δ, hδ, hδp⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ < D p := by
      by_cases htop : D p = ⊤
      · exact ⟨1, by norm_num, by simp [htop]⟩
      · have hpreal : 0 < (D p).toReal := ENNReal.toReal_pos hpD.ne' htop
        refine ⟨(D p).toReal / 2, half_pos hpreal, ?_⟩
        calc
          ENNReal.ofReal ((D p).toReal / 2) < ENNReal.ofReal (D p).toReal :=
            (ENNReal.ofReal_lt_ofReal_iff hpreal).2 (half_lt_self hpreal)
          _ = D p := ENNReal.ofReal_toReal htop
    refine ⟨δ, hδ, ?_⟩
    intro u hu v hv hD
    by_contra hnot
    have hSuv : (u, v) ∈ S := ⟨⟨hu, hv⟩, le_of_not_gt hnot⟩
    exact (not_lt_of_ge ((hmin hSuv).trans hD)) hδp
  · refine ⟨1, by norm_num, ?_⟩
    intro u hu v hv _
    by_contra hnot
    exact hSne ⟨(u, v), ⟨⟨hu, hv⟩, le_of_not_gt hnot⟩⟩

end SupercriticalLQGUniqueness.B2.PfeWeyl
