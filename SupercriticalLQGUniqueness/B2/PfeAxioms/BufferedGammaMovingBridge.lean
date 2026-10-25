import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaAnnulusGeom
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaAnnuli

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem eventually_buffered_bridge_at_junction
    {G : ℕ → LSCMetric} {D : LSCMetric} {K V : Set ℂ}
    (hsmall : SmallAnnulusCosts G D K V)
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {z w₁ w₂ : ℂ} (hzK : z ∈ K) (hzNS : IsNonsingular D z)
    (hw₁ : w₁ ≠ z) (hw₂ : w₂ ≠ z)
    (P Q : (n : ℕ) → BufferedMetricTrace (G n) V)
    (hPstart : Tendsto (fun n => (P n).path (P n).start) atTop (𝓝 w₁))
    (hPstop : Tendsto (fun n => (P n).path (P n).stop) atTop (𝓝 z))
    (hQstart : Tendsto (fun n => (Q n).path (Q n).start) atTop (𝓝 z))
    (hQstop : Tendsto (fun n => (Q n).path (Q n).stop) atTop (𝓝 w₂))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : EuclideanAnnulus,
      IsRationalDoubleAnnulus A ∧ A.toSet ⊆ V ∧
      ∀ᶠ n in atTop,
        ∃ R : BufferedMetricTrace (G n) V,
          ((P n).trace ∩ R.trace).Nonempty ∧
          (R.trace ∩ (Q n).trace).Nonempty ∧
          R.cost < ENNReal.ofReal δ := by
  have hd₁ : 0 < dist z w₁ := dist_pos.mpr hw₁.symm
  have hd₂ : 0 < dist z w₂ := dist_pos.mpr hw₂.symm
  let ρ : ℝ := min (dist z w₁) (dist z w₂) / 4
  have hρ : 0 < ρ := div_pos (lt_min hd₁ hd₂) (by norm_num)
  obtain ⟨A, hrat, hzA, hAρ, hAV, hcost⟩ :=
    hsmall z hzK hzNS δ hδ ρ hρ
  have hfar₁ : 2 * A.outerRadius < dist z w₁ := by
    have hmin : min (dist z w₁) (dist z w₂) ≤ dist z w₁ := min_le_left _ _
    dsimp [ρ] at hAρ
    linarith
  have hfar₂ : 2 * A.outerRadius < dist z w₂ := by
    have hmin : min (dist z w₁) (dist z w₂) ≤ dist z w₂ := min_le_right _ _
    dsimp [ρ] at hAρ
    linarith
  have hPa := eventually_outside_annulus A z w₁ hzA hfar₁ hPstart
  have hPb := eventually_inside_annulus A z hzA hPstop
  have hQc := eventually_inside_annulus A z hzA hQstart
  have hQd := eventually_outside_annulus A z w₂ hzA hfar₂ hQstop
  refine ⟨A, hrat, hAV, ?_⟩
  filter_upwards [hPa, hPb, hQc, hQd, hcost] with n hPa' hPb' hQc' hQd' hc
  exact exists_buffered_annular_bridge (G n) (hforget n) A hAV
    (P n) (Q n) hPa' hPb' hQc' hQd' hc

end SupercriticalLQGUniqueness.B2.PfeAxioms
