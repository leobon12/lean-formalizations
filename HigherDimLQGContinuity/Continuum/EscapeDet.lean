import HigherDimLQGContinuity.Continuum.Diam
import LQGMetric.Metric.Geodesic

/-! A strict annular barrier confines geodesics with endpoints in the inner ball. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

theorem continuum_escape_det {d : ℕ} (D : ContMetric d) {R S : ℝ}
    (hR : 0 < R) (hS : 4 ≤ S)
    (hbar : internalDiamRd D (closedBall (0 : Rd d) R) (ball 0 (2 * R)) <
      acrossDist D 0 (2 * R) (S * R)) :
    ¬ ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧
      IsGeodesicCurve (D.pt ∘ γ) 0 T ∧
      γ 0 ∈ closedBall (0 : Rd d) R ∧ γ T ∈ closedBall (0 : Rd d) R ∧
      ∃ t ∈ Icc (0 : ℝ) T, S * R ≤ ‖γ t‖ := by
  rintro ⟨γ, T, hT, hgeo, hx, hy, t, ht, htbig⟩
  have hγ : ContinuousOn γ (Icc (0 : ℝ) T) := by
    have h := D.continuous_unpt.comp_continuousOn hgeo.2.1
    simpa only [Function.comp_def, D.unpt_pt] using h
  have hcont : ContinuousOn (fun u : ℝ => ‖γ u‖) (Icc (0 : ℝ) t) :=
    hγ.norm.mono (Icc_subset_Icc le_rfl ht.2)
  have hstart : ‖γ 0‖ < 2 * R := by
    have hh : ‖γ 0‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
    linarith
  have htarget : ‖γ 0‖ ≤ S * R := by nlinarith
  obtain ⟨s₂, hs₂, hnorm₂⟩ := intermediate_value_Icc ht.1 hcont
    (show S * R ∈ Icc (‖γ 0‖) (‖γ t‖) from ⟨htarget, htbig⟩)
  have hcont₁ : ContinuousOn (fun u : ℝ => ‖γ u‖) (Icc (0 : ℝ) s₂) :=
    hcont.mono (Icc_subset_Icc le_rfl hs₂.2)
  have hmid : 2 * R ≤ S * R := by nlinarith
  obtain ⟨s₁, hs₁, hnorm₁⟩ := intermediate_value_Icc hs₂.1 hcont₁
    (show 2 * R ∈ Icc (‖γ 0‖) (‖γ s₂‖) from
      ⟨hstart.le, by change ‖γ s₂‖ = S * R at hnorm₂; rw [hnorm₂]; exact hmid⟩)
  have hs₁T : s₁ ≤ T := hs₁.2.trans (hs₂.2.trans ht.2)
  have hs₂T : s₂ ≤ T := hs₂.2.trans ht.2
  have hcross : acrossDist D 0 (2 * R) (S * R) ≤
      ENNReal.ofReal (D.1 (γ s₁, γ s₂)) := by
    unfold acrossDist
    apply (iInf₂_le (γ s₁) (by simpa only [mem_sphere, dist_zero_right] using hnorm₁)).trans
    exact iInf₂_le (γ s₂) (by simpa only [mem_sphere, dist_zero_right] using hnorm₂)
  have hlen : ENNReal.ofReal (D.1 (γ s₁, γ s₂)) ≤
      ENNReal.ofReal (D.1 (γ 0, γ T)) := by
    calc
      ENNReal.ofReal (D.1 (γ s₁, γ s₂)) ≤ D.len γ s₁ s₂ :=
        D.ofReal_le_len γ hs₁.2
      _ ≤ D.len γ 0 T := D.len_mono γ hs₁.1 hs₂T
      _ = ENNReal.ofReal (D.1 (γ 0, γ T)) := by
        simpa only [D.len_def, D.edist_pt, Function.comp_apply] using hgeo.2.2
  have hxy : ENNReal.ofReal (D.1 (γ 0, γ T)) ≤
      internalDiamRd D (closedBall (0 : Rd d) R) (ball 0 (2 * R)) := by
    calc
      ENNReal.ofReal (D.1 (γ 0, γ T)) ≤ D.internal (ball 0 (2 * R)) (γ 0) (γ T) :=
        D.ofReal_le_internal _ _ _
      _ ≤ internalDiamRd D (closedBall (0 : Rd d) R) (ball 0 (2 * R)) :=
        le_iSup₂_of_le (γ 0) hx (le_iSup₂_of_le (γ T) hy le_rfl)
  exact (not_lt_of_ge (hcross.trans (hlen.trans hxy))) hbar

end HigherDimLQGContinuity
