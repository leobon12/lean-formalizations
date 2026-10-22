import HigherDimLQGMetric.Amplify.BackArc
import HigherDimLQGMetric.Amplify.ScaleRatio

/-! A returned trial yields the exact arc conclusion in its macroscopic box. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Turn a good trial at `r • w` into the arc required by `FineFieldAmplification`.
The box is specified by a ball containment, so this lemma also applies to
other deterministic placements. -/
theorem amplify_arc_in_box
    (D Dt : ContMetric d) (hD : D.IsLength) [ProperSpace D.Space]
    (hDt : Dt.IsLength) [ProperSpace Dt.Space]
    {ξ Q cs c1 c2 ℓ δ ρ r K a₁ A₁ : ℝ}
    (hξ : 0 < ξ) (hcs : 0 < cs) (hc1 : 0 < c1) (hℓ : 0 < ℓ)
    (hδ : 0 ≤ δ) (hδsmall : Real.exp (4 * ξ * δ) < 2)
    (hc2 : Real.exp (4 * ξ * δ) * c1 < c2)
    (hρ : 0 < ρ) (hr : 0 < r) (w : Rd d) (H : DistRd d)
    (S : Set (Rd d))
    (hplace : Metric.ball w (5 * ρ) ⊆ S)
    (hgauss : |sphereAvg H (ρ * r) (r • w) - sphereAvg H r 0| ≤ K)
    (ha : a₁ ≤ Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) *
      (ρ ^ (ξ * Q) * Real.exp (-ξ * K)))
    (hA : cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ *
      (ρ ^ (ξ * Q) * Real.exp (ξ * K)) ≤ A₁)
    (hcomp : ∀ x y, cs * D.1 (x, y) ≤ Dt.1 (x, y))
    (hback : AmplifyBackEvent D Dt ξ Q cs c1 ℓ δ (ρ * r) (r • w) H) :
    ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (fun x => r • x) '' S) ∧
      Dt.len γ 0 1 ≤ ENNReal.ofReal (c2 * D.1 (γ 0, γ 1)) ∧
      a₁ * sNorm ξ Q H r 0 ≤ D.1 (γ 0, γ 1) ∧
      D.len γ 0 1 ≤ ENNReal.ofReal (A₁ * sNorm ξ Q H r 0) := by
  have hs : 0 < ρ * r := mul_pos hρ hr
  have hβ : 0 ≤ ξ * δ := mul_nonneg hξ.le hδ
  obtain ⟨γ, hγ, hrange, hratio, hlow, hupper⟩ :=
    amplify_backEvent_to_arc D Dt hD hDt hcs hc1 hℓ hs hβ hδsmall
      (r • w) H hcomp hback
  have hnorm := amplify_sNorm_ratio_bounds (ξ := ξ) (Q := Q) hξ H hρ hr w hgauss
  have hsn : 0 ≤ sNorm ξ Q H r 0 := by unfold sNorm; positivity
  have hal : 0 ≤ Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) := by positivity
  have hau : 0 ≤ cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ := by positivity
  have hballscale : (fun x : Rd d => r • x) '' Metric.ball w (5 * ρ) =
      Metric.ball (r • w) (5 * (ρ * r)) := by
    rw [Metric.smul_image_ball hr.ne' w (5 * ρ), Real.norm_eq_abs,
      abs_of_pos hr]
    congr 1
    ring
  refine ⟨γ, hγ, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have htball : γ t ∈ Metric.ball (r • w) (5 * (ρ * r)) := by
      change dist (γ t) (r • w) < 5 * (ρ * r)
      have hrange' := (hrange t ht).2
      change ‖γ t - r • w‖ < 3 * (ρ * r) at hrange'
      rw [dist_eq_norm]
      linarith
    rw [← hballscale] at htball
    obtain ⟨x, hx, hγx⟩ := htball
    exact ⟨x, hplace hx, hγx⟩
  · have hDd : 0 ≤ D.1 (γ 0, γ 1) := D.nonneg _ _
    calc
      Dt.len γ 0 1 ≤ ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1) *
          ENNReal.ofReal (D.1 (γ 0, γ 1)) := hratio
      _ = ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1 *
          D.1 (γ 0, γ 1)) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (4 * ξ * δ) * c1)]
      _ ≤ ENNReal.ofReal (c2 * D.1 (γ 0, γ 1)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hc2.le hDd
  · have hDd : 0 ≤ D.1 (γ 0, γ 1) := D.nonneg _ _
    have hlower : Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) *
        sNorm ξ Q H (ρ * r) (r • w) ≤ D.1 (γ 0, γ 1) :=
      (ENNReal.ofReal_le_ofReal_iff hDd).1 hlow
    calc
      a₁ * sNorm ξ Q H r 0 ≤
          (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) *
            (ρ ^ (ξ * Q) * Real.exp (-ξ * K))) * sNorm ξ Q H r 0 :=
              mul_le_mul_of_nonneg_right ha hsn
      _ ≤ Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) *
          sNorm ξ Q H (ρ * r) (r • w) := by
            calc
              _ = (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1))) *
                  (ρ ^ (ξ * Q) * Real.exp (-ξ * K) * sNorm ξ Q H r 0) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hnorm.1 hal
      _ ≤ D.1 (γ 0, γ 1) := hlower
  · have hupper' : cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ *
        sNorm ξ Q H (ρ * r) (r • w) ≤ A₁ * sNorm ξ Q H r 0 := by
      calc
        _ ≤ (cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ) *
            (ρ ^ (ξ * Q) * Real.exp (ξ * K) * sNorm ξ Q H r 0) := by
              simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_left hnorm.2 hau)
        _ = (cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ *
            (ρ ^ (ξ * Q) * Real.exp (ξ * K))) * sNorm ξ Q H r 0 := by ring
        _ ≤ A₁ * sNorm ξ Q H r 0 := mul_le_mul_of_nonneg_right hA hsn
    exact hupper.trans (ENNReal.ofReal_le_ofReal hupper')

end HigherDimLQGMetric
