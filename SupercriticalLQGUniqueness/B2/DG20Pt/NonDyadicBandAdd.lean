import SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicScaleLaw
import LQGMetric.Papers.DDDF.S6Sup
import LQGMetric.Field.WhiteNoiseVersion

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_phi_real_band_add_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∀ᵐ ω ∂P, ∀ x : ℂ,
      phiVer W P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 x ω =
        phiVer W P ((2 : ℝ) ^ (-((n : ℝ) + s)))
          ((2 : ℝ) ^ (-s)) x ω +
        phiVer W P ((2 : ℝ) ^ (-s)) 1 x ω := by
  have ha : 0 < (2 : ℝ) ^ (-((n : ℝ) + s)) := by positivity
  have hab : (2 : ℝ) ^ (-((n : ℝ) + s)) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hbc : (2 : ℝ) ^ (-s) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -s ≤ 0))
  have hHi := isPhiVersion_phiVer hW ha hab
  have hLo := isPhiVersion_phiVer hW (by positivity : 0 < (2 : ℝ) ^ (-s)) hbc
  have hFull := isPhiVersion_phiVer hW ha (hab.trans hbc)
  exact phi_version_add_ae hW ha hab hbc hHi.cont hLo.cont hFull.cont
    hHi.ae_eq hLo.ae_eq hFull.ae_eq

 

theorem dg20_low_band_unit_square_tight
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet,
        |phiVer W P ((2 : ℝ) ^ (-s)) 1 x ω| ≤ M} ≤ ENNReal.ofReal ε := by
  obtain ⟨M, hM, htail⟩ := LQGMetric.DDDF.S6.low_sup_tail hW hε
  refine ⟨M, hM, ?_⟩
  intro s hs0 hs1
  have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-s) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-1 : ℝ) ≤ -s by linarith)
    norm_num at h ⊢
    exact h
  have hone : (2 : ℝ) ^ (-s) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -s ≤ 0))
  exact htail _ hhalf hone

end SupercriticalLQGUniqueness.B2.DG20Pt
