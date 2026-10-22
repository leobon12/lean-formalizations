import HigherDimLQGMetric.LfppTight.PointTailLaw
import HigherDimLQGMetric.LfppTight.MedianBridge

/-! A7(4): the corrected lower-median comparison at small cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN e₁)

theorem l6a_median_comparison_small (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε))
    {L : ℝ}
    (hX : ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | L < |l6a_convSphereMean κ ε (h ω)|} ≤ (8⁻¹ : ℝ≥0∞)) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 ≤ M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        m ^ 2 * DGZ.aHat P' G ξ ε ≤ aEps κ ξ ε ∧
        aEps κ ξ ε ≤ M ^ 2 * DGZ.aHat P' G ξ ε := by
  obtain ⟨mB, MB, ε₀, hmB, hMB, hε₀, hB⟩ :=
    l6a_centered_point_tails_dist hL1e hDGZ hAdapter hβ0 hβ
      P h hh P' W hW G hG
      (by norm_num : (0 : ℝ) < 1 / 8)
  let m : ℝ := min mB (Real.exp (-|ξ| * L))
  let M : ℝ := max MB (Real.exp (|ξ| * L))
  have hm : 0 < m := lt_min hmB (Real.exp_pos _)
  have hM : 0 ≤ M := hMB.trans (le_max_left _ _)
  refine ⟨m, M, min ε₀ (1 / 2), hm, hM,
    lt_min hε₀ (by norm_num), ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  have hεB : ε ∈ Ioo (0 : ℝ) ε₀ :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hA : P {ω | Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) < m ∨
      M < Real.exp (ξ * l6a_convSphereMean κ ε (h ω))} ≤ (8⁻¹ : ℝ≥0∞) := by
    refine (measure_mono ?_).trans (hX ε hε1)
    intro ω hω
    by_contra hn
    have hXb : |l6a_convSphereMean κ ε (h ω)| ≤ L := le_of_not_gt hn
    have hprod : |ξ * l6a_convSphereMean κ ε (h ω)| ≤ |ξ| * L := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hXb (abs_nonneg ξ)
    have hlo : Real.exp (-|ξ| * L) ≤
        Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) :=
      Real.exp_le_exp.mpr (by nlinarith [neg_le_of_abs_le hprod])
    have hhi : Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) ≤
        Real.exp (|ξ| * L) :=
      Real.exp_le_exp.mpr (le_of_abs_le hprod)
    rcases hω with hω | hω
    · exact (not_lt_of_ge (le_trans (min_le_right _ _) hlo)) hω
    · exact (not_lt_of_ge (le_trans hhi (le_max_right _ _))) hω
  have hB' : P {ω | (DGZ.aHat P' G ξ ε)⁻¹ *
        HigherDimLFPP.lfppDistOn ξ (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d) < m ∨
      M < (DGZ.aHat P' G ξ ε)⁻¹ *
        HigherDimLFPP.lfppDistOn ξ (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d)} ≤
        (8⁻¹ : ℝ≥0∞) := by
    have he : ENNReal.ofReal (1 / 8 : ℝ) = (8⁻¹ : ℝ≥0∞) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8)]
      norm_num
    refine (measure_mono ?_).trans (by simpa only [he] using hB ε hεB)
    intro ω hω
    rcases hω with hw | hw
    · exact Or.inl (lt_of_lt_of_le hw (min_le_left _ _))
    · exact Or.inr (lt_of_le_of_lt (le_max_left _ _) hw)
  have ha : 0 < DGZ.aHat P' G ξ ε :=
    DGZ.aHat_pos (by have := hDGZ.dim; omega) hW (hG ε hε1) ξ
  exact l6a_aEps_bounds_of_factor_tails hDGZ.dim hDGZ.kernel ξ hε.1
    P h hh ha hm.le hM hA hB'

end HigherDimLQGMetric
