import HigherDimLQGMetric.LfppTight.FarMedianRaw

/-! The LFPP median is uniformly bounded above on cutoff intervals away from zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6a_aEps_upper_far {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {a : ℝ} (ha : 0 < a) :
    ∃ T : ℝ, 0 < T ∧ ∀ ε ∈ Ico a 1, aEps κ ξ ε ≤ T := by
  obtain ⟨L, hL0, hbad⟩ := l6a_far_field_sup_tail hd κ hκ P h hh
    (a := a) (R := 2) (θ := 1 / 4) ha (by norm_num)
  let T : ℝ := Real.exp (|ξ| * L)
  have hT : 0 < T := Real.exp_pos _
  refine ⟨T, hT, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := ha.trans_le hε.1
  let X : Ω → ℝ := fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)
  have hXm : AEMeasurable X P :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ P h hh hε0
  have hcont := l10a_ae_continuous_convMollify hd κ hκ P h hh hε0
  have hsub : ∀ᵐ ω ∂P, T < X ω →
      ∃ η ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) 2,
        L < |convMollify κ η (h ω) z| := by
    filter_upwards [hcont] with ω hc hω
    by_contra hn
    have hfield : ∀ z ∈ closedBall (0 : Rd d) (1 + 1),
        |convMollify κ ε (h ω) z| ≤ L := by
      intro z hz
      exact le_of_not_gt (fun hlt => hn ⟨ε, ⟨hε.1, hε.2.le⟩, z,
        by simpa only [one_add_one_eq_two] using hz, hlt⟩)
    have h0 : (0 : Rd d) ∈ closedBall 0 1 := by simp
    have he : e₁ d ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall, dist_zero_right, HigherDimLFPP.norm_e₁ (by omega : 0 < d)]
    have hhigh := l6a_fieldBound_localUpper hc (ξ := ξ) (R := 1) hfield
      0 h0 (e₁ d) he
    have hnorm : ‖(0 : Rd d) - e₁ d‖ = 1 := by
      rw [zero_sub, norm_neg, HigherDimLFPP.norm_e₁ (by omega : 0 < d)]
    change T < DGZ.lfppMetric ξ (convMollify κ ε (h ω)) 0 (e₁ d) at hω
    rw [hnorm, mul_one] at hhigh
    exact (not_lt_of_ge hhigh) hω
  have hcompl : P {ω | T < X ω} ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
    (measure_mono_ae hsub).trans hbad
  have hhalf : (2⁻¹ : ℝ≥0∞) ≤ P {ω | X ω ≤ T} := by
    have hs : {ω | T < X ω} = {ω | X ω ≤ T}ᶜ := by ext ω; simp
    rw [hs] at hcompl
    apply DGZ.adapter_half_le_measure_of_compl_le
    convert hcompl using 1
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by ring,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [l6a_aEps_eq_sample_lowerMedian hd κ hκ ξ hε0 P h hh,
    l6a_lowerMedian_eq_lowerQuantile_map P X hXm]
  exact DGZ.adapter_lowerMedian_le_of_half_le hXm hhalf

end HigherDimLQGMetric
