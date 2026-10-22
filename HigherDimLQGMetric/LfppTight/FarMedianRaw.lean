import HigherDimLQGMetric.LfppTight.FarFieldMetric
import HigherDimLQGMetric.LfppTight.MedianPos

/-! The normalized LGF LFPP median stays uniformly positive away from zero cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6a_aEps_lower_far {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {a : ℝ} (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ ∀ ε ∈ Ico a 1, t ≤ aEps κ ξ ε := by
  obtain ⟨L, hL0, hbad⟩ := l6a_far_field_sup_tail hd κ hκ P h hh
    (a := a) (R := Real.sqrt d + 1) (θ := 1 / 4) ha (by norm_num)
  let t : ℝ := Real.exp (-(ξ * L)) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨t, ht, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := ha.trans_le hε.1
  let X : Ω → ℝ := fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)
  have hXm : AEMeasurable X P :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ P h hh hε0
  have hcont := l10a_ae_continuous_convMollify hd κ hκ P h hh hε0
  have hsub : ∀ᵐ ω ∂P, X ω ≤ t →
      ∃ η ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) (Real.sqrt d + 1),
        L < |convMollify κ η (h ω) z| := by
    filter_upwards [hcont] with ω hc hω
    by_contra hn
    have hfield : ∀ z ∈ closedBall (0 : Rd d) (Real.sqrt d + 1),
        |convMollify κ ε (h ω) z| ≤ L := by
      intro z hz
      exact le_of_not_gt (fun hlt => hn ⟨ε, ⟨hε.1, hε.2.le⟩, z, hz, hlt⟩)
    have hlow := l6a_fieldBound_unitLower (by omega : 0 < d) hc
      hξ hfield
    have htlt : t < Real.exp (-(ξ * L)) := by
      dsimp [t]
      linarith [Real.exp_pos (-(ξ * L))]
    exact (not_le_of_gt (htlt.trans_le hlow)) hω
  have hmeasure : P {ω | X ω ≤ t} < (2⁻¹ : ℝ≥0∞) := by
    calc
      P {ω | X ω ≤ t} ≤
          P {ω | ∃ η ∈ Icc a 1,
            ∃ z ∈ closedBall (0 : Rd d) (Real.sqrt d + 1),
              L < |convMollify κ η (h ω) z|} := measure_mono_ae hsub
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := hbad
      _ < 2⁻¹ := by
        rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4⁻¹ : ℝ≥0∞) by
          rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by ring,
            ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
          norm_num]
        norm_num
  rw [l6a_aEps_eq_sample_lowerMedian hd κ hκ ξ hε0 P h hh,
    l6a_lowerMedian_eq_lowerQuantile_map P X hXm]
  exact (DGZ.adapter_lt_lowerMedian_of_measure_lt hXm hmeasure).le

end HigherDimLQGMetric
