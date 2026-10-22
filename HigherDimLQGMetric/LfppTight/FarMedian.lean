import HigherDimLQGMetric.DGZ.AdapterFixed

/-! A positive lower bound for the white-noise median on compact cutoff intervals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

theorem l6a_aHat_lower_far {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (ha₀1 : a₀ < 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ ε ∈ Ico a₀ 1, t ≤ DGZ.aHat P G ξ ε := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hd : 0 < d := by have := hDGZ.dim; omega
  obtain ⟨L, hL0, hbad⟩ := DGZ.adapter_fixed_band_sup hd hDGZ.kernel
    ha₀ ha₀1.le (R := 3) (θ := 1 / 4) (by norm_num) (by norm_num)
  let t : ℝ := Real.exp (-(ξ * L)) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨t, ht, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := ha₀.trans_le hε.1
  have hGε := hG ε ⟨hε0, hε.2⟩
  have hbadε : P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 3,
      L < |G ε z ω|} ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
    hbad hW hε.1 hε.2.le hGε
  let X : Ω → ℝ := fun ω => DGZ.lfppMetric ξ (fun z => G ε z ω) 0 (HigherDimLFPP.e₁ d)
  have hX : AEMeasurable X P :=
    (DGZ.measurable_lfppMetric hGε.continuous hGε.measurable ξ 0
      (HigherDimLFPP.e₁ d)).aemeasurable
  have hsub : {ω | X ω ≤ t} ⊆
      {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 3,
        L < |G ε z ω|} := by
    intro ω hω
    by_contra hg
    change ¬ ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 3,
      L < |G ε z ω| at hg
    have hg' : ¬ ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) (1 + 2),
        L < |G ε z ω| := by simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hg
    have hh := (DGZ.adapter_fixed_good_metric hd hDGZ.xi_pos
      (β := 1 / 2) (R := 1) (L := L)
      (by norm_num) (by norm_num) (by norm_num) hGε ω hg').1
    have htlt : t < Real.exp (-(ξ * L)) := by
      dsimp [t]
      linarith [Real.exp_pos (-(ξ * L))]
    exact (not_le_of_gt (htlt.trans_le hh)) hω
  have hmeasure : P {ω | X ω ≤ t} < (2⁻¹ : ℝ≥0∞) := by
    calc
      P {ω | X ω ≤ t} ≤
          P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 3,
            L < |G ε z ω|} := measure_mono hsub
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := hbadε
      _ < 2⁻¹ := by
        rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4⁻¹ : ℝ≥0∞) by
          rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by ring,
            ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
          norm_num]
        norm_num
  exact (DGZ.adapter_lt_lowerMedian_of_measure_lt hX hmeasure).le

end HigherDimLQGMetric
