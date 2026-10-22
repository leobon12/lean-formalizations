import HigherDimLQGMetric.DGZ.NondegDistanceCompare

/-! The high quantile is bounded by a constant times the median at all large indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_lambda_eventually {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧
      ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
            IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
              δ * aQ P H ξ n q ≤ aQ P H ξ n 2⁻¹ := by
  obtain ⟨q₀, hq₀0, hq₀1, hsmall⟩ := nd_smallShell_nondeg_uniform h
  refine ⟨q₀, hq₀0, hq₀1, ?_⟩
  intro q hq hq1
  have hd0 : 0 < d := by have hh := h.dim; omega
  let r : ℝ := 1 / (10 * Real.sqrt d + 4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : r * (10 * Real.sqrt d) ≤ 1 := by
    dsimp [r]
    have hden : 0 < 10 * Real.sqrt d + 4 := by positivity
    calc
      (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d) ≤
          (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d + 4) :=
        mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = 1 := by field_simp
  have hr1 : 2 * r ≤ 1 := by
    dsimp [r]
    have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hden : 0 < 10 * Real.sqrt d + 4 := by positivity
    have hh : (2 : ℝ) / (10 * Real.sqrt d + 4) ≤ 1 :=
      (div_le_iff₀ hden).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh
  obtain ⟨δ, hδ, N, hN⟩ :=
    hsmall q hq hq1 r hr hrd (1 / 4) (by norm_num) (by norm_num)
  refine ⟨δ, hδ, N, ?_⟩
  intro Ω _ P W H hH n hn
  let D : Ω → ℝ := fun ω => lfppDistance d ξ (fun z => H n z ω)
  let x : ℝ := δ * aQ P H ξ n q
  have hbad : P {ω | D ω ≤ x} ≤ (1 / 4 : ℝ≥0∞) := by
    calc
      P {ω | D ω ≤ x} ≤
        P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ x} :=
          measure_mono (fun ω hω =>
            (nd_across_le_lfppDistance hd0 ((hH.band n).continuous ω) hr hr1).trans hω)
      _ ≤ 1 / 4 := hN Ω P W H hH n hn
  by_contra hle
  have hlt : aQ P H ξ n 2⁻¹ < x := lt_of_not_ge hle
  have hDm : Measurable D := (hH.band n).measurable_lfppDistance ξ
  have hhalf : (2⁻¹ : ℝ≥0∞) ≤ P {ω | D ω ≤ x} := by
    have : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
    have hh := (LQGMetric.le_measure_Iic_iff_lowerQuantile_le
      (μ := P.map D) (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
      (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).2 hlt.le
    rwa [Measure.map_apply hDm measurableSet_Iic] at hh
  have : (2⁻¹ : ℝ≥0∞) ≤ 1 / 4 := hhalf.trans hbad
  norm_num at this

end HigherDimLQGMetric.DGZ
