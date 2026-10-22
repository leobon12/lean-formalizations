import HigherDimLQGContinuity.MomentsW1.CoarseTail
import LQGMetric.Papers.DDDF.FieldExpTail

/-! # Exponential moment of the coarse envelope -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

universe u

open HigherDimLFPP
open HigherDimLQGMetric.DGZ

/-- Moment bound from a specified coarse tail constant. -/
theorem wnZR_expMoment_of_tail {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (CZ : ℝ) (_hCZ : 0 < CZ)
    (htail : ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R u : ℝ, 1 ≤ R → 0 ≤ u →
          P {ω | u < wnZR (d := d) R Q CZ H ω} ≤
            ENNReal.ofReal (K * Real.exp (-(Real.sqrt (2 * d) / 2) * u)))
    {l : ℝ} (hl : 0 < l)
    (hlcrit : l ≤ Real.sqrt (2 * d) / 4) :
    ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R : ℝ, 1 ≤ R →
          ∫⁻ ω, ENNReal.ofReal (Real.exp (l * wnZR (d := d) R Q CZ H ω)) ∂P ≤
            ENNReal.ofReal C := by
  intro Q hQ
  obtain ⟨K, hK, htail⟩ := htail Q hQ
  let r : ℝ := Real.sqrt (2 * d) / 2
  let κ₀ : ℝ := r - l
  let B : ℝ := l * K * Real.exp r
  let C : ℝ := Real.exp r + K * Real.exp r + 1
  have hsqrt : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  have hr : 0 < r := by dsimp [r]; positivity
  have hlr : l ≤ r / 2 := by dsimp [r] at *; linarith
  have hκ₀ : 0 < κ₀ := by dsimp [κ₀]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W H hH R hR
  letI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  have hZmeas : Measurable (wnZR (d := d) R Q CZ H) :=
    measurable_wnZR_of_realization hH R Q CZ
  have hX0 : ∀ ω, 0 ≤ wnZR (d := d) R Q CZ H ω := fun _ => ENNReal.toReal_nonneg
  have htailReal (t : ℝ) (ht : 1 < t) :
      P.real {ω | t ≤ wnZR (d := d) R Q CZ H ω} ≤
        K * Real.exp (-r * (t - 1)) := by
    have hu : 0 ≤ t - 1 := by linarith
    have hsub : {ω | t ≤ wnZR (d := d) R Q CZ H ω} ⊆
        {ω | t - 1 < wnZR (d := d) R Q CZ H ω} := by
      intro ω hω
      dsimp at *
      linarith
    have hmeas := (measure_mono hsub).trans (htail hH R (t - 1) hR hu)
    have hfin : ENNReal.ofReal (K * Real.exp (-r * (t - 1))) ≠ ⊤ := ENNReal.ofReal_ne_top
    exact (ENNReal.toReal_mono hfin hmeas).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have htailDDDF (t : ℝ) (ht : 1 < t) :
      l * Real.exp (l * t) * P.real {ω | t ≤ wnZR (d := d) R Q CZ H ω} ≤
        B * Real.exp (-κ₀ * t) := by
    have hmul := mul_le_mul_of_nonneg_left (htailReal t ht)
      (mul_nonneg hl.le (Real.exp_pos (l * t)).le)
    have hexp : Real.exp (l * t) * Real.exp (-r * (t - 1)) =
        Real.exp r * Real.exp (-κ₀ * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [κ₀]
      ring
    calc
      l * Real.exp (l * t) * P.real {ω | t ≤ wnZR (d := d) R Q CZ H ω}
          ≤ l * Real.exp (l * t) * (K * Real.exp (-r * (t - 1))) := hmul
      _ = l * K * (Real.exp (l * t) * Real.exp (-r * (t - 1))) := by ring
      _ = B * Real.exp (-κ₀ * t) := by rw [hexp]; dsimp [B]; ring
  have hmoment := LQGMetric.DDDF.lintegral_exp_le_of_tail hX0
    hZmeas.aemeasurable hl (by norm_num : (0 : ℝ) ≤ 1) hκ₀ hB htailDDDF
  have hκle : l ≤ κ₀ := by dsimp [κ₀]; linarith
  have hexpneg : Real.exp (-κ₀) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hratio : B / κ₀ ≤ K * Real.exp r := by
    apply (div_le_iff₀ hκ₀).2
    dsimp [B]
    nlinarith [mul_nonneg (sub_nonneg.mpr hκle) (mul_nonneg hK.le (Real.exp_pos r).le)]
  have hscalar : Real.exp l + B * Real.exp (-κ₀) / κ₀ ≤ C := by
    have hfirst : Real.exp l ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
    have hsecond : B * Real.exp (-κ₀) / κ₀ ≤ B / κ₀ := by
      apply (div_le_div_iff_of_pos_right hκ₀).2
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hexpneg)]
    dsimp [C]
    linarith
  exact hmoment.trans (ENNReal.ofReal_le_ofReal (by simpa using hscalar))

/-- The coarse envelope has a uniform exponential moment up to one quarter of the
critical Gaussian slope. -/
theorem wnZR_expMoment {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {l : ℝ} (hl : 0 < l)
    (hlcrit : l ≤ Real.sqrt (2 * d) / 4) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R : ℝ, 1 ≤ R →
          ∫⁻ ω, ENNReal.ofReal (Real.exp (l * wnZR (d := d) R Q CZ H ω)) ∂P ≤
            ENNReal.ofReal C := by
  obtain ⟨CZ,hCZ,htail⟩ := wnZR_tail hd hκ
  exact ⟨CZ,hCZ,wnZR_expMoment_of_tail hd CZ hCZ htail hl hlcrit⟩

end HigherDimLQGContinuity
