import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1InputLogTail
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUpperTailFinite

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

universe u

theorem laneC_weighted_around_finite_of_J1_input
    (Qψ : PsiParams) (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
    ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
      (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
      (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
      LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
        Real.exp (C * Real.sqrt (K : ℝ)) →
      ∀ b ∈ T20B.nearIdx K,
        ∀ᵐ ω ∂P,
          ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
            (T20.dyCenter K b) ω)) *
            (lfppContMetric (ξ : ℝ)
              (fun z => psiMN Qψ W P 0 n z ω)
              ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
              (LaneCInputs.sourceAround K m b)
              (LaneCInputs.sourceInner K m b)
              (LaneCInputs.sourceOuter K m b) < ⊤ := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, htail⟩ := hJ1 ξ C p hC hp hp2
  refine ⟨K₀, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb
  let a : ℝ := (K : ℝ) ^ (3 * Qψ.ε₀)
  have ha : 0 < a := by dsimp [a]; positivity
  let Y : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
      (T20.dyCenter K b) ω)) *
      (lfppContMetric (ξ : ℝ)
        (fun z => psiMN Qψ W P 0 n z ω)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)
  let scale : ℝ := (2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)
  have hraw := htail P W hW n K m hK hKn hmK hmlo hmhi hΛ
  have hsingle : ∀ T,
      (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < T →
      P {ω | ENNReal.ofReal (T * scale) < Y ω} ≤
        ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
          Real.exp (-(c₁ * (Real.log T) ^ 2 /
            (a * Real.log (Real.log T))))) := by
    intro T hT
    have hsub : {ω | ENNReal.ofReal (T * scale) < Y ω} ⊆
        {ω | ∃ b' ∈ T20B.nearIdx K,
          ENNReal.ofReal (T * (2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) <
            ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
              (T20.dyCenter K b') ω)) *
              (lfppContMetric (ξ : ℝ)
                (fun z => psiMN Qψ W P 0 n z ω)
                ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                (LaneCInputs.sourceAround K m b')
                (LaneCInputs.sourceInner K m b')
                (LaneCInputs.sourceOuter K m b')} := by
      intro ω hω
      change ENNReal.ofReal (T * scale) < Y ω at hω
      exact ⟨b, hb, by simpa only [Y, scale, mul_assoc] using hω⟩
    calc
      P {ω | ENNReal.ofReal (T * scale) < Y ω} ≤
          P {ω | ∃ b' ∈ T20B.nearIdx K,
            ENNReal.ofReal (T * (2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) <
              ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
                (T20.dyCenter K b') ω)) *
                (lfppContMetric (ξ : ℝ)
                  (fun z => psiMN Qψ W P 0 n z ω)
                  ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                  (LaneCInputs.sourceAround K m b')
                  (LaneCInputs.sourceInner K m b')
                  (LaneCInputs.sourceOuter K m b')} := measure_mono hsub
      _ ≤ _ := by simpa only [a] using hraw T hT
  have htailY : ∀ t, max (Real.log
      ((2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)))) 3 + 1 < t →
      P {ω | ENNReal.ofReal (scale * Real.exp t) < Y ω} ≤
        ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
          Real.exp (-(c₁ / a) * t ^ 2 / Real.log t)) := by
    intro t ht
    have hbase : 0 < (2 : ℝ) ^
        ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) := by positivity
    have hT : (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) <
        Real.exp t := by
      rw [← Real.exp_log hbase]
      apply Real.exp_lt_exp.mpr
      linarith [le_max_left (Real.log
        ((2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)))) (3 : ℝ)]
    have h := hsingle (Real.exp t) hT
    have heq : -(c₁ * t ^ 2 / (a * Real.log t)) =
        -(c₁ / a) * t ^ 2 / Real.log t := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    simpa only [Real.log_exp, heq, mul_comm] using h
  have hfin := laneC_ae_finite_of_logsq_upper_tail P Y
    (scale := scale)
    (xMin := max (Real.log
      ((2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)))) 3 + 1)
    (N := c₀) (C := (5 : ℝ) ^ K) (c := c₁ / a)
    hc₀.le (by positivity) (div_pos hc₁ ha) htailY
  simpa only [Y] using hfin

end SupercriticalLQGUniqueness.B2.DG20Conc
