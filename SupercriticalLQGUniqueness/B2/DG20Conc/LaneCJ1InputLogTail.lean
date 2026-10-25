import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1LogTail
import LQGMetric.Papers.DDDF.S6Mul

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

universe u

theorem laneC_positive_log_tail_of_J1_input
    (Qψ : PsiParams) (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ t : ℝ, 0 < t →
          (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < Real.exp (t / 2) →
          P {ω | ∃ b ∈ T20B.nearIdx K,
            t ≤ Real.log (max 1
              (((ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
                  (T20.dyCenter K b) ω)) *
                  (lfppContMetric (ξ : ℝ)
                    (fun z => psiMN Qψ W P 0 n z ω)
                    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                    (LaneCInputs.sourceAround K m b)
                    (LaneCInputs.sourceInner K m b)
                    (LaneCInputs.sourceOuter K m b)).toReal) /
                ((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K))))} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (t / 2) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (t / 2))))) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, htail⟩ := hJ1 ξ C p hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K m hK hKn hmK hmlo hmhi hΛ t ht hT
  let scale : ℝ := (2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact mul_pos (by positivity) (lambdaN_pos hW (n - K))
  have hraw := htail P W hW n K m hK hKn hmK hmlo hmhi hΛ
  have hsub : {ω | ∃ b ∈ T20B.nearIdx K,
      t ≤ Real.log (max 1
        (((ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
          (T20.dyCenter K b) ω)) *
          (lfppContMetric (ξ : ℝ)
            (fun z => psiMN Qψ W P 0 n z ω)
            ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
            (LaneCInputs.sourceAround K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b)).toReal) / scale))} ⊆
      {ω | ∃ b ∈ T20B.nearIdx K,
        ENNReal.ofReal (Real.exp (t / 2) * scale) <
          ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
            (T20.dyCenter K b) ω)) *
          (lfppContMetric (ξ : ℝ)
            (fun z => psiMN Qψ W P 0 n z ω)
            ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
            (LaneCInputs.sourceAround K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b)} := by
    intro ω ⟨b, hb, hlog⟩
    refine ⟨b, hb, ?_⟩
    let V : ℝ≥0∞ :=
      ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
        (T20.dyCenter K b) ω)) *
        (lfppContMetric (ξ : ℝ)
          (fun z => psiMN Qψ W P 0 n z ω)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b)
    have hreal : Real.exp (t / 2) * scale < V.toReal := by
      
      have hmaxpos : 0 < max 1 (V.toReal / scale) :=
        lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hexp : Real.exp t ≤ max 1 (V.toReal / scale) := by
        rw [← Real.exp_log hmaxpos]
        exact Real.exp_le_exp.mpr hlog
      have hmaxgt : 1 < max 1 (V.toReal / scale) :=
        (Real.one_lt_exp_iff.mpr ht).trans_le hexp
      have hratio : 1 ≤ V.toReal / scale := by
        rcases le_total (V.toReal / scale) 1 with hle | hle
        · simp only [max_eq_left hle] at hmaxgt
          exact False.elim (lt_irrefl _ hmaxgt)
        · exact hle
      rw [max_eq_right hratio] at hexp
      have hfirst : scale * Real.exp t ≤ V.toReal := by
        simpa only [mul_comm] using (le_div_iff₀ hscale).mp hexp
      have hsecond : scale * Real.exp (t / 2) < scale * Real.exp t := by
        apply mul_lt_mul_of_pos_left _ hscale
        apply Real.exp_lt_exp.mpr
        linarith
      simpa only [mul_comm] using hsecond.trans_le hfirst
    have hpos : 0 ≤ Real.exp (t / 2) * scale := (mul_pos (Real.exp_pos _) hscale).le
    have hENN : ENNReal.ofReal (Real.exp (t / 2) * scale) <
        ENNReal.ofReal V.toReal :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).2 hreal
    exact hENN.trans_le ENNReal.ofReal_toReal_le
  calc
    P {ω | ∃ b ∈ T20B.nearIdx K,
      t ≤ Real.log (max 1
        (((ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
          (T20.dyCenter K b) ω)) *
          (lfppContMetric (ξ : ℝ)
            (fun z => psiMN Qψ W P 0 n z ω)
            ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
            (LaneCInputs.sourceAround K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b)).toReal) / scale))}
      ≤ P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal (Real.exp (t / 2) * scale) <
            ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
              (T20.dyCenter K b) ω)) *
            (lfppContMetric (ξ : ℝ)
              (fun z => psiMN Qψ W P 0 n z ω)
              ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
              (LaneCInputs.sourceAround K m b)
              (LaneCInputs.sourceInner K m b)
              (LaneCInputs.sourceOuter K m b)} := measure_mono hsub
    _ ≤ _ := by
      simpa only [scale, mul_assoc, neg_div, neg_mul, Real.log_exp] using
        hraw (Real.exp (t / 2)) hT

end SupercriticalLQGUniqueness.B2.DG20Conc
