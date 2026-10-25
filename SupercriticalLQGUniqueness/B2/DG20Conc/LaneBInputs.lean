import SupercriticalLQGUniqueness.B2.Iface.Statements
import LQGMetric.Papers.DDDF.LenObs
import LQGMetric.Papers.DDDF.PsiField

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs

open LQGMetric.DDDF LQGMetric.WhiteNoise

 


def B3ChosenCutoffSubaddTails (Qψ : PsiParams) : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
  ∀ ζ C p : ℝ, 0 < ζ → 0 < C → 0 < p → p < 2⁻¹ →
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ n K : ℕ, K₀ ≤ K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ T : ℝ, (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < T →
          P {ω | lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω <
            T⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - K)} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (Real.log T) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (Real.log T))))) ∧
          P {ω | T * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - K) <
                lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (Real.log T) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (Real.log T)))))

 


def B3ConditionalMedianStep : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
  ∀ ζ C p : ℝ, 0 < ζ → 0 < C → 0 < p → p < 2⁻¹ →
    ∃ K₀ : ℕ, ∃ D : ℝ, 0 < D ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ n K : ℕ, K₀ ≤ K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        D⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
          lambdaN (ξ : ℝ) W P (n - K) ≤ lambdaN (ξ : ℝ) W P n ∧
        lambdaN (ξ : ℝ) W P n ≤
          D * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
            lambdaN (ξ : ℝ) W P (n - K)

 

def B4ExactExponentRelation : Prop := Iface.DG20ExponentRelation

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs
