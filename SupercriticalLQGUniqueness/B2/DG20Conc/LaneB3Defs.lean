import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs

 











set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

def B3FixedPSubaddTails (Qψ : PsiParams) (ξ : Ioi (0 : ℝ)) (Q p : ℝ) : Prop :=
  ∀ ζ C : ℝ, 0 < ζ → 0 < C →
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
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

 

def B3FixedPMedianStep (ξ : Ioi (0 : ℝ)) (Q p : ℝ) : Prop :=
  ∀ ζ C : ℝ, 0 < ζ → 0 < C →
    ∃ K₀ : ℕ, ∃ D : ℝ, 0 < D ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ n K : ℕ, K₀ ≤ K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        D⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
          lambdaN (ξ : ℝ) W P (n - K) ≤ lambdaN (ξ : ℝ) W P n ∧
        lambdaN (ξ : ℝ) W P n ≤
          D * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (K : ℝ)) *
            lambdaN (ξ : ℝ) W P (n - K)

 
theorem b3ChosenCutoffSubaddTails_iff (Qψ : PsiParams) :
    LaneBInputs.B3ChosenCutoffSubaddTails.{u} Qψ ↔
      ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
        ∀ p : ℝ, 0 < p → p < 2⁻¹ → B3FixedPSubaddTails.{u} Qψ ξ Q p :=
  ⟨fun h ξ Q hQ p hp hp2 ζ C hζ hC => h ξ Q hQ ζ C p hζ hC hp hp2,
    fun h ξ Q hQ ζ C p hζ hC hp hp2 => h ξ Q hQ p hp hp2 ζ C hζ hC⟩

 
theorem b3ConditionalMedianStep_iff :
    LaneBInputs.B3ConditionalMedianStep.{u} ↔
      ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
        ∀ p : ℝ, 0 < p → p < 2⁻¹ → B3FixedPMedianStep.{u} ξ Q p :=
  ⟨fun h ξ Q hQ p hp hp2 ζ C hζ hC => h ξ Q hQ ζ C p hζ hC hp hp2,
    fun h ξ Q hQ ζ C p hζ hC hp hp2 => h ξ Q hQ p hp hp2 ζ C hζ hC⟩

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs
