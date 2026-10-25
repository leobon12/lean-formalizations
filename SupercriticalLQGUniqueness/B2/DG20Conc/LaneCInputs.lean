import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs
import LQGMetric.Papers.DDDF.T20BBlocks
import LQGMetric.Papers.DDDF.LenObs
import LQGMetric.Papers.DDDF.D5T
import LQGMetric.LFPP.ContMetric
import LQGMetric.Topo.Disconnect

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

def sourceRadius (K m : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (K - m)

def sourceAround (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  {z | sourceRadius K m < dist z (T20.dyCenter K b) ∧
    dist z (T20.dyCenter K b) < 2 * sourceRadius K m}

def sourceInner (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  sphere (T20.dyCenter K b) (sourceRadius K m)

def sourceOuter (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  sphere (T20.dyCenter K b) (2 * sourceRadius K m)

 
def B3SubaddTails.{u} (Qψ : PsiParams) : Prop :=
  LaneBInputs.B3ChosenCutoffSubaddTails.{u} Qψ

 




def J1ChosenCutoffAroundTail (Qψ : PsiParams) : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ C p : ℝ, 0 < C → 0 < p → p < 2⁻¹ →
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ T : ℝ, (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < T →
          P {ω | ∃ b ∈ T20B.nearIdx K,
            ENNReal.ofReal (T * (2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) <
              ENNReal.ofReal (Real.exp (-(ξ : ℝ) * phiMN W P 0 K
                (T20.dyCenter K b) ω)) *
                (lfppContMetric (ξ : ℝ)
                  (fun z => psiMN Qψ W P 0 n z ω)
                  ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                  (sourceAround K m b) (sourceInner K m b)
                    (sourceOuter K m b)} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (Real.log T) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (Real.log T)))))

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
