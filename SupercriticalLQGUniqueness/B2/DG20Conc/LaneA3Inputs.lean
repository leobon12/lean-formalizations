import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSelection
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import LQGMetric.Papers.DDDF.T20CDefs

 











set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Classical

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Inputs

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
open SupercriticalLQGUniqueness.B2.DG20Conc

 



def PersistentVisit {Ω : Type*} (γ : ℕ → ℕ → Ω → ℝ → ℂ)
    (n K : ℕ) (b : ℤ × ℤ) (s : ℝ) : Set Ω :=
  {ω | ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
    (ω, ω) ∈ T20C.visSet (γ j) n K b s}

 


def C1GlobalPhysicalResampling (Qψ : PsiParams) : Prop :=
  ∀ (ξ : ℝ), ∃ K₀ : ℕ,
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W),
    ∀ n K m : ℕ, K₀ ≤ K → K ≤ n → m + 1 ≤ K →
      (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
      (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
    ∃ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Qψ W P (((j : ℝ) + 1)⁻¹) (γ j)) ∧
      (∀ b ∈ T20B.nearIdx K,
        MeasurableSet (PersistentVisit γ n K b
          (LaneCInputs.sourceRadius K m)) ∧
        ∀ᵐ z ∂(P.prod P),
          (rectLen ξ (fun x => psiMN Qψ W P 0 n x z.1 -
            T20B.blkKn Qψ W P K n b x z.1 +
            T20B.blkKn Qψ W P K n b x z.2) (rectAB 1 1)).toReal ≤
          T20C.lenPsi ξ Qψ W P n z.1 +
            if z.1 ∈ PersistentVisit γ n K b
                (LaneCInputs.sourceRadius K m) then
              ((lfppContMetric ξ
                (fun x => psiMN Qψ W P 0 n x z.1)
                ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)).aroundDist
                (LaneCInputs.sourceAround K m b)
                (LaneCInputs.sourceInner K m b)
                (LaneCInputs.sourceOuter K m b)).toReal
            else 0)

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Inputs
