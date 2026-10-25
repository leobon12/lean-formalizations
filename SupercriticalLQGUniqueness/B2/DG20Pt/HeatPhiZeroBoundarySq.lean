import LQGMetric.Papers.DDDF.S6P29Inc3
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiPathComparison

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.P29WN
  LQGMetric.WhiteNoise LQGMetric.HeatSq LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_zero_boundary_heat_phi_sup_tail
    (U : Set ℂ) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hsub : closure U ⊆ ((LQGMetric.HeatSq.sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (Xh : LQGMetric.BddOn ((LQGMetric.HeatSq.sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) → Ω → ℝ)
        (W : WNSpace → Ω → ℝ) (Y : ℂ → Ω → ℝ),
        IsProbabilityMeasure P ∧
        IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh P ∧
        IsWhiteNoise P W ∧
        IsContVersion (fun z => Xh (heatBdd (LQGMetric.HeatSq.sqOpens (-1) 3)
          ((((2 : ℝ)⁻¹ ^ n) ^ 2) / 2) z)) Y P ∧
        ∀ x : ℝ, 0 ≤ x →
          P {ω | ENNReal.ofReal x ≤ ⨆ z ∈ U,
            ENNReal.ofReal |phiMN W P 0 n z ω - Y z ω|} ≤
            ENNReal.ofReal (C * Real.exp (-c * x ^ 2)) := by
  obtain ⟨C, c, hC, hc, h29⟩ := dddfProp29Sq U hU hK hsub
  refine ⟨C, c, hC, hc, ?_⟩
  intro n hn
  let δ : ℝ := ((2 : ℝ)⁻¹) ^ n
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 / 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    dsimp [δ]
    rw [pow_succ]
    have hj : ((2 : ℝ)⁻¹) ^ j ≤ 1 := by
      apply pow_le_one₀
      · norm_num
      · norm_num
    nlinarith
  have ht : δ ^ 2 ∈ Ioo (0 : ℝ) (1 / 2) := by
    constructor
    · positivity
    · nlinarith
  obtain ⟨Ω, iΩ, P, Xh, W, Y, hP, hG, hW, hY, htail⟩ := h29 (δ ^ 2) ht
  refine ⟨Ω, iΩ, P, Xh, W, Y, hP, hG, hW, ?_, ?_⟩
  · simpa only [δ] using hY
  · intro x hx
    have heq : phiVer W P (Real.sqrt (δ ^ 2)) 1 = phiMN W P 0 n := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hδ]
      simp only [phiMN, pow_zero, δ]
    simpa only [heq] using htail x hx

end SupercriticalLQGUniqueness.B2.DG20Pt
