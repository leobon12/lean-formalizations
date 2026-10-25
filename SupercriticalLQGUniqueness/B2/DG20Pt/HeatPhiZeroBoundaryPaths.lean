import SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiZeroBoundarySq

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.P29WN
  LQGMetric.WhiteNoise LQGMetric.HeatSq LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_zero_boundary_heat_phi_sup_tail_and_path_lengths
    (U : Set ℂ) (hU : IsOpen U) (hcl : IsCompact (closure U))
    (hsub : closure U ⊆ ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (Xh : BddOn ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) → Ω → ℝ)
        (W : WNSpace → Ω → ℝ) (Y : ℂ → Ω → ℝ),
        IsProbabilityMeasure P ∧
        IsZBGFFProcessExt (sqOpens (-1) 3) Xh P ∧
        IsWhiteNoise P W ∧
        IsContVersion (fun z => Xh (heatBdd (sqOpens (-1) 3)
          ((((2 : ℝ)⁻¹ ^ n) ^ 2) / 2) z)) Y P ∧
        (∀ a : ℝ, 0 ≤ a →
          P {ω | ENNReal.ofReal a ≤ ⨆ z ∈ U,
            ENNReal.ofReal |phiMN W P 0 n z ω - Y z ω|} ≤
            ENNReal.ofReal (C * Real.exp (-c * a ^ 2))) ∧
        ∀ (ξ : ℝ) (K : Set ℂ), IsCompact K → K ⊆ U →
          ∀ (γ : ℝ → ℂ), (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) →
          ∀ a : ℝ, 0 < a →
            P {ω | ¬ (
              lfppLen ξ (fun z => Y z ω) γ ≤
                ENNReal.ofReal (Real.exp (|ξ| * a)) *
                  lfppLen ξ (fun z => phiMN W P 0 n z ω) γ ∧
              lfppLen ξ (fun z => phiMN W P 0 n z ω) γ ≤
                ENNReal.ofReal (Real.exp (|ξ| * a)) *
                  lfppLen ξ (fun z => Y z ω) γ)} ≤
              ENNReal.ofReal (C * Real.exp (-c * a ^ 2)) := by
  obtain ⟨C, c, hC, hc, hcouple⟩ :=
    dg20_zero_boundary_heat_phi_sup_tail U hU hcl hsub
  refine ⟨C, c, hC, hc, ?_⟩
  intro n hn
  obtain ⟨Ω, iΩ, P, Xh, W, Y, hP, hG, hW, hY, htail⟩ := hcouple n hn
  refine ⟨Ω, iΩ, P, Xh, W, Y, hP, hG, hW, hY, htail, ?_⟩
  intro ξ K _hK hKU γ hγ a ha
  have hsubset :
      {ω | ¬ (
        lfppLen ξ (fun z => Y z ω) γ ≤
          ENNReal.ofReal (Real.exp (|ξ| * a)) *
            lfppLen ξ (fun z => phiMN W P 0 n z ω) γ ∧
        lfppLen ξ (fun z => phiMN W P 0 n z ω) γ ≤
          ENNReal.ofReal (Real.exp (|ξ| * a)) *
            lfppLen ξ (fun z => Y z ω) γ)} ⊆
      {ω | ENNReal.ofReal a ≤ ⨆ z ∈ U,
        ENNReal.ofReal |phiMN W P 0 n z ω - Y z ω|} := by
    intro ω hbad
    by_contra hsup
    have hsup_lt : (⨆ z ∈ U,
        ENNReal.ofReal |phiMN W P 0 n z ω - Y z ω|) < ENNReal.ofReal a :=
      lt_of_not_ge hsup
    have hcomp : ∀ z ∈ K,
        |Y z ω - phiMN W P 0 n z ω| ≤ a := by
      intro z hz
      have hle : ENNReal.ofReal |phiMN W P 0 n z ω - Y z ω| ≤
          (⨆ z ∈ U, ENNReal.ofReal |phiMN W P 0 n z ω - Y z ω|) :=
        le_iSup_of_le z (le_iSup_of_le (hKU hz) le_rfl)
      have hreal := (ENNReal.ofReal_lt_ofReal_iff ha).mp (lt_of_le_of_lt hle hsup_lt)
      rw [abs_sub_comm]
      exact hreal.le
    exact hbad (dg20_heat_phi_lfppLen_compare_on_compact ξ
      (fun z => Y z ω) (fun z => phiMN W P 0 n z ω) K γ a hγ hcomp)
  exact (measure_mono hsubset).trans (htail a ha.le)

end SupercriticalLQGUniqueness.B2.DG20Pt
