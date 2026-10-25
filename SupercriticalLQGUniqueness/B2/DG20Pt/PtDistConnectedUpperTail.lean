import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainProb
import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalNormalizedTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_connected_upper_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) :
    ∃ (k₀ N : ℕ) (C Clam c₀ c₁ : ℝ),
      1 ≤ k₀ ∧ 0 < C ∧ 0 < Clam ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, k₀ ≤ n →
        ∀ T L β : ℝ, 3 < T → 0 ≤ L → 0 < β →
        0 < (ξ : ℝ) * Q - 3 * ζ - 2 * β →
          let q := (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))
          let Kc := 2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)
          P {ω | ¬ lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω) U z w ≤
              (N + 1 : ℝ≥0∞) * ENNReal.ofReal
                (Kc * T ^ 2 * Real.exp L * lambdaN ξ W P n * q ^ k₀)} ≤
          (N + 1 : ℝ≥0∞) *
            (ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
            2 * ENNReal.ofReal
              (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
                (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
                  (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β))))) := by
  obtain ⟨K, V, hK, hKU, hV, hconv, k₀, hk₀, hcollar,
    N, p, hp0, hpN, hpKV, hpstep, hterminal⟩ :=
    pt_dist_chain_geometry hU hUc hz hw
  obtain ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, htail⟩ :=
    pt_dist_local_normalized_upper_tail_of_inputs
      hPerc hExp ξ Q hQ ζ hζ V hV hconv 1 (le_refl _)
  refine ⟨k₀, N, C, Clam, c₀, c₁, hk₀, hC, hClam, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n hkn T L β hT hL hβ hα
  dsimp
  let A : ℝ≥0∞ := ENNReal.ofReal
    ((2 * Clam + 4 + C + 6 * (2 + C) /
        (1 - (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β)))) *
      T ^ 2 * Real.exp L * lambdaN ξ W P n *
      ((2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))) ^ k₀)
  let b : ℝ≥0∞ := ENNReal.ofReal
      (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
      2 * ENNReal.ofReal
        (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
          (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
            (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β))))
  have hedge (j : ℕ) (hj : j ≤ N) :
      P {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
          U (p j) (p (j + 1)) ≤ A} ≤ b := by
    have hj₁ : j ≤ N + 1 := by omega
    have hj₂ : j + 1 ≤ N + 1 := by omega
    have hjK := (hpKV j hj₁).1
    have hjK' := (hpKV (j + 1) hj₂).1
    have hjV := (hpKV j hj₁).2
    have hjV' := (hpKV (j + 1) hj₂).2
    have htermj := hterminal n hkn j hj₁
    have htermj' := hterminal n hkn (j + 1) hj₂
    exact htail P W hW n k₀ hk₀ hkn U (p j) (p (j + 1))
      hjV hjV' (hpstep j hj).le
      (fun k hk x hx => hcollar k hk (p j) hjK x hx)
      (fun k hk x hx => hcollar k hk (p (j + 1)) hjK' x hx)
      (fun _ hx => (htermj hx).2)
      (fun _ hx => (htermj' hx).2)
      (fun _ hx => (htermj hx).1)
      (fun _ hx => (htermj' hx).1)
      T L β hT hL hβ hα
  have hchain := pt_dist_chain_failure_measure_le P (ξ : ℝ)
    (fun ω y => phiMN W P 0 n y ω) U p N A b hedge
  simpa only [hp0, hpN, A, b] using hchain

end SupercriticalLQGUniqueness.B2.DG20Pt
