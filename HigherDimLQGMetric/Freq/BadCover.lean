import HigherDimLQGMetric.Freq.Translate
import HigherDimLQGMetric.Events.ShellCover

/-! The probability half of the bad-scale shell-cover argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open scoped ENNReal

variable {d : ℕ}

/-- If fewer than three quarters of the scales have witness probability
`pstar`, the remaining shells meet the hypotheses of Lemma 5.2. -/
theorem s4c_bad_scales_cover
    (hd : 2 ≤ d) {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (U a A₀ ℓ β₀ t δ pstar p C ε₁ L R ε : ℝ)
    (hps : 0 ≤ pstar) (hcost : δ + pstar ≤ 1 - p)
    (hregular : ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      ENNReal.ofReal (1 - δ) ≤
        P (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z))
    (hcover : ∀ R ε : ℝ, 0 < R → 0 < ε → ε < ε₁ → ∀ T : Finset ℤ,
      (∀ j ∈ T, j ∈ scaleWin ε R) →
      (1 / 4 : ℝ) * Real.logb 64 ε⁻¹ - 1 ≤ T.card →
      (∀ j ∈ T, ∀ z : Rd d,
        ENNReal.ofReal p ≤ P (h ⁻¹'
          (RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j) z \
            WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) z))) →
      P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (L * R),
        ∃ j ∈ T, ∃ k : Fin d → ℤ,
          ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
          h ω ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j)
            (latPt ((64 : ℝ) ^ j / (100 * d)) k) \
              WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j)
                (latPt ((64 : ℝ) ^ j / (100 * d)) k)} ≤
        ENNReal.ofReal (C * ε))
    (hR : 0 < R) (hε : 0 < ε) (hε64 : ε < (1 / 64 : ℝ))
    (hε₁ : ε < ε₁)
    (hfail : (({j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} :
          Set ℤ).ncard : ℝ) <
        (3 / 4 : ℝ) * (scaleWin ε R).ncard) :
    ∃ T : Finset ℤ,
      (∀ j ∈ T, j ∈ scaleWin ε R) ∧
      (1 / 4 : ℝ) * Real.logb 64 ε⁻¹ - 1 ≤ T.card ∧
      P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (L * R),
        ∃ j ∈ T, ∃ k : Fin d → ℤ,
          ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
          h ω ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j)
            (latPt ((64 : ℝ) ^ j / (100 * d)) k) \
              WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j)
                (latPt ((64 : ℝ) ^ j / (100 * d)) k)} ≤
        ENNReal.ofReal (C * ε) := by
  let S := scaleWin ε R
  let G : Set ℤ := {j ∈ S | ENNReal.ofReal pstar ≤
    P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)}
  have hS : S.Finite := s4c_scaleWin_finite hε hR
  have hBad : (S \ G).Finite := hS.sdiff
  let T : Finset ℤ := hBad.toFinset
  have hT : ∀ j ∈ T, j ∈ S := by
    intro j hj
    exact (hBad.mem_toFinset.mp hj).1
  have hcount : (1 / 4 : ℝ) * Real.logb 64 ε⁻¹ - 1 ≤ T.card := by
    have hb := s4c_bad_scale_count hS
      (fun j => ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)) hfail
    have hw := s4c_scaleWin_count hε hε64 hR
    have hcard : ((S \ G).ncard : ℝ) = (T.card : ℝ) := by
      simp only [T, Set.ncard_eq_toFinset_card _ hBad]
    rw [hcard] at hb
    linarith only [hb, hw]
  have hprob : ∀ j ∈ T, ∀ z : Rd d,
      ENNReal.ofReal p ≤ P (h ⁻¹'
        (RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j) z \
          WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) z)) := by
    intro j hj z
    have hjBad : j ∈ S \ G := hBad.mem_toFinset.mp hj
    have hjNo : P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0) <
        ENNReal.ofReal pstar := lt_of_not_ge (by
      intro hge
      exact hjBad.2 ⟨hjBad.1, hge⟩)
    have hr : 0 < (64 : ℝ) ^ j := zpow_pos (by norm_num) _
    have hcenter := s4c_witEvent_law_center P h hh hA hB hd
      U a A₀ ℓ β₀ t hr z
    have hreg := hregular ((64 : ℝ) ^ j) hr z
    have hdiff := s4c_prob_diff P
      (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j) z)
      (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) z)
      hps hcost hreg (by rw [hcenter]; exact hjNo)
    simpa only [preimage_sdiff] using hdiff
  exact ⟨T, hT, hcount, hcover R ε hR hε hε₁ T hT hcount hprob⟩

end HigherDimLQGMetric
