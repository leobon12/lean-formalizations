import HigherDimLQGMetric.Freq.NoRatio

/-! Probability bridge from the deterministic frequency contradiction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory Metric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open scoped ENNReal

variable {d : ℕ}

/-- A ratio witness forces at least one of the confinement, modulus, or
shell-cover exceptions. -/
theorem s4c_G_prob_le_exceptions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hproper : ∀ᵐ ω ∂P, ProperSpace (A (h ω)).Space)
    (U a A₀ ℓ β₀ t u β R ε α Lcov : ℝ)
    (hratio : ∀ᵐ ω ∂P, ∀ x y : Rd d,
      (B (h ω)).1 (x, y) ≤ U * (A (h ω)).1 (x, y))
    (hℓ : 0 < ℓ) (hℓa : ℓ < a / 100) (haA₀ : 0 < a ∧ a < A₀)
    (ht : 0 < t) (htU : t < U) (hKu : U - a / A₀ * (U - t) < u)
    (hR : 0 < R) (hε : 0 < ε) (hε1 : ε < 1 / 8)
    (hεβ : 8 * ε < β)
    (hgap : 2 * U * (8 * ε) ^ α <
      (u - (U - a / A₀ * (U - t))) * β)
    (T : Finset ℤ) (hT : ∀ j ∈ T, j ∈ scaleWin ε R) :
    P (h ⁻¹' GEvent A B ξ Q u β R) ≤
      P {ω | ∃ (γ : ℝ → Rd d) (L : ℝ), 0 ≤ L ∧
        IsGeodesicCurve ((A (h ω)).pt ∘ γ) 0 L ∧
        ‖γ 0‖ < 3 * R ∧ ‖γ L‖ < 3 * R ∧
        ∃ s ∈ Icc (0 : ℝ) L, Lcov * R ≤ ‖γ s‖} +
      P {ω | ∃ x y : Rd d, ‖x‖ < 3 * R ∧ ‖y‖ < 3 * R ∧
        ‖x - y‖ ≤ 8 * ε * R ∧
        (8 * ε) ^ α * sNorm ξ Q (h ω) R 0 < (A (h ω)).1 (x, y)} +
      P {ω | ¬ ∀ w ∈ ball (0 : Rd d) (Lcov * R),
        ∃ j ∈ T, ∃ k : Fin d → ℤ,
          ‖w - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
          h ω ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j)
            (latPt ((64 : ℝ) ^ j / (100 * d)) k) \
              WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j)
                (latPt ((64 : ℝ) ^ j / (100 * d)) k)} := by
  let E₁ : Set Ω := {ω | ∃ (γ : ℝ → Rd d) (L : ℝ), 0 ≤ L ∧
    IsGeodesicCurve ((A (h ω)).pt ∘ γ) 0 L ∧
    ‖γ 0‖ < 3 * R ∧ ‖γ L‖ < 3 * R ∧
    ∃ s ∈ Icc (0 : ℝ) L, Lcov * R ≤ ‖γ s‖}
  let E₂ : Set Ω := {ω | ∃ x y : Rd d, ‖x‖ < 3 * R ∧ ‖y‖ < 3 * R ∧
    ‖x - y‖ ≤ 8 * ε * R ∧
    (8 * ε) ^ α * sNorm ξ Q (h ω) R 0 < (A (h ω)).1 (x, y)}
  let E₃ : Set Ω := {ω | ¬ ∀ w ∈ ball (0 : Rd d) (Lcov * R),
    ∃ j ∈ T, ∃ k : Fin d → ℤ,
      ‖w - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
      h ω ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j)
        (latPt ((64 : ℝ) ^ j / (100 * d)) k) \
          WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j)
            (latPt ((64 : ℝ) ^ j / (100 * d)) k)}
  have hsubset : h ⁻¹' GEvent A B ξ Q u β R ≤ᵐ[P] E₁ ∪ E₂ ∪ E₃ := by
    filter_upwards [hA.length P h hh.isLGFPlusCont, hproper, hratio]
      with ω hlen hprop hrat hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨hn₁, hn₂⟩, hn₃⟩ := hn
    haveI : ProperSpace (A (h ω)).Space := hprop
    exact (s4c_no_G_of_cover A B ξ Q U a A₀ ℓ β₀ t u β R ε α Lcov
      (h ω) hlen hrat hℓ hℓa haA₀ ht htU hKu hR hε hε1 hεβ
      hgap T hT hn₁ hn₂ (by simpa only [E₃, mem_ofPred_eq, not_not] using hn₃)) hω
  calc
    P (h ⁻¹' GEvent A B ξ Q u β R) ≤ P (E₁ ∪ E₂ ∪ E₃) :=
      measure_mono_ae hsubset
    _ ≤ P E₁ + P E₂ + P E₃ := by
      calc
        P (E₁ ∪ E₂ ∪ E₃) ≤ P (E₁ ∪ E₂) + P E₃ := measure_union_le _ _
        _ ≤ P E₁ + P E₂ + P E₃ := by gcongr; exact measure_union_le _ _

end HigherDimLQGMetric
