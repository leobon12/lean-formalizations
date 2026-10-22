import HigherDimLQGMetric.Sharp.W3Combine
import LQGMetric.Papers.DFGPS.P3_10Moment

/-! Sharp normalized-diameter tails and moments (E5). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem w3_e5_tail_positive (hd : 3 ≤ d) {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K) (hKU : K ⊆ U) {a : ℝ}
    (ha : a < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 1 ≤ t₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ t : ℝ, t₀ ≤ t →
      P {ω | ENNReal.ofReal t < normDiam ξ Q D (h ω) U K r z} ≤
        ENNReal.ofReal (C * t ^ (-a)) := by
  obtain ⟨q, ζ, p, a', θ, hq0, hqQ, hζ, hζsmall,
    hp, hgap, ha'0, ha'q, hθ0, hθ1, hθp, hγa⟩ :=
      w3_choose_parameters hξ hQ ha
  obtain ⟨T, B, J, C₀, hT, hB, hJ, hC₀, hJoint⟩ :=
    w3_two_parameter_tail hd hξ hQ hq0 hqQ hζ hζsmall hp hgap ha'q
      hD hU hK hKc hKU
  obtain ⟨C, t₀, ht₀, hC, hComb⟩ :=
    w3_combine_tail hξ hp ha'0 hθ0 hθ1 hθp hγa hT hB hJ hC₀
  refine ⟨C, t₀, hC, ht₀, ?_⟩
  intro Ω _ P _ h hh r hr z t ht
  exact hComb P (fun ω => normDiam ξ Q D (h ω) U K r z)
    (fun A hA C hC => hJoint P h hh r hr z A hA C hC) t ht

/-- Corrected Proposition 4.12: any exponent strictly below the sharp
threshold controls the normalized internal-diameter tail uniformly in scale
and location. -/
theorem e5_tail_sharp (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K) (hKU : K ⊆ U) {a : ℝ}
    (ha : a < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) :
    ∃ C t₀ : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ t : ℝ, t₀ ≤ t →
      P {ω | ENNReal.ofReal t < normDiam ξ Q D (h ω) U K r z} ≤
        ENNReal.ofReal (C * t ^ (-a)) := by
  obtain ⟨C, t₀, _, _, htail⟩ :=
    w3_e5_tail_positive hd hξ hQ hD hU hK hKc hKU ha
  exact ⟨C, t₀, htail⟩

/-- Corrected (E5): a uniform moment for every order below the sharp tail
threshold. -/
theorem e5_sharp (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K) (hKU : K ⊆ U) {p : ℝ}
    (hp0 : 0 < p) (hp : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) :
    ∃ M : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      ∫⁻ ω, normDiam ξ Q D (h ω) U K r z ^ p ∂P ≤ ENNReal.ofReal M := by
  let a : ℝ := (p + (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) / 2
  have hpa : p < a := by dsimp [a]; linarith only [hp]
  have ha : a < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ := by
    dsimp [a]
    linarith only [hp]
  obtain ⟨C, t₀, hC, ht₀, htail⟩ :=
    w3_e5_tail_positive hd hξ hQ hD hU hK hKc hKU ha
  let M : ℝ := LQGMetric.DFGPS.momBd p a C t₀
  refine ⟨M, ?_⟩
  intro Ω _ P _ h hh r hr z
  exact LQGMetric.DFGPS.lintegral_rpow_le_of_tail P
    (fun ω => normDiam ξ Q D (h ω) U K r z) hp0 hpa hC ht₀
    (fun t ht => htail P h hh r hr z t ht)

/-- Core interface: the sharp weak class satisfies (E5) without an auxiliary
assumption. -/
theorem e5_sharp_moment (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D) :
    E5SharpMoment d ξ Q D := by
  intro U K hU hK hKc hKU p hp0 hp
  exact e5_sharp hd hξ hQ hD hU hK hKc hKU hp0 hp

end HigherDimLQGMetric
