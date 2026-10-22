import HigherDimLQGMetric.Freq.Local
import HigherDimLQGMetric.Freq.ConstLaw
import HigherDimLQGMetric.LGF.Exists

/-! # Uniform Section 5 frequency package -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Transfer the local frequency estimate to every LGF with the same threshold. -/
private theorem s4c_frequency_uniform
    (hd : 3 ≤ d) {ξ Q : ℝ}
    {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    {U a A₀ ℓ β₀ pstar : ℝ}
    {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    [IsProbabilityMeasure P₀] (h₀ : Ω₀ → DistRd d)
    (hh₀ : IsWholeSpaceLGF h₀ P₀)
    (H : ∀ t u β : ℝ, 0 < t → t < U →
      U - a / A₀ * (U - t) < u → 0 < β →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R : ℝ, 0 < R →
        ENNReal.ofReal β ≤ P₀ (h₀ ⁻¹' GEvent A B ξ Q u β R) →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (3 / 4 : ℝ) * (scaleWin ε R).ncard ≤
          ({j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
            P₀ (h₀ ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} : Set ℤ).ncard) :
    FrequencyLemma d ξ Q A B U a A₀ ℓ β₀ pstar := by
  intro t u β ht htU hKu hβ
  obtain ⟨ε₀, hε₀, Hε⟩ := H t u β ht htU hKu hβ
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω _ P _ h hh R hR hG ε hε hε₀
  have hG₀ : ENNReal.ofReal β ≤ P₀ (h₀ ⁻¹' GEvent A B ξ Q u β R) := by
    rwa [s4c_gEvent_law_eq P P₀ h h₀ hh hh₀ hA hB (by omega : 2 ≤ d) u β hR] at hG
  have hset :
      ({j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
        P₀ (h₀ ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} : Set ℤ) =
      {j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} := by
    ext j
    have hr : 0 < (64 : ℝ) ^ j := zpow_pos (by norm_num) _
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    intro _
    rw [s4c_witEvent_law_eq P P₀ h h₀ hh hh₀ hA hB
      (by omega : 2 ≤ d) U a A₀ ℓ β₀ t hr 0]
  rw [← hset]
  exact Hε R hR hG₀ ε hε hε₀

/-- Proposition 5.4, including all smaller witness probability thresholds. -/
theorem section5Package
    (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hE5 : E5SharpMoment d ξ Q A)
    (U : ℝ) (hU : 0 < U)
    (hupper : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ᵐ ω ∂P, ∀ x y : Rd d,
        (B (h ω)).1 (x, y) ≤ U * (A (h ω)).1 (x, y)) :
    Section5Package d ξ Q A B U := by
  obtain ⟨a, A₀, ℓ, β₀, pstar, ha, haA₀, hℓ, hℓa, hβ₀, hβ₀one,
    hpstar, Hlocal⟩ := s4c_section5_local hd hξ hQ hA hB hE5 U hU hupper
  obtain ⟨Ω₀, m₀, P₀, h₀, hp₀, hh₀⟩ := exists_isWholeSpaceLGF (by omega : 1 ≤ d)
  letI : MeasurableSpace Ω₀ := m₀
  letI : IsProbabilityMeasure P₀ := hp₀
  have H : FrequencyLemma d ξ Q A B U a A₀ ℓ β₀ pstar :=
    s4c_frequency_uniform hd hA hB P₀ h₀ hh₀ (Hlocal P₀ h₀ hh₀)
  refine ⟨a, A₀, ℓ, β₀, pstar, ha, haA₀, hℓ, hℓa,
    hβ₀, hβ₀one, hpstar, ?_⟩
  intro pstar' hpstar' t u β ht htU hKu hβ
  obtain ⟨ε₀, hε₀, Hε⟩ := H t u β ht htU hKu hβ
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω _ P _ h hh R hR hG ε hε hε₀
  have hsubset :
      {j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} ⊆
      {j ∈ scaleWin ε R | ENNReal.ofReal pstar' ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} := by
    intro j hj
    exact ⟨hj.1, (ENNReal.ofReal_le_ofReal hpstar'.2).trans hj.2⟩
  have hfin : ({j ∈ scaleWin ε R | ENNReal.ofReal pstar' ≤
      P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} : Set ℤ).Finite :=
    (s4c_scaleWin_finite hε hR).subset (by intro j hj; exact hj.1)
  have hcard := Set.ncard_le_ncard hsubset hfin
  exact (Hε P h hh R hR hG ε hε hε₀).trans (by exact_mod_cast hcard)

end HigherDimLQGMetric
