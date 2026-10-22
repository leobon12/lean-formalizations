import HigherDimLQGMetric.Freq.CorEvent

/-! # Corollary 5.5 for finite sets of thresholds -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Optimality plus the frequency lemma yields Corollary 5.5. -/
theorem s4c_cor55_of_frequency
    (hd : 3 ≤ d) {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    {U a A₀ ℓ β₀ pstar : ℝ}
    (ha : 0 < a) (haA₀ : a < A₀)
    (hfreq : FrequencyLemma d ξ Q A B U a A₀ ℓ β₀ pstar)
    (hopt : IsOptUpper d A B U) :
    Cor55 d ξ Q A B U a A₀ ℓ β₀ pstar := by
  obtain ⟨Ω₀, m₀, P₀, h₀, hp₀, hh₀⟩ :=
    exists_isWholeSpaceLGF (by omega : 1 ≤ d)
  letI : MeasurableSpace Ω₀ := m₀
  letI : IsProbabilityMeasure P₀ := hp₀
  intro ts hts
  induction ts using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro R₁ _
      refine ⟨1, by norm_num, ?_⟩
      intro t ht
      simp at ht
  | @insert t ts hnot ih =>
      have ht : 0 < t ∧ t < U := hts t (Finset.mem_insert_self _ _)
      have hts' : ∀ s ∈ ts, 0 < s ∧ s < U := by
        intro s hs
        exact hts s (Finset.mem_insert_of_mem hs)
      obtain ⟨Rs, hRs, Hs⟩ := ih hts'
      let k : ℝ := U - a / A₀ * (U - t)
      let u : ℝ := (k + U) / 2
      have hA₀ : 0 < A₀ := ha.trans haA₀
      have hkU : k < U := by
        dsimp [k]
        have hm : 0 < a / A₀ * (U - t) :=
          mul_pos (div_pos ha hA₀) (sub_pos.mpr ht.2)
        linarith only [hm]
      have hku : k < u := by dsimp [u]; linarith only [hkU]
      have huU : u < U := by dsimp [u]; linarith only [hkU]
      obtain ⟨n, m, hpos⟩ :=
        s4c_optimal_G_positive (ξ := ξ) (Q := Q) P₀ h₀
          (hopt.2 u huU P₀ h₀ hh₀)
      let Rt : ℝ := n + 1
      have hRt : 0 < Rt := by dsimp [Rt]; positivity
      let R₀ : ℝ := max Rs Rt
      have hR₀ : 0 < R₀ := hRs.trans_le (le_max_left _ _)
      refine ⟨R₀, hR₀, ?_⟩
      intro R₁ hR₁
      obtain ⟨εs, hεs, Hεs⟩ := Hs R₁ ((le_max_left _ _).trans hR₁)
      obtain ⟨m', hpos'⟩ := s4c_GEvent_positive_larger
        (ξ := ξ) (Q := Q) P₀ h₀ hRt ((le_max_right _ _).trans hR₁) hpos
      have hR₁pos : 0 < R₁ := hR₀.trans_le hR₁
      obtain ⟨β, hβ, hG₀⟩ := s4c_GEvent_probability_beta
        (ξ := ξ) (Q := Q) P₀ h₀ hR₁pos
        (by positivity : 0 < (1 / (m' + 1 : ℝ))) hpos'
      obtain ⟨εt, hεt, Hεt⟩ := hfreq t u β ht.1 ht.2 hku hβ
      refine ⟨min εs εt, lt_min hεs hεt, ?_⟩
      intro s hs Ω _ P _ h hh ε hε hεmin
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · have hG : ENNReal.ofReal β ≤ P (h ⁻¹' GEvent A B ξ Q u β R₁) := by
          rw [s4c_gEvent_law_eq P P₀ h h₀ hh hh₀ hA hB
            (by omega : 2 ≤ d) u β hR₁pos]
          exact hG₀
        exact Hεt P h hh R₁ hR₁pos hG ε hε (hεmin.trans_le (min_le_right _ _))
      · exact Hεs s hs' P h hh ε hε (hεmin.trans_le (min_le_left _ _))

/-- The requested Section 5 package and Corollary 5.5 with shared constants. -/
theorem section5Package_cor55
    (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hE5 : E5SharpMoment d ξ Q A)
    (U : ℝ) (hU : 0 < U)
    (hopt : IsOptUpper d A B U) :
    ∃ a A₀ ℓ β₀ pstar : ℝ,
      0 < a ∧ a < A₀ ∧ 0 < ℓ ∧ ℓ < a / 100 ∧
      0 < β₀ ∧ β₀ < 1 ∧ 0 < pstar ∧
      ∀ pstar' ∈ Ioc 0 pstar,
        FrequencyLemma d ξ Q A B U a A₀ ℓ β₀ pstar' ∧
        Cor55 d ξ Q A B U a A₀ ℓ β₀ pstar' := by
  obtain ⟨a, A₀, ℓ, β₀, pstar, ha, haA₀, hℓ, hℓa,
    hβ₀, hβ₀one, hpstar, Hfreq⟩ :=
    section5Package hd hξ hQ hA hB hE5 U hU hopt.1
  refine ⟨a, A₀, ℓ, β₀, pstar, ha, haA₀, hℓ, hℓa,
    hβ₀, hβ₀one, hpstar, ?_⟩
  intro pstar' hpstar'
  have hf := Hfreq pstar' hpstar'
  exact ⟨hf, s4c_cor55_of_frequency hd hA hB ha haA₀ hf hopt⟩

end HigherDimLQGMetric
