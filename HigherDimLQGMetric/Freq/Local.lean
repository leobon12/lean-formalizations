import HigherDimLQGMetric.Freq.SmallEps
import HigherDimLQGMetric.Modulus.Lemma26
import HigherDimLQGMetric.Proper.Confine
import HigherDimLQGMetric.Events.RegularProof

/-! Proposition 5.4 on one probability space. The next file moves its
threshold to all LGF realizations by the event-law lemmas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory Metric LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open scoped ENNReal

variable {d : ℕ}

/-- The §5 constants give Proposition 5.4 with a threshold that may initially
depend on the LGF realization. -/
theorem s4c_section5_local
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
    ∃ a A₀ ℓ β₀ pstar : ℝ,
      0 < a ∧ a < A₀ ∧ 0 < ℓ ∧ ℓ < a / 100 ∧
      0 < β₀ ∧ β₀ < 1 ∧ 0 < pstar ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ t u β : ℝ, 0 < t → t < U → U - a / A₀ * (U - t) < u → 0 < β →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R : ℝ, 0 < R →
        ENNReal.ofReal β ≤ P (h ⁻¹' GEvent A B ξ Q u β R) →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (3 / 4 : ℝ) * (scaleWin ε R).ncard ≤
          ({j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
            P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} : Set ℤ).ncard := by
  obtain ⟨p, hp, hsc⟩ := shellCover (by omega : 1 ≤ d)
    (1 / 4) 1 (by norm_num) (by norm_num)
  let δ : ℝ := (1 - p) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hp]
  obtain ⟨a, A₀, ℓ, β₀, ha, haA₀, hℓ, hℓa, hβ₀, hβ₀one, Hreg⟩ :=
    regularEvents_of_sharp (by omega : 2 ≤ d) hA hB U δ hU hδ
  refine ⟨a, A₀, ℓ, β₀, δ, ha, haA₀, hℓ, hℓa,
    hβ₀, hβ₀one, hδ, ?_⟩
  intro Ω _ P _ h hh t u β ht htU hKu hβ
  let α : ℝ := ξ * (Q - Real.sqrt (2 * d)) / 2
  have hξQ : 0 < ξ * (Q - Real.sqrt (2 * d)) :=
    mul_pos hξ (sub_pos.mpr hQ)
  have hα : 0 < α := by dsimp [α]; linarith only [hξQ]
  have hα' : α < ξ * (Q - Real.sqrt (2 * d)) := by
    dsimp [α]
    linarith only [hξQ]
  obtain ⟨Ac, hAc, Hconf⟩ := lemma27_confine hd hξ hQ hA P h hh
    3 (β / 10) (by norm_num) (by positivity)
  let Lcov : ℝ := Ac + 4
  have hLcov : 0 < Lcov := by dsimp [Lcov]; linarith only [hAc]
  have hAcLe : Ac ≤ Lcov := by dsimp [Lcov]; linarith
  obtain ⟨aexp, haexp, Cmod, Hmod⟩ :=
    lemma26_modulus hd hξ hQ hA hE5 P h hh α hα hα' 3 (by norm_num)
  obtain ⟨Ccov, ε₁, hε₁, Hcov⟩ := hsc Lcov 1 hLcov (by norm_num)
  let gap : ℝ := u - (U - a / A₀ * (U - t))
  have hgap : 0 < gap := sub_pos.mpr hKu
  obtain ⟨ε₀, hε₀, Hε⟩ := s4c_choose_epsilon hα haexp hβ hU hgap
    (le_max_right Cmod 0) (le_max_right Ccov 0) hε₁
  refine ⟨ε₀, hε₀, ?_⟩
  intro R hR hG ε hε hεsmall
  by_contra hfreq
  have hfail : (({j ∈ scaleWin ε R | ENNReal.ofReal δ ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} :
          Set ℤ).ncard : ℝ) <
        (3 / 4 : ℝ) * (scaleWin ε R).ncard := lt_of_not_ge hfreq
  obtain ⟨hε64, hε8, hεβ, hε₁small, herror, hgapε⟩ := Hε ε hε hεsmall
  have hsc' : ∀ R ε : ℝ, 0 < R → 0 < ε → ε < ε₁ → ∀ T : Finset ℤ,
      (∀ j ∈ T, j ∈ scaleWin ε R) →
      (1 / 4 : ℝ) * Real.logb 64 ε⁻¹ - 1 ≤ T.card →
      (∀ j ∈ T, ∀ z : Rd d,
        ENNReal.ofReal p ≤ P (h ⁻¹'
          (RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j) z \
            WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) z))) →
      P {ω | ¬ ∀ x ∈ ball (0 : Rd d) (Lcov * R),
        ∃ j ∈ T, ∃ k : Fin d → ℤ,
          ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
          h ω ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j)
            (latPt ((64 : ℝ) ^ j / (100 * d)) k) \
              WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j)
                (latPt ((64 : ℝ) ^ j / (100 * d)) k)} ≤
        ENNReal.ofReal (Ccov * ε) := by
    intro R' ε' hR' hε' hε₁' T hT hcount hprob
    simpa only [Set.mem_preimage, Real.rpow_one] using Hcov P h hh
      (fun z r => h ⁻¹' (RegEvent A B ξ Q U a A₀ ℓ β₀ r z \
        WitEvent A B ξ Q U a A₀ ℓ β₀ t r z))
      (hA.isShellLocal_regDiffWit P h hh hB (by omega) U a A₀ ℓ β₀ t)
      R' ε' hR' hε' hε₁' T hT hcount hprob
  obtain ⟨T, hT, _, hPcov⟩ :=
    s4c_bad_scales_cover (by omega : 2 ≤ d) hA hB P h hh
      U a A₀ ℓ β₀ t δ δ p Ccov ε₁ Lcov R ε hδ.le
      (by dsimp [δ]; linarith) (Hreg P h hh) hsc' hR hε hε64 hε₁small hfail
  have hPconf : P {ω | ∃ (γ : ℝ → Rd d) (L : ℝ), 0 ≤ L ∧
      IsGeodesicCurve ((A (h ω)).pt ∘ γ) 0 L ∧
      ‖γ 0‖ < 3 * R ∧ ‖γ L‖ < 3 * R ∧
      ∃ s ∈ Icc (0 : ℝ) L, Lcov * R ≤ ‖γ s‖} ≤ ENNReal.ofReal (β / 10) := by
    refine (measure_mono ?_).trans (Hconf R hR)
    rintro ω ⟨γ, L, hL, hgeo, h0, h1, s, hs, hfar⟩
    exact ⟨γ, L, hL, hgeo, h0, h1, s, hs,
      (mul_le_mul_of_nonneg_right hAcLe hR.le).trans hfar⟩
  have hPmod : P {ω | ∃ x y : Rd d, ‖x‖ < 3 * R ∧ ‖y‖ < 3 * R ∧
      ‖x - y‖ ≤ 8 * ε * R ∧
      (8 * ε) ^ α * sNorm ξ Q (h ω) R 0 < (A (h ω)).1 (x, y)} ≤
      ENNReal.ofReal (Cmod * (8 * ε) ^ aexp) :=
    Hmod R hR (8 * ε) ⟨by positivity, by linarith only [hε8]⟩
  have hPbound := s4c_G_prob_le_exceptions P h hh hA
    (lemma27_proper hd hξ hQ hA P h hh)
    U a A₀ ℓ β₀ t u β R ε α Lcov (hupper P h hh)
    hℓ hℓa ⟨ha, haA₀⟩ ht htU hKu hR hε hε8 hεβ hgapε T hT
  have hPsum : P (h ⁻¹' GEvent A B ξ Q u β R) ≤
      ENNReal.ofReal (β / 10) +
        ENNReal.ofReal (Cmod * (8 * ε) ^ aexp) +
          ENNReal.ofReal (Ccov * ε) := by
    exact hPbound.trans (add_le_add (add_le_add hPconf hPmod) hPcov)
  have hCmod : Cmod * (8 * ε) ^ aexp ≤ max Cmod 0 * (8 * ε) ^ aexp :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos (by positivity) _).le
  have hCcov : Ccov * ε ≤ max Ccov 0 * ε :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
  have hPsum' : P (h ⁻¹' GEvent A B ξ Q u β R) ≤
      ENNReal.ofReal (β / 10) +
        ENNReal.ofReal (max Cmod 0 * (8 * ε) ^ aexp) +
          ENNReal.ofReal (max Ccov 0 * ε) := by
    exact hPsum.trans (add_le_add (add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal hCmod)) (ENNReal.ofReal_le_ofReal hCcov))
  have hsmall : ENNReal.ofReal (β / 10) +
      ENNReal.ofReal (max Cmod 0 * (8 * ε) ^ aexp) +
        ENNReal.ofReal (max Ccov 0 * ε) < ENNReal.ofReal β := by
    have hm : 0 ≤ max Cmod 0 * (8 * ε) ^ aexp :=
      mul_nonneg (le_max_right _ _) (Real.rpow_pos_of_pos (by positivity) _).le
    have hc : 0 ≤ max Ccov 0 * ε := mul_nonneg (le_max_right _ _) hε.le
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ β / 10) hm,
      ← ENNReal.ofReal_add (by linarith : 0 ≤ β / 10 + max Cmod 0 * (8 * ε) ^ aexp) hc]
    exact (ENNReal.ofReal_lt_ofReal_iff hβ).2 herror
  exact (not_lt_of_ge hG) (hPsum'.trans_lt hsmall)

end HigherDimLQGMetric
