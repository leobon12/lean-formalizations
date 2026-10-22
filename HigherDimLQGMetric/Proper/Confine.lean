import HigherDimLQGMetric.Proper.Upper

/-!
# [S] Lemma 2.7: uniform confinement of geodesics

The high-probability sphere barrier and tight diameter bound are combined with the
deterministic geodesic argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- **[S] Lemma 2.7 (confinement)**: uniformly in the base radius, all geodesics with endpoints
in `B_{LR}` stay in a larger Euclidean ball with probability at least `1 - δ`. -/
theorem lemma27_confine (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 < R →
      P {ω | ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧
          IsGeodesicCurve ((D (h ω)).pt ∘ γ) 0 T ∧
          ‖γ 0‖ < L * R ∧ ‖γ T‖ < L * R ∧
          ∃ t ∈ Icc (0 : ℝ) T, A * R ≤ ‖γ t‖} ≤ ENNReal.ofReal δ := by
  have hQ0 : 0 < Q := (Real.sqrt_nonneg _).trans_lt hQ
  have hhalf : 0 < δ / 2 := by linarith
  have hLplus : L < L + 1 := by linarith only [hL]
  obtain ⟨b, hb, hupper⟩ := proper_exists_ball_upper hD P h hh L
    (ENNReal.ofReal_pos.mpr hhalf)
  obtain ⟨A, hLA', _, hsphere⟩ := proper_exists_high_sphere
    (show 2 ≤ d by omega) hξ hQ0 hD P h hh (2 * b) (δ / 2) hhalf (L + 1)
  have hLA : L < A := hLplus.trans hLA'
  have hApos : 0 < A := hL.trans hLA
  refine ⟨A, hApos, fun R hR => ?_⟩
  let E₁ : Set Ω := {ω | ¬ ∀ v : Rd d, ‖v‖ = A * R →
    2 * b * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (0, v)}
  let E₂ : Set Ω := {ω | ¬ ∀ x y : Rd d, ‖x‖ < L * R → ‖y‖ < L * R →
    (D (h ω)).1 (x, y) < b * sNorm ξ Q (h ω) R 0}
  have hsubset : {ω | ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧
          IsGeodesicCurve ((D (h ω)).pt ∘ γ) 0 T ∧
          ‖γ 0‖ < L * R ∧ ‖γ T‖ < L * R ∧
          ∃ t ∈ Icc (0 : ℝ) T, A * R ≤ ‖γ t‖} ⊆ E₁ ∪ E₂ := by
    intro ω hω
    by_contra hnot
    have hS : ∀ v : Rd d, ‖v‖ = A * R →
        2 * b * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (0, v) := by
      by_contra hbad
      exact hnot (Or.inl hbad)
    have hU : ∀ x y : Rd d, ‖x‖ < L * R → ‖y‖ < L * R →
        (D (h ω)).1 (x, y) < b * sNorm ξ Q (h ω) R 0 := by
      by_contra hbad
      exact hnot (Or.inr hbad)
    exact (proper_no_geodesic_escape (D (h ω)) hR hLA (by
      simpa only [mul_assoc] using hS) hU) hω
  have hE₁ : P E₁ < ENNReal.ofReal (δ / 2) := hsphere R hR
  have hE₂ : P E₂ < ENNReal.ofReal (δ / 2) := hupper R hR
  apply le_of_lt
  calc
    P {ω | ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧
        IsGeodesicCurve ((D (h ω)).pt ∘ γ) 0 T ∧
        ‖γ 0‖ < L * R ∧ ‖γ T‖ < L * R ∧
        ∃ t ∈ Icc (0 : ℝ) T, A * R ≤ ‖γ t‖}
        ≤ P (E₁ ∪ E₂) := measure_mono hsubset
    _ ≤ P E₁ + P E₂ := measure_union_le _ _
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add hE₁ hE₂
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

end HigherDimLQGMetric
