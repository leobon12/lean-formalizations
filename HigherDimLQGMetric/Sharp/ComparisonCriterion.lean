import HigherDimLQGMetric.Sharp.CompareCover
import HigherDimLQGMetric.Sharp.ShellMeas

/-!
# Field-measurable comparison criterion

The shell decoupling input gives almost-sure grid covers. The deterministic
sphere-chain estimate then compares arbitrary length metrics pathwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem gridPts_countable (s : ℝ) : (gridPts (d := d) s).Countable := by
  have heq : gridPts (d := d) s =
      range (fun m : Fin d → ℤ => WithLp.toLp 2 (fun i => s * (m i : ℝ))) := by
    ext w
    simp only [gridPts, mem_ofPred_eq, mem_range]
    exact exists_congr fun m => eq_comm
  rw [heq]
  exact countable_range _

/-- [1] Prop. 3.13 in the `AEEventIn` form. The only probabilistic
input is the exact Appendix A shell estimate `ShellInputA1`. -/
theorem comparison_criterion_aeLength (hA1 : ShellInputA1 d) (hd : 3 ≤ d) :
    ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (D₁ D₂ : Ω → ContMetric d) (C : ℝ), 0 < C →
        (∀ᵐ ω ∂P, (D₁ ω).IsLength) → (∀ᵐ ω ∂P, (D₂ ω).IsLength) →
        (∀ z r, 0 < r → ∃ E : Set Ω,
          AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) E ∧
          E =ᵐ[P] {ω | sphereDiam (D₂ ω) z r ≤
            ENNReal.ofReal C * acrossDist (D₁ ω) z (r / 2) r} ∧
          p₀ ≤ (P E).toReal) →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, (D₂ ω).1 (u, v) ≤ C * (D₁ ω).1 (u, v) := by
  classical
  obtain ⟨p₀, hp₀, Hp⟩ := goodScales_ae_eventually hA1 hd
  refine ⟨p₀, hp₀, ?_⟩
  intro Ω _ P _ h hh D₁ D₂ C hC hLen₁ _hLen₂ H
  let E : Rd d → ℝ → Set Ω := fun z r =>
    if hr : 0 < r then Classical.choose (H z r hr) else ∅
  have hspec (z : Rd d) (r : ℝ) (hr : 0 < r) :
      AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) (E z r) ∧
      E z r =ᵐ[P] {ω | sphereDiam (D₂ ω) z r ≤
        ENNReal.ofReal C * acrossDist (D₁ ω) z (r / 2) r} ∧
      p₀ ≤ (P (E z r)).toReal := by
    simpa [E, hr] using Classical.choose_spec (H z r hr)
  have hEm (z : Rd d) (r : ℝ) (hr : 0 < r) :
      AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) (E z r) :=
    (hspec z r hr).1
  have hpE (z : Rd d) (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal p₀ ≤ P (E z r) := by
    have hfin : P (E z r) ≠ ∞ :=
      ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (prob_le_one)
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).2 (hspec z r hr).2.2
  have hGoodAE := Hp P h hh E hEm hpE
  have hEqAE : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)), ∀ k : ℕ,
        ω ∈ E w (1 / 2 ^ k) ↔
        sphereDiam (D₂ ω) w (1 / 2 ^ k) ≤
          ENNReal.ofReal C * acrossDist (D₁ ω) w ((1 / 2 ^ k) / 2) (1 / 2 ^ k) := by
    refine ae_all_iff.2 fun n => (ae_ball_iff (gridPts_countable _)).2 fun w hw =>
      ae_all_iff.2 fun k => ?_
    exact Filter.eventuallyEqSet_iff.mp (hspec w (1 / 2 ^ k) (by positivity)).2.1
  filter_upwards [hGoodAE, hEqAE, hLen₁] with ω hgood heq hlen
  apply compare_of_eventual_grids hd (D₁ ω) (D₂ ω) hlen hC
  filter_upwards [hgood] with n hn
  intro w hw
  obtain ⟨k, hlow, hupp, hEwk⟩ := hn w hw
  exact ⟨k, hlow, hupp, (heq n w hw.1 k).mp hEwk⟩

/-- The pathwise-length form of the field-measurable criterion. -/
theorem comparison_criterion_ae (hA1 : ShellInputA1 d) (hd : 3 ≤ d) :
    ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (D₁ D₂ : Ω → ContMetric d) (C : ℝ), 0 < C →
        (∀ ω, (D₁ ω).IsLength) → (∀ ω, (D₂ ω).IsLength) →
        (∀ z r, 0 < r → ∃ E : Set Ω,
          AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) E ∧
          E =ᵐ[P] {ω | sphereDiam (D₂ ω) z r ≤
            ENNReal.ofReal C * acrossDist (D₁ ω) z (r / 2) r} ∧
          p₀ ≤ (P E).toReal) →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, (D₂ ω).1 (u, v) ≤ C * (D₁ ω).1 (u, v) := by
  obtain ⟨p₀, hp₀, H⟩ := comparison_criterion_aeLength hA1 hd
  refine ⟨p₀, hp₀, ?_⟩
  intro Ω _ P _ h hh D₁ D₂ C hC hL₁ hL₂ hE
  exact H P h hh D₁ D₂ C hC (Filter.Eventually.of_forall hL₁)
    (Filter.Eventually.of_forall hL₂) hE

/-- [1] Prop. 3.13 with events explicitly measurable for the recentered
shell restriction. -/
theorem comparison_criterion (hA1 : ShellInputA1 d) (hd : 3 ≤ d) :
    ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (D₁ D₂ : Ω → ContMetric d) (C : ℝ), 0 < C →
        (∀ ω, (D₁ ω).IsLength) → (∀ ω, (D₂ ω).IsLength) →
        (∀ z r, 0 < r → ∃ E : Set Ω,
          MeasurableSet[shellSigma h z r (1 / 4) 4] E ∧
          E =ᵐ[P] {ω | sphereDiam (D₂ ω) z r ≤
            ENNReal.ofReal C * acrossDist (D₁ ω) z (r / 2) r} ∧
          p₀ ≤ (P E).toReal) →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, (D₂ ω).1 (u, v) ≤ C * (D₁ ω).1 (u, v) := by
  obtain ⟨p₀, hp₀, H⟩ := comparison_criterion_ae hA1 hd
  refine ⟨p₀, hp₀, ?_⟩
  intro Ω _ P _ h hh D₁ D₂ C hC hL₁ hL₂ hE
  exact H P h hh D₁ D₂ C hC hL₁ hL₂ (by
    intro z r hr
    obtain ⟨E, hEm, hEq, hp⟩ := hE z r hr
    exact ⟨E, shellSigma_event_aeEventIn (by omega : 2 ≤ d) hh z hr E hEm,
      hEq, hp⟩)

end HigherDimLQGMetric
