import HigherDimLQGMetric.Core.Defs

/-!
# Finite-centre shell decoupling

The finite union bound used in the good-scale covering argument. This is the
part of MA6 P4 that does not depend on the geometry of the grid.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- A finite union of failures of shell events, using the Appendix A input. -/
theorem goodScales_finite {d : ℕ} (hA1 : ShellInputA1 d) {A : ℝ} (hA : 0 < A) :
    ∃ p : ℝ, p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ (F : Finset (Rd d)) (r : ℕ → ℝ),
        (∀ i, 0 < r i) → (∀ i, r (i + 1) ≤ (1 / 2 : ℝ) * r i) →
      ∀ (E : Rd d → ℝ → Set Ω),
        (∀ w ∈ F, ∀ i, AEEventIn P (fieldSigma0 h (ann w ((1 / 4) * r i)
          (4 * r i))) (E w (r i))) →
        (∀ w ∈ F, ∀ i, ENNReal.ofReal p ≤ P (E w (r i))) →
      ∀ n : ℕ, 0 < n →
        P {ω | ∃ w ∈ F, ∀ i ∈ Finset.range n, ω ∉ E w (r i)} ≤
          (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * n)) := by
  classical
  obtain ⟨p, hp, H⟩ := hA1 (1 / 4) 4 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) A (1 / 2) hA (by norm_num)
    (by norm_num)
  refine ⟨p, hp, ?_⟩
  intro Ω _ P _ h hh F r hr hratio E hE hpE n hn
  have hone (w : Rd d) (hw : w ∈ F) :
      P {ω | ∀ i ∈ Finset.range n, ω ∉ E w (r i)} ≤
        ENNReal.ofReal (Real.exp (-A * n)) := by
    have H' := H P h hh w r hr hratio (fun i => E w (r i))
      (fun i => hE w hw i) (fun i => hpE w hw i) n
    refine (measure_mono ?_).trans H'
    intro ω hω
    change (((Finset.range n).filter (fun i => ω ∈ E w (r i))).card : ℝ) <
      (1 / 2 : ℝ) * n
    have hempty : (Finset.range n).filter (fun i => ω ∈ E w (r i)) = ∅ := by
      exact Finset.filter_eq_empty_iff.mpr (fun i hi => hω i hi)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  calc
    P {ω | ∃ w ∈ F, ∀ i ∈ Finset.range n, ω ∉ E w (r i)}
        = P (⋃ w ∈ F, {ω | ∀ i ∈ Finset.range n, ω ∉ E w (r i)}) := by
            congr 1
            ext ω
            simp only [mem_ofPred_eq, mem_iUnion]
            constructor
            · rintro ⟨w, hw, h⟩
              exact ⟨w, hw, h⟩
            · rintro ⟨w, hw, h⟩
              exact ⟨w, hw, h⟩
    _ ≤ ∑ w ∈ F, P {ω | ∀ i ∈ Finset.range n, ω ∉ E w (r i)} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ F, ENNReal.ofReal (Real.exp (-A * n)) := by
      exact Finset.sum_le_sum fun w hw => hone w hw
    _ = (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * n)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

end HigherDimLQGMetric
