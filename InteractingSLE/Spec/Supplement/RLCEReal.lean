/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.ThresholdVisit

/-!
# The real-contact completion between the seeds, per datum, at a visited constant interval

Packet PROVE-RLC-E, piece (iii) of `RLC.RetainedChartRealCompletionStatement` (PROVE-RLC-D, "What remains" 4), the
case of an untouched interval between the two chart seeds. Source: W5's real local frame (supplement pp. 535–536: "G2a
supplies complete proper ordered reference curves […] The same G7a single-density comparison transfers the full fresh
stopped pair law"), with Lemma 5.1 of the shortcut note (R52: a visited middle interval has an admissible height).

In the chart of a retained pair the second flow starts at `0` (angle `θ₂`), the first at `w > 0` (angle `θ₁ < θ₂`).
Let the datum be constant `C` on an interval `(a, b) ⊂ (0, w)` free of its jumps (an untouched original interval: by
`RLC.IsUntouchedWord` its height is the original one). If either flow visits `(a, b)` strictly before its lifetime, then
`C` is admissible (`RLC.ae_admissible_of_visit'`, now unconditional), so the datum agrees near `(a, b)` with the
explicit G2a word `g2aData κ θ₁ θ₂ 0 w (midWord κ θ₁ θ₂ a b C)`, and G2a with G3 (`RLC.ae_isChartCompletable_of_middle`)
makes every pair of prefixes inside a buffer `V` over `(a, b)` completable.

* **`RLC.ae_isChartCompletable_of_visit`** (conditional on the named G2a and G3, PROVE-RLC-C/RLC-A).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

/-- **Completability at a visited untouched interval between the seeds (one datum).** Chart datum `c` (jumps `J`),
angle-`θ₁` flow `Γ₁` from `w > 0` and angle-`θ₂` flow `Γ₂` from `0`; `c = C` on `(a, b) ⊂ (0, w)`, which contains no
jump candidate; `V` a bounded open buffer whose closure meets `ℝ` only over `(a, b)`. Almost surely, if either flow
visits `(a, b)` strictly before its lifetime, every pair of prefixes within the exit times from `V` is completable. -/
theorem ae_isChartCompletable_of_visit (hG2a : G2aReferenceStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ w a b C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (ha : 0 < a) (hab : a < b) (hbw : b < w)
    {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J)
    (hJ : ∀ y ∈ Ioo a b, y ∉ J) (hcC : ∀ y ∈ Ioo a b, c y = C)
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hVO : ∀ z ∈ closure V, z.im = 0 → z.re ∈ Ioo a b)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c J)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c J w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ((∃ t : ℝ≥0, (t : ℝ≥0∞) < U₁ x ∧ ∃ y ∈ Ioo a b, Γ₁ x t = y) ∨
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < U₂ x ∧ ∃ y ∈ Ioo a b, Γ₂ x t = y)) →
      ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime V (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) ≤ exitTime V (Γ₂ x) (U₂ x) → IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  by_cases hadm : -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ
  · -- an admissible height: the datum is the explicit G2a word on `(a, b)`
    have hcO : ∀ x ∈ Ioo a b, c x = g2aData κ θ₁ θ₂ 0 w (midWord κ θ₁ θ₂ a b C) x := fun x hx => by
      have h0 : ¬ x < 0 := not_lt.2 (ha.trans hx.1).le
      have hw : x < w := hx.2.trans hbw
      have hna : ¬ x < a := not_lt.2 hx.1.le
      simp only [g2aData, midWord, h0, hw, hna, hx.2, ite_false, ite_true]
      exact hcC x hx
    have hJO : ∀ x ∈ Ioo a b, x ∈ J ↔ x ∈ insert 0 (insert w ({a, b} : Finset ℝ)) := fun x hx => by
      refine iff_of_false (hJ x hx) ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(ha.trans hx.1).ne', (hx.2.trans hbw).ne, hx.1.ne', hx.2.ne⟩
    filter_upwards [ae_isChartCompletable_of_middle hG2a hG3 hκ hκ4 hθ ha hab hbw hadm hc isOpen_Ioo hcO hJO hV
      hVb hVO Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂] with x hx _
    exact hx
  · -- an inadmissible height: Lemma 5.1 excludes every visit before the lifetimes
    filter_upwards [ae_admissible_of_visit' hκ hκ4 hθ hc ha.le hbw.le (fun y hy _ => hcC y hy) Q₀ H₀ hH Γ₁ Γ₂
      U₁ U₂ h₁ h₂] with x hx hvis
    exact absurd (hx hvis) hadm

end RLC

end InteractingSLE
