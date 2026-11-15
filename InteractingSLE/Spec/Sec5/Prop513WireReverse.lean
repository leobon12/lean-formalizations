/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513WireCharts
import InteractingSLE.Spec.Sec5.Prop513WireRegularity

/-! # The remaining probabilistic reverse-visit law, with chart geometry proved

The input is in physical E coordinates for the actual pulled-back Q prefixes.
Starting points, chart domains, pole avoidance, conversion of counterflow time,
and positivity of the visits are proved by the deterministic adapters.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Sec4 Prop513Target Prop513Schedule Prop513TreeExtract

/-- The physical E-coordinate prefix in its original Q clock. -/
def stripTree {Ω : Type*} (q : ℝ) (E : Schedule → ℕ → Ω → Driver) : ℕ → Ω → ℝ → ℂ :=
  fun n ω => pullPrefix q (treeTime n) (driverTree E n ω)

/-- The remaining probabilistic law: the completed physical counterflow visits
the actual finite prefixes in reverse order. No chart-domain or capacity-clock
conclusion is part of this hypothesis. -/
def StripReverseVisitLaw {Ω : Type*} [MeasurableSpace Ω] (q : ℝ) (P : Measure Ω)
    (E : Schedule → ℕ → Ω → Driver) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ᵐ ω ∂P, ∀ n, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ treeTime n →
    ∃ u ∈ Icc (0 : ℝ) 1, stripCounterflowPath q (γ ω) u = stripTree q E n ω t ∧
      ∀ r ∈ Icc (0 : ℝ) u, stripCounterflowPath q (γ ω) r ≠ stripTree q E n ω s

/-- The physical prefix is rooted at zero and stays in H, independently of
any reverse-visit assertion. -/
theorem ae_stripTree_interior {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : 0 < q) {E : Schedule → ℕ → Ω → Driver}
    (hi : ∀ᵐ ω ∂P, ∀ n, driverTree E n ω 0 = 0 ∧
      ∀ t : ℝ, 0 < t → t ≤ treeTime n → driverTree E n ω t ∈ H) :
    ∀ᵐ ω ∂P, ∀ n, stripTree q E n ω 0 = 0 ∧
      ∀ t : ℝ, 0 < t → stripTree q E n ω t ∈ H := by
  filter_upwards [hi] with ω hω n
  exact ⟨pullPrefix_zero q (treeTime_pos n).le (hω n).1,
    pullPrefix_mem_H hq (treeTime_pos n) (hω n).2⟩

/-- Deterministic chart and clock conversion discharges the former
`TargetLemma57Statement` from the physical reverse-visit law. -/
theorem targetLemma57_of_stripReverseVisit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : 0 < q) {E : Schedule → ℕ → Ω → Driver} {γ : Ω → ℝ≥0 → ℂ}
    (hγ0 : ∀ᵐ ω ∂P, γ ω 0 = 0)
    (hγH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hi : ∀ᵐ ω ∂P, ∀ n, driverTree E n ω 0 = 0 ∧
      ∀ t : ℝ, 0 < t → t ≤ treeTime n → driverTree E n ω t ∈ H)
    (hR : StripReverseVisitLaw q P E γ) : TargetLemma57Statement P E γ := by
  filter_upwards [hγ0, hγH, hi, hR] with ω h0 hH hη hRω n s t hs hst ht
  exact target_reverseVisit_of_pullback hq (treeTime_pos n) h0 hH
    (hη n).1 (hη n).2 (hRω n) hs hst ht

end InteractingSLE.Sec5.Prop513Wire
