/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCM
import InteractingSLE.Spec.Supplement.RLCDG3

/-!
# Lemma G3 from flow locality for Cameron–Martin shift pairs

Packet PROVE-L1-CM. Source: Lemma G3 and its proof (supplement §7.3, `source/spec/p481-528.md` L290–L320,
pp. 492–493). A copy of `RLC.g3ChartComparisonStatement_of_locality` (`RLCDG3.lean`) that uses flow locality only for
the shift pair it builds: the density `Z` and the shift `T` of `RLC.exists_shift_isGFFWithBoundaryData` (for the
compact `closure V`), so that `Ĥ = H₀ + T` exactly.

* **`g3ChartComparisonStatement_of_shiftLocality`**: `RLC.G3ChartComparisonStatement` from
  `FlowStopIdentCM.FlowLocalityShiftStatement` and Theorems 1.2 (param) / 1.3;
* **`g3ChartComparisonStatement_of_CM`**: the same from the named input `FlowStopIdentCM.FlowLineStopIdentCMStatement`
  ((L1) for shift pairs on the enlargement, with the lifetime clause), the WFS kernel target
  (`WFS.ThroughKernelStatement`, Aux. lemma 54 for Galmarino stops) and Theorems 1.2 (param) / 1.3.

R43/R48: this serves Theorem 1.5 only (Lemma G3 is an input of W5); Theorems 1.2–1.3 are hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric

namespace InteractingSLE

namespace RLC

open Restart.FlowStopIdentCM

/-- **Lemma G3 (`RLC.G3ChartComparisonStatement`) from flow locality for shift pairs and Theorems 1.2 (param) /
1.3.** The shift pair is `RLC.exists_shift_isGFFWithBoundaryData` for `K = closure V`; the reference flow lines are
the canonical ones of `H₀ + T` under `Z · Q₀`. -/
theorem g3ChartComparisonStatement_of_shiftLocality (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hloc : FlowLocalityShiftStatement.{0}) : G3ChartComparisonStatement.{0} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO _hJO V hV hVb hVO y₁ y₂ θ₁ θ₂ S _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  obtain ⟨Z, T, N, hNo, hKN, hNO, hZm, hZpos, hZ1, hĤ, hT0⟩ :=
    exists_shift_isGFFWithBoundaryData hb hbR hO hbO hVb.isCompact_closure hVO Q₀ hH
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (Z x) with hQ
  have hint : Integrable Z Q₀ := Integrable.of_integral_ne_zero (by rw [hZ1]; exact one_ne_zero)
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (hZpos.mono fun x hx => hx.le), hZ1, ENNReal.ofReal_one]
  have hPQ : Q₀ ≪ Q := by
    refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hZm).aemeasurable ?_
    filter_upwards [hZpos] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne'
  have hQP : Q ≪ Q₀ := withDensity_absolutelyContinuous _ _
  obtain ⟨α₁, ζ₁, hα₁⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₁ θ₁ hĤ
  obtain ⟨α₂, ζ₂, hα₂⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₂ θ₂ hĤ
  refine ⟨Z, fun x => H₀ x + T, α₁, α₂, ζ₁, ζ₂, hZm.aemeasurable, hZpos, hZ1, hĤ, hα₁, hα₂, ?_⟩
  filter_upwards [hloc κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hNo hNO V hV hVb hKN y₁ θ₁ Q₀ Q hPQ hQP H₀ _ T hH hĤ
      (fun _ => rfl) hT0 Γ₁ α₁ U₁ ζ₁ h₁ hα₁,
    hloc κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hNo hNO V hV hVb hKN y₂ θ₂ Q₀ Q hPQ hQP H₀ _ T hH hĤ
      (fun _ => rfl) hT0 Γ₂ α₂ U₂ ζ₂ h₂ hα₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

/-- **Lemma G3 from (L1) for shift pairs on the enlargement** (`FlowLineStopIdentCMStatement`, with the lifetime
clause), the WFS kernel target for `0 < κ < 4` and Theorems 1.2 (param) / 1.3. -/
theorem g3ChartComparisonStatement_of_CM (hCM : FlowLineStopIdentCMStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3ChartComparisonStatement.{0} :=
  g3ChartComparisonStatement_of_shiftLocality h12p h13 (flowLocalityShiftStatement_of_CM_through hCM hT h12p h13)

end RLC

end InteractingSLE
