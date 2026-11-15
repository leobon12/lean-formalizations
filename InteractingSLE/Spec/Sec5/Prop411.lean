/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma56
import InteractingSLE.Spec.Sec5.CrossRestartLaw
import InteractingSLE.Spec.Sec5.CrossRestartMeasPathVersion
import InteractingSLE.Spec.Sec5.Prop51Final

/-!
# Proposition 4.11's containment for the §5 counterflows

Packet PROVE-SEC5-J (specification p. 121, Proposition 4.11: "the flow line `η` starting from `0` is equal to the
left boundary of the counterflow line `η′` of the field minus `π/2 χ` starting from `z₀`"; its use in the proof of
Proposition 5.5, p. 136: "Proposition 4.11 implies that `η_{θ₁}|[0, τ₁^ε]` is contained in the left boundary of
`η′_{θ₁}`").

Proposition 5.5 needs only the **containment** half of Proposition 4.11 for the flow line `η_{θ₁}` of `h` and the
counterflow `η′_{θ₁}` of `h + (θ₁ − π/2)χ`. In the frame `α = θ₁ − π/2` of `Carrier.lean` this flow line is the flow
line of `h + αχ` at the relative angle `π/2`, and the containment is Lemma 5.7 at the extreme angle `θ = π/2` (the
proof of Lemma 4.7 under Remark 4.8's hypotheses is the same argument; specification p. 138). This file:

* `stripCounterflowPath_image_inter_H_subset`: the points of `ℍ` on the completed counterflow are points of
  `stripCounterflowRange q γ ⊤` (the terminal point `0` is real);
* `LiesRightOf.of_inter_H`: only the points in `ℍ` matter for `LiesRightOf`;
* **`ae_image_inter_H_subset_stripCounterflowRange`** (conditional helper, distinct name): Proposition 4.11's
  containment `η([0, T]) ∩ ℍ ⊆ η′`, for the flow line of `h + αχ` at relative angle `π/2` and the counterflow of
  `h + αχ`, from SEC5-I's counterflow restart inputs (Zhan's Part A inputs at `16/κ`, `PartAInputsSixteenDiv`, and the
  restart law `CrossRestart.CounterflowRestartKernelOnStatement`) through
  `counterflowSegmentRestartStatement_of_kernelOn` and Lemma 5.7 (`lemma57_of_counterflowSegmentRestart'`). The
  remaining hypotheses are the coupling (conditional independence of `η` and `η′` given `h`, a source premise of
  Proposition 4.11 and Lemma 5.7), the counterflow's continuity and transience to its target (Remark 5.8), and the
  horizon `T` before which `η` is alive and in `ℍ` (Lemma 5.6's non-boundary-intersecting regime).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec5

open Sec4 (stripCounterflowChart stripCounterflowPath IsStripCounterflowDriver)

/-- The points of `ℍ` on the completed counterflow `stripCounterflowPath q γ` (parametrized on `[0, 1]`, terminal point
`0`) are physical points `M_q⁻¹(γ(t))` of the trace. -/
theorem stripCounterflowPath_image_inter_H_subset (q : ℝ) (γ : ℝ≥0 → ℂ) :
    stripCounterflowPath q γ '' Icc 0 1 ∩ H ⊆ stripCounterflowRange q γ ⊤ := by
  rintro _ ⟨⟨s, hs, rfl⟩, hH⟩
  by_cases h1 : s < 1
  · rw [Sec4.stripCounterflowPath_of_lt h1]
    exact ⟨_, ⟨_, ENNReal.coe_lt_top, rfl⟩, rfl⟩
  · have hs1 : s = 1 := le_antisymm hs.2 (not_lt.1 h1)
    subst hs1
    rw [Sec4.stripCounterflowPath_one] at hH
    exact absurd hH (by simp [QuantumZipper.H])

/-- Only the points of `K` in `ℍ` can be strictly on the left of `A`. -/
theorem LiesRightOf.of_inter_H {K A : Set ℂ} (h : LiesRightOf (K ∩ H) A) : LiesRightOf K A := by
  rw [liesRightOf_iff] at h ⊢
  intro z hz hzL
  exact h z ⟨hz, (stripLeftSide_subset A hzL).1⟩ hzL

theorem LiesLeftOf.of_inter_H {K A : Set ℂ} (h : LiesLeftOf (K ∩ H) A) : LiesLeftOf K A := by
  rw [liesLeftOf_iff] at h ⊢
  intro z hz hzR
  exact h z ⟨hz, (stripRightSide_subset A hzR).1⟩ hzR

variable {κ α x₀ a b a' b' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}

/-- **Proposition 4.11's containment for the §5 counterflow** (conditional helper: SEC5-I's restart inputs). Let
`0 < κ < 4`, let `h + αχ` have the data of Figure 5.1 with the bounds of §5, let `η` be the flow line of `h + αχ` with
relative angle `π/2` (the flow line `η_{θ₁}` of `h` when `α = θ₁ − π/2`) and `η′` the counterflow of `h + αχ` from `z₀`
(trace `γ′` in the chart `M_q`), conditionally independent of `η` given `h`. Assume the counterflow is continuous,
avoids the strip end `+∞` (`γ′ ≠ −1`) and reaches its target (`‖γ′‖ → ∞`), and let `T > 0` be a horizon before which
`η` is alive and in `ℍ`. Then almost surely `η([0, T]) ∩ ℍ` is contained in the counterflow range
`M_q⁻¹(γ′([0, ∞)))`. -/
theorem ae_image_inter_H_subset_stripCounterflowRange (hA : PartAInputsSixteenDiv)
    (hK : CrossRestart.CounterflowRestartKernelOnStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α (π / 2) (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h
      η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H) :
    ∀ᵐ ω ∂P, (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω) ∩ H ⊆
      stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) ⊤ := by
  have hR := CrossRestart.counterflowSegmentRestartStatement_of_kernelOn hA hK
  have h57 := lemma57_of_counterflowSegmentRestart' hR (aux7Statement_sixteen_div_of_partA hA hκ hκ4) hκ hκ4
    hbd (by linarith [Real.pi_pos]) le_rfl hhm hh hη hcf htr' hci hγ hT0 hT
  filter_upwards [h57] with ω ⟨_, hsub, _⟩
  exact (inter_subset_inter_left H hsub).trans (stripCounterflowPath_image_inter_H_subset _ _)

/-- **Proposition 4.11's containment, in the form used by Proposition 5.5**: whatever lies to the right of the
counterflow of `h + αχ` contains the explored segment `η([0, T])` of the relative-angle-`π/2` flow line on its right
(hypotheses as in `ae_image_inter_H_subset_stripCounterflowRange`; `A ω` any obstacle). -/
theorem ae_liesRightOf_image_of_liesRightOf_counterflow (hA : PartAInputsSixteenDiv)
    (hK : CrossRestart.CounterflowRestartKernelOnStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α (π / 2) (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h
      η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H)
    {A : Ω → Set ℂ}
    (hcfA : ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) ⊤) (A ω)) :
    ∀ᵐ ω ∂P, LiesRightOf ((fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω)) (A ω) := by
  filter_upwards [ae_image_inter_H_subset_stripCounterflowRange hA hK hκ hκ4 hbd hhm hh hη hcf htr' hci hγ
    hT0 hT, hcfA] with ω hsub hω
  exact LiesRightOf.of_inter_H (hω.mono hsub)

end Sec5

end InteractingSLE
