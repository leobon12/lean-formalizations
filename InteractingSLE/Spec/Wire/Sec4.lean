/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prop412
import InteractingSLE.Spec.Sec4.ZeroMarksCharts
import InteractingSLE.Spec.Zhan.WordsEscape

/-!
# Proposition 4.12, Lemmas 4.3 and 4.5 and Aux. lemma 22's ends for `κ ≤ 4`, unconditional

Packet PROVE-WIRE1 (no new mathematics). Aux. lemma 7 and the transience of separated words are theorems for
`0 < κ ≤ 4` (`Zhan.aux7Statement`, `Zhan.separatedTransienceStatement`, `Spec/Zhan/WordsEscape.lean`). This file
discharges that input from every landed §4.2 result that takes it, for the parameters where it is proved:

* `prop412`: **Proposition 4.12** (`0 < κ < 4`, weights satisfying (4.4)) — `Sec4.prop412_of_separatedTransience`;
* Lemma 4.3 (both signs of the upper height), Lemma 4.5 (both charts) and the end alternatives of Aux. lemma 22, in
  the passive-mark form of `Spec/Sec4/Prob41*.lean` and the zero-mark form of `Spec/Sec4/ZeroMarks*.lean`, and the
  transience of flow lines and evolutions with admissible nonzero partial sums — each for `0 < k ≤ 4`.

Each theorem has the conclusion and the binders of the landed result, with `h7 : Aux7Statement k` replaced by
`hk4 : k ≤ 4` (and `hk : 0 < k` added where the landed result did not take it). The landed results with
`Aux7Statement (16 / κ)` (Lemma 4.7/Remark 4.8 in `Spec/Sec4/Remark48.lean`, Lemma 5.7 and Proposition 5.9 in
`Spec/Sec5/`) are not wired: there `16/κ > 4`, where Aux. lemma 7 is not yet proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Wire

open Sec4

variable {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **Proposition 4.12** (Specification p. 122): for `0 < κ < 4` and an ordered force word whose weights satisfy
(4.4), almost surely the lifetime is infinite, the driver has a continuous generating trace on `[0, ∞)`, and every
such trace tends to `∞`. Unconditional: `Sec4.prop412_of_separatedTransience` with
`Zhan.separatedTransienceStatement`. -/
theorem prop412 {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Cond44 κ ρL ρR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop :=
  prop412_of_separatedTransience hκ hκ4 (Zhan.separatedTransienceStatement hκ hκ4.le) hF h44 hE

/-! ### Passive-mark form (`Spec/Sec4/Prob41*.lean`) -/

/-- **Transience of the flow line from `0` for `0 < k ≤ 4`** (`Sec4.IsFlowLine.ae_tendsto_of_aux7` with Aux. lemma 7
proved). -/
theorem isFlowLine_ae_tendsto_of_le_four (hk : 0 < k) (hk4 : k ≤ 4)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η ω t ≠ x) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop :=
  Sec4.IsFlowLine.ae_tendsto_of_aux7 (Zhan.aux7Statement hk hk4) hk hb hL hR hfl

/-- **Lemma 4.3, `a ≤ −Λ`; Aux. lemma 22, all upper heights `≤ −Λ`**, for `0 < k ≤ 4` (`Sec4.lemma43_right_of_aux7`
with Aux. lemma 7 proved). -/
theorem lemma43_right_of_le_four (hk : 0 < k) (hk4 : k ≤ 4) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ upperLineH) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (stripInv (η ω t)).re) atTop atTop :=
  lemma43_right_of_aux7 (Zhan.aux7Statement hk hk4) hk hbL hbU hU hlowL hlowR hfl

/-- **Lemma 4.3, `a ≥ Λ`; Aux. lemma 22, all upper heights `≥ Λ`**, for `0 < k ≤ 4` (`Sec4.lemma43_left_of_aux7`
with Aux. lemma 7 proved). -/
theorem lemma43_left_of_le_four (hk : 0 < k) (hk4 : k ≤ 4) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsLeftEndFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' Ioi 1) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (-Complex.log (1 - η ω t) / π).re) atTop atBot :=
  lemma43_left_of_aux7 (Zhan.aux7Statement hk hk4) hk hbL hbU hU hlowL hlowR hfl

/-- **Lemma 4.5** (ℍ chart), for `0 < k ≤ 4` (`Sec4.lemma45_of_aux7` with Aux. lemma 7 proved). -/
theorem lemma45_of_le_four (hk : 0 < k) (hk4 : k ≤ 4) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => ‖η ω t‖) atTop atTop :=
  lemma45_of_aux7 (Zhan.aux7Statement hk hk4) hk hbL hbU hUle hUge hlowL hlowR hfl

/-- **Lemma 4.5** (strip chart: the limit is the marked upper point `x₀ + i`), for `0 < k ≤ 4`
(`Sec4.lemma45_strip_of_aux7` with Aux. lemma 7 proved). -/
theorem lemma45_strip_of_le_four (hk : 0 < k) (hk4 : k ≤ 4) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => stripQInv (Real.exp (π * x₀)) (η ω t)) atTop (𝓝 ((x₀ : ℂ) + I)) :=
  lemma45_strip_of_aux7 (Zhan.aux7Statement hk hk4) hk hbL hbU hUle hUge hlowL hlowR hfl

/-! ### Zero-mark form (`Spec/Sec4/ZeroMarks*.lean`) -/

/-- **Transience under admissible nonzero partial sums**, for `0 < k ≤ 4`
(`Sec4.IsIntegratedSLEEvolution.ae_tendsto_of_aux7_of_nonzero` with Aux. lemma 7 proved). -/
theorem isIntegratedSLEEvolution_ae_tendsto_of_nonzero_of_le_four (hk : 0 < k) (hk4 : k ≤ 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hword : IsOrderedForceWord xL xR) (hadm : HasAdmissibleNonzeroPartialSums k ρL ρR xL xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
        Tendsto (fun t => ‖η t‖) atTop atTop :=
  Sec4.IsIntegratedSLEEvolution.ae_tendsto_of_aux7_of_nonzero (Zhan.aux7Statement hk hk4) hword hadm h

/-- **Transience of the flow line from `0` with zero-mark lower data**, for `0 < k ≤ 4`
(`Sec4.IsFlowLine.ae_tendsto_of_aux7_of_nonzero` with Aux. lemma 7 proved). -/
theorem isFlowLine_ae_tendsto_of_nonzero_of_le_four (hk : 0 < k) (hk4 : k ≤ 4)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) →
      b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0,
      (∀ x : ℝ, x < 0 → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) → η ω t ≠ x) ∧
        ∀ x : ℝ, 0 < x → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) → η ω t ≠ x) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop :=
  Sec4.IsFlowLine.ae_tendsto_of_aux7_of_nonzero (Zhan.aux7Statement hk hk4) hk hb hL hR hfl

/-- **Lemma 4.3, `a ≤ −Λ`; Aux. lemma 22, all upper heights `≤ −Λ`** (zero-mark lower data), for `0 < k ≤ 4`
(`Sec4.lemma43_right_of_aux7_basic` with Aux. lemma 7 proved). -/
theorem lemma43_right_of_le_four_basic (hk : 0 < k) (hk4 : k ≤ 4) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ upperLineH) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (stripInv (η ω t)).re) atTop atTop :=
  lemma43_right_of_aux7_basic (Zhan.aux7Statement hk hk4) hk hbL hbU hU hlowL hlowR hfl

/-- **Lemma 4.3, `a ≥ Λ`; Aux. lemma 22, all upper heights `≥ Λ`** (zero-mark lower data), for `0 < k ≤ 4`
(`Sec4.lemma43_left_of_aux7_basic` with Aux. lemma 7 proved). -/
theorem lemma43_left_of_le_four_basic (hk : 0 < k) (hk4 : k ≤ 4) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsLeftEndFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' Ioi 1) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (-Complex.log (1 - η ω t) / π).re) atTop atBot :=
  lemma43_left_of_aux7_basic (Zhan.aux7Statement hk hk4) hk hbL hbU hU hlowL hlowR hfl

/-- **Lemma 4.5** (ℍ chart, zero-mark lower data), for `0 < k ≤ 4` (`Sec4.lemma45_of_aux7_basic` with Aux. lemma 7
proved). -/
theorem lemma45_of_le_four_basic (hk : 0 < k) (hk4 : k ≤ 4) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => ‖η ω t‖) atTop atTop :=
  lemma45_of_aux7_basic (Zhan.aux7Statement hk hk4) hk hbL hbU hUle hUge hlowL hlowR hfl

/-- **Lemma 4.5** (strip chart, zero-mark lower data), for `0 < k ≤ 4` (`Sec4.lemma45_strip_of_aux7_basic` with
Aux. lemma 7 proved). -/
theorem lemma45_strip_of_le_four_basic (hk : 0 < k) (hk4 : k ≤ 4) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ JL ∧ bL y ≠ -sleLambda k) →
      bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ JL ∧ bL y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => stripQInv (Real.exp (π * x₀)) (η ω t)) atTop (𝓝 ((x₀ : ℂ) + I)) :=
  lemma45_strip_of_aux7_basic (Zhan.aux7Statement hk hk4) hk hbL hbU hUle hUge hlowL hlowR hfl

end Wire

end InteractingSLE
