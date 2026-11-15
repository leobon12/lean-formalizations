/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1LawPatch
import InteractingSLE.Spec.ZhanGT4.A1CoreInputs

/-!
# A.1's density identity at a stop, by optional sampling of the coordinate density martingale

Packet PROVE-A1-LAW (R76). Source: Astra, *Follow-up 5* §1.3 (`ig1_followup5.txt` L203–L211): "On each protected
rectangle, that construction supplies a continuous joint density `M(s, t)` … with axis values one and the two
coordinate martingale identities. These are true martingales in the usual marginal filtrations. If `τ` is bounded by
the large-curve protection time, optional sampling gives the density `M(s, τ)`. For bounded stopped-record tests,
its identity is `E_coupled[F G] = E_{P₁ ⊗ P₂}[M(s, τ) F G]`, `G ∈ F²_τ` (1.7)."

The countable patch (`A1LawPatch`) gives the identity (1.7) on each rectangle's exit records with the exit density
`M(S₁, S₂)`. Here it is moved to a stop `σ ≤ S₂` of the conditioning curve: for almost every frozen image record `x`,
`t ↦ M(x, t)` is a nonnegative right-continuous martingale of the conditioning curve's filtration, so optional
sampling replaces `M(x, S₂)` by `M(x, σ)` on the events of the stopped σ-algebra at `σ` (A1CORE's
`dens_of_rect_optional`, `lintegral_ofReal_stoppedValue_eq`). This is the `dens` field of PROVE-A1-FROZEN's
`FamilyRect` / `FamilyRectFst` at a stopping time.

## Main results

* `rect_of_rectDens`: (1.7) on `𝓐 ⊗ 𝓑` gives the rectangle identity;
* **`rectDens_stop_of_exit`**: (1.7) on the exit records and the coordinate martingale in the conditioning
  coordinate (on `Y`) give (1.7) on the image record and the stopped σ-algebra at `σ`, with density `M(x, σ)`;
* **`rectDens_stop_of_exit_fst`**: the mirror (conditioning coordinate on `X`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Law

variable {X Y : Type*} {𝓐 : MeasurableSpace X} {𝓑 : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- **(1.7) gives the rectangle identity** `μ(A × B) = ∫_{A × B} D d(P₁ ⊗ P₂)` for `A ∈ 𝓐`, `B ∈ 𝓑`. -/
theorem rect_of_rectDens {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {D : X × Y → ℝ≥0∞}
    (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) (h : RectDens 𝓐 𝓑 P₁ P₂ μ D) (A : Set X) (B : Set Y)
    (hA : MeasurableSet[𝓐] A) (hB : MeasurableSet[𝓑] B) :
    μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D z ∂(P₁.prod P₂) := by
  have hAB : MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (A ×ˢ B) := by
    let _ : MeasurableSpace X := 𝓐
    let _ : MeasurableSpace Y := 𝓑
    exact hA.prod hB
  have hAB' : MeasurableSet (A ×ˢ B) := (h𝓐 _ hA).prod (h𝓑 _ hB)
  have hm := h ((A ×ˢ B).indicator 1) (by
    let _ : MeasurableSpace (X × Y) := @Prod.instMeasurableSpace X Y 𝓐 𝓑
    exact measurable_const.indicator hAB)
  rw [lintegral_indicator_one hAB'] at hm
  rw [hm, ← lintegral_indicator hAB']
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ A ×ˢ B
  · simp only [indicator_of_mem hz, Pi.one_apply, one_mul]
  · simp only [indicator_of_notMem hz, zero_mul]

/-- **(1.7) at a stop of the conditioning curve (on `Y`)** (follow-up 5 §1.3). Let `μ` satisfy (1.7) on the exit
records `𝓐 ⊗ 𝓑` with the exit density `D₀(x, y) = M(x, S(y))`, where for almost every image record `x` the process
`t ↦ M(x, t)` is a nonnegative right-continuous martingale of a filtration `𝓖` of the conditioning curve under its
marginal `P₂`, and `S ≤ T` is a bounded `𝓖`-stopping time. Then at every `𝓖`-stopping time `σ ≤ S` whose stopped
σ-algebra lies in `𝓑`, (1.7) holds on `𝓐 ⊗ 𝓖_σ` with the density `D(x, y) = M(x, σ(y))`. -/
theorem rectDens_stop_of_exit {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [IsFiniteMeasure P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) {D₀ D : X × Y → ℝ≥0∞}
    (hD₀ : Measurable D₀) (hD : Measurable D) (hexit : RectDens 𝓐 𝓑 P₁ P₂ μ D₀)
    {𝓖 : Filtration ℝ≥0 mY} {M : X → ℝ≥0 → Y → ℝ} (hM : ∀ᵐ x ∂P₁, Martingale (M x) 𝓖 P₂)
    (hMrc : ∀ x y t, ContinuousWithinAt (M x · y) (Ici t) t) (hpos : ∀ x t y, 0 ≤ M x t y)
    {σ S : Y → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓖 σ) (hS : IsStoppingTime 𝓖 S) (hσS : σ ≤ S) {T : ℝ≥0}
    (hST : ∀ y, S y ≤ T) (hD₀M : ∀ x y, D₀ (x, y) = ENNReal.ofReal (stoppedValue (M x) S y))
    (hDM : ∀ x y, D (x, y) = ENNReal.ofReal (stoppedValue (M x) σ y)) (hσ𝓑 : hσ.measurableSpace ≤ 𝓑) :
    RectDens 𝓐 hσ.measurableSpace P₁ P₂ μ D := by
  intro f hf
  refine A1Core.dens_of_rect_optional h𝓐 hσ𝓑 h𝓑 hD₀ hD (rect_of_rectDens h𝓐 h𝓑 hexit) ?_ f hf
  filter_upwards [hM] with x hx B hB
  simp only [hD₀M, hDM]
  exact A1Core.lintegral_ofReal_stoppedValue_eq hx (hMrc x) (hpos x) hσ hS hσS hST hB

/-- **(1.7) at a stop of the conditioning curve (on `X`)**: the mirror of `rectDens_stop_of_exit`, with the
coordinate martingale `t ↦ M(t, y)` of a filtration of the conditioning curve under `P₁` for almost every image
record `y`. -/
theorem rectDens_stop_of_exit_fst {P₁ : Measure X} {P₂ : Measure Y} [IsFiniteMeasure P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) {D₀ D : X × Y → ℝ≥0∞}
    (hD₀ : Measurable D₀) (hD : Measurable D) (hexit : RectDens 𝓐 𝓑 P₁ P₂ μ D₀)
    {𝓖 : Filtration ℝ≥0 mX} {M : Y → ℝ≥0 → X → ℝ} (hM : ∀ᵐ y ∂P₂, Martingale (M y) 𝓖 P₁)
    (hMrc : ∀ y x t, ContinuousWithinAt (M y · x) (Ici t) t) (hpos : ∀ y t x, 0 ≤ M y t x)
    {σ S : X → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓖 σ) (hS : IsStoppingTime 𝓖 S) (hσS : σ ≤ S) {T : ℝ≥0}
    (hST : ∀ x, S x ≤ T) (hD₀M : ∀ x y, D₀ (x, y) = ENNReal.ofReal (stoppedValue (M y) S x))
    (hDM : ∀ x y, D (x, y) = ENNReal.ofReal (stoppedValue (M y) σ x)) (hσ𝓐 : hσ.measurableSpace ≤ 𝓐) :
    RectDens hσ.measurableSpace 𝓑 P₁ P₂ μ D := by
  intro f hf
  refine A1Core.dens_of_rect_optional_fst hσ𝓐 h𝓐 h𝓑 hD₀ hD (rect_of_rectDens h𝓐 h𝓑 hexit) ?_ f hf
  filter_upwards [hM] with y hy A hA
  simp only [hD₀M, hDM]
  exact A1Core.lintegral_ofReal_stoppedValue_eq hy (hMrc y) (hpos y) hσ hS hσS hST hA

end InteractingSLE.ZhanGT4.A1Law
