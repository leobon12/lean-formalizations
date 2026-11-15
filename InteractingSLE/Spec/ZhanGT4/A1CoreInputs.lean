/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CoreFibre
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# A.1's rectangle core: tools for the inputs of the density form

Packet PROVE-A1CORE. Source: follow-up 5 §1.3 (`source/external/AstraIG1/ig1_followup5.txt` L203–L216, R73): "On each
protected rectangle, that construction supplies a continuous joint density `M(s, t)` … with axis values one and the
two coordinate martingale identities. These are true martingales in the usual marginal filtrations. If `τ` is bounded
by the large-curve protection time, optional sampling gives the density `M(s, τ)`. … (1.7) … Conditional Girsanov
gives the image SDE."

The inputs of `IsRectImageCore` / `IsRectImageCoreFst` (`A1CoreRect`) in the source's terms:

* **`lintegral_ofReal_stoppedValue_eq`**: optional sampling of the coordinate martingale `t ↦ M(s, t)`
  (right-continuous, nonnegative, bounded stopping times) in lower-integral form;
* **`dens_of_rect_optional`** / **`dens_of_rect_optional_fst`**: (1.7) — the exit-time rectangle law with density
  `D₀ = M(S₁, S₂)` and the optional sampling identity give the density identity with `D = M(S₁, τ)` for every
  test function measurable for the two stopped records (the `hdens` clause of the density form);
* **`fib_of_agree`** / **`fib_of_agree_fst`**: the frozen-hull fibre law (`hfib`) from a Brownian motion of the
  rectangle's own filtration under the tilted law that agrees with the image noise up to the cap (the output form of
  the frozen-hull Girsanov theorems, e.g. `DualHyp.exists_condLaw₁`), by `isStoppedBM_of_agree`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Core

open A1Canon

/-! ### Optional sampling of the coordinate martingale -/

section Optional

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Optional sampling of a nonnegative right-continuous martingale, lower-integral form**: for bounded stopping
times `σ ≤ τ` and `A ∈ 𝓕_σ`, `∫_A M_τ = ∫_A M_σ`. -/
theorem lintegral_ofReal_stoppedValue_eq {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hMrc : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t) (hpos : ∀ t ω, 0 ≤ M t ω)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫⁻ ω in A, ENNReal.ofReal (stoppedValue M τ ω) ∂P = ∫⁻ ω in A, ENNReal.ofReal (stoppedValue M σ ω) ∂P := by
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hle ω).trans (hτT ω)
  have hint : ∀ {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ), (∀ ω, ρ ω ≤ T) →
      Integrable (stoppedValue M ρ) P := fun hρ hρT =>
    integrable_condExp.congr (InteractingSLE.Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hM hMrc hρ
      (isStoppingTime_const 𝓕 T) hρT (fun _ => le_rfl)).symm
  have hp : ∀ ρ : Ω → WithTop ℝ≥0, ∀ ω, 0 ≤ stoppedValue M ρ ω := fun ρ ω => hpos _ ω
  rw [← ofReal_integral_eq_lintegral_ofReal (hint hτ hτT).integrableOn (ae_of_all _ (hp τ)),
    ← ofReal_integral_eq_lintegral_ofReal (hint hσ hσT).integrableOn (ae_of_all _ (hp σ)),
    InteractingSLE.setIntegral_stoppedValue_eq_of_rightContinuous hM hMrc hσ hτ hle hτT hA]

end Optional

/-! ### (1.7) assembled -/

section Dens

variable {X Y : Type*} {𝓐 𝓐' : MeasurableSpace X} {𝓑 𝓑' : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- **(1.7), the density clause of `IsRectImageCore`**: the exit-time rectangle law (density `D₀`, σ-algebras
`𝓐`, `𝓑` of the two stopped records) and the optional sampling identity in the conditioning coordinate (`𝓑' ≤ 𝓑`,
density `D`) give `∫ f dμ = ∫ f D d(P₁ ⊗ P₂)` for every `𝓐 ⊗ 𝓑'`-measurable `f ≥ 0`. -/
theorem dens_of_rect_optional {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] (h𝓐 : 𝓐 ≤ mX) (h𝓑' : 𝓑' ≤ 𝓑) (h𝓑 : 𝓑 ≤ mY)
    {D₀ D : X × Y → ℝ≥0∞} (hD₀ : Measurable D₀) (hD : Measurable D)
    (hrect : ∀ A B, MeasurableSet[𝓐] A → MeasurableSet[𝓑] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ z ∂(P₁.prod P₂))
    (hopt : ∀ᵐ x ∂P₁, ∀ B, MeasurableSet[𝓑'] B → ∫⁻ y in B, D₀ (x, y) ∂P₂ = ∫⁻ y in B, D (x, y) ∂P₂)
    (f : X × Y → ℝ≥0∞) (hf : Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑'] f) :
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂) :=
  lintegral_eq_of_rect h𝓐 (h𝓑'.trans h𝓑) hD (rect_of_optional h𝓑' h𝓑 hD₀ hD hrect hopt) hf

/-- (1.7) with the conditioning coordinate on the first factor: the exit-time rectangle law on `𝓐 × 𝓑` and the
optional sampling identity in `x` (`𝓐' ≤ 𝓐`) give the density identity on `𝓐' ⊗ 𝓑`. -/
theorem dens_of_rect_optional_fst {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] (h𝓐' : 𝓐' ≤ 𝓐) (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY)
    {D₀ D : X × Y → ℝ≥0∞} (hD₀ : Measurable D₀) (hD : Measurable D)
    (hrect : ∀ A B, MeasurableSet[𝓐] A → MeasurableSet[𝓑] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ z ∂(P₁.prod P₂))
    (hopt : ∀ᵐ y ∂P₂, ∀ A, MeasurableSet[𝓐'] A → ∫⁻ x in A, D₀ (x, y) ∂P₁ = ∫⁻ x in A, D (x, y) ∂P₁)
    (f : X × Y → ℝ≥0∞) (hf : Measurable[@Prod.instMeasurableSpace X Y 𝓐' 𝓑] f) :
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂) := by
  refine lintegral_eq_of_rect (h𝓐'.trans h𝓐) h𝓑 hD (fun A B hA hB => ?_) hf
  have hAm : MeasurableSet[mX] A := h𝓐 A (h𝓐' A hA)
  rw [hrect A B (h𝓐' A hA) hB, ← Measure.prod_restrict, lintegral_prod_symm _ hD₀.aemeasurable,
    lintegral_prod_symm _ hD.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hopt] with y hy
  exact hy A hA

end Dens

/-! ### The frozen-hull fibre law from a rectangle Brownian motion -/

section Fib

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The fibre law at a frozen conditioning sample `y`** (conditional Girsanov at a frozen hull): if under the image
curve's law tilted by `D(·, y)` a Brownian motion `B` of a filtration `𝓗'` (the rectangle's own filtration) agrees with
the image noise at `y` up to the cap, the cap is a stopping time of the section filtration, and the section filtration
agrees with `𝓗'` before the cap, then the fibre identity of the density form holds at `y`. -/
theorem fib_of_agree {P₁ : Measure X} {D : X × Y → ℝ≥0∞} (hD : Measurable D) {y : Y}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    {𝓗' : Filtration ℝ≥0 mX} {B : ℝ≥0 → X → ℝ}
    (hB : IsFilteredBrownianReal 𝓗' B (P₁.withDensity fun x => D (x, y))) (hBc : ∀ x, Continuous (B · x))
    (hNc : ∀ z, Continuous (N · z)) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime (sectionFiltration 𝓖 y) fun x => (S (x, y) : WithTop ℝ≥0))
    (hagree : ∀ (s : ℝ≥0) (A : Set X), MeasurableSet[sectionFiltration 𝓖 y s] A →
      MeasurableSet[𝓗' s] (A ∩ {x | s < S (x, y)}))
    (heq : ∀ᵐ x ∂(P₁.withDensity fun x => D (x, y)), ∀ t, t ≤ S (x, y) → B t x = N t (x, y)) :
    ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₁ =
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₁ := by
  have : IsProbabilityMeasure (P₁.withDensity fun x => D (x, y)) := hB.isProbabilityMeasure'
  have hNy : ∀ t, Measurable[sectionFiltration 𝓖 y t] fun x => N t (x, y) := fun t =>
    (hNa t).comp (comap_measurable fun x => (x, y))
  exact fib_of_isStoppedBM_withDensity hD
    (isStoppedBM_of_agree hB hBc (fun x => hNc (x, y)) hNy hS hagree heq)

/-- The mirror of `fib_of_agree` (frozen conditioning sample `x ∈ X`, image curve on `Y`). -/
theorem fib_of_agree_fst {P₂ : Measure Y} {D : X × Y → ℝ≥0∞} (hD : Measurable D) {x : X}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    {𝓗' : Filtration ℝ≥0 mY} {B : ℝ≥0 → Y → ℝ}
    (hB : IsFilteredBrownianReal 𝓗' B (P₂.withDensity fun y => D (x, y))) (hBc : ∀ y, Continuous (B · y))
    (hNc : ∀ z, Continuous (N · z)) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime (sectionFiltrationFst 𝓖 x) fun y => (S (x, y) : WithTop ℝ≥0))
    (hagree : ∀ (s : ℝ≥0) (A : Set Y), MeasurableSet[sectionFiltrationFst 𝓖 x s] A →
      MeasurableSet[𝓗' s] (A ∩ {y | s < S (x, y)}))
    (heq : ∀ᵐ y ∂(P₂.withDensity fun y => D (x, y)), ∀ t, t ≤ S (x, y) → B t y = N t (x, y)) :
    ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₂ =
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₂ := by
  have : IsProbabilityMeasure (P₂.withDensity fun y => D (x, y)) := hB.isProbabilityMeasure'
  have hNx : ∀ t, Measurable[sectionFiltrationFst 𝓖 x t] fun y => N t (x, y) := fun t =>
    (hNa t).comp (comap_measurable fun y => (x, y))
  exact fib_of_isStoppedBM_withDensity_fst hD
    (isStoppedBM_of_agree hB hBc (fun y => hNc (x, y)) hNx hS hagree heq)

end Fib

end InteractingSLE.ZhanGT4.A1Core
