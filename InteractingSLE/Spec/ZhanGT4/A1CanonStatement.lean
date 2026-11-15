/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CanonCore
import InteractingSLE.Spec.ZhanGT4.A1RefStatement
import InteractingSLE.Spec.Restart.ConverseBefore

/-!
# A.1 (R72): the Canon statements from their rectangle cores

Packet PROVE-ZHAN-A1CANON. Ruling R72: `A1Ref.A1DualCoupling{G3,Eight}CanonStatement` are the A.1 line's target. This
file reduces them to the **rectangle core** statements `A1DualCoupling{G3,Eight}CoreStatement`: the same two marginal
evolutions on one standard Borel coupling space, with `A1Ref.IsCanonImageLaw` replaced in both directions by
`A1Canon.IsCanonImageCore` (the image noise is a Brownian motion up to each rectangle cap, the caps cover the image
lifetime; measurability of the live events, words and the canonical image). The reference space of the Canon
statements is the coupling space times the Wiener space `ℕ → ℝ` (`Restart.ConverseBefore.exists_noiseBM`), whose
Brownian motion continues the image noises after the first contact:

* **`a1DualCouplingG3CanonStatement_of_core`**, **`a1DualCouplingEightCanonStatement_of_core`**;
* chained: `a1DualCouplingG3RefUAStatement_of_core`, `a1DualCouplingEightRefUAStatement_of_core` and
  `firstSwallowCrosscutStatement_of_core` (A.3 with A.2's three parts, as
  `A1Ref.firstSwallowCrosscutStatement_of_canon`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A1Canon

open A2X A1Ref

/-- **The rectangle core of A.1 (G3)** (`4 < κ < 8`, `y < x < 0`): one standard Borel coupling space carrying the large
curve (from `0`, marks `x, y` with weights `κ − 4, −4`) and the small curve (`κ̂ = 16/κ`, from `0`, its word
`![0], ![0, x − y, −y]`), with the two directional rectangle cores (`IsCanonImageCore`) for the usual augmentations,
with the image data of `A1Ref.A1DualCouplingG3CanonStatement`. -/
def A1DualCouplingG3CoreStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (X : Type) (_ : MeasurableSpace X) (_ : StandardBorelSpace X) (μ : Measure X)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (W₂ : ℝ≥0 → X → ℝ) (VL₂ : Fin 2 → ℝ≥0 → X → ℝ) (VR₂ : Fin 0 → ℝ≥0 → X → ℝ) (B₂ : ℝ≥0 → X → ℝ)
      (ζ₂ : X → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) μ 𝓕₁ W₁ VL₁ VR₁ B₁
        ζ₁ ∧
      IsCanonImageCore (kh κ) μ (usualAugmentation 𝓕₂ μ)
        (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0 W₂ (fun _ _ => ![0])
        (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ) (smallG3RhoR κ) ∧
      IsCanonImageCore κ μ (usualAugmentation 𝓕₁ μ) (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
        (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **The rectangle core of A.1 (Eight)** (`8 ≤ κ`, `x < 0`), with the image data of
`A1Ref.A1DualCouplingEightCanonStatement`. -/
def A1DualCouplingEightCoreStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (X : Type) (_ : MeasurableSpace X) (_ : StandardBorelSpace X) (μ : Measure X)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (W₂ : ℝ≥0 → X → ℝ) (VL₂ : Fin 1 → ℝ≥0 → X → ℝ) (VR₂ : Fin 0 → ℝ≥0 → X → ℝ) (B₂ : ℝ≥0 → X → ℝ)
      (ζ₂ : X → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) μ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      IsCanonImageCore (kh κ) μ (usualAugmentation 𝓕₂ μ)
        (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0 W₂ (fun _ _ => ![0])
        (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
      IsCanonImageCore κ μ (usualAugmentation 𝓕₁ μ) (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
        (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

theorem map_fst_prod_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure ν] : (μ.prod ν).map Prod.fst = μ := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- **A.1 (G3), canonical form, from its rectangle core** (R72): the reference space is the coupling space times the
Wiener space `ℕ → ℝ`. -/
theorem a1DualCouplingG3CanonStatement_of_core {κ : ℝ} (h : A1DualCouplingG3CoreStatement κ) :
    A1DualCouplingG3CanonStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, mX, hX, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hc₁, hc₂⟩ :=
    h hκ4 hκ8 y x hyx hx
  obtain ⟨ν, hν, 𝓦, β, hβ, hβc, hβ0⟩ := Restart.ConverseBefore.exists_noiseBM
  have hmap := map_fst_prod_eq μ ν
  exact ⟨X × (ℕ → ℝ), inferInstance, inferInstance, μ.prod ν, inferInstance,
    Coupling.filtrationComap 𝓕₂ measurable_fst, Coupling.filtrationComap 𝓕₁ measurable_fst,
    fun t ω => W₂ t ω.1, fun i t ω => VL₂ i t ω.1, fun i t ω => VR₂ i t ω.1, fun t ω => B₂ t ω.1,
    fun ω => ζ₂ ω.1, fun t ω => W₁ t ω.1, fun i t ω => VL₁ i t ω.1, fun i t ω => VR₁ i t ω.1,
    fun t ω => B₁ t ω.1, fun ω => ζ₁ ω.1,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hmap h₂,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hmap h₁,
    isCanonImageLaw_prod_of_core hc₁ hβ hβc hβ0, isCanonImageLaw_prod_of_core hc₂ hβ hβc hβ0⟩

/-- **A.1 (Eight), canonical form, from its rectangle core** (R72). -/
theorem a1DualCouplingEightCanonStatement_of_core {κ : ℝ} (h : A1DualCouplingEightCoreStatement κ) :
    A1DualCouplingEightCanonStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, mX, hX, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hc₁, hc₂⟩ := h hκ8 x hx
  obtain ⟨ν, hν, 𝓦, β, hβ, hβc, hβ0⟩ := Restart.ConverseBefore.exists_noiseBM
  have hmap := map_fst_prod_eq μ ν
  exact ⟨X × (ℕ → ℝ), inferInstance, inferInstance, μ.prod ν, inferInstance,
    Coupling.filtrationComap 𝓕₂ measurable_fst, Coupling.filtrationComap 𝓕₁ measurable_fst,
    fun t ω => W₂ t ω.1, fun i t ω => VL₂ i t ω.1, fun i t ω => VR₂ i t ω.1, fun t ω => B₂ t ω.1,
    fun ω => ζ₂ ω.1, fun t ω => W₁ t ω.1, fun i t ω => VL₁ i t ω.1, fun i t ω => VR₁ i t ω.1,
    fun t ω => B₁ t ω.1, fun ω => ζ₁ ω.1,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hmap h₂,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hmap h₁,
    isCanonImageLaw_prod_of_core hc₁ hβ hβc hβ0, isCanonImageLaw_prod_of_core hc₂ hβ hβc hβ0⟩

/-- The rectangle core (G3) gives A1DUAL's Ref statement with usual-augmentation filtrations. -/
theorem a1DualCouplingG3RefUAStatement_of_core {κ : ℝ} (h : A1DualCouplingG3CoreStatement κ) :
    A1DualCouplingG3RefUAStatement κ :=
  a1DualCouplingG3RefUAStatement_of_canon (a1DualCouplingG3CanonStatement_of_core h)

/-- The rectangle core (Eight) gives A1DUAL's Ref statement with usual-augmentation filtrations. -/
theorem a1DualCouplingEightRefUAStatement_of_core {κ : ℝ} (h : A1DualCouplingEightCoreStatement κ) :
    A1DualCouplingEightRefUAStatement κ :=
  a1DualCouplingEightRefUAStatement_of_canon (a1DualCouplingEightCanonStatement_of_core h)

/-- **A.3 from the two rectangle cores and A.2's three parts** (as `A1Ref.firstSwallowCrosscutStatement_of_canon`). -/
theorem firstSwallowCrosscutStatement_of_core {κ : ℝ} (hA1 : A1DualCouplingG3CoreStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightCoreStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  firstSwallowCrosscutStatement_of_canon (a1DualCouplingG3CanonStatement_of_core hA1) h1 h2 h3
    (a1DualCouplingEightCanonStatement_of_core hA1') h1' h2' h3'

end InteractingSLE.ZhanGT4.A1Canon
