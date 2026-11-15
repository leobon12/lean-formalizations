/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CoreRect
import InteractingSLE.Spec.ZhanGT4.A1CanonStatement

/-!
# A.1's rectangle cores from the density form on the product of the two path spaces

Packet PROVE-A1CORE. Source: Astra, *Follow-up 5* §1.3 (`source/external/AstraIG1/ig1_followup5.txt` L203–L222,
R73), *Follow-up proofs* §A.1.5 (`ig1_followup_proofs.txt` L409–L425, R38: "For its first `n` pairs use (D11) to
obtain a coupling of the two fixed complete marginal path laws"), follow-up 4 §2.5.4 (R71).

A1CANON reduced R72's Canon statements to `A1Canon.A1DualCoupling{G3,Eight}CoreStatement` (one coupling space; at
every usual-augmentation stopping time of the coupling, the image noise a Brownian motion stopped at each rectangle cap
under the coupling). The source's A.1.5 coupling is a coupling `μ` of the two **complete marginal path laws** `P₁`
(small curve, on `X`) and `P₂` (large curve, on `Y`) — the form of A22's `exists_seedCoupling_of_prefix_laws` — and
its §1.3 supplies the image law per rectangle through the joint density and conditional Girsanov. The statements here
are the Core statements in that form:

* **`A1DualCouplingG3RectStatement κ`**, **`A1DualCouplingEightRectStatement κ`**: two standard Borel path spaces
  with the two complete marginal evolutions, a coupling `μ` of `X × Y` with these marginals, and the two directional
  density-form rectangle cores `IsRectImageCore` (small curve's image given the large curve, stopping times of the
  large curve's own usual augmentation under `P₂`) and `IsRectImageCoreFst` (large given small);
* **`a1DualCouplingG3CoreStatement_of_rect`**, **`a1DualCouplingEightCoreStatement_of_rect`** (the pullback evolutions
  and `isCanonImageCore_of_rect{,_fst}`), chained to R72's Canon statements
  (`a1DualCoupling{G3,Eight}CanonStatement_of_rect`) and A.3 (`firstSwallowCrosscutStatement_of_rect`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A1Core

open A2X A1Ref A1Canon

/-- **A.1 (G3) in density form** (`4 < κ < 8`, `y < x < 0`): the small curve's complete law `P₁` on a standard Borel
space `X` (`κ̂ = 16/κ`, its word `![0], ![0, x − y, −y]`), the large curve's complete law `P₂` on `Y` (from `0`, marks
`x, y` with weights `κ − 4, −4`), a coupling `μ` of `X × Y` with these marginals, and the two directional rectangle
cores in density form with the image data of `A1Ref.A1DualCouplingG3CanonStatement`. -/
def A1DualCouplingG3RectStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (μ : Measure (X × Y)) (_ : IsProbabilityMeasure μ)
      (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁
        ζ₁ ∧
      IsRectImageCore (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
        W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
        (smallG3RhoR κ) ∧
      IsRectImageCoreFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
        (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight) in density form** (`8 ≤ κ`, `x < 0`), with the image data of
`A1Ref.A1DualCouplingEightCanonStatement`. -/
def A1DualCouplingEightRectStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (μ : Measure (X × Y)) (_ : IsProbabilityMeasure μ)
      (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      IsRectImageCore (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
        W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
      IsRectImageCoreFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
        (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **The density form gives A1CANON's rectangle core (G3)**: the coupling space is `X × Y`, the marginal evolutions
are pulled back (`Coupling.IsIntegratedSLEEvolution.comap`), and the two directional cores come from
`isCanonImageCore_of_rect` and `isCanonImageCore_of_rect_fst`. -/
theorem a1DualCouplingG3CoreStatement_of_rect {κ : ℝ} (h : A1DualCouplingG3RectStatement κ) :
    A1DualCouplingG3CoreStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hc₁, hc₂⟩ := h hκ4 hκ8 y x hyx hx
  exact ⟨X × Y, inferInstance, inferInstance, μ, hμ, Coupling.filtrationComap 𝓕₂ measurable_snd,
    Coupling.filtrationComap 𝓕₁ measurable_fst, fun t z => W₂ t z.2, fun i t z => VL₂ i t z.2,
    fun i t z => VR₂ i t z.2, fun t z => B₂ t z.2, fun z => ζ₂ z.2, fun t z => W₁ t z.1,
    fun i t z => VL₁ i t z.1, fun i t z => VR₁ i t z.1, fun t z => B₁ t z.1, fun z => ζ₁ z.1,
    Coupling.IsIntegratedSLEEvolution.comap measurable_snd hm₂ h₂,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hm₁ h₁,
    isCanonImageCore_of_rect hm₂ hc₁, isCanonImageCore_of_rect_fst hm₁ hc₂⟩

/-- **The density form gives A1CANON's rectangle core (Eight).** -/
theorem a1DualCouplingEightCoreStatement_of_rect {κ : ℝ} (h : A1DualCouplingEightRectStatement κ) :
    A1DualCouplingEightCoreStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hc₁, hc₂⟩ := h hκ8 x hx
  exact ⟨X × Y, inferInstance, inferInstance, μ, hμ, Coupling.filtrationComap 𝓕₂ measurable_snd,
    Coupling.filtrationComap 𝓕₁ measurable_fst, fun t z => W₂ t z.2, fun i t z => VL₂ i t z.2,
    fun i t z => VR₂ i t z.2, fun t z => B₂ t z.2, fun z => ζ₂ z.2, fun t z => W₁ t z.1,
    fun i t z => VL₁ i t z.1, fun i t z => VR₁ i t z.1, fun t z => B₁ t z.1, fun z => ζ₁ z.1,
    Coupling.IsIntegratedSLEEvolution.comap measurable_snd hm₂ h₂,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hm₁ h₁,
    isCanonImageCore_of_rect hm₂ hc₁, isCanonImageCore_of_rect_fst hm₁ hc₂⟩

/-- R72's Canon statement (G3) from the density form. -/
theorem a1DualCouplingG3CanonStatement_of_rect {κ : ℝ} (h : A1DualCouplingG3RectStatement κ) :
    A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_core (a1DualCouplingG3CoreStatement_of_rect h)

/-- R72's Canon statement (Eight) from the density form. -/
theorem a1DualCouplingEightCanonStatement_of_rect {κ : ℝ} (h : A1DualCouplingEightRectStatement κ) :
    A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_core (a1DualCouplingEightCoreStatement_of_rect h)

/-- **A.3 from the two density forms and A.2's three parts.** -/
theorem firstSwallowCrosscutStatement_of_rect {κ : ℝ} (hA1 : A1DualCouplingG3RectStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightRectStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  firstSwallowCrosscutStatement_of_core (a1DualCouplingG3CoreStatement_of_rect hA1) h1 h2 h3
    (a1DualCouplingEightCoreStatement_of_rect hA1') h1' h2' h3'

end InteractingSLE.ZhanGT4.A1Core
