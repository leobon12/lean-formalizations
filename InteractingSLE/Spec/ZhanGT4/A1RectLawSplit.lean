/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmG3
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Statement

/-!
# Zhan's A.1: the law input (I2) split into its two directions

Packet PROVE-A1-RECTLAW. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.6 (`ig1_followup_proofs.txt` L300–L500),
*Follow-up 5* §1.3 (L203–L211); R76, R80.

A1-ASSEMBLE's law inputs `A1Asm.EightRectLaw κ` and `A1Asm.G3RectLaw κ` conclude, for every coupling `μ` with the
seeded rectangle densities of the patched cofinal rectangles, two independent family laws:

* **the small-curve direction** `HasFamilyLaw`: the image of the small curve (on `X`) in the chart of the large curve
  (on `Y`) frozen at a stopping time of the large curve's filtration (A22's seeded one-curve line, the seed word of
  the small curve's own start);
* **the large-curve direction** `HasFamilyLawFst`: the image of the large curve in the chart of the small curve frozen
  at a stopping time of the small curve's filtration (A1-LARGEDENS's frozen-chart line).

The two directions use different stochastic inputs, so they are stated separately here with exactly the binders of
`EightRectLaw` / `G3RectLaw`:

* `EightRectLawSnd`, `EightRectLawFst`, `G3RectLawSnd`, `G3RectLawFst`;
* **`eightRectLaw_of_dirs`**, **`g3RectLaw_of_dirs`**: the two directions give the law input;
* **`a1DualCouplingEightSeedMStatement_of_dirs`**: with A22's `a1DualCouplingEightSeedMStatement_of_rectLaw`, the two
  Eight directions give `A1EightSeed.A1DualCouplingEightSeedMStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectLaw

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm

/-! ### Eight -/

/-- **(I2) for Eight, the small-curve direction**: the binders of `EightRectLaw`, concluding its first conjunct (the
image of the small curve given the large curve frozen at a stopping time of `𝓕₂`). -/
def EightRectLawSnd (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∀ (W₂' : ℝ≥0 → Y → ℝ) (VL₂' : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂' : Fin 0 → ℝ≥0 → Y → ℝ) (B₂' : ℝ≥0 → Y → ℝ)
        (ζ₂' : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 2 → ℝ≥0 → X → ℝ)
        (B₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞),
      IsPatchOf κ ![x] ![] ![0] ![] (fun _ _ _ _ _ => True) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₂' VL₂' VR₂' B₂' ζ₂' →
      IsPatchOf (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) GoodSmallEight P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁
        W₁' VL₁' VR₁' B₁' ζ₁' →
      ∀ (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁' ζ₁' m ω : WithTop ℝ≥0))
        (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂' ζ₂' m ω : WithTop ℝ≥0))
        (μ : Measure (X × Y)), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
        (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
          ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁' VL₁' VR₁' W₂' (eightS₁ x W₁' ζ₁') m) ω
            (eightS₁ x W₁' ζ₁' m ω.1) (eightS₂ x W₂' ζ₂' m ω.2))) →
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ)

/-- **(I2) for Eight, the large-curve direction**: the binders of `EightRectLaw`, concluding its second conjunct (the
image of the large curve given the small curve frozen at a stopping time of `𝓕₁`). -/
def EightRectLawFst (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∀ (W₂' : ℝ≥0 → Y → ℝ) (VL₂' : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂' : Fin 0 → ℝ≥0 → Y → ℝ) (B₂' : ℝ≥0 → Y → ℝ)
        (ζ₂' : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 2 → ℝ≥0 → X → ℝ)
        (B₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞),
      IsPatchOf κ ![x] ![] ![0] ![] (fun _ _ _ _ _ => True) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₂' VL₂' VR₂' B₂' ζ₂' →
      IsPatchOf (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) GoodSmallEight P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁
        W₁' VL₁' VR₁' B₁' ζ₁' →
      ∀ (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁' ζ₁' m ω : WithTop ℝ≥0))
        (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂' ζ₂' m ω : WithTop ℝ≥0))
        (μ : Measure (X × Y)), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
        (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
          ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁' VL₁' VR₁' W₂' (eightS₁ x W₁' ζ₁') m) ω
            (eightS₁ x W₁' ζ₁' m ω.1) (eightS₂ x W₂' ζ₂' m ω.2))) →
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **The two Eight directions give A1-ASSEMBLE's law input (I2).** -/
theorem eightRectLaw_of_dirs {κ : ℝ} (hS : EightRectLawSnd κ) (hF : EightRectLawFst κ) : EightRectLaw κ :=
  fun hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd =>
    ⟨hS hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd,
     hF hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd⟩

/-- **A.1 (Eight), rectangle-wise seeded form, from the two directions of (I2)** (A22's
`a1DualCouplingEightSeedMStatement_of_rectLaw`). -/
theorem a1DualCouplingEightSeedMStatement_of_dirs {κ : ℝ} (hS : EightRectLawSnd κ) (hF : EightRectLawFst κ) :
    A1DualCouplingEightSeedMStatement κ :=
  a1DualCouplingEightSeedMStatement_of_rectLaw (eightRectLaw_of_dirs hS hF)

/-! ### G3 -/

/-- **(I2) for G3, the small-curve direction**: the binders of `G3RectLaw`, concluding its first conjunct. -/
def G3RectLawSnd (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∀ (W₂' : ℝ≥0 → Y → ℝ) (VL₂' : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂' : Fin 0 → ℝ≥0 → Y → ℝ) (B₂' : ℝ≥0 → Y → ℝ)
        (ζ₂' : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 3 → ℝ≥0 → X → ℝ)
        (B₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞),
      IsPatchOf κ ![x, y] ![] ![κ - 4, -4] ![] (fun _ _ _ _ _ => True) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
        W₂' VL₂' VR₂' B₂' ζ₂' →
      IsPatchOf (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) GoodSmallG3 P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁
        W₁' VL₁' VR₁' B₁' ζ₁' →
      ∀ (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁' ζ₁' m ω : WithTop ℝ≥0))
        (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂' ζ₂' m ω : WithTop ℝ≥0))
        (μ : Measure (X × Y)), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
        (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
          ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') m) ω
            (g3S₁ x y W₁' ζ₁' m ω.1) (g3S₂ x y W₂' ζ₂' m ω.2))) →
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ)

/-- **(I2) for G3, the large-curve direction**: the binders of `G3RectLaw`, concluding its second conjunct. -/
def G3RectLawFst (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∀ (W₂' : ℝ≥0 → Y → ℝ) (VL₂' : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂' : Fin 0 → ℝ≥0 → Y → ℝ) (B₂' : ℝ≥0 → Y → ℝ)
        (ζ₂' : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 3 → ℝ≥0 → X → ℝ)
        (B₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞),
      IsPatchOf κ ![x, y] ![] ![κ - 4, -4] ![] (fun _ _ _ _ _ => True) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
        W₂' VL₂' VR₂' B₂' ζ₂' →
      IsPatchOf (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) GoodSmallG3 P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁
        W₁' VL₁' VR₁' B₁' ζ₁' →
      ∀ (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁' ζ₁' m ω : WithTop ℝ≥0))
        (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂' ζ₂' m ω : WithTop ℝ≥0))
        (μ : Measure (X × Y)), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
        (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
          ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') m) ω
            (g3S₁ x y W₁' ζ₁' m ω.1) (g3S₂ x y W₂' ζ₂' m ω.2))) →
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω,
            VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **The two G3 directions give A1-ASSEMBLE's law input (I2).** -/
theorem g3RectLaw_of_dirs {κ : ℝ} (hS : G3RectLawSnd κ) (hF : G3RectLawFst κ) : G3RectLaw κ :=
  fun hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
      VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd =>
    ⟨hS hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
      VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd,
     hF hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
      VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd⟩

end InteractingSLE.ZhanGT4.A1RectLaw
