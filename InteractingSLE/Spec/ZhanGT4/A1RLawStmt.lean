/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawWire

/-!
# Zhan's A.1 under R83: the law input (I2) with the C families, and its two directions

Packet PROVE-A1-RECTLAW2 (R83). A1-ASSEMBLE's law inputs `A1Asm.EightRectLaw` / `A1Asm.G3RectLaw` conclude
`HasFamilyLaw ∧ HasFamilyLawFst`, whose families ask for a globally continuous image noise (refuted in general by
PROVE-A1-RECTLAW, R83). Their successors conclude `HasFamilyLawC ∧ HasFamilyLawFstC` with exactly the same binders:

* **`EightRectLawC`**, **`G3RectLawC`**, and the direction splits `EightRectLawSndC`, `EightRectLawFstC`,
  `G3RectLawSndC`, `G3RectLawFstC` (A1-RECTLAW's split, each one conjunct);
* **`eightRectLawC_of_dirs`**, **`g3RectLawC_of_dirs`**; the old inputs give the new ones (`*_of_*`);
* **`a1DualCouplingEightSeedMCStatement_of_rectLawC`** (A22's `a1DualCouplingEightSeedMStatement_of_rectLaw` for the C
  law), **`a1DualCouplingG3SeedGCStatement_of_rowLawC`** (A1-RECTMEAS's `a1DualCouplingG3SeedGStatement_of_rowLaw`);
* **`a1DualCouplingEightCoreStatement_of_dirsC`**, **`a1DualCouplingG3CoreStatement_of_dirsC`**: the two directions
  (and G3's rows) give A1CORE's Core statements.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1RectLaw

/-! ### The law inputs under R83 -/

/-- **The law input (I2) of Eight under R83** (A1-ASSEMBLE's `EightRectLaw` with the C families; `hlaw`): for every
pair of regular Eight marginals and every pair of patched versions (`IsPatchOf`), every coupling of the two laws whose
density on each cofinal rectangle of the patched versions is the seeded height field (`RectDens`) has the C law
property of A.1 (Eight) for the original marginals. -/
def EightRectLawC (κ : ℝ) : Prop :=
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
        HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
            W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
          HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
            (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
            (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
            (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **The law input (I2) of G3 under R83** (A1-ASSEMBLE's `G3RectLaw` with the C families; `hlaw`): for every pair
of regular G3 marginals and every pair of patched versions (`IsPatchOf`), every coupling of the two laws whose density
on each rectangle of the patched versions is the seeded height field (`RectDens`) has the C law property of A.1 (G3)
for the original marginals. -/
def G3RectLawC (κ : ℝ) : Prop :=
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
        HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
            W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
            (smallG3RhoR κ) ∧
          HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
            (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
            (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω,
              VL₁ 0 t ω - VR₁ 2 t ω])
            (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **(I2) for Eight under R83, the small-curve direction**: the binders of `EightRectLawC`, concluding its first
conjunct (the image of the small curve given the large curve frozen at a stopping time of `𝓕₂`). -/
def EightRectLawSndC (κ : ℝ) : Prop :=
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
        HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ)

/-- **(I2) for Eight under R83, the large-curve direction**: the binders of `EightRectLawC`, concluding its second
conjunct (the image of the large curve given the small curve frozen at a stopping time of `𝓕₁`). -/
def EightRectLawFstC (κ : ℝ) : Prop :=
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
        HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **(I2) for G3 under R83, the small-curve direction**: the binders of `G3RectLawC`, concluding its first conjunct. -/
def G3RectLawSndC (κ : ℝ) : Prop :=
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
        HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ)

/-- **(I2) for G3 under R83, the large-curve direction**: the binders of `G3RectLawC`, concluding its second
conjunct. -/
def G3RectLawFstC (κ : ℝ) : Prop :=
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
        HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω,
            VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-! ### The two directions; the old inputs give the new ones -/

/-- **The two Eight directions give the C law input.** -/
theorem eightRectLawC_of_dirs {κ : ℝ} (hS : EightRectLawSndC κ) (hF : EightRectLawFstC κ) : EightRectLawC κ :=
  fun hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd =>
    ⟨hS hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd,
     hF hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd⟩

/-- **The two G3 directions give the C law input.** -/
theorem g3RectLawC_of_dirs {κ : ℝ} (hS : G3RectLawSndC κ) (hF : G3RectLawFstC κ) : G3RectLawC κ :=
  fun hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂'
      B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd =>
    ⟨hS hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
      VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd,
     hF hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
      VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd⟩

/-- The old Eight law input gives the C one. -/
theorem eightRectLawC_of_eightRectLaw {κ : ℝ} (h : EightRectLaw κ) : EightRectLawC κ :=
  fun hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd =>
    have hl := h hκ x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂'
      B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd
    ⟨HasFamilyLaw.toC hl.1, HasFamilyLawFst.toC hl.2⟩

/-- The old G3 law input gives the C one. -/
theorem g3RectLawC_of_g3RectLaw {κ : ℝ} (h : G3RectLaw κ) : G3RectLawC κ :=
  fun hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂'
      B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd =>
    have hl := h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂'
      VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd
    ⟨HasFamilyLaw.toC hl.1, HasFamilyLawFst.toC hl.2⟩

/-! ### The seeded statements from the C law inputs -/

/-- **A.1 (Eight), rectangle-wise seeded C form, from the C law input alone** (A22's
`a1DualCouplingEightSeedMStatement_of_rectLaw` for `EightRectLawC`: null patching, rectangles, columns, rows and the
seeded fields' measurability are all constructed). -/
theorem a1DualCouplingEightSeedMCStatement_of_rectLawC {κ : ℝ} (hL : EightRectLawC κ) :
    A1DualCouplingEightSeedMCStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨W₁', VL₁', VR₁', B₁', ζ₁', hp₁⟩ := exists_isPatchOf h₁ GoodSmallEight (ae_goodSmallEight hκ8 hx h₁)
  obtain ⟨W₂', VL₂', VR₂', B₂', ζ₂', hp₂⟩ :=
    exists_isPatchOf h₂ (fun _ _ _ _ _ => True) (Eventually.of_forall fun _ => trivial)
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := id hp₁
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := id hp₂
  exact seedFieldInputM_of_patched hκ8 hx h₁' hB₁' hg₁' h₂' hB₂'
    (isFieldMeas_eight_of_patched hκ8 hx h₁' hB₁' hg₁' h₂' hB₂')
    (fun hs₁ hs₂ μ hμ hμ₁ hμ₂ hd => hL hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁
      VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd)

/-- **A.1 (G3), rectangle-wise mixed-mark seeded C form, from the rows and the C law input** (A1-ASSEMBLE's
`a1DualCouplingG3SeedGStatement_of_rect` with A1-RECTMEAS's `g3RectMeas`). -/
theorem a1DualCouplingG3SeedGCStatement_of_rowLawC {κ : ℝ} (hR : G3RectRow κ) (hL : G3RectLawC κ) :
    A1DualCouplingG3SeedGCStatement κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨W₁', VL₁', VR₁', B₁', ζ₁', hp₁⟩ := exists_isPatchOf h₁ GoodSmallG3 (ae_goodSmallG3 hκ4 hκ8 hyx hx h₁)
  obtain ⟨W₂', VL₂', VR₂', B₂', ζ₂', hp₂⟩ :=
    exists_isPatchOf h₂ (fun _ _ _ _ _ => True) (Eventually.of_forall fun _ => trivial)
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := id hp₁
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := id hp₂
  obtain ⟨hrow, hrowc⟩ := hR hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ _ _ inferInstance inferInstance
    W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' h₂' hB₂' h₁' hB₁' hg₁'
  exact seedFieldInputG_of_patched hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hrow hrowc
    (A1RectMeas.g3RectMeas κ hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ _ _ inferInstance inferInstance W₂'
      VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' h₂' hB₂' h₁' hB₁' hg₁')
    (fun hs₁ hs₂ μ hμ hμ₁ hμ₂ hd => hL hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
      W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd)

/-- **A1CORE's Core statement (Eight) from the two directions of the C law input.** -/
theorem a1DualCouplingEightCoreStatement_of_dirsC {κ : ℝ} (hS : EightRectLawSndC κ) (hF : EightRectLawFstC κ) :
    A1DualCouplingEightCoreStatement κ :=
  a1DualCouplingEightCoreStatement_of_seedMC (a1DualCouplingEightSeedMCStatement_of_rectLawC
    (eightRectLawC_of_dirs hS hF))

/-- **A1CORE's Core statement (G3) from the rows and the two directions of the C law input.** -/
theorem a1DualCouplingG3CoreStatement_of_dirsC {κ : ℝ} (hR : G3RectRow κ) (hS : G3RectLawSndC κ)
    (hF : G3RectLawFstC κ) : A1DualCouplingG3CoreStatement κ :=
  a1DualCouplingG3CoreStatement_of_seedGC (a1DualCouplingG3SeedGCStatement_of_rowLawC hR (g3RectLawC_of_dirs hS hF))

end InteractingSLE.ZhanGT4.A1RLaw
