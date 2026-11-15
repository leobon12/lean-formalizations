/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawFrozen
import InteractingSLE.Spec.ZhanGT4.A1RectLawSplit
import InteractingSLE.Spec.ZhanGT4.A1RectMeasG3
import InteractingSLE.Spec.ZhanGT4.CrosscutRestart

/-!
# Zhan's A.1 under R83: the successor wiring onto the C cores

Packet PROVE-A1-RECTLAW2 (R83). The image noise of A.1's rectangle cores is continuous only before each cap
(`A1RectLaw.IsRectImageCoreC`, `IsRectImageCoreFstC`). This file re-wires the whole A.1 line onto that form; the
targets downstream of the cores (A1CORE's `A1DualCoupling{G3,Eight}CoreStatement`, A1REF's Canon statements, A.3) are
unchanged, because `A1RectLaw.isCanonImageCore_of_rectC` gives A1CANON's core (with global continuity) back.

* `HasFamilyLawC`, `HasFamilyLawFstC` (the family inputs with `FrozenFamilyC`), `HasFamilyLaw.toC`,
  `HasFamilyLawFst.toC`;
* `isRectImageCoreC_strip_of_family`, `isRectImageCoreFstC_lt_of_family`: for regular marginals the family inputs give
  the C cores;
* **`A1DualCouplingG3RectCStatement`**, **`A1DualCouplingEightRectCStatement`** (R76's Rect statements with the C
  cores), `a1DualCoupling{G3,Eight}RectCStatement_of_rect` (old ⇒ new),
  **`a1DualCoupling{G3,Eight}CoreStatement_of_rectC`**, `a1DualCoupling{G3,Eight}CanonStatement_of_rectC`,
  `firstSwallowCrosscutStatement_of_rectC`;
* **`A1DualCouplingEightSeedMCStatement`**, **`A1DualCouplingG3SeedGCStatement`** (the seeded forms with the C laws),
  the old ⇒ new implications, and **`a1DualCoupling{Eight,G3}RectCStatement_of_seed{MC,GC}`**.

The C forms of A1-ASSEMBLE's law inputs `EightRectLaw` / `G3RectLaw` and their direction splits are in `A1RLawStmt`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1RectLaw

/-! ### The family inputs with the C families -/

section Family

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-- **The frozen-curve family input under R83, conditioning curve on `Y`**: `A1Law.HasFamilyLaw` with a
`FrozenFamilyC` (image noise continuous before each cap). -/
def HasFamilyLawC (a : ℝ) (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (𝓕k : Filtration ℝ≥0 mY)
    (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (ΘL : ℝ≥0 → Y → Fin nL → ℝ) (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ F : FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR,
    ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (FamilyRectC F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})

/-- **The frozen-curve family input under R83, conditioning curve on `X`** (mirror of `HasFamilyLawC`). -/
def HasFamilyLawFstC (a : ℝ) (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (𝓕k : Filtration ℝ≥0 mX)
    (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ F : FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR,
    ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (FamilyRectFstC F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})

variable {a : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)}

/-- The old family input gives the new one. -/
theorem HasFamilyLaw.toC {𝓕k : Filtration ℝ≥0 mY} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ}
    {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : HasFamilyLaw a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    HasFamilyLawC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨F, hR⟩ := h
  exact ⟨FrozenFamily.toC F, fun τ hτ => (hR τ hτ).map FamilyRect.toC⟩

/-- The old family input gives the new one (conditioning curve on `X`). -/
theorem HasFamilyLawFst.toC {𝓕k : Filtration ℝ≥0 mX} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ}
    {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : HasFamilyLawFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    HasFamilyLawFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨F, hR⟩ := h
  exact ⟨FrozenFamilyFst.toC F, fun τ hτ => (hR τ hτ).map FamilyRectFst.toC⟩

/-- **The C core, conditioning curve on `Y` with live event the strip life of its mark `i₀`**, from regular marginals
and the C family input (A1-LAW's `rectLawPart_strip_of_family` and A1-MARG's `isRectImageCore_strip_of_reg`, with
`isRectImageCoreC_of_family`). -/
theorem isRectImageCoreC_strip_of_family {ak aj : ℝ} {nLk nRk nLj nRj : ℕ}
    {xLk : Fin nLk → ℝ} {xRk : Fin nRk → ℝ} {ρLk : Fin nLk → ℝ} {ρRk : Fin nRk → ℝ}
    {xLj : Fin nLj → ℝ} {xRj : Fin nRj → ℝ} {ρLj : Fin nLj → ℝ} {ρRj : Fin nRj → ℝ}
    {𝓕k : Filtration ℝ≥0 mY} {𝓕j : Filtration ℝ≥0 mX}
    {Wk : ℝ≥0 → Y → ℝ} {VLk : Fin nLk → ℝ≥0 → Y → ℝ} {VRk : Fin nRk → ℝ≥0 → Y → ℝ} {Bk : ℝ≥0 → Y → ℝ}
    {ζk : Y → ℝ≥0∞} {Wj : ℝ≥0 → X → ℝ} {VLj : Fin nLj → ℝ≥0 → X → ℝ} {VRj : Fin nRj → ℝ≥0 → X → ℝ}
    {Bj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    (hk : IsRegMarginal ak xLk xRk ρLk ρRk P₂ 𝓕k Wk VLk VRk Bk ζk)
    (hj : IsRegMarginal aj xLj xRj ρLj ρRj P₁ 𝓕j Wj VLj VRj Bj ζj) (i₀ : Fin nLk) (xj xk : ℝ)
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hΘL : IsStronglyProgressive 𝓕k ΘL) (hΘR : IsStronglyProgressive 𝓕k ΘR)
    (h : HasFamilyLawC a P₁ P₂ μ 𝓕k (fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) xj Wj ζj xk Wk
      ΘL ΘR ρL ρR) :
    IsRectImageCoreC a P₁ P₂ μ 𝓕k (fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) xj Wj ζj xk Wk
      ΘL ΘR ρL ρR := by
  obtain ⟨F, hR⟩ := h
  have hcW : ∀ y, ContinuousOn (Wk · y) {s | (s : ℝ≥0∞) < ζk y} := fun y => (hk.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VLk i₀ · y) {s | (s : ℝ≥0∞) < ζk y} := fun y => (hk.path y).2.2.2.2.1 i₀
  have hm1 := isStronglyProgressive_indicator_isStripLife hk.evol.2.1 hk.progW (hk.progVL i₀) hcW hcV
  have hlive := measurableSet_live_of_isStronglyProgressive hm1
  obtain ⟨hm3, hm4⟩ := measurable_rDrv_rLife
    (live := fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) hlive (fun _ _ h => h.1)
    (fun x => (hj.path x).2.2.2.1)
    (fun x => (hj.path x).1) hcW (fun y => (hk.path y).1) (measurable_of_isStronglyProgressive hj.progW)
    (measurable_of_isStronglyProgressive hk.progW) (measurable_lifetime hj.evol.2.1)
    (measurable_lifetime hk.evol.2.1) xj xk
  exact isRectImageCoreC_of_family (isStronglyProgressive_usualAugmentation hm1 P₂)
    (isStronglyProgressive_usualAugmentation hΘL P₂) (isStronglyProgressive_usualAugmentation hΘR P₂) hm3 hm4 F hR

/-- **The C core, conditioning curve on `X`, live event `t < ζ`**, image lifetime the end of the strip life of the
image curve's mark `i₀`, from regular marginals and the C family input. -/
theorem isRectImageCoreFstC_lt_of_family {ak aj : ℝ} {nLk nRk nLj nRj : ℕ}
    {xLk : Fin nLk → ℝ} {xRk : Fin nRk → ℝ} {ρLk : Fin nLk → ℝ} {ρRk : Fin nRk → ℝ}
    {xLj : Fin nLj → ℝ} {xRj : Fin nRj → ℝ} {ρLj : Fin nLj → ℝ} {ρRj : Fin nRj → ℝ}
    {𝓕k : Filtration ℝ≥0 mX} {𝓕j : Filtration ℝ≥0 mY}
    {Wk : ℝ≥0 → X → ℝ} {VLk : Fin nLk → ℝ≥0 → X → ℝ} {VRk : Fin nRk → ℝ≥0 → X → ℝ} {Bk : ℝ≥0 → X → ℝ}
    {ζk : X → ℝ≥0∞} {Wj : ℝ≥0 → Y → ℝ} {VLj : Fin nLj → ℝ≥0 → Y → ℝ} {VRj : Fin nRj → ℝ≥0 → Y → ℝ}
    {Bj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    (hk : IsRegMarginal ak xLk xRk ρLk ρRk P₁ 𝓕k Wk VLk VRk Bk ζk)
    (hj : IsRegMarginal aj xLj xRj ρLj ρRj P₂ 𝓕j Wj VLj VRj Bj ζj) (i₀ : Fin nLj) (xj xk : ℝ)
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hΘL : IsStronglyProgressive 𝓕k ΘL) (hΘR : IsStronglyProgressive 𝓕k ΘR)
    (h : HasFamilyLawFstC a P₁ P₂ μ 𝓕k (fun t ω => (t : ℝ≥0∞) < ζk ω) xj Wj
      (fun ω => lifeEnd (Wj · ω) (VLj i₀ · ω) (ζj ω)) xk Wk ΘL ΘR ρL ρR) :
    IsRectImageCoreFstC a P₁ P₂ μ 𝓕k (fun t ω => (t : ℝ≥0∞) < ζk ω) xj Wj
      (fun ω => lifeEnd (Wj · ω) (VLj i₀ · ω) (ζj ω)) xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨F, hR⟩ := h
  have hm1 := isStronglyProgressive_indicator_lt hk.evol.2.1
  have hlive := measurableSet_live_of_isStronglyProgressive hm1
  have hcW : ∀ y, ContinuousOn (Wj · y) {s | (s : ℝ≥0∞) < ζj y} := fun y => (hj.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VLj i₀ · y) {s | (s : ℝ≥0∞) < ζj y} := fun y => (hj.path y).2.2.2.2.1 i₀
  have hS := measurableSet_live_of_isStronglyProgressive
    (isStronglyProgressive_indicator_isStripLife hj.evol.2.1 hj.progW (hj.progVL i₀) hcW hcV)
  obtain ⟨hm3, hm4⟩ := measurable_rDrvFst_rLifeFst
    (live := fun t ω => (t : ℝ≥0∞) < ζk ω) hlive (fun _ _ h => h)
    (fun y => (hcW y).mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _)) (fun y => (hj.path y).1)
    (fun x => (hk.path x).2.2.2.1) (fun x => (hk.path x).1) (measurable_of_isStronglyProgressive hj.progW)
    (measurable_of_isStronglyProgressive hk.progW) (measurable_lifeEnd hS) (measurable_lifetime hk.evol.2.1) xj xk
  exact isRectImageCoreFstC_of_family (isStronglyProgressive_usualAugmentation hm1 P₁)
    (isStronglyProgressive_usualAugmentation hΘL P₁) (isStronglyProgressive_usualAugmentation hΘR P₁) hm3 hm4 F hR

end Family

/-! ### R76's Rect statements with the C cores -/

section Rect

/-- **A.1 (G3) in density form under R83**: R76's `A1Core.A1DualCouplingG3RectStatement` with the C cores
(`IsRectImageCoreC`, `IsRectImageCoreFstC`: the image noise continuous before each cap). -/
def A1DualCouplingG3RectCStatement (κ : ℝ) : Prop :=
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
      IsRectImageCoreC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
        W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
        (smallG3RhoR κ) ∧
      IsRectImageCoreFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
        (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight) in density form under R83**: R76's `A1Core.A1DualCouplingEightRectStatement` with the C cores. -/
def A1DualCouplingEightRectCStatement (κ : ℝ) : Prop :=
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
      IsRectImageCoreC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
        W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
      IsRectImageCoreFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
        (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- The old Rect statement (G3) gives the C one. -/
theorem a1DualCouplingG3RectCStatement_of_rect {κ : ℝ} (h : A1DualCouplingG3RectStatement κ) :
    A1DualCouplingG3RectCStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hc₁, hc₂⟩ := h hκ4 hκ8 y x hyx hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, IsRectImageCore.toC hc₁, IsRectImageCoreFst.toC hc₂⟩

/-- The old Rect statement (Eight) gives the C one. -/
theorem a1DualCouplingEightRectCStatement_of_rect {κ : ℝ} (h : A1DualCouplingEightRectStatement κ) :
    A1DualCouplingEightRectCStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hc₁, hc₂⟩ := h hκ8 x hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, IsRectImageCore.toC hc₁, IsRectImageCoreFst.toC hc₂⟩

/-- **The C density form gives A1CANON's rectangle core (G3)**: as A1CORE's `a1DualCouplingG3CoreStatement_of_rect`,
with `isCanonImageCore_of_rectC` (and its mirror) in place of `isCanonImageCore_of_rect`; the auxiliary continuous
Brownian motion is a continuous version of the small marginal's driving Brownian motion
(`ZhanGT4.exists_continuous_version_zero`). -/
theorem a1DualCouplingG3CoreStatement_of_rectC {κ : ℝ} (h : A1DualCouplingG3RectCStatement κ) :
    A1DualCouplingG3CoreStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hc₁, hc₂⟩ := h hκ4 hκ8 y x hyx hx
  obtain ⟨β, -, hβc, hβ0, hβ, -⟩ := ZhanGT4.exists_continuous_version_zero h₁.1
  exact ⟨X × Y, inferInstance, inferInstance, μ, hμ, Coupling.filtrationComap 𝓕₂ measurable_snd,
    Coupling.filtrationComap 𝓕₁ measurable_fst, fun t z => W₂ t z.2, fun i t z => VL₂ i t z.2,
    fun i t z => VR₂ i t z.2, fun t z => B₂ t z.2, fun z => ζ₂ z.2, fun t z => W₁ t z.1,
    fun i t z => VL₁ i t z.1, fun i t z => VR₁ i t z.1, fun t z => B₁ t z.1, fun z => ζ₁ z.1,
    Coupling.IsIntegratedSLEEvolution.comap measurable_snd hm₂ h₂,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hm₁ h₁,
    isCanonImageCore_of_rectC hm₂ hc₁ hβ hβc hβ0, isCanonImageCore_of_rectC_fst hm₁ hc₂ hβ hβc hβ0⟩

/-- **The C density form gives A1CANON's rectangle core (Eight).** -/
theorem a1DualCouplingEightCoreStatement_of_rectC {κ : ℝ} (h : A1DualCouplingEightRectCStatement κ) :
    A1DualCouplingEightCoreStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hc₁, hc₂⟩ := h hκ8 x hx
  obtain ⟨β, -, hβc, hβ0, hβ, -⟩ := ZhanGT4.exists_continuous_version_zero h₁.1
  exact ⟨X × Y, inferInstance, inferInstance, μ, hμ, Coupling.filtrationComap 𝓕₂ measurable_snd,
    Coupling.filtrationComap 𝓕₁ measurable_fst, fun t z => W₂ t z.2, fun i t z => VL₂ i t z.2,
    fun i t z => VR₂ i t z.2, fun t z => B₂ t z.2, fun z => ζ₂ z.2, fun t z => W₁ t z.1,
    fun i t z => VL₁ i t z.1, fun i t z => VR₁ i t z.1, fun t z => B₁ t z.1, fun z => ζ₁ z.1,
    Coupling.IsIntegratedSLEEvolution.comap measurable_snd hm₂ h₂,
    Coupling.IsIntegratedSLEEvolution.comap measurable_fst hm₁ h₁,
    isCanonImageCore_of_rectC hm₂ hc₁ hβ hβc hβ0, isCanonImageCore_of_rectC_fst hm₁ hc₂ hβ hβc hβ0⟩

/-- R72's Canon statement (G3) from the C density form. -/
theorem a1DualCouplingG3CanonStatement_of_rectC {κ : ℝ} (h : A1DualCouplingG3RectCStatement κ) :
    A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_core (a1DualCouplingG3CoreStatement_of_rectC h)

/-- R72's Canon statement (Eight) from the C density form. -/
theorem a1DualCouplingEightCanonStatement_of_rectC {κ : ℝ} (h : A1DualCouplingEightRectCStatement κ) :
    A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_core (a1DualCouplingEightCoreStatement_of_rectC h)

/-- **A.3 from the two C density forms and A.2's three parts.** -/
theorem firstSwallowCrosscutStatement_of_rectC {κ : ℝ} (hA1 : A1DualCouplingG3RectCStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightRectCStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  firstSwallowCrosscutStatement_of_core (a1DualCouplingG3CoreStatement_of_rectC hA1) h1 h2 h3
    (a1DualCouplingEightCoreStatement_of_rectC hA1') h1' h2' h3'

end Rect

/-! ### The seeded forms with the C laws -/

section Seed

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- `SeedFieldInputM` is monotone in the law property. -/
theorem seedFieldInputM_mono {P₁ : Measure X} {P₂ : Measure Y} {κ : ℝ} {Law Law' : Measure (X × Y) → Prop}
    (h : SeedFieldInputM P₁ P₂ κ Law) (hL : ∀ μ, Law μ → Law' μ) : SeedFieldInputM P₁ P₂ κ Law' := by
  obtain ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hc, hrow, hrowc,
    hmeas, hlaw⟩ := h
  exact ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hc, hrow, hrowc,
    hmeas, fun μ hμ hμ₁ hμ₂ hd => hL μ (hlaw μ hμ hμ₁ hμ₂ hd)⟩

/-- `SeedFieldInputG` is monotone in the law property. -/
theorem seedFieldInputG_mono {P₁ : Measure X} {P₂ : Measure Y} {κ : ℝ} {Law Law' : Measure (X × Y) → Prop}
    (h : SeedFieldInputG P₁ P₂ κ Law) (hL : ∀ μ, Law μ → Law' μ) : SeedFieldInputG P₁ P₂ κ Law' := by
  obtain ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hc, hrow, hrowc,
    hmeas, hlaw⟩ := h
  exact ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hc, hrow, hrowc,
    hmeas, fun μ hμ hμ₁ hμ₂ hd => hL μ (hlaw μ hμ hμ₁ hμ₂ hd)⟩

end Seed

section SeedConfig

/-- **A.1 (Eight), rectangle-wise seeded form under R83**: A1-EIGHTSEED's `A1DualCouplingEightSeedMStatement` with the
law property `HasFamilyLawC ∧ HasFamilyLawFstC` (the C families). -/
def A1DualCouplingEightSeedMCStatement (κ : ℝ) : Prop :=
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
      SeedFieldInputM P₁ P₂ (kh κ) fun μ =>
        HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **A.1 (G3), rectangle-wise mixed-mark seeded form under R83**: A1-G3CALC's `A1DualCouplingG3SeedGStatement` with
the law property `HasFamilyLawC ∧ HasFamilyLawFstC`. -/
def A1DualCouplingG3SeedGCStatement (κ : ℝ) : Prop :=
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
      SeedFieldInputG P₁ P₂ (kh κ) fun μ =>
        HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- The old seeded Eight statement gives the C one. -/
theorem a1DualCouplingEightSeedMCStatement_of_seedM {κ : ℝ} (h : A1DualCouplingEightSeedMStatement κ) :
    A1DualCouplingEightSeedMCStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact seedFieldInputM_mono (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)
    fun _ hl => ⟨HasFamilyLaw.toC hl.1, HasFamilyLawFst.toC hl.2⟩

/-- The old seeded G3 statement gives the C one. -/
theorem a1DualCouplingG3SeedGCStatement_of_seedG {κ : ℝ} (h : A1DualCouplingG3SeedGStatement κ) :
    A1DualCouplingG3SeedGCStatement κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact seedFieldInputG_mono
    (h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)
    fun _ hl => ⟨HasFamilyLaw.toC hl.1, HasFamilyLawFst.toC hl.2⟩

/-- **The C seeded form gives the C Rect statement (Eight)**: regular marginals exist (`exists_regMarginals_Eight`);
the seeded data are the finite patches (`fieldPatchSigmaInput_of_seedFieldInputM`,
`patchInput_of_fieldPatchSigmaInput`), the countable patch gives the coupling (`exists_coupling_of_patchInput`), and
the C family inputs give the C cores. -/
theorem a1DualCouplingEightRectCStatement_of_seedMC {κ : ℝ} (h : A1DualCouplingEightSeedMCStatement κ) :
    A1DualCouplingEightRectCStatement κ := by
  intro hκ8 x hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_Eight hκ8 hx
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := exists_coupling_of_patchInput (patchInput_of_fieldPatchSigmaInput
    (fieldPatchSigmaInput_of_seedFieldInputM hk
      (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)))
  refine ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂.evol, h₁.evol, ?_, ?_⟩
  · exact isRectImageCoreC_strip_of_family h₂ h₁ 0 x 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 0))
          isStronglyProgressive_nil)) hl₁
  · exact isRectImageCoreFstC_lt_of_family h₁ h₂ 0 0 x
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 1))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 1))
            isStronglyProgressive_nil)))
      (isStronglyProgressive_const _ _) hl₂

/-- **The C seeded form gives the C Rect statement (G3).** -/
theorem a1DualCouplingG3RectCStatement_of_seedGC {κ : ℝ} (h : A1DualCouplingG3SeedGCStatement κ) :
    A1DualCouplingG3RectCStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_G3 hκ4 hyx hx
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := exists_coupling_of_patchInput (patchInput_of_fieldPatchSigmaInput
    (fieldPatchSigmaInput_of_seedFieldInputG hk
      (h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)))
  refine ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂.evol, h₁.evol, ?_, ?_⟩
  · exact isRectImageCoreC_strip_of_family h₂ h₁ 0 y 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₂.progVL 0) (h₂.progVL 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 1))
            isStronglyProgressive_nil))) hl₁
  · exact isRectImageCoreFstC_lt_of_family h₁ h₂ 0 0 y
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 1) (h₁.progVR 2))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 2))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 2))
            (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 2))
              isStronglyProgressive_nil))))
      (isStronglyProgressive_const _ _) hl₂

/-- **A1CORE's Core statement (Eight) from the C seeded form.** -/
theorem a1DualCouplingEightCoreStatement_of_seedMC {κ : ℝ} (h : A1DualCouplingEightSeedMCStatement κ) :
    A1DualCouplingEightCoreStatement κ :=
  a1DualCouplingEightCoreStatement_of_rectC (a1DualCouplingEightRectCStatement_of_seedMC h)

/-- **A1CORE's Core statement (G3) from the C seeded form.** -/
theorem a1DualCouplingG3CoreStatement_of_seedGC {κ : ℝ} (h : A1DualCouplingG3SeedGCStatement κ) :
    A1DualCouplingG3CoreStatement κ :=
  a1DualCouplingG3CoreStatement_of_rectC (a1DualCouplingG3RectCStatement_of_seedGC h)

/-- R72's Canon statement (Eight) from the C seeded form. -/
theorem a1DualCouplingEightCanonStatement_of_seedMC {κ : ℝ} (h : A1DualCouplingEightSeedMCStatement κ) :
    A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_core (a1DualCouplingEightCoreStatement_of_seedMC h)

/-- R72's Canon statement (G3) from the C seeded form. -/
theorem a1DualCouplingG3CanonStatement_of_seedGC {κ : ℝ} (h : A1DualCouplingG3SeedGCStatement κ) :
    A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_core (a1DualCouplingG3CoreStatement_of_seedGC h)

end SeedConfig

end InteractingSLE.ZhanGT4.A1RLaw
