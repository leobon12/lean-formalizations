/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmRow

/-!
# Zhan's A.1 (Eight): the assembly of the rectangle-wise seeded input

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.6 (`ig1_followup_proofs.txt` L300–L500), R76,
R80.

`A1EightSeed.A1DualCouplingEightSeedMStatement κ` asks, for every pair of regular Eight marginals, for A1-EIGHTSEED's
rectangle-wise seeded input `SeedFieldInputM`. Everything except the measurability of the seeded height fields on the
rectangles (`hmeas`) and the law input (I2) (`hlaw`) is now proved:

1. **Patching** (A1-COMMON's `IsRegMarginal.exists_patch`): the small marginal is replaced, off a measurable null set,
   by one that is `GoodSmallEight` and has continuous Brownian paths at every sample, the large one by one with
   continuous Brownian paths at every sample (`IsPatchOf`), both regular in the usual augmentations;
2. **Rectangles**: A15F's cofinal family for the source `−x` (`isEnclFamily_cof`) and the lifetime-capped exits
   `eightS₁`, `eightS₂` (stopping times of the usual augmentations); A1-COMMON's `eight_rect` gives every pathwise
   rectangle hypothesis;
3. **Columns**: `isColumnStoch_eightRec_of_reg` (`A1AsmCol`);
4. **Rows**: `isRowStoch_large_lifeExit` (`A1AsmRow`), so A1-EIGHTFIN's `seedFieldInputM_of_eight_rows` applies.

Main results:

* **`seedFieldInputM_of_patched`**: `SeedFieldInputM` for patched marginals, from `hmeas` and `hlaw` for the
  rectangles `eightS₁`, `eightS₂` only;
* `IsPatchOf`, `exists_isPatchOf`;
* the two named remaining inputs, stated for every patched pair: **`EightRectMeas κ`** (`hmeas`) and
  **`EightRectLaw κ`** ((I2), concluding the law property of the original marginals);
* **`a1DualCouplingEightSeedMStatement_of_rect`**: `EightRectMeas κ → EightRectLaw κ →
  A1DualCouplingEightSeedMStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin

/-! ### Patched marginals -/

section Patch

variable {nL nR : ℕ}

/-- **A patched version of a regular marginal** (A1-COMMON's `IsRegMarginal.exists_patch`): regular in the usual
augmentation of the filtration, with continuous Brownian paths and `Good` path tuples at every sample, and equal to the
original processes on a measurable full-measure set. -/
def IsPatchOf (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (Good : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop)
    {X : Type*} {mX : MeasurableSpace X} (P : Measure X) (𝓕 : Filtration ℝ≥0 mX) (W : ℝ≥0 → X → ℝ)
    (VL : Fin nL → ℝ≥0 → X → ℝ) (VR : Fin nR → ℝ≥0 → X → ℝ) (B : ℝ≥0 → X → ℝ) (ζ : X → ℝ≥0∞)
    (W' : ℝ≥0 → X → ℝ) (VL' : Fin nL → ℝ≥0 → X → ℝ) (VR' : Fin nR → ℝ≥0 → X → ℝ) (B' : ℝ≥0 → X → ℝ)
    (ζ' : X → ℝ≥0∞) : Prop :=
  ∃ G : Set X, MeasurableSet G ∧ P Gᶜ = 0 ∧
    IsRegMarginal a xL xR ρL ρR P (usualAugmentation 𝓕 P) W' VL' VR' B' ζ' ∧
    (∀ x, Continuous (B' · x)) ∧
    (∀ x, Good (W' · x) (fun i t => VL' i t x) (fun i t => VR' i t x) (B' · x) (ζ' x)) ∧
    ∀ x ∈ G, (∀ t, W' t x = W t x) ∧ (∀ i t, VL' i t x = VL i t x) ∧ (∀ i t, VR' i t x = VR i t x) ∧
      (∀ t, B' t x = B t x) ∧ ζ' x = ζ x

/-- Every regular marginal on a probability space has a patched version for any almost sure `Good`. -/
theorem exists_isPatchOf {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {X : Type*} {mX : MeasurableSpace X} {P : Measure X} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mX}
    {W : ℝ≥0 → X → ℝ} {VL : Fin nL → ℝ≥0 → X → ℝ} {VR : Fin nR → ℝ≥0 → X → ℝ} {B : ℝ≥0 → X → ℝ}
    {ζ : X → ℝ≥0∞} (h : IsRegMarginal a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (Good : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop)
    (hGood : ∀ᵐ x ∂P, Good (W · x) (fun i t => VL i t x) (fun i t => VR i t x) (B · x) (ζ x)) :
    ∃ (W' : ℝ≥0 → X → ℝ) (VL' : Fin nL → ℝ≥0 → X → ℝ) (VR' : Fin nR → ℝ≥0 → X → ℝ) (B' : ℝ≥0 → X → ℝ)
      (ζ' : X → ℝ≥0∞), IsPatchOf a xL xR ρL ρR Good P 𝓕 W VL VR B ζ W' VL' VR' B' ζ' := by
  obtain ⟨G, W', VL', VR', B', ζ', hG, hGc, h', hB', hg', hag⟩ := h.exists_patch Good hGood
  exact ⟨W', VL', VR', B', ζ', G, hG, hGc, h', hB', hg', hag⟩

end Patch

/-! ### The rectangles and the assembly for patched marginals -/

section Patched

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The small exits of the Eight assembly**: the small curve's exits from the members of A15F's cofinal family for
the source `−x` (no ordinary marks), capped by the members' caps and by the lifetime. -/
def eightS₁ (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (m : ℕ) (ω : X) : ℝ≥0 :=
  lifeExit (W₁ · ω) (ζ₁ ω) (cofH₁ (-x) (![] : Fin 0 → ℝ) m) (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap

/-- **The large exits of the Eight assembly**: the large curve's exits (driver shifted to its source `−x`) from the
members of the cofinal family, capped by the caps and by the lifetime. -/
def eightS₂ (x : ℝ) (W₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (m : ℕ) (ω : Y) : ℝ≥0 :=
  lifeExit (fun t => W₂ t ω + -x) (ζ₂ ω) (cofH₂ (-x) (![] : Fin 0 → ℝ) m) (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap

/-- **The Eight rectangle-wise seeded input for patched marginals.** For regular Eight marginals in right-continuous
filtrations whose Brownian paths are continuous at every sample and whose small curve is `GoodSmallEight` at every
sample, `SeedFieldInputM` holds with the cofinal rectangles `eightS₁`, `eightS₂` as soon as their seeded height fields
are measurable on the rectangles (`hmeas`) and the law input (I2) holds for them (`hlaw`). -/
theorem seedFieldInputM_of_patched {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₂] {Law : Measure (X × Y) → Prop} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hmeas : ∀ m, IsFieldMeas (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m))
      (fun _ : Unit => eightS₁ x W₁ ζ₁ m) (fun _ : Unit => eightS₂ x W₂ ζ₂ m))
    (hlaw : ∀ (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
      (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0)) (μ : Measure (X × Y)),
      IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
        ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m) ω
          (eightS₁ x W₁ ζ₁ m ω.1) (eightS₂ x W₂ ζ₂ m ω.2))) → Law μ) :
    SeedFieldInputM P₁ P₂ (kh κ) Law := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨hU, hgood₁, hsep₁, hc₂, h0₂, hgood₂, hS₂pos, hlt₂⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) m
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  have hstoch : ∀ m (ω₂ : Y), 0 < (eightS₂ x W₂ ζ₂ m ω₂ : ℝ) → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓖₁ P₁ (kh κ) (fun ω => eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m
        (eightS₂ x W₂ ζ₂ m ω₂) (ω, ω₂)) (eightS₁ x W₁ ζ₁ m) B D := by
    intro m ω₂ _
    have hlt : ∀ ω (s : ℝ≥0), s ≤ eightS₁ x W₁ ζ₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
    exact ⟨B₁, _, isColumnStoch_eightRec_of_reg hk h₁ hB₁ (hs₁ m) (fun ω => (hgood₁ m ω).1)
      (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).2)
      (fun ω s hsS => smallEight_sepP_of_good hx (h₁.path ω) (hg₁ ω) s (hlt ω s hsS))⟩
  exact seedFieldInputM_of_eight_rows (by linarith) 𝓖₁ 𝓖₂ (eightS₁ x W₁ ζ₁) (eightS₂ x W₂ ζ₂)
    (cofH₁ (-x) ![]) (cofH₂ (-x) ![]) (cofδ (-x) ![]) (cofq (-x) ![]) (cofd (-x) ![]) (cofTm (-x) ![]) hs₁ hs₂
    hF.pp hU h₁.path rfl rfl hgood₁ hsep₁ hc₂ h0₂ hgood₂ hS₂pos hstoch (x₀ := fun _ => -(-x))
    (fun m => (hF.pp m).sep_pos) (fun _ => by linarith) (fun m => hF.disjoint_ball_neg_src m)
    (fun m => isRowStoch_large_lifeExit hx h₂ hB₂ hF hlt₂ m) hmeas (hlaw hs₁ hs₂)

end Patched

/-! ### The named remaining inputs and the Eight statement -/

section Statement

/-- **The remaining input `hmeas` of Eight** (A1-EIGHTSEED's `IsFieldMeas` per rectangle): for every pair of regular
Eight marginals (any filtrations) with continuous Brownian paths at every sample and a `GoodSmallEight` small curve at
every sample, the seeded height field of every cofinal rectangle `eightS₁ m`, `eightS₂ m` is measurable on the
rectangle. -/
def EightRectMeas (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂ → (∀ ω, Continuous (B₂ · ω)) →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      (∀ ω, Continuous (B₁ · ω)) →
      (∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω)) →
      ∀ m, IsFieldMeas (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m))
        (fun _ : Unit => eightS₁ x W₁ ζ₁ m) (fun _ : Unit => eightS₂ x W₂ ζ₂ m)

/-- **The remaining input (I2) of Eight** (`hlaw`): for every pair of regular Eight marginals and every pair of patched
versions (`IsPatchOf`), every coupling of the two laws whose density on each cofinal rectangle of the patched versions
is the seeded height field (`RectDens`) has the law property of A.1 (Eight) for the original marginals. -/
def EightRectLaw (κ : ℝ) : Prop :=
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
            W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
          HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
            (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
            (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
            (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **A.1 (Eight), rectangle-wise seeded form, from the two named remaining inputs**: the measurability of the
seeded height fields on the cofinal rectangles (`EightRectMeas`) and the law input (I2) for them (`EightRectLaw`)
give `A1DualCouplingEightSeedMStatement κ` (the expanded Theorem 1.2's `hSeed`). Every other clause of
`SeedFieldInputM` is proved: patching, rectangles, columns and rows. -/
theorem a1DualCouplingEightSeedMStatement_of_rect {κ : ℝ} (hM : EightRectMeas κ) (hL : EightRectLaw κ) :
    A1DualCouplingEightSeedMStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨W₁', VL₁', VR₁', B₁', ζ₁', hp₁⟩ := exists_isPatchOf h₁ GoodSmallEight (ae_goodSmallEight hκ8 hx h₁)
  obtain ⟨W₂', VL₂', VR₂', B₂', ζ₂', hp₂⟩ :=
    exists_isPatchOf h₂ (fun _ _ _ _ _ => True) (Eventually.of_forall fun _ => trivial)
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := id hp₁
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := id hp₂
  exact seedFieldInputM_of_patched hκ8 hx h₁' hB₁' hg₁' h₂' hB₂'
    (hM hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ _ _ W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' h₂' hB₂' h₁' hB₁'
      hg₁')
    (fun hs₁ hs₂ μ hμ hμ₁ hμ₂ hd => hL hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁
      VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd)

end Statement

end InteractingSLE.ZhanGT4.A1Asm
