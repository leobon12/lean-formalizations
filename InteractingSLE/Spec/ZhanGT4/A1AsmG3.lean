/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmEight
import InteractingSLE.Spec.ZhanGT4.A1AsmCofG

/-!
# Zhan's A.1 (G3): the assembly of the rectangle-wise mixed-mark seeded input

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.6 (`ig1_followup_proofs.txt` L300–L500), R76,
R80.

`A1G3Calc.A1DualCouplingG3SeedGStatement κ` asks, for every pair of regular G3 marginals (small curve from `0` with the
seeds `0±`, the ordinary mark `x − y` and the other source `−y`; large curve from `−y`), for A1-G3CALC's
`SeedFieldInputG`. Proved here: patching (`IsPatchOf` with `GoodSmallG3`), the rectangles (the segment family
`cofGH₁`, `cofGH₂` of `A1AsmCofG` for the source `−y` with `qlo = x − y`, so that every member is an
`IsProtectedPairG` with `x − y ≤ q`; exits `g3S₁`, `g3S₂`), every pathwise rectangle hypothesis (A1-COMMON's `g3_rect`),
and the columns (`isColumnStoch_g3Rec_of_reg`). What remains is named:

* **`G3RectRow κ`**: the row martingales and their continuity (`hrow`, `hrowc`; the opposite view of the G3 records,
  A22's and PROVE-A1-G3ROW's line);
* **`G3RectMeas κ`**: the measurability of the seeded height fields on the rectangles (`hmeas`);
* **`G3RectLaw κ`**: the law input (I2) for the rectangles (`hlaw`).

Main results: **`seedFieldInputG_of_patched`** and **`a1DualCouplingG3SeedGStatement_of_rect`**
(`G3RectRow κ → G3RectMeas κ → G3RectLaw κ → A1DualCouplingG3SeedGStatement κ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin

/-! ### The rectangles and the assembly for patched marginals -/

section Patched

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The small exits of the G3 assembly**: the small curve's exits from the members of the segment family for the
source `−y`, the ordinary mark `x − y` and `qlo = x − y`, capped by the caps and by the lifetime. -/
def g3S₁ (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (m : ℕ) (ω : X) : ℝ≥0 :=
  lifeExit (W₁ · ω) (ζ₁ ω) (cofGH₁ (-y) (x - y) ![x - y] m) (cofGN (-y) (x - y) ![x - y] m)

/-- **The large exits of the G3 assembly** (driver shifted to its source `−y`). -/
def g3S₂ (x y : ℝ) (W₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (m : ℕ) (ω : Y) : ℝ≥0 :=
  lifeExit (fun t => W₂ t ω + -y) (ζ₂ ω) (cofGH₂ (-y) (x - y) ![x - y] m) (cofGN (-y) (x - y) ![x - y] m)

/-- **The G3 rectangle-wise mixed-mark input for patched marginals.** For regular G3 marginals in right-continuous
filtrations with continuous Brownian paths at every sample and a `GoodSmallG3` small curve at every sample,
`SeedFieldInputG` holds with the rectangles `g3S₁`, `g3S₂` as soon as their row martingales are known (`hrow`,
`hrowc`), their seeded height fields are measurable on the rectangles (`hmeas`) and the law input (I2) holds for them
(`hlaw`). -/
theorem seedFieldInputG_of_patched {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {P₁ : Measure X} {P₂ : Measure Y} {Law : Measure (X × Y) → Prop} {𝓖₁ : Filtration ℝ≥0 mX}
    {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hrow : ∀ m (ω₁ : X) (a : ℝ), 0 ≤ a → a ≤ g3S₁ x y W₁ ζ₁ m ω₁ →
      Martingale (fun (t : ℝ≥0) ω₂ => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) (ω₁, ω₂) a
        (min (t : ℝ) (g3S₂ x y W₂ ζ₂ m ω₂))) 𝓖₂ P₂)
    (hrowc : ∀ m (ω₁ : X) (ω₂ : Y) (a : ℝ), 0 ≤ a → a ≤ g3S₁ x y W₁ ζ₁ m ω₁ →
      Continuous fun t : ℝ≥0 => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) (ω₁, ω₂) a
        (min (t : ℝ) (g3S₂ x y W₂ ζ₂ m ω₂)))
    (hmeas : ∀ m, IsFieldMeas (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m))
      (fun _ : Unit => g3S₁ x y W₁ ζ₁ m) (fun _ : Unit => g3S₂ x y W₂ ζ₂ m))
    (hlaw : ∀ (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
      (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0)) (μ : Measure (X × Y)),
      IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
        ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) ω
          (g3S₁ x y W₁ ζ₁ m ω.1) (g3S₂ x y W₂ ζ₂ m ω.2))) → Law μ) :
    SeedFieldInputG P₁ P₂ (kh κ) Law := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨hU, hgood₁, hsep₁, hsepO, hneP, hc₂, h0₂, hgood₂, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (cofGN (-y) (x - y) ![x - y]) m
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (cofGN (-y) (x - y) ![x - y]) (-y) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  have hstoch : ∀ m (ω₂ : Y), 0 < (g3S₂ x y W₂ ζ₂ m ω₂ : ℝ) → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓖₁ P₁ (kh κ) (fun ω => g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m
        (g3S₂ x y W₂ ζ₂ m ω₂) (ω, ω₂)) (g3S₁ x y W₁ ζ₁ m) B D := by
    intro m ω₂ _
    have hlt : ∀ ω (s : ℝ≥0), s ≤ g3S₁ x y W₁ ζ₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
    refine ⟨B₁, _, isColumnStoch_g3Rec_of_reg hk h₁ hB₁ (hs₁ m) (fun ω => (hgood₁ m ω).1)
      (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω j s hs hsS => ?_)
      (fun ω s hsS => hneP ω s (hlt ω s hsS))⟩
    fin_cases j
    · exact (hsep₁ ω s hs (hlt ω s hsS)).2
    · exact hsepO ω s (hlt ω s hsS)
    · exact hneP ω s (hlt ω s hsS)
  exact seedFieldInputG_of_g3 𝓖₁ 𝓖₂ (g3S₁ x y W₁ ζ₁) (g3S₂ x y W₂ ζ₂) (cofGH₁ (-y) (x - y) ![x - y])
    (cofGH₂ (-y) (x - y) ![x - y]) (cofGδ (-y) (x - y) ![x - y]) (cofGq (-y) (x - y) ![x - y])
    (cofGd (-y) (x - y) ![x - y]) (cofGTm (-y) (x - y) ![x - y]) hs₁ hs₂ (isProtectedPairG_cofG hne) hU h₁.path
    rfl rfl (by simp; linarith) (fun m => by simpa using qlo_le_cofGq hne m) hgood₁ hsep₁ hsepO hc₂ h0₂ hgood₂
    hstoch hrow hrowc hmeas (hlaw hs₁ hs₂)

end Patched

/-! ### The named remaining inputs and the G3 statement -/

section Statement

/-- **The remaining row input of G3** (`hrow`, `hrowc` of `seedFieldInputG_of_g3`; the opposite view of the G3
records): for every pair of regular G3 marginals in right-continuous filtrations with continuous Brownian paths at
every sample and a `GoodSmallG3` small curve at every sample, the rows of the seeded height field of every rectangle
`g3S₁ m`, `g3S₂ m` (small own time `a` fixed, large time running and stopped at `g3S₂ m`) are martingales of the
large curve's filtration with continuous paths. -/
def G3RectRow (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y)) (_ : 𝓖₁.IsRightContinuous)
      (_ : 𝓖₂.IsRightContinuous)
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂ → (∀ ω, Continuous (B₂ · ω)) →
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      (∀ ω, Continuous (B₁ · ω)) →
      (∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω)) →
      (∀ m (ω₁ : X) (a : ℝ), 0 ≤ a → a ≤ g3S₁ x y W₁ ζ₁ m ω₁ →
        Martingale (fun (t : ℝ≥0) ω₂ => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m)
          (ω₁, ω₂) a (min (t : ℝ) (g3S₂ x y W₂ ζ₂ m ω₂))) 𝓖₂ P₂) ∧
      ∀ m (ω₁ : X) (ω₂ : Y) (a : ℝ), 0 ≤ a → a ≤ g3S₁ x y W₁ ζ₁ m ω₁ →
        Continuous fun t : ℝ≥0 => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) (ω₁, ω₂) a
          (min (t : ℝ) (g3S₂ x y W₂ ζ₂ m ω₂))

/-- **The remaining input `hmeas` of G3**: for every pair of regular G3 marginals as in `G3RectRow`, the seeded height
field of every rectangle is measurable on the rectangle. -/
def G3RectMeas (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y)) (_ : 𝓖₁.IsRightContinuous)
      (_ : 𝓖₂.IsRightContinuous)
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂ → (∀ ω, Continuous (B₂ · ω)) →
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      (∀ ω, Continuous (B₁ · ω)) →
      (∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω)) →
      ∀ m, IsFieldMeas (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m))
        (fun _ : Unit => g3S₁ x y W₁ ζ₁ m) (fun _ : Unit => g3S₂ x y W₂ ζ₂ m)

/-- **The remaining input (I2) of G3** (`hlaw`): for every pair of regular G3 marginals and every pair of patched
versions (`IsPatchOf`), every coupling of the two laws whose density on each rectangle of the patched versions is the
seeded height field (`RectDens`) has the law property of A.1 (G3) for the original marginals. -/
def G3RectLaw (κ : ℝ) : Prop :=
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
            (smallG3RhoR κ) ∧
          HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
            (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
            (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω,
              VL₁ 0 t ω - VR₁ 2 t ω])
            (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (G3), rectangle-wise mixed-mark form, from the three named remaining inputs**: the rows (`G3RectRow`), the
measurability on the rectangles (`G3RectMeas`) and the law input (I2) (`G3RectLaw`) give
`A1DualCouplingG3SeedGStatement κ` (the expanded Theorem 1.2's `hSeedG`). Every other clause of `SeedFieldInputG` is
proved: patching, the segment family (`IsProtectedPairG`, `x − y ≤ q`), rectangles and columns. -/
theorem a1DualCouplingG3SeedGStatement_of_rect {κ : ℝ} (hR : G3RectRow κ) (hM : G3RectMeas κ) (hL : G3RectLaw κ) :
    A1DualCouplingG3SeedGStatement κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  obtain ⟨W₁', VL₁', VR₁', B₁', ζ₁', hp₁⟩ := exists_isPatchOf h₁ GoodSmallG3 (ae_goodSmallG3 hκ4 hκ8 hyx hx h₁)
  obtain ⟨W₂', VL₂', VR₂', B₂', ζ₂', hp₂⟩ :=
    exists_isPatchOf h₂ (fun _ _ _ _ _ => True) (Eventually.of_forall fun _ => trivial)
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := id hp₁
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := id hp₂
  obtain ⟨hrow, hrowc⟩ := hR hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ _ _ inferInstance inferInstance
    W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' h₂' hB₂' h₁' hB₁' hg₁'
  exact seedFieldInputG_of_patched hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hrow hrowc
    (hM hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ _ _ inferInstance inferInstance W₂' VL₂' VR₂' B₂' ζ₂'
      W₁' VL₁' VR₁' B₁' ζ₁' h₂' hB₂' h₁' hB₁' hg₁')
    (fun hs₁ hs₂ μ hμ hμ₁ hμ₂ hd => hL hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
      W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd)

end Statement

end InteractingSLE.ZhanGT4.A1Asm
