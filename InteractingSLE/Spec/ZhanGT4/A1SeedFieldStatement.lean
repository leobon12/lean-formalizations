/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldCol
import InteractingSLE.Spec.ZhanGT4.A1PatchStatement

/-!
# Zhan's A.1 (R80): the field statement from the seeded source data

Packet PROVE-A1-SEEDFIELD. PROVE-A1-PATCH reduced R76's Rect statements to `A1Patch.A1DualCoupling{G3,Eight}Field
Statement`, whose input is `FieldPatchSigmaInput`: a sequence of protected rectangles of ONE two-time field
(`IsRectField` for each), positivity and axis values one, the field measurability `IsFieldMeas`, and the law input (I2)
for every coupling with (1.7) on the rectangles. Here the field is A22's seeded height field `seedHeightField d` and
every field of `IsRectField` except the row is supplied by the source records (`A1SeedFieldCol`):

* `SeedFieldInput P₁ P₂ κ Law`: filtrations, the rectangles `(S₁ m, S₂ m)` with their protected enclosure pairs, the
  seeded records `d t (x, y)`, the source columns at the frozen exit heights, the source records at all lower heights
  (for (D9)), the identity chart at height zero, the row martingales (the opposite-time view), `IsFieldMeas`, and the
  law input (I2) on the stopped σ-algebras of the rectangles;
* **`fieldPatchSigmaInput_of_seedFieldInput`**: `SeedFieldInput → FieldPatchSigmaInput` (A1-PATCH's input);
* `A1DualCouplingEightSeedStatement`: A1-PATCH's `A1DualCouplingEightFieldLawStatement` with `FieldPatchSigmaInput`
  replaced by `SeedFieldInput` (binders and law property copied verbatim by script);
* **`a1DualCouplingEightFieldStatement_of_seed`** and the chained `…RectStatement_of_seed` (R76),
  `…CanonStatement_of_seed` (R72).

The Eight configuration's growing (small) curve carries only seed marks (`x⁻`, `x⁺`) and the other source, which is
the setting of A22's `seeded_source_calculus_right`. The G3 configuration's small curve carries in addition the
ordinary mark `x` (weight `κ̂ − 4`), which `IsSourceRecord` (all marks seeds) does not cover; see the handoff.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1SeedField

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch

section Input

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The seeded-field data of A.1** for two marginals `P₁` (growing curve of parameter `κ`, seeded) and `P₂`:
filtrations; rectangles `(S₁ m, S₂ m)` (bounded stopping times) with protected enclosure pairs around the sources `0`
and `p`; seeded records `d t (x, y)` (curve `1` growing, curve `2` frozen at height `t`) such that the column at every
positive frozen exit height is a source column, every record at a positive height `t ≤ S₂ m y` is a source record up
to `S₁ m x`, and the zero-height records are identity charts; the row martingales of the seeded height field (the
opposite-time view); the field measurability; and the law input (I2) for every coupling with (1.7) on the stopped
σ-algebras of every rectangle. -/
def SeedFieldInput (P₁ : Measure X) (P₂ : Measure Y) (κ : ℝ) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (n : ℕ) (rr : Fin n → ℝ) (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0)
    (S₂ : ℕ → Y → ℝ≥0) (d : ℝ → X × Y → SeedData n) (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ) (p : ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0)),
    (∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m)) ∧
    (∀ m, ∃ U : ℝ≥0, (∀ x, S₁ m x ≤ U) ∧ ∀ y, S₂ m y ≤ U) ∧
    (∀ m y, 0 < (S₂ m y : ℝ) →
      IsSourceColumn (H₁ m) (H₂ m) p (Tm m) κ rr 𝓕₁ P₁ (S₂ m y) (fun x => d (S₂ m y) (x, y)) (S₁ m)) ∧
    (∀ m x y (t : ℝ), 0 < t → t ≤ S₂ m y →
      ∃ (W₂ Vlo Vhi : ℝ → ℝ), IsSourceRecord (H₁ m) (H₂ m) p (Tm m) κ rr W₂ t (d t (x, y)) Vlo Vhi (S₁ m x)) ∧
    (∀ x y s, (d 0 (x, y)).normEll s = (d 0 (x, y)).normEll 0) ∧
    (∀ m x (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField d (x, y) a (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂) ∧
    (∀ m x y (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Continuous fun t : ℝ≥0 => seedHeightField d (x, y) a (min (t : ℝ) (S₂ m y))) ∧
    IsFieldMeas (seedHeightField d) S₁ S₂ ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h₁ m).measurableSpace (h₂ m).measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (seedHeightField d ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ

/-- **The seeded-field data give A1-PATCH's field input**: each rectangle is an `IsRectField` of the seeded height
field (`isRectField_of_source`), which is positive with axis values one (`seedHeightField_pos`,
`seedHeightField_zero_left`, `seedHeightField_zero_right` from the identity chart). -/
theorem fieldPatchSigmaInput_of_seedFieldInput {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁]
    {κ : ℝ} (hκ : 0 < κ) {Law : Measure (X × Y) → Prop} (h : SeedFieldInput P₁ P₂ κ Law) :
    FieldPatchSigmaInput P₁ P₂ Law := by
  obtain ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hrow, hrowc,
    hmeas, hlaw⟩ := h
  have hR : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) (seedHeightField d) := fun m =>
    isRectField_of_source (hpp m) hκ (h₁ m) (h₂ m) (hU m) (hcol m) (hrec m) hzero (hrow m) (hrowc m)
  exact ⟨𝓕₁, 𝓕₂, S₁, S₂, seedHeightField d, hR, seedHeightField_pos d, seedHeightField_zero_left d,
    seedHeightField_zero_right (fun ω s => hzero ω.1 ω.2 s), hmeas, fun μ hμ h1 h2 hrect => hlaw μ hμ h1 h2 hrect⟩

end Input

section Config

/-- **A.1 (Eight), seeded form for every pair of regular marginals**: A1-PATCH's
`A1DualCouplingEightFieldLawStatement` with `FieldPatchSigmaInput` replaced by `SeedFieldInput` (growing curve: the
small curve of parameter `κ̂ = 16/κ`). -/
def A1DualCouplingEightSeedStatement (κ : ℝ) : Prop :=
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
      SeedFieldInput P₁ P₂ (kh κ) fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- The seeded form gives A1-PATCH's field form for every pair of regular marginals (Eight). -/
theorem a1DualCouplingEightFieldLawStatement_of_seed {κ : ℝ} (h : A1DualCouplingEightSeedStatement κ) :
    A1DualCouplingEightFieldLawStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  exact fieldPatchSigmaInput_of_seedFieldInput hk
    (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)

/-- **The seeded form gives A1-PATCH's field statement (Eight).** -/
theorem a1DualCouplingEightFieldStatement_of_seed {κ : ℝ} (h : A1DualCouplingEightSeedStatement κ) :
    A1DualCouplingEightFieldStatement κ :=
  a1DualCouplingEightFieldStatement_of_fieldLaw (a1DualCouplingEightFieldLawStatement_of_seed h)

/-- **The seeded form gives R76's Rect statement (Eight).** -/
theorem a1DualCouplingEightRectStatement_of_seed {κ : ℝ} (h : A1DualCouplingEightSeedStatement κ) :
    A1DualCouplingEightRectStatement κ :=
  a1DualCouplingEightRectStatement_of_field (a1DualCouplingEightFieldStatement_of_seed h)

/-- The seeded form gives R72's Canon statement (Eight). -/
theorem a1DualCouplingEightCanonStatement_of_seed {κ : ℝ} (h : A1DualCouplingEightSeedStatement κ) :
    A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_field (a1DualCouplingEightFieldStatement_of_seed h)

end Config

end InteractingSLE.ZhanGT4.A1SeedField
