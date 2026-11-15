/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1PatchNull

/-!
# A.1's statements with the finite patches supplied by the two-time field

Packet PROVE-A1-PATCH (R80). PROVE-A1-LAW reduced R76's Rect statements to `A1Law.A1DualCoupling{G3,Eight}Patch
Statement`, whose input (I1) asks for finite couplings `π N` with (1.7) on the rectangles `m ≤ N`. Here (I1) is
replaced by the data the source's construction uses (follow-up 4 §2.5 item 4: "the staircase density (D11)–(D12) …
uses only coordinate martingales and their axis values"): a sequence of protected rectangles of one two-time field
(`IsRectField`, for any filtrations, e.g. the usual augmentations), with the law input (I2) stated on the stopped
σ-algebras of the rectangles (`FieldPatchSigmaInput`). The finite patches and the records are then constructed
(`patchInput_of_fieldPatchSigmaInput`: the staircase coupling of `A1PatchStair`; records generating the stopped
σ-algebras modulo null sets, `A1PatchNull`).

## Main results

* `A1DualCoupling{G3,Eight}FieldStatement`, `A1DualCoupling{G3,Eight}FieldLawStatement`: the Patch statements of
  PROVE-A1-LAW with `PatchInput` replaced by `FieldPatchSigmaInput` (the binders and the law property verbatim);
* **`a1DualCoupling{G3,Eight}PatchStatement_of_field`**, `…PatchLawStatement_of_fieldLaw`, and the chained
  `…MargStatement_of_field`, `…RectStatement_of_field` (R76), `…CanonStatement_of_field` (R72),
  `…FieldStatement_of_fieldLaw`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Patch

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law

section Config

/-- **A.1 (G3), field form**: some regular marginals of the two complete laws carry the field data of the finite
patches (`FieldPatchSigmaInput`: a sequence of protected rectangles of one two-time field with its coordinate
martingale identities), with the two frozen-curve family inputs (I2) for every coupling with (1.7) on the stopped
σ-algebras of every rectangle — `A1Law.A1DualCouplingG3PatchStatement` with (I1) replaced by its field data. -/
def A1DualCouplingG3FieldStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      FieldPatchSigmaInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight), field form.** -/
def A1DualCouplingEightFieldStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      FieldPatchSigmaInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **A.1 (G3), field form for every pair of regular marginals.** -/
def A1DualCouplingG3FieldLawStatement (κ : ℝ) : Prop :=
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
      FieldPatchSigmaInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight), field form for every pair of regular marginals.** -/
def A1DualCouplingEightFieldLawStatement (κ : ℝ) : Prop :=
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
      FieldPatchSigmaInput P₁ P₂ fun μ =>
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **The field form gives the patch form (G3)**: the staircase couplings are the finite patches. -/
theorem a1DualCouplingG3PatchStatement_of_field {κ : ℝ} (h : A1DualCouplingG3FieldStatement κ) :
    A1DualCouplingG3PatchStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hI⟩ :=
    h hκ4 hκ8 y x hyx hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁,
    patchInput_of_fieldPatchSigmaInput hI⟩

/-- **The field form gives the patch form (Eight).** -/
theorem a1DualCouplingEightPatchStatement_of_field {κ : ℝ} (h : A1DualCouplingEightFieldStatement κ) :
    A1DualCouplingEightPatchStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hI⟩ :=
    h hκ8 x hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁,
    patchInput_of_fieldPatchSigmaInput hI⟩

/-- **The field law form gives the patch law form (G3).** -/
theorem a1DualCouplingG3PatchLawStatement_of_fieldLaw {κ : ℝ} (h : A1DualCouplingG3FieldLawStatement κ) :
    A1DualCouplingG3PatchLawStatement κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact patchInput_of_fieldPatchSigmaInput
    (h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)

/-- **The field law form gives the patch law form (Eight).** -/
theorem a1DualCouplingEightPatchLawStatement_of_fieldLaw {κ : ℝ} (h : A1DualCouplingEightFieldLawStatement κ) :
    A1DualCouplingEightPatchLawStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact patchInput_of_fieldPatchSigmaInput
    (h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)

/-- **The field law form gives the field form (G3)** (regular marginals exist: `exists_regMarginals_G3`). -/
theorem a1DualCouplingG3FieldStatement_of_fieldLaw {κ : ℝ} (h : A1DualCouplingG3FieldLawStatement κ) :
    A1DualCouplingG3FieldStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_G3 hκ4 hyx hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    h₂, h₁, h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁
      h₂ h₁⟩

/-- **The field law form gives the field form (Eight)** (`exists_regMarginals_Eight`). -/
theorem a1DualCouplingEightFieldStatement_of_fieldLaw {κ : ℝ} (h : A1DualCouplingEightFieldLawStatement κ) :
    A1DualCouplingEightFieldStatement κ := by
  intro hκ8 x hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_Eight hκ8 hx
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    h₂, h₁, h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁⟩

/-- The field form gives MARG's marginal form (G3). -/
theorem a1DualCouplingG3MargStatement_of_field {κ : ℝ} (h : A1DualCouplingG3FieldStatement κ) :
    A1DualCouplingG3MargStatement κ :=
  a1DualCouplingG3MargStatement_of_patch (a1DualCouplingG3PatchStatement_of_field h)

/-- The field form gives MARG's marginal form (Eight). -/
theorem a1DualCouplingEightMargStatement_of_field {κ : ℝ} (h : A1DualCouplingEightFieldStatement κ) :
    A1DualCouplingEightMargStatement κ :=
  a1DualCouplingEightMargStatement_of_patch (a1DualCouplingEightPatchStatement_of_field h)

/-- **The field form gives R76's Rect statement (G3).** -/
theorem a1DualCouplingG3RectStatement_of_field {κ : ℝ} (h : A1DualCouplingG3FieldStatement κ) :
    A1DualCouplingG3RectStatement κ :=
  a1DualCouplingG3RectStatement_of_patch (a1DualCouplingG3PatchStatement_of_field h)

/-- **The field form gives R76's Rect statement (Eight).** -/
theorem a1DualCouplingEightRectStatement_of_field {κ : ℝ} (h : A1DualCouplingEightFieldStatement κ) :
    A1DualCouplingEightRectStatement κ :=
  a1DualCouplingEightRectStatement_of_patch (a1DualCouplingEightPatchStatement_of_field h)

/-- The field form gives R72's Canon statement (G3). -/
theorem a1DualCouplingG3CanonStatement_of_field {κ : ℝ} (h : A1DualCouplingG3FieldStatement κ) :
    A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_patch (a1DualCouplingG3PatchStatement_of_field h)

/-- The field form gives R72's Canon statement (Eight). -/
theorem a1DualCouplingEightCanonStatement_of_field {κ : ℝ} (h : A1DualCouplingEightFieldStatement κ) :
    A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_patch (a1DualCouplingEightPatchStatement_of_field h)

end Config

end InteractingSLE.ZhanGT4.A1Patch
