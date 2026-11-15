/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcRecord

/-!
# Zhan's A.1, G3: the rectangle-wise seeded statement with mixed marks

Packet PROVE-A1-G3CALC (R48, R80). A1-EIGHTSEED's rectangle-wise seeded input `SeedFieldInputM` and its reduction to
A1-PATCH's `FieldPatchSigmaInput`, for G3's growing (small) curve, whose marks are its two seeds and the ordinary mark
`x` (`IsSourceRecordG`, `IsSourceColumnG`, `IsProtectedPairG`). The G3 statement below is A1-PATCH's
`A1DualCouplingG3FieldLawStatement` with `FieldPatchSigmaInput` replaced by `SeedFieldInputG` (binders and law
property copied verbatim by script; checked by a printed-statement comparison).

## Main results

* **`SeedFieldInputG`**, **`fieldPatchSigmaInput_of_seedFieldInputG`**;
* **`A1DualCouplingG3SeedGStatement`** and the chain `a1DualCouplingG3{FieldLaw,Field,Rect,Canon}Statement_of_seedG`
  (R80, R76, R72).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Calc

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed

section Input

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The rectangle-wise seeded-field data of A.1 with mixed marks**: A1-EIGHTSEED's `SeedFieldInputM` with the
protected pairs, source columns and source records of `A1G3CalcRecord` (marks: seeds or ordinary marks in the
extended interval; the segment `(0, q m]` far from `H₂ m`). -/
def SeedFieldInputG (P₁ : Measure X) (P₂ : Measure Y) (κ : ℝ) (Law : Measure (X × Y) → Prop) : Prop :=
  ∃ (n : ℕ) (rr : Fin n → ℝ) (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0)
    (S₂ : ℕ → Y → ℝ≥0) (d : ℕ → ℝ → X × Y → SeedData n) (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ) (p : ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0)),
    (∀ m, IsProtectedPairG (H₁ m) (H₂ m) (δ m) p (q m) (dd m)) ∧
    (∀ m, ∃ U : ℝ≥0, (∀ x, S₁ m x ≤ U) ∧ ∀ y, S₂ m y ≤ U) ∧
    (∀ m y, 0 < (S₂ m y : ℝ) →
      IsSourceColumnG (H₁ m) (H₂ m) p (q m) (Tm m) κ rr 𝓕₁ P₁ (S₂ m y) (fun x => d m (S₂ m y) (x, y))
        (S₁ m)) ∧
    (∀ m x y (t : ℝ), 0 < t → t ≤ S₂ m y →
      ∃ (W₂ Vlo Vhi : ℝ → ℝ),
        IsSourceRecordG (H₁ m) (H₂ m) p (q m) (Tm m) κ rr W₂ t (d m t (x, y)) Vlo Vhi (S₁ m x)) ∧
    (∀ m x y (s : ℝ), 0 ≤ s → s ≤ S₁ m x → (d m 0 (x, y)).normEll s = (d m 0 (x, y)).normEll 0) ∧
    RecCompat d S₁ S₂ ∧
    (∀ m x (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Martingale (fun (t : ℝ≥0) y => seedHeightField (d m) (x, y) a (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂) ∧
    (∀ m x y (a : ℝ), 0 ≤ a → a ≤ S₁ m x →
      Continuous fun t : ℝ≥0 => seedHeightField (d m) (x, y) a (min (t : ℝ) (S₂ m y))) ∧
    (∀ m, IsFieldMeas (seedHeightField (d m)) (fun _ : Unit => S₁ m) (fun _ : Unit => S₂ m)) ∧
    ∀ μ : Measure (X × Y), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
      (∀ m, RectDens (h₁ m).measurableSpace (h₂ m).measurableSpace P₁ P₂ μ
        fun ω => ENNReal.ofReal (seedHeightField (d m) ω (S₁ m ω.1) (S₂ m ω.2))) →
      Law μ

/-- **The mixed rectangle-wise data give A1-PATCH's field input**: rectangle `m` is an `IsRectField` of its own seeded
height field (`isRectField_of_sourceG`), hence of A1-EIGHTSEED's glued field, which is positive, has axis values one
and is measurable on the rectangles (A1-EIGHTSEED's proof of `fieldPatchSigmaInput_of_seedFieldInputM`). -/
theorem fieldPatchSigmaInput_of_seedFieldInputG {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁]
    {κ : ℝ} (hκ : 0 < κ) {Law : Measure (X × Y) → Prop} (h : SeedFieldInputG P₁ P₂ κ Law) :
    FieldPatchSigmaInput P₁ P₂ Law := by
  obtain ⟨n, rr, 𝓕₁, 𝓕₂, S₁, S₂, d, H₁, H₂, δ, q, dd, Tm, p, h₁, h₂, hpp, hU, hcol, hrec, hzero, hc, hrow, hrowc,
    hmeas, hlaw⟩ := h
  have hR₀ : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) (seedHeightField (d m)) := fun m =>
    isRectField_of_sourceG (hpp m) hκ (h₁ m) (h₂ m) (hU m) (hcol m) (hrec m) (hzero m) (hrow m) (hrowc m)
  have hR : ∀ m, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ m) (S₂ m) (glueField d S₁ S₂) := fun m =>
    isRectField_congr (hR₀ m) fun x y s t hs hsS ht htS => (glueField_eq hc hs hsS ht htS).symm
  refine ⟨𝓕₁, 𝓕₂, S₁, S₂, glueField d S₁ S₂, hR, glueField_pos d S₁ S₂, glueField_zero_left d S₁ S₂,
    glueField_zero_right hzero,
    isFieldMeas_glueField (fun m => measurable_coe_of_isStoppingTime (h₁ m))
      (fun m => measurable_coe_of_isStoppingTime (h₂ m)) hmeas, fun μ hμ hμ₁ hμ₂ hd => hlaw μ hμ hμ₁ hμ₂ ?_⟩
  intro m
  have e : (fun ω : X × Y => ENNReal.ofReal (glueField d S₁ S₂ ω (S₁ m ω.1) (S₂ m ω.2))) =
      fun ω => ENNReal.ofReal (seedHeightField (d m) ω (S₁ m ω.1) (S₂ m ω.2)) := by
    funext ω
    rw [glueField_eq hc (S₁ m ω.1).coe_nonneg le_rfl (S₂ m ω.2).coe_nonneg le_rfl]
  have hdm := hd m
  rw [e] at hdm
  exact hdm

end Input

section Config

/-- **A.1 (G3), rectangle-wise seeded form with mixed marks, for every pair of regular marginals**: A1-PATCH's
`A1DualCouplingG3FieldLawStatement` with `FieldPatchSigmaInput` replaced by `SeedFieldInputG` (growing curve: the small
curve of parameter `κ̂ = 16/κ`, with its seeds `y±` and the ordinary mark `x`). -/
def A1DualCouplingG3SeedGStatement (κ : ℝ) : Prop :=
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
        HasFamilyLaw (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        HasFamilyLawFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- The mixed seeded form gives A1-PATCH's field form for every pair of regular marginals (G3). -/
theorem a1DualCouplingG3FieldLawStatement_of_seedG {κ : ℝ} (h : A1DualCouplingG3SeedGStatement κ) :
    A1DualCouplingG3FieldLawStatement κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  exact fieldPatchSigmaInput_of_seedFieldInputG hk
    (h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁)

/-- **The mixed seeded form gives A1-PATCH's field statement (G3).** -/
theorem a1DualCouplingG3FieldStatement_of_seedG {κ : ℝ} (h : A1DualCouplingG3SeedGStatement κ) :
    A1DualCouplingG3FieldStatement κ :=
  a1DualCouplingG3FieldStatement_of_fieldLaw (a1DualCouplingG3FieldLawStatement_of_seedG h)

/-- **The mixed seeded form gives R76's Rect statement (G3).** -/
theorem a1DualCouplingG3RectStatement_of_seedG {κ : ℝ} (h : A1DualCouplingG3SeedGStatement κ) :
    A1DualCouplingG3RectStatement κ :=
  a1DualCouplingG3RectStatement_of_field (a1DualCouplingG3FieldStatement_of_seedG h)

/-- The mixed seeded form gives R72's Canon statement (G3). -/
theorem a1DualCouplingG3CanonStatement_of_seedG {κ : ℝ} (h : A1DualCouplingG3SeedGStatement κ) :
    A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_field (a1DualCouplingG3FieldStatement_of_seedG h)

end Config

end InteractingSLE.ZhanGT4.A1G3Calc
