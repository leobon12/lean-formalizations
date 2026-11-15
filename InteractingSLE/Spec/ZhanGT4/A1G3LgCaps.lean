/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgIdent

/-!
# G3 large direction: the other rectangle caps

The cap comparison hypotheses for the one-sample law follow from the canonical
clock at protected exits and its monotonicity.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap drive IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR A1G3Id Girsanov A1G3Row A1LargeDens A1MultiMark A1Family
  A1G3L2 A1Forces A1Core

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable [IsProbabilityMeasure P₂]
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous]

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y]
    (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω)
    (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

omit mX mY in
omit hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ in
/-- Own stopping times of the raw caps at a fixed small sample. -/
def g3FstTk (σ : ℝ≥0) (x₀ : X) (k : ℕ) (y₀ : Y) : ℝ≥0 :=
  if σ ≤ g3S₁ x y W₁ ζ₁ k x₀ then g3S₂ x y W₂ ζ₂ k y₀ else 0

omit [IsProbabilityMeasure P₂] [𝓖₁.IsRightContinuous] hκ4 hκ8 h₁ hB₁ hg₁ hB₂ in
/-- These own times are stopping times of the large filtration. -/
theorem isStoppingTime_g3FstTk (σ : ℝ≥0) (x₀ : X) (k : ℕ) :
    IsStoppingTime 𝓖₂ fun y₀ => (g3FstTk (x := x) (y := y) (W₁ := W₁)
      (ζ₁ := ζ₁) (W₂ := W₂) (ζ₂ := ζ₂) σ x₀ k y₀ : WithTop ℝ≥0) := by
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  have hF := isEnclFamily_cofG hne
  unfold g3FstTk
  split_ifs
  · exact isStoppingTime_rect₂ (fun y₀ => (h₂.path y₀).2.2.2.1) h₂.evol.2.1
      (fun m => (hF.pp m).hull₂) (cofGN (-y) (x - y) ![x - y]) (-y) k
  · exact isStoppingTime_const 𝓖₂ (0 : ℝ≥0)

/-- The cap-clock identity without choosing an image chain in the statement. -/
theorem g3Fst_cap_eq_clock (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) =
      (A1Ref.imgClk 0 (Strip.extPath (W₂ · y₀)) y (Strip.extPath (W₁ · x₀)) σ
        (g3S₂ x y W₂ ζ₂ k y₀)).toNNReal := by
  obtain ⟨a, W', hown⟩ := exists_ownData_g3Fst hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  exact g3Fst_cap_eq_imgClk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown y₀

variable (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
  (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {a W' : Y → ℝ → ℝ}
  (hown₁ : ∀ y₀, OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
    (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀))

include hσ hσS hown₁

/-- Other caps before the chosen exit are the image clock at their own stopping times. -/
theorem g3Fst_cap_eq_clk (k' : ℕ) (y₀ : Y)
    (hle : g3FstTk (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
      (W₂ := W₂) (ζ₂ := ζ₂) σ x₀ k' y₀ ≤ g3S₂ x y W₂ ζ₂ k y₀) :
    (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) : ℝ) =
      a y₀ (g3FstTk (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
        (W₂ := W₂) (ζ₂ := ζ₂) σ x₀ k' y₀) := by
  have hclk := (g3Fst_ident hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀).1
  by_cases hg : σ ≤ g3S₁ x y W₁ ζ₁ k' x₀
  · simp only [g3FstTk, hg, ↓reduceIte] at hle ⊢
    have hmem : (g3S₂ x y W₂ ζ₂ k' y₀ : ℝ) ∈ Icc 0 (g3S₂ x y W₂ ζ₂ k y₀ : ℝ) :=
      ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 hle⟩
    rw [g3Fst_cap_eq_clock hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' x₀ y₀ hσ hg, hclk hmem]
    have h0 : 0 ≤ a y₀ (g3S₂ x y W₂ ζ₂ k' y₀) := by
      rw [← (hown₁ y₀).a0]
      exact (hown₁ y₀).mono.monotoneOn ⟨le_rfl, (hown₁ y₀).pos.le⟩ hmem hmem.1
    exact Real.coe_toNNReal _ h0
  · simp only [g3FstTk, hg, ↓reduceIte, NNReal.coe_zero, (hown₁ y₀).a0]
    unfold g3FstCap
    rw [capFst_of_nonpos]
    · rfl
    · simp only [g3FstOwn, hg, ↓reduceIte, le_refl]

/-- A cap whose own time follows the chosen exit dominates its cap. -/
theorem g3Fst_cap_le_cap (k' : ℕ) (y₀ : Y)
    (hle : g3S₂ x y W₂ ζ₂ k y₀ ≤ g3FstTk (x := x) (y := y) (W₁ := W₁)
      (ζ₁ := ζ₁) (W₂ := W₂) (ζ₂ := ζ₂) σ x₀ k' y₀) :
    g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) ≤
      g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) := by
  have hg : σ ≤ g3S₁ x y W₁ ζ₁ k' x₀ := by
    by_contra h
    simp only [g3FstTk, h, ↓reduceIte] at hle
    exact not_le_of_gt (show (0 : ℝ≥0) < g3S₂ x y W₂ ζ₂ k y₀ from
      (hown₁ y₀).pos) hle
  simp only [g3FstTk, hg, ↓reduceIte] at hle
  obtain ⟨a', W'', hown'⟩ := exists_ownData_g3Fst hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' x₀
    (by exact_mod_cast hσ) (by exact_mod_cast hg)
  obtain ⟨-, -, hgood', hk, -⟩ :=
    g3Fst_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' x₀ hσ hg hown' y₀
  rw [g3Fst_cap_eq_clock hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀ hσ hσS,
    g3Fst_cap_eq_clock hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' x₀ y₀ hσ hg]
  obtain ⟨-, hmono, -⟩ := exists_isImgDrvOn
    (fun T hT => continuousOn_extPath_Icc ((A1G3Law.g3Fst_facts h₁ h₂).2.1 y₀) hT)
    (extPath_zero_of (h₂.path y₀).1) hk (extPath_zero_of (h₁.path x₀).1) σ.coe_nonneg hgood'
  exact Real.toNNReal_le_toNNReal (hmono.monotoneOn
    ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 hle⟩ ⟨NNReal.coe_nonneg _, le_rfl⟩ (NNReal.coe_le_coe.2 hle))

end InteractingSLE.ZhanGT4.A1G3Lg

