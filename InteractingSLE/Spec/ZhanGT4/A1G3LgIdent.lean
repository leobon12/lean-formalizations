/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgData

/-!
# G3 large direction: canonical clock, driver, and caps

The canonical image agrees with any image chain of the stopped large driver
through the protected exit.
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

omit [IsProbabilityMeasure P₂] [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] in
/-- The canonical identification hypotheses at a protected small prefix. -/
theorem g3Fst_facts (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {a W' : Y → ℝ → ℝ}
    (hown₁ : ∀ y₀, OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀)) (y₀ : Y) :
    OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
        (physHull (y - 0) (Strip.extPath (W₁ · x₀)) σ)
        (physMap (y - 0) (Strip.extPath (W₁ · x₀)) σ)
        (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀) ∧
      EqOn (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀) (Strip.extPath (W₂ · y₀))
        (Icc 0 (g3S₂ x y W₂ ζ₂ k y₀ : ℝ)) ∧
      A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀))
        (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y (Strip.extPath (W₁ · x₀)) σ
        (g3S₂ x y W₂ ζ₂ k y₀) ∧
      (∃ r, (σ : ℝ) < r ∧ ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 r)) ∧
      (σ : ℝ≥0∞) < ζ₁ x₀ := by
  have hphys := g3Fst_physical hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσS
  have hown := hown₁ y₀
  rw [hphys.1, hphys.2] at hown
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  obtain ⟨-, hg, -⟩ := g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
  have hσζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hg k x₀).1
  exact ⟨by simpa only [sub_zero] using hown, eightDrv_eqOn W₂ (g3S₂ x y W₂ ζ₂) k y₀,
    g3Fst_isGoodTime hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀ hσ hσS,
    exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1 hσζ, hσζ⟩

variable (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
  (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {a W' : Y → ℝ → ℝ}
  (hown₁ : ∀ y₀, OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
    (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀))

include hσ hσS hown₁

/-- The canonical clock and image driver agree with the stopped-driver image chain. -/
theorem g3Fst_ident (y₀ : Y) :
    EqOn (A1Ref.imgClk 0 (Strip.extPath (W₂ · y₀)) y (Strip.extPath (W₁ · x₀)) σ)
        (a y₀) (Icc 0 (g3S₂ x y W₂ ζ₂ k y₀ : ℝ)) ∧
      EqOn (A1Ref.imgDrv 0 (Strip.extPath (W₂ · y₀))
        (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y (Strip.extPath (W₁ · x₀)) σ)
        (fun t => W' y₀ t + 0) (Icc 0 (a y₀ (g3S₂ x y W₂ ζ₂ k y₀))) := by
  obtain ⟨hown, heq, hgood, hk, -⟩ :=
    g3Fst_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀
  have hj := (A1G3Law.g3Fst_facts h₁ h₂).2.1 y₀
  exact imgClk_imgDrv_eqOn_of_ownData hown heq
    (fun T hT => continuousOn_extPath_Icc hj hT) (extPath_zero_of (h₂.path y₀).1)
    hk (extPath_zero_of (h₁.path x₀).1) σ.coe_nonneg hgood

/-- The raw cap at the protected exit is the canonical clock there. -/
theorem g3Fst_cap_eq_imgClk (y₀ : Y) :
    g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) =
      (A1Ref.imgClk 0 (Strip.extPath (W₂ · y₀)) y (Strip.extPath (W₁ · x₀)) σ
        (g3S₂ x y W₂ ζ₂ k y₀)).toNNReal := by
  obtain ⟨-, -, hgood, hk, hlive⟩ :=
    g3Fst_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀
  have hT : g3FstOwn x y W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) = (g3S₂ x y W₂ ζ₂ k y₀ : ℝ) := by
    simp only [g3FstOwn, hσS, ↓reduceIte]
  unfold g3FstCap
  rw [capFst_congr_pt (T' := fun _ => (g3S₂ x y W₂ ζ₂ k y₀ : ℝ)) hT]
  exact capFst_eq_of_isGoodTime hlive
    (fun T hT => continuousOn_extPath_Icc ((A1G3Law.g3Fst_facts h₁ h₂).2.1 y₀) hT)
    (h₂.path y₀).1 hk (h₁.path x₀).1 hgood

/-- The raw cap is the seeded capacity horizon. -/
theorem g3Fst_cap_eq (y₀ : Y) :
    g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) =
      seedCapacityHorizon (g3FstData (κ := κ) (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
        (W₂ := W₂) (ζ₂ := ζ₂) k σ x₀ a W') (g3S₂ x y W₂ ζ₂ k) y₀ := by
  rw [g3Fst_cap_eq_imgClk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀,
    (g3Fst_ident hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀).1
      ⟨NNReal.coe_nonneg _, le_rfl⟩]
  rfl

/-- The canonical driver is the seeded capacity driver through the protected cap. -/
theorem g3Fst_rDrv_eq :
    let d := g3FstData (κ := κ) (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
      (W₂ := W₂) (ζ₂ := ζ₂) k σ x₀ a W'
    ∀ y₀ t, t ≤ seedCapacityHorizon d (g3S₂ x y W₂ ζ₂ k) y₀ →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) t (x₀, y₀) =
      seedCapacityDriver d (g3S₂ x y W₂ ζ₂ k) t y₀ := by
  intro d y₀ t ht
  obtain ⟨hown, heq, hgood, hk, hlive⟩ :=
    g3Fst_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀
  obtain ⟨hCc, hCs, c, hc, hClb, -⟩ :=
    g3FstData_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁
  have hownD : ∀ y₀, OwnData (d y₀).W
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (d y₀).φ (g3S₂ x y W₂ ζ₂ k y₀) (d y₀).a (d y₀).W' := hown₁
  have ht' : (t : ℝ) ≤ a y₀ (g3S₂ x y W₂ ζ₂ k y₀) := by
    exact (NNReal.coe_le_coe.2 ht).trans (coe_seedCapacityHorizon hownD y₀).le
  rw [seedCapacityDriver_eq_sub hownD hCc hCs hc hClb y₀ ht,
    show (d y₀).W' = W' y₀ from rfl,
    ← imgDrv_sub_eq_of_ownData hown heq
      (fun T hT => continuousOn_extPath_Icc ((A1G3Law.g3Fst_facts h₁ h₂).2.1 y₀) hT)
      (extPath_zero_of (h₂.path y₀).1) hk (extPath_zero_of (h₁.path x₀).1)
      σ.coe_nonneg hgood t.coe_nonneg ht']
  simp only [rDrvFst, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive]

end InteractingSLE.ZhanGT4.A1G3Lg

