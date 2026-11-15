/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgForce
import InteractingSLE.Spec.ZhanGT4.A1G3LgCaps
import InteractingSLE.Spec.ZhanGT4.A1G3LgLaw
/-!
# G3 large direction: the canonical positive-time sample law

The seeded rectangle law transfers to the canonical clock, driver, and forces.
At an unprotected positive frozen time the corresponding cap vanishes.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap drive IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR A1G3Id Girsanov A1G3Row A1LargeDens A1MultiMark A1Family
  A1Forces A1Core A1Canon

variable {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable [StandardBorelSpace X] [StandardBorelSpace Y]
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
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

/-- The canonical large-direction sample law at every protected positive frozen time. -/
theorem g3Fst_isSeedSampleLaw_live (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    IsSeedSampleLaw (P₂.withDensity fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀))
      (fun t y₀ => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) t (x₀, y₀))
      (fun y₀ => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) (x₀, y₀))
      (fun i t y₀ => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y₀ => seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) t (x₀, y₀))
        (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀))
        (fun j _ => (j.elim0 : ℝ)) t)
      (fun k' y₀ => g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀)) k := by
  obtain ⟨a, W', hown⟩ := exists_ownData_g3Fst hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  let d := g3FstData (κ := κ) (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
    (W₂ := W₂) (ζ₂ := ζ₂) k σ x₀ a W'
  have hcap := fun y₀ => g3Fst_cap_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown y₀
  have hWs : eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ = W₁ σ x₀ := by
    simpa only [extPath_coe] using
      eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀ ⟨σ.coe_nonneg, NNReal.coe_le_coe.2 hσS⟩
  have hmarks : largeG3Marks y (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ =
      ![VR₁ 1 σ x₀ - -y, VR₁ 0 σ x₀ - -y,
        eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ - -y, VL₁ 0 σ x₀ - -y] := by
    rw [hWs]
    funext i
    fin_cases i <;> simp [largeG3Marks, sub_neg_eq_add, add_comm]
  refine g3Fst_isSeedSampleLaw hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown
    (d := d) (A' := fun _ => fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    hown (fun _ => rfl) (fun _ => rfl) hcap
    (fun y₀ t ht => g3Fst_rDrv_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown
      y₀ t (hcap y₀ ▸ ht)) (fun y₀ i t ht => ?_) (fun _ _ _ => rfl)
    (fun y₀ => capFst_le_rLifeFst _ (x₀, y₀))
    (g3FstTk (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁) (W₂ := W₂) (ζ₂ := ζ₂) σ x₀)
    (fun k' => isStoppingTime_g3FstTk hyx hx h₂ σ x₀ k')
    (fun k' y₀ hle => g3Fst_cap_eq_clk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown k' y₀ hle)
    (fun k' y₀ hle => g3Fst_cap_le_cap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown k' y₀ hle)
  simpa only [hmarks] using
    g3Fst_VL_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown y₀ i t (hcap y₀ ▸ ht)

/-- The canonical large-direction sample law at every positive frozen time. -/
theorem g3Fst_isSeedSampleLaw_pos (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ) :
    IsSeedSampleLaw (P₂.withDensity fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀))
      (fun t y₀ => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) t (x₀, y₀))
      (fun y₀ => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) (x₀, y₀))
      (fun i t y₀ => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y₀ => seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) t (x₀, y₀))
        (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀))
        (fun j _ => (j.elim0 : ℝ)) t)
      (fun k' y₀ => g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀)) k := by
  by_cases hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀
  · exact g3Fst_isSeedSampleLaw_live hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  obtain ⟨-, hg, -⟩ := g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
  have hpos : 0 < g3S₁ x y W₁ ζ₁ k x₀ := (hg k x₀).2.1
  have hlaw := g3Fst_isSeedSampleLaw_live hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hpos le_rfl
  have hD : (fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ (g3S₁ x y W₁ ζ₁ k x₀) k (x₀, y₀)) =
      fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) := by
    funext y₀
    simp only [g3FstD, min_self, min_eq_right (le_of_not_ge hσS)]
  rw [hD] at hlaw
  refine isSeedSampleLaw_of_cap_zero_of_law hlaw (fun y₀ => ?_) (fun y₀ => ?_)
  · simp only [A1RLaw.seedCapacityNoise_zero, rDrvFst, A1RLaw.cImgDrvM_zero, zero_div]
  · unfold g3FstCap
    apply capFst_of_nonpos
    simp only [g3FstOwn, hσS, ↓reduceIte, le_refl]

end InteractingSLE.ZhanGT4.A1G3Lg

