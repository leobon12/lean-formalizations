/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgD9

/-!
# G3 large direction: capacity data and their geometry

The capacity carrier has the stopped large driver and its image chain. Its
four force coordinates are the frozen small curve's marks and tip.
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
/-- The stopped small hull and chart are the original small hull and chart in the physical frame. -/
theorem g3Fst_physical (k : ℕ) (x₀ : X) {σ : ℝ≥0}
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ =
        physHull y (Strip.extPath (W₁ · x₀)) σ ∧
      frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ =
        physMap y (Strip.extPath (W₁ · x₀)) σ := by
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  obtain ⟨-, hgood₁, -, -, -, -, -, -, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
  obtain ⟨r, hr, hcr⟩ := exists_continuousOn_extPath_beyond
    (h₁.path x₀).2.2.2.1 (hgood₁ k x₀).1
  have hcsmall : Continuous (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀) :=
    continuous_eightDrv (h₁.path x₀).2.2.2.1 (hgood₁ k x₀).1
  have heq : EqOn (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀)
      (Strip.extPath (W₁ · x₀)) (Icc 0 (σ : ℝ)) :=
    fun u hu => eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀
      ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hσS)⟩
  constructor
  · rw [A1G3Row.fwdHull_sub_const_eq_physHull, neg_neg]
    exact A1SeedGeom.physHull_congr_of_continuousOn hcsmall.continuousOn hcr
      σ.coe_nonneg ((NNReal.coe_le_coe.2 hσS).trans_lt hr) heq
  · rw [A1G3Row.frzChart_sub_const_eq_physMap, neg_neg]
    exact physMap_congr σ.coe_nonneg heq

omit mX mY in
omit hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ in
/-- Capacity data for an image chain of the stopped large driver, with its physical other source. -/
def g3FstData (k : ℕ) (σ : ℝ≥0) (x₀ : X) (a W' : Y → ℝ → ℝ) (y₀ : Y) : SeedData 0 :=
  SeedData.fromSource (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀) (W' y₀) (a y₀)
    (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    κ Fin.elim0 (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ - -y) y Fin.elim0

/-- The capacity clocks and four frozen force coordinates of the large image have the G3 geometry. -/
theorem g3FstData_geometry (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {a W' : Y → ℝ → ℝ}
    (hown₁ : ∀ y₀, OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀)) :
    let d := g3FstData (κ := κ) (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
      (W₂ := W₂) (ζ₂ := ζ₂) k σ x₀ a W'
    let S := g3S₂ x y W₂ ζ₂ k
    (∀ y₀, Continuous (seedQuadClock (seedCapacityCoeff d S) y₀)) ∧
      (∀ y₀, StrictMono (seedQuadClock (seedCapacityCoeff d S) y₀)) ∧
      ∃ c : ℝ, 0 < c ∧ (∀ y₀ r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y₀ r) ∧
        ∀ y₀, SeedImageGeometry (g3FstWord W₁ VL₁ VR₁ σ x₀) ![] (largeG3ImgRhoL κ) ![]
          (seedCapacityDriver d S · y₀)
          (fun i t => capForce d S (fun y₀ => frzImg (d y₀).W' (d y₀).a
            (largeG3Marks y (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i)) t y₀)
          (fun j => Fin.elim0 j) (seedCapacityHorizon d S y₀) := by
  intro d S
  have hκ : 0 < κ := by linarith
  have hsqrt : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  let B : ℝ≥0 → Y → ℝ := fun t y₀ => eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀ t / Real.sqrt κ
  have hdrv : ∀ y₀, drive κ B y₀ = eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀ := by
    intro y₀
    funext u
    change Real.sqrt κ * (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀ (u.toNNReal : ℝ) / Real.sqrt κ) = _
    rw [← eightDrv_toNNReal W₂ (g3S₂ x y W₂ ζ₂) k y₀ u]
    exact mul_div_cancel₀ _ hsqrt
  have hownB := fun y₀ => (hdrv y₀).symm ▸ hown₁ y₀
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ :=
    g3Fst_d10Hyp hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hownB
      (fun y₀ u hu => by rw [hdrv]; exact eightDrv_eqOn W₂ (g3S₂ x y W₂ ζ₂) k y₀ hu)
  have hown : ∀ y₀, OwnData (d y₀).W
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (d y₀).φ (S y₀) (d y₀).a (d y₀).W' := hown₁
  have hclock := seedQuadClock_eq_bmClk hown (fun _ => rfl)
  have hCc : ∀ y₀, Continuous (seedQuadClock (seedCapacityCoeff d S) y₀) := by
    rw [hclock]; exact hH.continuous_bmClk
  have hCs : ∀ y₀, StrictMono (seedQuadClock (seedCapacityCoeff d S) y₀) := by
    rw [hclock]; exact hH.strictMono_bmClk
  obtain ⟨yref⟩ := nonempty_of_isProbabilityMeasure P₂
  have hc : 0 < min (a₀ ^ 2) 1 := lt_min (sq_pos_of_pos (hH.d9 yref).a0) zero_lt_one
  have hClb : ∀ y₀ r, min (a₀ ^ 2) 1 * r ≤ seedQuadClock (seedCapacityCoeff d S) y₀ r := by
    rw [hclock]; exact hH.le_bmClk
  have hphys := g3Fst_physical hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσS
  have hφ : ∀ y₀, (d y₀).φ = physMap y (Strip.extPath (W₁ · x₀)) σ := fun _ => hphys.2
  have hownp : ∀ y₀, OwnData (d y₀).W (physHull y (Strip.extPath (W₁ · x₀)) σ)
      (d y₀).φ (S y₀) (d y₀).a (d y₀).W' := by
    rw [← hphys.1]; exact hown
  have hσζ : (σ : ℝ≥0∞) < ζ₁ x₀ := by
    have hqlo : 0 < x - y := sub_pos.2 hyx
    have hqlox : x - y < -y := by linarith
    have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
      goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
        (fun i => by fin_cases i; simp; linarith)
    obtain ⟨-, hg, -⟩ := g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hg k x₀).1
  have hWs : eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ = W₁ σ x₀ := by
    simpa only [extPath_coe] using
      eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀ ⟨σ.coe_nonneg, NNReal.coe_le_coe.2 hσS⟩
  have hv : ∀ y₀ i, ∃ v, IsForwardSol (d y₀).W'
      (largeG3Marks y (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i)
      ((d y₀).a (S y₀)) v := by
    intro y₀ i
    dsimp only [d, S, g3FstData, SeedData.fromSource]
    fin_cases i
    · simpa [largeG3Marks, sub_neg_eq_add, add_comm] using hH.alive y₀ 0
    · simpa [largeG3Marks, sub_neg_eq_add, add_comm] using hH.alive y₀ 1
    · simpa [largeG3Marks, hWs, sub_neg_eq_add, add_comm] using hH.alive₀ y₀
    · simpa [largeG3Marks, sub_neg_eq_add, add_comm] using hH.alive y₀ 2
  refine ⟨hCc, hCs, _, hc, hClb, fun y₀ => ?_⟩
  exact seedImageGeometry_largeG3 hCc hCs hc hClb hx (h₁.path x₀) hσζ
    (x₀ := y) (sub_self y) hownp hφ y₀ (hv y₀)
    (fun i u hu => sub_ne_zero.1 ((hown y₀).frzImg_sub_ne_zero (hv y₀ i).choose_spec hu))

end InteractingSLE.ZhanGT4.A1G3Lg
