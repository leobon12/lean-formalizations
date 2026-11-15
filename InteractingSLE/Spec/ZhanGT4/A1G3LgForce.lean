/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgIdent

/-!
# G3 large direction: canonical forces and geometry

The measurable canonical force family agrees with the frozen coordinates of
the capacity image chain.
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

variable (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
  (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {a W' : Y → ℝ → ℝ}
  (hown₁ : ∀ y₀, OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
    (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
    (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀))

include hσ hσS hown₁

/-- Each canonical large-direction force is its frozen capacity coordinate. -/
theorem g3Fst_VL_eq :
    let d := g3FstData (κ := κ) (x := x) (y := y) (W₁ := W₁) (ζ₁ := ζ₁)
      (W₂ := W₂) (ζ₂ := ζ₂) k σ x₀ a W'
    ∀ y₀ i t, t ≤ seedCapacityHorizon d (g3S₂ x y W₂ ζ₂ k) y₀ →
      g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀) =
      capForce d (g3S₂ x y W₂ ζ₂ k)
        (fun y₀ => frzImg (d y₀).W' (d y₀).a
          (largeG3Marks y (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i)) t y₀ := by
  intro d y₀ i t ht
  obtain ⟨hCc, hCs, c, hc, hClb, hgeo⟩ :=
    g3FstData_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁
  by_cases ht0 : t = 0
  · subst ht0
    rw [g3FstVL_zero]
    exact ((hgeo y₀).left_zero i).symm
  obtain ⟨hown, heq, hgood, hk, hlive⟩ :=
    g3Fst_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀
  have hownD : ∀ y₀, OwnData (d y₀).W
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (d y₀).φ (g3S₂ x y W₂ ζ₂ k y₀) (d y₀).a (d y₀).W' := hown₁
  have hstart : W' y₀ 0 = y + VR₁ 2 σ x₀ := by
    have h := hown
    simp only [sub_zero] at h
    exact W'_zero_eq_of_path (h₁.path x₀) 2 hlive
      (fun r hr => smallG3_sepP_of_good hκ4 hκ8 hyx hx (h₁.path x₀) (hg₁ x₀) r
        (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hlive)) (by simp) h
  have hp : ∀ i, largeG3Marks (y - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀)
      (fun j t => VR₁ j t x₀) σ i = g3FstWord W₁ VL₁ VR₁ σ x₀ i + W' y₀ 0 + 0 := by
    rw [hstart]
    intro i
    fin_cases i <;> simp [largeG3Marks, g3FstWord] <;> ring
  have hxi : g3FstWord W₁ VL₁ VR₁ σ x₀ i ≠ 0 := by
    have hlt := (largeG3_marks_lt hx (h₁.path x₀) hlive).2 (y - 0) i
    rw [hp i, sub_zero, ← hstart] at hlt
    intro hi
    rw [hi, zero_add, add_zero] at hlt
    exact lt_irrefl _ hlt
  have hTa := (coe_seedCapacityHorizon hownD y₀).le
  have hw : ∀ u, u ≤ seedCapacityHorizon d (g3S₂ x y W₂ ζ₂ k) y₀ →
      seedCapacityDriver d (g3S₂ x y W₂ ζ₂ k) u y₀ = W' y₀ u - W' y₀ 0 :=
    fun u hu => seedCapacityDriver_eq_sub hownD hCc hCs hc hClb y₀ hu
  simp only [g3FstVL, ite_eq_right ht0]
  exact canonForce_eq_of_geometry_left
    (L := {z : X × Y | (σ : ℝ≥0∞) < ζ₁ z.1})
    (wj := fun z t => W₂ t z.2)
    (ζj := fun z => lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2))
    (wk := fun z t => W₁ t z.1) (τ := fun _ => σ) (ω := (x₀, y₀))
    hown heq (fun T hT => continuousOn_extPath_Icc ((A1G3Law.g3Fst_facts h₁ h₂).2.1 y₀) hT)
    (extPath_zero_of (h₂.path y₀).1) hk (extPath_zero_of (h₁.path x₀).1) hgood
    (hgeo y₀) hTa hw hlive i hxi (hp i) ht

/-- The canonical large-direction family, stopped at its protected cap, has the G3 image geometry. -/
theorem g3Fst_geometry (y₀ : Y) :
    SeedImageGeometry (g3FstWord W₁ VL₁ VR₁ σ x₀) ![] (largeG3ImgRhoL κ) ![]
      (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ)
        (min t (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀))) (x₀, y₀))
      (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i
        (min t (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀))) (x₀, y₀))
      (fun j _ => (j.elim0 : ℝ))
      (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀)) := by
  obtain ⟨-, -, c, hc, hlb, hgeo⟩ :=
    g3FstData_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁
  have hcap := g3Fst_cap_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀
  have h := hgeo y₀
  rw [← hcap] at h
  exact h.stop_of_eqOn
    (vR' := fun j _ => (j.elim0 : ℝ))
    (fun t ht => g3Fst_rDrv_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀ t (hcap ▸ ht))
    (fun i t ht => g3Fst_VL_eq hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown₁ y₀ i t (hcap ▸ ht))
    (fun j => j.elim0)

end InteractingSLE.ZhanGT4.A1G3Lg

