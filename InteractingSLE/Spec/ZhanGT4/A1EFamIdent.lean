/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EFamD10

/-!
# Zhan's A.1 under R83, (Eight), large-curve direction: the identification step and the protected one-sample law

Packet PROVE-A1-EIGHTFAM. At a small sample `x₀` and a protected frozen time `σ ∈ (0, S₁ᵐ(x₀)]` (patched marginals:
regular, continuous Brownian paths and `GoodSmallEight` at every sample):

* `eightFst_phys`: the frozen small hull and chart in the physical frame (`physHull`, `physMap`);
* **`eightFstSeed`**, **`eightFst_seed`**: the seeded data of the large curve (driver `√κB₂`, an image chain against
  the frozen small hull up to the large exit), with the clock facts of its quadratic clock and the forward solutions
  of the three frozen-chart marks (from `eightFst_frzD10Hyp`);
* `eightFst_imgClk_eq`: the canonical clock is the image chain's clock up to the exit;
* **`eightFst_ident`**: the masked canonical driver of the original family is the seeded capacity driver, its forces
  are the replacement family's forces and the capacity coordinates of the marks, the raw cap at the exit is the
  capacity horizon, and the deterministic geometry (`SeedImageGeometry`) holds up to every cap below the horizon;
* **`eightFst_law_prot`**: the one-sample law (`IsSeedSampleLaw`) with the raw caps `eightFstCap` and the residual as
  the noise, under `P₂.withDensity (eightFstD … σ m (x₀, ·))` (A1-EIGHTLAW's `eightFst_isSeedSampleLaw`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1EFam
open QuantumZipper (H fwdMap fwdHull drive IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm A1Forces A1MultiMark A1Family A1RLaw

section Frame
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}

/-- The frozen small hull and chart at a protected time, in the physical frame. -/
theorem eightFst_phys (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) :
    fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ = physHull x (Strip.extPath (W₁ · x₀)) σ ∧
      frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ =
        physMap x (Strip.extPath (W₁ · x₀)) σ := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  have hlt : (eightS₁ x W₁ ζ₁ m x₀ : ℝ≥0∞) < ζ₁ x₀ := (hgood₁ m x₀).1
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hlt
  have hdc : Continuous (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) :=
    continuous_eightDrv (h₁.path x₀).2.2.2.1 hlt
  have heq : EqOn (Strip.extPath (W₁ · x₀)) (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) (Icc 0 (σ : ℝ)) :=
    fun u hu => (A1Ref.stopDrv_eqOn _ _ ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hσ)⟩).symm
  have e1 := A1G3Row.fwdHull_sub_const_eq_physHull (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) (-x) σ
  have e2 := A1G3Row.frzChart_sub_const_eq_physMap (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) (-x) σ
  rw [neg_neg] at e1 e2
  rw [e1, e2, A1SeedGeom.physHull_congr_of_continuousOn hcT' hdc.continuousOn σ.coe_nonneg
    ((NNReal.coe_le_coe.2 hσ).trans_lt hT') heq, physMap_congr σ.coe_nonneg heq]
  exact ⟨rfl, rfl⟩


/-- **The seeded data of the large Eight direction**: driver `√κB₂`, the image chain `(a, W')` against the frozen
small hull, the chart `φ` (no seeds of its own). -/
def eightFstSeed (κ : ℝ) (B₂ : ℝ≥0 → Y → ℝ) (a W' : Y → ℝ → ℝ) (φ : ℂ → ℂ) (y : Y) : SeedData 0 :=
  { W := drive κ B₂ y, W' := W' y, a := a y, φ := φ, κ := κ, r := ![], ζ₀ := 0, V₀ := 0, G₀ := 0, V := ![] }

/-- **The seeded large Eight direction at a protected sample**: an image chain of `√κB₂` against the frozen small
hull up to the large exit, the clock facts of its seeded data, and the forward solutions of the three frozen-chart
marks up to the image of the exit. -/
theorem eightFst_seed (hκ8 : 8 ≤ κ) (hx : x < 0) [𝓖₂.IsRightContinuous]
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ0 : 0 < σ) (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) :
    ∃ a W' : Y → ℝ → ℝ,
      (∀ y, OwnData (drive κ B₂ y) (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ)
        (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y)) ∧
      (∀ y, Continuous (seedQuadClock (seedCapacityCoeff
        (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)) y)) ∧
      (∀ y, StrictMono (seedQuadClock (seedCapacityCoeff
        (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)) y)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff
        (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)) y r) ∧
      ∀ y i, ∃ v, IsForwardSol (W' y) (largeEightMarks x (W₁ · x₀) (fun i t => VL₁ i t x₀)
        (fun j t => VR₁ j t x₀) σ i) (a y (eightS₂ x W₂ ζ₂ m y)) v := by
  have hσ' : (σ : ℝ) ≤ eightS₁ x W₁ ζ₁ m x₀ := NNReal.coe_le_coe.2 hσ
  obtain ⟨a, W', haW⟩ := exists_ownData_eightFst hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := σ) hσ0 hσ'
  obtain ⟨r, a₀, γ, Γ, lam, L, Tm, hH⟩ := eightFst_frzD10Hyp hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ0 hσ' haW
  obtain ⟨hph, hpm⟩ := eightFst_phys hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ
  set d := eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ) with hd
  have hown : ∀ y, OwnData (d y).W (physHull x (Strip.extPath (W₁ · x₀)) σ) (d y).φ (eightS₂ x W₂ ζ₂ m y)
      (d y).a (d y).W' := fun y => by
    have h := haW y
    rw [hph, hpm] at h
    exact h
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  have hS₂ : IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0) :=
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) m
  have := nonempty_of_isFilteredBrownianReal h₂.evol.1
  obtain ⟨hCc, hCs, -, hlb⟩ := seedClock_facts (d := d) hH hown (fun y => rfl) (fun u => h₂.evol.1.2.1 u) hB₂ hS₂
  refine ⟨a, W', haW, hCc, hCs, ⟨_, lt_min (pow_pos (hH.d9 (Classical.arbitrary Y)).a0 2) one_pos, hlb⟩,
    fun y i => ?_⟩
  have hW1 : eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ σ = W₁ σ x₀ := by
    rw [eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) m x₀ ⟨σ.coe_nonneg, hσ'⟩, extPath_coe]
  fin_cases i
  · obtain ⟨v, hv⟩ := hH.alive y 0
    refine ⟨v, ?_⟩
    convert hv using 2
    have e : x + VR₁ 0 σ x₀ = Strip.extPath (VR₁ 0 · x₀) σ - -x := by rw [extPath_coe]; ring
    simp only [largeEightMarks]
    rw [e]; rfl
  · obtain ⟨v, hv⟩ := hH.alive₀ y
    refine ⟨v, ?_⟩
    convert hv using 2
    have e : x + W₁ σ x₀ = eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ σ - -x := by rw [hW1]; ring
    simp only [largeEightMarks]
    rw [e]; rfl
  · obtain ⟨v, hv⟩ := hH.alive y 1
    refine ⟨v, ?_⟩
    convert hv using 2
    have e : x + VL₁ 0 σ x₀ = Strip.extPath (VL₁ 0 · x₀) σ - -x := by rw [extPath_coe]; ring
    simp only [largeEightMarks]
    rw [e]; rfl


/-- **The canonical clock is the image chain's clock** up to the large exit (protected frozen small time). -/
theorem eightFst_imgClk_eq (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) {a W' : Y → ℝ → ℝ}
    (haW : ∀ y, OwnData (drive κ B₂ y) (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ)
      (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y))
    (y : Y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (eightS₂ x W₂ ζ₂ m y)) :
    A1Ref.imgClk 0 (Strip.extPath (W₂ · y)) x (Strip.extPath (W₁ · x₀)) σ t = a y t := by
  obtain ⟨hph, hpm⟩ := eightFst_phys hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ
  have hown : OwnData (drive κ B₂ y) (physHull x (Strip.extPath (W₁ · x₀)) σ)
      (physMap x (Strip.extPath (W₁ · x₀)) σ) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y) := by
    have h := haW y
    rw [hph, hpm] at h
    exact h
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, -, -, -, -, -, -, hlt₂⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  obtain ⟨hdc, -, -, -, -, hdrive, -, -⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := 0)
    (NNReal.coe_nonneg _)
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₂.path y).2.2.2.1 (hlt₂ m y)
  rw [← A1SeedGeom.imgClk_congr σ.coe_nonneg (fun _ _ => rfl) (hdc y).continuousOn hcT' (ht.2.trans_lt hT')
    fun u hu => hdrive y u ⟨hu.1, hu.2.trans ht.2⟩, (isImgDrvOn_of_ownData hown).2 ht]

/-- **The canonical image of the large Eight direction is the seeded image chain** at a protected sample (patched
data): the masked canonical driver is the seeded capacity driver, the canonical forces are the capacity coordinates of
the frozen-chart marks, the raw cap is the capacity horizon, and the deterministic geometry holds up to every cap below
the horizon. -/
theorem eightFst_ident (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) {a W' : Y → ℝ → ℝ}
    (haW : ∀ y, OwnData (drive κ B₂ y) (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ)
      (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) σ) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff
      (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff
      (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)) y))
    {c : ℝ} (hc : 0 < c) (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff
      (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)) y r)
    (hv : ∀ y i, ∃ v, IsForwardSol (W' y) (largeEightMarks x (W₁ · x₀) (fun i t => VL₁ i t x₀)
      (fun j t => VR₁ j t x₀) σ i) (a y (eightS₂ x W₂ ζ₂ m y)) v) (y : Y) :
    (∀ t : ℝ≥0, t ≤ seedCapacityHorizon (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ))
        (eightS₂ x W₂ ζ₂ m) y →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) t (x₀, y) =
      seedCapacityDriver (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)
        t y) ∧
    (∀ i (t : ℝ≥0), t ≤ seedCapacityHorizon (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ))
        (eightS₂ x W₂ ζ₂ m) y →
      eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y) =
        rForceFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ)
          (fun x' => largeEightMarks (x - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i) t
          (x₀, y)) ∧
    (∀ i (t : ℝ≥0), t ≤ seedCapacityHorizon (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ))
        (eightS₂ x W₂ ζ₂ m) y →
      eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y) =
        capForce (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)
          (fun y => frzImg (W' y) (a y) (largeEightMarks x (W₁ · x₀) (fun i t => VL₁ i t x₀)
            (fun j t => VR₁ j t x₀) σ i)) t y) ∧
    (∀ T : X × Y → ℝ, T (x₀, y) = eightS₂ x W₂ ζ₂ m y →
      capFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) T (x₀, y) =
      seedCapacityHorizon (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ))
        (eightS₂ x W₂ ζ₂ m) y) ∧
    ∀ cap : ℝ≥0, cap ≤ seedCapacityHorizon (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ))
        (eightS₂ x W₂ ζ₂ m) y →
      SeedImageGeometry (eightFstWord W₁ VL₁ VR₁ σ x₀) ![] (largeEightImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun _ => σ) (min t cap) (x₀, y))
        (fun i t => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i (min t cap) (x₀, y)) (fun j _ => (j.elim0 : ℝ)) cap := by
  have hx0 : x - 0 = x := sub_zero x
  obtain ⟨hph, hpm⟩ := eightFst_phys hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ
  set d := eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ) with hd
  have hown : ∀ y, OwnData (d y).W (physHull (x - 0) (Strip.extPath (W₁ · x₀)) σ) (d y).φ (eightS₂ x W₂ ζ₂ m y)
      (d y).a (d y).W' := fun y => by
    have h := haW y
    rw [hph, hpm] at h
    rw [hx0]; exact h
  have hφ : ∀ y, (d y).φ = physMap (x - 0) (Strip.extPath (W₁ · x₀)) σ := fun y => by rw [hx0]; rfl
  have hW : ∀ y, (d y).W = Strip.extPath (driveFam κ B₂ · y) := fun y => rfl
  obtain ⟨hdc, hd0, -, -, -, hdrive, -, -⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := 0)
    (NNReal.coe_nonneg _)
  have hj : ∀ y (T : ℝ), ENNReal.ofReal T < (fun _ : Y => (⊤ : ℝ≥0∞)) y → ContinuousOn (d y).W (Icc 0 T) :=
    fun y T _ => (hdc y).continuousOn
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  have hσζ : (σ : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσ) (hgood₁ m x₀).1
  obtain ⟨τ', hτ', hcτ'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hσζ
  have hgood : ∀ y, IsGoodTime 0 (d y).W ((fun _ : Y => (⊤ : ℝ≥0∞)) y) (x - 0) (Strip.extPath (W₁ · x₀)) σ
      (eightS₂ x W₂ ζ₂ m y) := fun y => by
    rw [hx0]; exact eightFst_isGoodTime_drive hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ
  set live : ℝ≥0 → X → Prop := fun t ω => (t : ℝ≥0∞) < ζ₁ ω with hlivedef
  have hlive : live σ x₀ := hσζ
  have hd0' : driveFam κ B₂ 0 y = 0 := by
    have h := hd0 y
    simpa only [drive, Real.toNNReal_zero, driveFam] using h
  have hjo : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 T) := fun T hT =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y).2.2.2.1 (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _))
  have hjeq : ∀ t : ℝ≥0, (t : ℝ) ≤ eightS₂ x W₂ ζ₂ m y → driveFam κ B₂ t y = W₂ t y := fun t ht => by
    have h := hdrive y t ⟨t.coe_nonneg, ht⟩
    simpa only [drive, Real.toNNReal_coe, Strip.extPath, driveFam] using h
  -- times below the horizon are below the canonical clock of the exit
  have htle : ∀ t : ℝ≥0, t ≤ seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y →
      (t : ℝ) ≤ A1Ref.imgClk 0 (Strip.extPath (W₂ · y)) x (Strip.extPath (W₁ · x₀)) σ (eightS₂ x W₂ ζ₂ m y) :=
    fun t ht => by
    rw [eightFst_imgClk_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ haW y ⟨NNReal.coe_nonneg _, le_rfl⟩]
    exact coe_le_a_of_le_horizon hown (fun _ => rfl) ht
  -- the driver
  have hI1 : ∀ t : ℝ≥0, t ≤ seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) t (x₀, y) = seedCapacityDriver d (eightS₂ x W₂ ζ₂ m) t y := fun t ht => by
    rw [← eightFst_rDrvFst_drive_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ hlive hlive (htle t ht)]
    exact rDrvFst_eq_seedCapacityDriver (xj := 0) (xk := x) hlive hW hown hφ hj ⟨τ', hτ', hcτ'⟩ (h₁.path x₀).1
      hgood hCc hCs hc hClb y ht
  -- the forces: original family = replacement family below the horizon
  have hk : ∃ τ', (((fun _ : X => σ) x₀ : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 τ') :=
    ⟨τ', hτ', hcτ'⟩
  have hForce : ∀ i (t : ℝ≥0), t ≤ seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y →
      rForceFst live 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ)
        (fun x' => largeEightMarks (x - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i) t
        (x₀, y) =
      rForceFst live 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ (fun _ => σ)
        (fun x' => largeEightMarks (x - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i) t
        (x₀, y) := fun i t ht =>
    rForceFst_congr (z := (x₀, y)) (T := eightS₂ x W₂ ζ₂ m y) hlive hlive hjo (h₂.path y).1
      (fun T _ => (show Continuous (Strip.extPath (driveFam κ B₂ · y)) from hdc y).continuousOn) hd0' hk
      (h₁.path x₀).1 hk (h₁.path x₀).1 (eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ)
      (eightFst_isGoodTime_drive hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ) hjeq (fun _ _ => rfl) rfl (htle t ht)
  -- the geometry of the replacement family
  have hv' : ∀ i, ∃ v, IsForwardSol (d y).W' (largeEightMarks (x - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀)
      (fun j t => VR₁ j t x₀) σ i : ℂ) ((d y).a (eightS₂ x W₂ ζ₂ m y)) v := fun i => by
    rw [hx0]; exact hv y i
  have hne' : ∀ i, ∀ u ∈ Icc (0 : ℝ) (eightS₂ x W₂ ζ₂ m y), frzImg (d y).W' (d y).a
      (largeEightMarks (x - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i) u ≠
        (d y).A 0 u := fun i u hu => by
    obtain ⟨v, hv1⟩ := hv' i
    exact sub_ne_zero.1 ((hown y).frzImg_sub_ne_zero hv1 hu)
  have hgeoD : ∀ cap : ℝ≥0, cap ≤ seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y →
      SeedImageGeometry (eightFstWord W₁ VL₁ VR₁ σ x₀) ![] (largeEightImgRhoL κ) ![]
        (fun t => rDrvFst live 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ) (min t cap) (x₀, y))
        (fun i t => rForceFst live 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ)
          (fun x' => largeEightMarks (x - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i)
          (min t cap) (x₀, y))
        (fun j t => (fun (j : Fin 0) (_ : ℝ≥0) => (j.elim0 : ℝ)) j (min t cap)) cap := fun cap hcap =>
    seedImageGeometry_rDrvFst_largeEight_force (VR := fun j _ => (j.elim0 : ℝ)) (live := live) (xk := x)
      (Wj := driveFam κ B₂) (ζj := fun _ => ⊤) (τ := fun _ => σ) (d := d) (S := eightS₂ x W₂ ζ₂ m) hx
      (h₁.path x₀) hlive hσζ (by rw [sub_zero, sub_self]) hW hown hφ hj hgood hCc hCs hc hClb y hv' hne' hcap
  -- the family forces are the replacement forces below the horizon
  have hV : ∀ i (t : ℝ≥0), t ≤ seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y →
      eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y) =
        rForceFst live 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ)
          (fun x' => largeEightMarks (x - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i) t
          (x₀, y) := fun i t ht => by
    by_cases ht0 : t = 0
    · subst ht0
      rw [eightFstVL_zero]
      have h := (hgeoD 0 bot_le).left_zero i
      simp only [min_self] at h
      exact h.symm
    · rw [hForce i t ht]
      unfold eightFstVL
      exact ite_eq_right_of_eq_false _ _ (eq_false ht0)
  have hI3 : ∀ i (t : ℝ≥0), t ≤ seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y →
      eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y) =
        capForce d (eightS₂ x W₂ ζ₂ m) (fun y => frzImg (W' y) (a y) (largeEightMarks x (W₁ · x₀)
          (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i)) t y := fun i t ht => by
    rw [hV i t ht, rForceFst_eq_rFrzFst_of_seed (live := live) (Wj := driveFam κ B₂) (ζj := fun _ => ⊤) (xk := x)
      (Wk := W₁) (τ := fun _ => σ) (x := x₀) (d := d) (S := eightS₂ x W₂ ζ₂ m) hlive hW hown hφ hj hk
      (h₁.path x₀).1 hgood y (hv' i) ht, rFrzFst_eq_capForce (live := live) (Wj := driveFam κ B₂)
      (ζj := fun _ => ⊤) (xk := x) (Wk := W₁) (τ := fun _ => σ) (x := x₀) (d := d) (S := eightS₂ x W₂ ζ₂ m) hlive
      hW hown hφ hj hk (h₁.path x₀).1 hgood hCc hCs hc hClb y ht]
    simp only [hx0]
    rfl
  have hI5 : ∀ T : X × Y → ℝ, T (x₀, y) = eightS₂ x W₂ ζ₂ m y →
      capFst live 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ (fun _ => σ) T (x₀, y) =
        seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y := fun T hT => by
    have hG := eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ
    rw [← hT] at hG
    rw [capFst_eq_of_isGoodTime (z := (x₀, y)) (τ := fun _ => σ) (T := T) hlive hjo (h₂.path y).1 hk
      (h₁.path x₀).1 hG, hT, eightFst_imgClk_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ haW y
      ⟨NNReal.coe_nonneg _, le_rfl⟩]
    rfl
  refine ⟨hI1, hV, hI3, hI5, fun cap hcap => ?_⟩
  have e1 : (fun t => rDrvFst live 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ (fun _ => σ)
      (min t cap) (x₀, y)) =
      fun t => rDrvFst live 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ) (min t cap) (x₀, y) := funext fun t =>
    (eightFst_rDrvFst_drive_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ hlive hlive
      (htle _ ((min_le_right t cap).trans hcap))).symm
  have e2 : (fun i t => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i (min t cap) (x₀, y)) =
      fun i t => rForceFst live 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ)
        (fun x' => largeEightMarks (x - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i)
        (min t cap) (x₀, y) := funext fun i => funext fun t =>
    hV i _ ((min_le_right t cap).trans hcap)
  have e3 : (fun (j : Fin 0) (_ : ℝ≥0) => (j.elim0 : ℝ)) =
      fun j t => (fun (j : Fin 0) (_ : ℝ≥0) => (j.elim0 : ℝ)) j (min t cap) := funext fun j => j.elim0
  rw [e1, e2, e3]
  exact hgeoD cap hcap

/-- **The protected one-sample law of the large Eight direction** (patched data, raw caps, residual noise): at every
small sample `x₀` and protected frozen time `σ ∈ (0, S₁ᵐ(x₀)]`, under `P₂.withDensity (eightFstD … σ m (x₀, ·))`, the
canonical image data of the large curve satisfy `IsSeedSampleLaw` for the cap `m` (A1-EIGHTLAW's
`eightFst_isSeedSampleLaw` with the identifications of `eightFst_ident`). -/
theorem eightFst_law_prot [𝓖₂.IsRightContinuous] (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ0 : 0 < σ) (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) :
    IsSeedSampleLaw (P₂.withDensity fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ m (x₀, y))
      (fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) t (x₀, y))
      (fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) (x₀, y))
      (fun i t y => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
        (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
          W₁ (fun _ => σ) s (x₀, y))
        (fun i s => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x₀, y)) (fun j _ => (j.elim0 : ℝ)) t)
      (fun k y => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y)) m := by
  obtain ⟨a, W', haW, hCc, hCs, ⟨c, hc, hClb⟩, hv⟩ := eightFst_seed hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ0 hσ
  have hid := eightFst_ident hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ haW hCc hCs hc hClb hv
  set d := eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ) with hd
  obtain ⟨hph, hpm⟩ := eightFst_phys hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ
  have hown : ∀ y, OwnData (d y).W (physHull x (Strip.extPath (W₁ · x₀)) σ) (d y).φ (eightS₂ x W₂ ζ₂ m y)
      (d y).a (d y).W' := fun y => by
    have h := haW y
    rw [hph, hpm] at h
    exact h
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, -, -, -, -, hS₂pos, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hσζ : (σ : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσ) (hgood₁ m x₀).1
  obtain ⟨τ', hτ', hcτ'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hσζ
  have hk : ∃ τ', (((fun _ : X => σ) x₀ : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 τ') :=
    ⟨τ', hτ', hcτ'⟩
  have hjo : ∀ y (T : ℝ), ENNReal.ofReal T < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 T) := fun y T hT =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y).2.2.2.1 (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _))
  have hlive : (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) ((fun _ : X => σ) x₀) x₀ := hσζ
  -- the own times of the raw caps
  set Tk : ℕ → Y → ℝ≥0 := fun k y => if σ ≤ eightS₁ x W₁ ζ₁ k x₀ then eightS₂ x W₂ ζ₂ k y else 0 with hTkdef
  have hOwn : ∀ k y, eightFstOwn x W₁ ζ₁ W₂ ζ₂ σ k (x₀, y) = (Tk k y : ℝ) := fun k y => by
    simp only [eightFstOwn, hTkdef]
    split_ifs <;> simp
  have hSm : ∀ y, eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y) =
      seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y := fun y =>
    (hid y).2.2.2.1 _ (by rw [hOwn m y]; simp only [hTkdef, hσ, ↓reduceIte])
  have hmk : ∀ i, largeEightMarks x (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) σ i =
      ![Strip.extPath (VR₁ 0 · x₀) σ - -x, eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ σ - -x,
        Strip.extPath (VL₁ 0 · x₀) σ - -x] i := fun i => by
    have hW1 : eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ σ = W₁ σ x₀ := by
      rw [eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) m x₀ ⟨σ.coe_nonneg, NNReal.coe_le_coe.2 hσ⟩, extPath_coe]
    fin_cases i
    · show x + VR₁ 0 σ x₀ = Strip.extPath (VR₁ 0 · x₀) σ - -x
      rw [extPath_coe]; ring
    · show x + W₁ σ x₀ = eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ σ - -x
      rw [hW1]; ring
    · show x + VL₁ 0 σ x₀ = Strip.extPath (VL₁ 0 · x₀) σ - -x
      rw [extPath_coe]; ring
  have hgoodk : ∀ k y, 0 < Tk k y → σ ≤ eightS₁ x W₁ ζ₁ k x₀ ∧ Tk k y = eightS₂ x W₂ ζ₂ k y := fun k y hT => by
    by_cases h : σ ≤ eightS₁ x W₁ ζ₁ k x₀
    · exact ⟨h, by simp only [hTkdef, h, ↓reduceIte]⟩
    · simp only [hTkdef, h, ↓reduceIte] at hT; exact absurd hT (lt_irrefl 0)
  have hlaw := eightFst_isSeedSampleLaw hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := σ) (NNReal.coe_pos.2 hσ0)
    (NNReal.coe_le_coe.2 hσ) haW (d := d) (A' := fun _ => physHull x (Strip.extPath (W₁ · x₀)) σ) hown
    (fun _ => rfl) (fun _ => rfl) (m' := m)
    (Wi := fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
      W₁ (fun _ => σ) t (x₀, y))
    (ζi := fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
      W₁ (fun _ => σ) (x₀, y))
    (VL := fun i t y => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y)) (VR := fun j _ _ => (j.elim0 : ℝ))
    (N := fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
        (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
          W₁ (fun _ => σ) s (x₀, y))
        (fun i s => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x₀, y)) (fun j _ => (j.elim0 : ℝ)) t)
    (Scap := fun k y => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y)) hSm
    (fun y t ht => (hid y).1 t (by rw [← hSm y]; exact ht))
    (fun y i t ht => by
      rw [(hid y).2.2.1 i t (by rw [← hSm y]; exact ht)]
      simp only [hmk i]
      rfl)
    (fun y t _ => rfl)
    (fun y => by unfold eightFstCap; exact capFst_le_rLifeFst _ _)
    Tk (fun k => ?_) (fun k y hle => ?_) (fun k y hle => ?_)
  · have e : (fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ m (x₀, y)) = fun y =>
        ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (x₀, y) σ (eightS₂ x W₂ ζ₂ m y)) := funext fun y => by
      simp only [eightFstD, eightM, min_eq_left hσ]
    rw [e]
    exact hlaw
  · by_cases h : σ ≤ eightS₁ x W₁ ζ₁ k x₀
    · simp only [hTkdef, h, ↓reduceIte]
      exact isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
        (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) k
    · simp only [hTkdef, h, ↓reduceIte]
      exact isStoppingTime_const _ _
  · -- `hcap₁`: below the exit the cap is the image chain's clock
    by_cases hT0 : Tk k y = 0
    · rw [hT0]
      unfold eightFstCap
      rw [capFst_of_nonpos (by rw [hOwn k y, hT0, NNReal.coe_zero]), NNReal.coe_zero]
      exact (hown y).a0.symm
    · have hTpos : 0 < Tk k y := pos_iff_ne_zero.2 hT0
      have hG := eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y hσ
      have hGk : IsGoodTime 0 (Strip.extPath (W₂ · y)) (lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x
          (Strip.extPath (W₁ · x₀)) σ (eightFstOwn x W₁ ζ₁ W₂ ζ₂ σ k (x₀, y)) := by
        rw [hOwn k y]
        exact ⟨NNReal.coe_pos.2 hTpos, (ENNReal.ofReal_le_ofReal (NNReal.coe_le_coe.2 hle)).trans_lt hG.2⟩
      have h0 : 0 ≤ a y (Tk k y) := by
        rw [← (hown y).a0]
        exact (hown y).mono.monotoneOn ⟨le_rfl, (hown y).pos.le⟩ ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 hle⟩
          (NNReal.coe_nonneg _)
      unfold eightFstCap
      rw [capFst_eq_of_isGoodTime (z := (x₀, y)) (τ := fun _ => σ) (T := eightFstOwn x W₁ ζ₁ W₂ ζ₂ σ k) hlive
        (hjo y) (h₂.path y).1 hk (h₁.path x₀).1 hGk, hOwn k y, eightFst_imgClk_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ
        haW y ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 hle⟩]
      exact Real.coe_toNNReal _ h0
  · -- `hcap₂`: beyond the exit the caps grow
    have hTpos : 0 < Tk k y := lt_of_lt_of_le (NNReal.coe_pos.1 (hS₂pos m y)) hle
    obtain ⟨hσk, hTk⟩ := hgoodk k y hTpos
    have hTm : Tk m y = eightS₂ x W₂ ζ₂ m y := by simp only [hTkdef, hσ, ↓reduceIte]
    unfold eightFstCap
    refine capFst_mono (z := (x₀, y)) ?_ fun _ => ?_
    · rw [hOwn m y, hOwn k y, hTm]
      exact NNReal.coe_le_coe.2 hle
    · rw [hOwn k y, hTk, clkSup_eq_of_isGoodTime (hjo y) (by simp only [Strip.extPath, Real.toNNReal_zero,
        (h₂.path y).1]) hk (by simp only [Strip.extPath, Real.toNNReal_zero, (h₁.path x₀).1]) σ.coe_nonneg
        (eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y hσk)]
      exact ENNReal.ofReal_ne_top

end Frame
end InteractingSLE.ZhanGT4.A1EFam
