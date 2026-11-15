/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgGood
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndZeroId
import InteractingSLE.Spec.ZhanGT4.A1EFamZero

/-!
# G3 large direction: identification at frozen time zero

The empty frozen hull leaves the large curve unchanged. The four image forces
are the two original forces, with the outer force repeated three times.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1G3Lg
open QuantumZipper (fwdMap fwdHull IsForwardSol)
open A2X A1Ref A1Core A1Marg A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Forces A1MultiMark A1Family A1RLaw A1G3Law A1G3L2 A1SeedGeom

/-- The original large force corresponding to each of the four frozen marks. -/
def g3Fst0Idx : Fin 4 → Fin 2 := ![0, 1, 1, 1]

/-- Both large forces lie strictly left of the driver on its strip lifetime. -/
theorem g3Large_force_lt {κ x y : ℝ} {W : ℝ≥0 → ℝ} {VL : Fin 2 → ℝ≥0 → ℝ}
    {VR : Fin 0 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] W VL VR B ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < lifeEnd W (VL 0) ζ) (i : Fin 2) : VL i t < W t := by
  obtain ⟨-, -, -, -, -, -, hanti, -⟩ := hP
  have h := A2X.P3.isStripLife_of_lt_lifeEnd ht
  exact lt_of_le_of_lt (hanti t h.1 (show (0 : Fin 2) ≤ i from Fin.zero_le i)) (h.2 t le_rfl)

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y]
    (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω)
    (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))

include h₁ in
/-- The word and physical marks at frozen time zero are the original large marks. -/
theorem g3Fst_zero_marks (x₀ : X) :
    (∀ i, g3FstWord W₁ VL₁ VR₁ 0 x₀ i = (![x, y] : Fin 2 → ℝ) (g3Fst0Idx i)) ∧
      ∀ i, largeG3Marks (y - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀)
        (fun j t => VR₁ j t x₀) 0 i = (![x, y] : Fin 2 → ℝ) (g3Fst0Idx i) := by
  obtain ⟨hw, hl, hr, -⟩ := h₁.path x₀
  constructor <;> intro i <;> fin_cases i <;>
    simp [g3FstWord, largeG3Marks, g3Fst0Idx, hw, hl, hr]

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- At the trivial frozen time the canonical driver, lifetime, forces and caps
are the large curve's original data. -/
theorem g3Fst_zero_ident (x₀ : X) (y₀ : Y) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun _ => 0) t (x₀, y₀) = W₂ t y₀) ∧
    rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun _ => 0) (x₀, y₀) = lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) ∧
    (∀ i (t : ℝ≥0), (t : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) →
      g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y₀) = VL₂ (g3Fst0Idx i) t y₀) ∧
    ∀ k, g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) =
      g3S₂ x y W₂ ζ₂ k y₀ := by
  obtain ⟨hR1, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hζ₁ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt bot_le (hR1 0 x₀).1
  obtain ⟨τ', hτ', hcτ'⟩ := exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1 hζ₁
  rw [NNReal.coe_zero] at hτ'
  have hjo : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) →
      ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 T) := fun T hT =>
    continuousOn_extPath_Icc (h₂.path y₀).2.2.2.1 (hT.trans_le (lifeEnd_le _ _ _))
  have hj0 : Strip.extPath (W₂ · y₀) 0 = 0 := by simp [Strip.extPath, (h₂.path y₀).1]
  have hk0 : Strip.extPath (W₁ · x₀) 0 = 0 := by simp [Strip.extPath, (h₁.path x₀).1]
  obtain ⟨hct, hclk, hdrv, hlife⟩ := A1EFam.imgZero_facts (xk := y) hjo hj0 ⟨τ', hτ', hcτ'⟩ hk0
  have hL0 : (0 : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) :=
    lt_of_le_of_lt bot_le (g3Fst_lt_lifeEnd hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ 0 x₀ y₀)
  have hdrv' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) →
      A1Ref.imgDrv 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
        (Strip.extPath (W₁ · x₀)) 0 t = W₂ t y₀ := fun t ht => by
    rw [hdrv t t.coe_nonneg (by rwa [ENNReal.ofReal_coe_nnreal]), extPath_coe]
  have hdrv0 : A1Ref.imgDrv 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) 0 0 = 0 := by
    rw [hdrv 0 le_rfl (by rwa [ENNReal.ofReal_zero]), hj0]
  refine ⟨fun t ht => ?_, ?_, fun i t ht => ?_, fun k => ?_⟩
  · simp only [rDrvFst, cImgDrvM, cImgDrv, cImgSrc, hζ₁, ↓reduceIte, NNReal.coe_zero]
    rw [hdrv' t ht, hdrv0, sub_zero]
  · simp only [rLifeFst, cImgLifeM, cImgLife, hζ₁, ↓reduceIte, NNReal.coe_zero]
    exact hlife
  · have hp := (g3Fst_zero_marks h₁ x₀).2 i
    have hvL0 := (h₂.path y₀).2.1 (g3Fst0Idx i)
    by_cases ht0 : t = 0
    · subst ht0
      rw [g3FstVL_zero, (g3Fst_zero_marks h₁ x₀).1 i]
      exact hvL0.symm
    · simp only [g3FstVL, ite_eq_right ht0]
      have hlt : ENNReal.ofReal (t : ℝ) < A1Ref.imgLife 0 (Strip.extPath (W₂ · y₀))
          (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y (Strip.extPath (W₁ · x₀)) 0 := by
        rw [hlife, ENNReal.ofReal_coe_nnreal]; exact ht
      simp only [rForceFst, canonForce, mem_ofPred_eq, hζ₁, true_and, NNReal.coe_zero, hlt, ↓reduceIte]
      rw [hdrv' t ht, hdrv0, hp]
      have hst : stopDrv (A1Ref.imgDrv 0 (Strip.extPath (W₂ · y₀))
          (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y (Strip.extPath (W₁ · x₀)) 0) t =
          stopDrv (Strip.extPath (W₂ · y₀)) t := funext fun s => by
        simp only [stopDrv]
        have hm : max 0 (min s t) ∈ Icc (0 : ℝ) t :=
          ⟨le_max_left _ _, max_le t.coe_nonneg (min_le_right _ _)⟩
        exact hdrv _ hm.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hm.2)
          (by rwa [ENNReal.ofReal_coe_nnreal]))
      rw [hst]
      have hlt₂ := ht.trans_le (lifeEnd_le _ _ _)
      obtain ⟨-, -, -, -, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := h₂.path y₀
      have hveq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₂ y₀ →
          VL₂ (g3Fst0Idx i) s y₀ = (![x, y] : Fin 2 → ℝ) (g3Fst0Idx i) +
            ∫ r in (0 : ℝ)..s, 2 / (VL₂ (g3Fst0Idx i) r.toNNReal y₀ - W₂ r.toNNReal y₀) :=
        fun s hs => hvLeq s hs (g3Fst0Idx i)
      have hct' := hjo t (by rwa [ENNReal.ofReal_coe_nnreal])
      have hv := A1G3Calc.isForwardSol_of_force (hcvL (g3Fst0Idx i)) hveq hlt₂
        (fun r hr => (g3Large_force_lt (h₂.path y₀)
          (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht) (g3Fst0Idx i)).ne) hct' (fun _ _ => rfl)
      rw [fwdRe_stopDrv_eq hct' t.coe_nonneg hv,
        QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨t.coe_nonneg, le_rfl⟩]
      simp only [ofReal_re, extPath_coe]
      ring
  · have hOwn : g3FstOwn x y W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) = g3S₂ x y W₂ ζ₂ k y₀ := by
      simp only [g3FstOwn, zero_le, ↓reduceIte]
    have hL := g3Fst_lt_lifeEnd hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀
    have hG : A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀))
        (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y (Strip.extPath (W₁ · x₀))
        ((0 : ℝ≥0) : ℝ) (g3FstOwn x y W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀)) := by
      rw [hOwn, NNReal.coe_zero]
      exact ⟨(g3Fst_frame hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
          (s := 0) (NNReal.coe_nonneg _)).2.2.1 y₀,
        by rw [hct, ENNReal.ofReal_coe_nnreal]; exact hL⟩
    unfold g3FstCap
    rw [capFst_eq_of_isGoodTime (z := (x₀, y₀)) (τ := fun _ => (0 : ℝ≥0))
      (T := g3FstOwn x y W₁ ζ₁ W₂ ζ₂ 0 k) hζ₁ hjo (h₂.path y₀).1
      ⟨τ', by rw [NNReal.coe_zero]; exact hτ', hcτ'⟩ (h₁.path x₀).1 hG, hOwn,
      NNReal.coe_zero, hclk _ (NNReal.coe_nonneg _) (by rw [ENNReal.ofReal_coe_nnreal]; exact hL)]
    exact Real.toNNReal_coe

end InteractingSLE.ZhanGT4.A1G3Lg
