/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgZeroId
import InteractingSLE.Spec.ZhanGT4.A1G3LgCaps

/-!
# G3 large direction: geometry and noise at frozen time zero

The repeated outer force has total weight `-4`, so the compensated image noise
is the large marginal's original Brownian motion.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1G3Lg
open A2X A1Ref A1Core A1Marg A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Forces A1MultiMark A1Family A1RLaw A1G3Law A1G3L2 A1SeedGeom

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

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- The compensated residual at frozen time zero is the large Brownian motion. -/
theorem g3Fst0_noise (k : ℕ) (x₀ : X) (y₀ : Y) {t : ℝ≥0}
    (ht : t ≤ g3S₂ x y W₂ ζ₂ k y₀) :
    seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
      (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) s (x₀, y₀))
      (fun i s => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x₀, y₀))
      (fun j _ => (j.elim0 : ℝ)) t = B₂ t y₀ := by
  obtain ⟨hW, -, hV, -⟩ := g3Fst_zero_ident hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y₀
  have hlt : ∀ s : ℝ≥0, s ≤ t → (s : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) :=
    fun s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hs.trans ht))
      (g3Fst_lt_lifeEnd hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀)
  have hint : ∀ i, (∫ s in (0 : ℝ)..t, largeG3ImgRhoL κ i /
      (rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) s.toNNReal (x₀, y₀) -
        g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i s.toNNReal (x₀, y₀))) =
      largeG3ImgRhoL κ i *
        (∫ s in (0 : ℝ)..t, (W₂ s.toNNReal y₀ - VL₂ (g3Fst0Idx i) s.toNNReal y₀)⁻¹) := by
    intro i
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hs' := Real.toNNReal_le_iff_le_coe.2 hs.2
    simp only [hW _ (hlt _ hs'), hV i _ (hlt _ hs'), div_eq_mul_inv]
  have hbase : ∀ (i : Fin 2) (c : ℝ),
      (∫ s in (0 : ℝ)..t, c / (W₂ s.toNNReal y₀ - VL₂ i s.toNNReal y₀)) =
        c * (∫ s in (0 : ℝ)..t, (W₂ s.toNNReal y₀ - VL₂ i s.toNNReal y₀)⁻¹) := by
    intro i c
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun _ _ => div_eq_mul_inv _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -⟩ := h₂.path y₀
  have hw := hweq t ((hlt t le_rfl).trans_le (lifeEnd_le _ _ _))
  simp only [Fin.sum_univ_two, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, hbase] at hw
  unfold seedCapacityNoise
  beta_reduce
  rw [hW t (hlt t le_rfl)]
  simp_rw [hint]
  simp only [Fin.sum_univ_four, Finset.univ_eq_empty, Finset.sum_empty,
    largeG3ImgRhoL, g3Fst0Idx, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_zero]
  rw [hw]
  apply (div_eq_iff (Real.sqrt_pos.2 (show 0 < κ by linarith)).ne').2
  ring

/-- The canonical geometry at frozen time zero, through any cap before the strip lifetime. -/
theorem g3Fst_geom_zero (x₀ : X) (y₀ : Y) {cap : ℝ≥0}
    (hcap : (cap : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) :
    SeedImageGeometry (g3FstWord W₁ VL₁ VR₁ 0 x₀) ![] (largeG3ImgRhoL κ) ![]
      (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) (min t cap) (x₀, y₀))
      (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i (min t cap) (x₀, y₀))
      (fun j _ => (j.elim0 : ℝ)) cap := by
  obtain ⟨hW, -, hV, -⟩ := g3Fst_zero_ident hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y₀
  have hlt : ∀ t : ℝ≥0, ((min t cap : ℝ≥0) : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) :=
    fun t => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hcap
  have ew := funext fun t => hW _ (hlt t)
  have ev := funext fun i => funext fun t => hV i _ (hlt t)
  rw [ew, ev]
  obtain ⟨hR1, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hlive : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt bot_le (hR1 0 x₀).1
  have hword := isSeedWord_g3FstWord hx h₁.path 0 x₀ hlive
  have hinit := (g3Fst_zero_marks h₁ x₀).1
  have hζ : ∀ t : ℝ≥0, t ≤ cap → (t : ℝ≥0∞) < ζ₂ y₀ :=
    fun t ht => (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hcap).trans_le (lifeEnd_le _ _ _)
  obtain ⟨hw0, hv0, -, hcw, hcv, -, -, -, -, -, hint, -, -, hveq, -⟩ := h₂.path y₀
  dsimp only at hw0 hv0 hint hveq
  have hm : ∀ (t : ℝ≥0), t ≤ cap → ∀ s ∈ uIcc (0 : ℝ) t, min s.toNNReal cap = s.toNNReal :=
    fun t ht s hs => min_eq_left ((Real.toNNReal_le_iff_le_coe.2
      (by rw [uIcc_of_le t.coe_nonneg] at hs; exact hs.2)).trans ht)
  refine seedImageGeometry_of_isSeedWord hword (by simp only [zero_le, min_eq_left, hw0])
    (fun i => by rw [min_eq_left (zero_le (a := cap)), hv0, hinit]) (fun j => j.elim0)
    (continuous_stopped hcw (hζ cap le_rfl))
    (fun i => continuous_stopped (hcv (g3Fst0Idx i)) (hζ cap le_rfl)) (fun j => j.elim0)
    (fun t ht i => ?_) (fun _ _ j => j.elim0) (fun t ht i => ?_)
    (fun _ _ j => j.elim0) (fun t _ ht i => ?_) (fun _ _ _ j => j.elim0)
  · refine (hint t (hζ t ht) (g3Fst0Idx i)).congr fun s hs => ?_
    simp only [hm t ht s (uIoc_subset_uIcc hs)]
  · rw [min_eq_left ht, hveq t (hζ t ht) (g3Fst0Idx i), hinit]
    congr 1
    exact intervalIntegral.integral_congr fun s hs => by simp only [hm t ht s hs]
  · rw [min_eq_left ht]
    exact g3Large_force_lt (h₂.path y₀) (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hcap) _

end InteractingSLE.ZhanGT4.A1G3Lg
