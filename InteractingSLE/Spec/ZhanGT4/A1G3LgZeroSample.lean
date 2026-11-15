/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgZeroLaw

/-!
# G3 large direction: the one-sample law at frozen time zero

The density is one and the canonical processes agree with the large marginal
through each cap, so its own filtration and Brownian motion supply the law.
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

/-- The large-direction sample law at the trivial frozen time. -/
theorem g3Fst_isSeedSampleLaw_zero [𝓖₂.IsRightContinuous] (m : ℕ) (x₀ : X) :
    IsSeedSampleLaw (P₂.withDensity fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 m (x₀, y₀))
      (fun t y₀ => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) t (x₀, y₀))
      (fun y₀ => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) (x₀, y₀))
      (fun i t y₀ => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y₀)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y₀ => seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) t (x₀, y₀))
        (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y₀))
        (fun j _ => (j.elim0 : ℝ)) t)
      (fun m' y₀ => g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m' (x₀, y₀)) m := by
  have hS₂ : ∀ k, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ k ω : WithTop ℝ≥0) := fun k => by
    simpa only [g3FstTk, zero_le, ↓reduceIte] using
      isStoppingTime_g3FstTk (W₁ := W₁) (ζ₁ := ζ₁) hyx hx h₂ 0 x₀ k
  have hid := fun y₀ => g3Fst_zero_ident hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y₀
  have hL : ∀ y₀, (g3S₂ x y W₂ ζ₂ m y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) :=
    fun y₀ => g3Fst_lt_lifeEnd hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀
  have hlt : ∀ y₀ (s : ℝ≥0), s ≤ g3S₂ x y W₂ ζ₂ m y₀ →
      (s : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) :=
    fun y₀ s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hL y₀)
  -- the density is `1`
  have e : (fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 m (x₀, y₀)) = fun _ => 1 := funext fun y₀ => by
    simp only [g3FstD, zero_le, min_eq_left, NNReal.coe_zero, seedHeightField_zero_left, ENNReal.ofReal_one]
  rw [e, show (fun _ : Y => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  -- the cap is the large exit
  have hcap : ∀ y₀, g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y₀) = g3S₂ x y W₂ ζ₂ m y₀ := fun y₀ =>
    (hid y₀).2.2.2 m
  have hE : ∀ s : ℝ≥0, MeasurableSet[𝓖₂ s] {y₀ | s < g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y₀)} :=
    fun s => by
    simp only [hcap]
    have h := (hS₂ m).measurableSet_gt s
    simpa only [WithTop.coe_lt_coe] using h
  have hNres := fun y₀ (t : ℝ≥0) (ht : t ≤ g3S₂ x y W₂ ζ₂ m y₀) =>
    (g3Fst0_noise hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀ ht).symm
  refine ⟨𝓖₂, B₂, h₂.evol.1, hB₂, hE, fun s g hg => ?_, Eventually.of_forall fun y₀ t ht =>
    hNres y₀ t (by rw [← hcap y₀]; exact ht)⟩
  obtain ⟨r, hr, hcase⟩ := hg
  set E := {y₀ | s < g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y₀)} with hEdef
  have hrE : ∀ y₀ ∈ E, r ≤ g3S₂ x y W₂ ζ₂ m y₀ := fun y₀ hy => by
    have h : s < g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y₀) := hy
    rw [hcap y₀] at h
    exact hr.trans h.le
  have hle : 𝓖₂ r ≤ 𝓖₂ s := 𝓖₂.mono hr
  have key : ∀ (f g' : Y → ℝ), (∀ y₀ ∈ E, f y₀ = g' y₀) → Measurable[𝓖₂ r] g' → ∀ U : Set ℝ, MeasurableSet U →
      MeasurableSet[𝓖₂ s] (f ⁻¹' U ∩ E) := fun f g' hfg hg' U hU =>
    measurableSet_preimage_inter_of_eqOn (𝓜 := {A | MeasurableSet[𝓖₂ s] A}) hfg ((hle _ (hg' hU)).inter (hE s))
  rcases hcase with ⟨U, hU, hA | ⟨i, hA⟩ | ⟨j, hA⟩ | hA⟩ | ⟨k, hA⟩ | hA
  · rw [hA]
    exact key _ (W₂ r) (fun y₀ hy => (hid y₀).1 r (hlt y₀ r (hrE y₀ hy)))
      (h₂.progW.stronglyAdapted r).measurable U hU
  · rw [hA]
    exact key _ (VL₂ (g3Fst0Idx i) r) (fun y₀ hy => (hid y₀).2.2.1 i r (hlt y₀ r (hrE y₀ hy)))
      ((h₂.progVL (g3Fst0Idx i)).stronglyAdapted r).measurable U hU
  · exact j.elim0
  · rw [hA]
    exact key _ (B₂ r) (fun y₀ hy => (hNres y₀ r (hrE y₀ hy)).symm) (h₂.evol.1.2.1 r) U hU
  · rw [hA]
    have e2 : {y₀ | g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) ≤ r} =
        {y₀ | g3S₂ x y W₂ ζ₂ k y₀ ≤ r} := by
      ext y₀
      simp only [Set.mem_ofPred_eq, (hid y₀).2.2.2 k]
    rw [e2]
    have h := (hS₂ k).measurableSet_le r
    simp only [WithTop.coe_le_coe] at h
    exact (hle _ h).inter (hE s)
  · rw [hA]
    have e3 : {y₀ | (r : ℝ≥0∞) < rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => 0) (x₀, y₀)} ∩ E = E := by
      ext y₀
      refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
      show (r : ℝ≥0∞) < rLifeFst _ _ _ _ _ _ _ _
      rw [(hid y₀).2.1]
      exact hlt y₀ r (hrE y₀ hy)
    rw [e3]
    exact hE s

end InteractingSLE.ZhanGT4.A1G3Lg
