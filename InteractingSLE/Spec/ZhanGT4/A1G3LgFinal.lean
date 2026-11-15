/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgMain
import InteractingSLE.Spec.ZhanGT4.A1G3LgZeroMasked
import InteractingSLE.Spec.ZhanGT4.A1G3L2FstStopMain

/-!
# G3 large direction: the full rectangle law under R83

Time zero, positive frozen times and the landed stopped-record theorem supply
all inputs of the masked-cap family assembly.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1G3Lg
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed
  A1G3Calc A1Common A1EightFin A1Asm A1Family A1Forces A1RLaw A1G3Law A1G3L2

/-- The full large-direction family law for regular marginals and their supplied patches. -/
theorem hasFamilyLawFstC_g3_fstC {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
    {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)}
    [IsProbabilityMeasure μ] {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {VL₂' : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂' : Fin 0 → ℝ≥0 → Y → ℝ} {B₂' : ℝ≥0 → Y → ℝ}
    {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ} {VR₁' : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (h₂' : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂' VL₂' VR₂' B₂' ζ₂')
    (hB₂' : ∀ ω, Continuous (B₂' · ω))
    (h₁' : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
      W₁' VL₁' VR₁' B₁' ζ₁')
    (hB₁' : ∀ ω, Continuous (B₁' · ω))
    (hg₁' : ∀ ω, GoodSmallG3 (W₁' · ω) (fun i t => VL₁' i t ω) (fun i t => VR₁' i t ω) (B₁' · ω) (ζ₁' ω))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hG₂0 : P₂ G₂ᶜ = 0)
    (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁ t x' = W₁' t x') ∧ (∀ i t, VL₁ i t x' = VL₁' i t x') ∧
      (∀ j t, VR₁ j t x' = VR₁' j t x') ∧ ζ₁ x' = ζ₁' x')
    (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂ t y' = W₂' t y') ∧ (∀ i t, VL₂ i t y' = VL₂' i t y') ∧ ζ₂ y' = ζ₂' y')
    (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁' ζ₁' m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂' ζ₂' m ω : WithTop ℝ≥0))
    (hμ₁ : μ.map Prod.fst = P₁) (hμ₂ : μ.map Prod.snd = P₂)
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') m) ω
        (g3S₁ x y W₁' ζ₁' m ω.1) (g3S₂ x y W₂' ζ₂' m ω.2))) :
    HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
      (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω,
        W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
      (fun _ _ => ![]) (largeG3ImgRhoL κ) ![] := by
  have hR := fun k => g3_isRectField hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' k
  have hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k) :=
    fun k => measurable_of_isStoppingTime (hR k).stop₁
  have hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k) :=
    fun k => measurable_of_isStoppingTime (hR k).stop₂
  refine hasFamilyLawFstC_g3_of_inputsC (by linarith) hx h₂ h₁ hS₁ hS₂ hG₁ hG₂ hG₁0
    (fun k => measurable_g3FstD hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' k)
    (fun σ k z hz₁ hz₂ hpos => ?_) (fun k => ?_)
    (g3FstStop_of_good hκ4 hκ8 hyx hx h₂' hB₂' h₁' hB₁' hg₁'
      (fun k x₀ y₀ => g3Fst_lt_lifeEnd hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' k x₀ y₀)
      (fun k x₀ y₀ {σ} hσ hσS =>
        g3Fst_isGoodTime hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' k x₀ y₀ hσ hσS)
      hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ hs₁ hs₂ hμ₁ hμ₂ hd)
  · rcases eq_zero_or_pos σ with h0 | hσ
    · subst h0
      exact g3Fst_hgeo_zero hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ k hz₁ hz₂
    · exact g3Fst_hgeo_pos hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ hσ k hz₁ hz₂ hpos
  · refine Eventually.of_forall fun x₀ hx₀ σ => ?_
    rcases eq_zero_or_pos σ with h0 | hσ
    · subst h0
      exact g3Fst_hlaw_zero hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ hG₂ hG₂0 k hx₀
    · exact g3Fst_hlaw_pos hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ hG₂ hG₂0 k hx₀ hσ

/-- Zhan's G3 large-direction rectangle law under R83, for every parameter. -/
theorem g3RectLawFstC_holds (κ : ℝ) : G3RectLawFstC κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
    W₂' VL₂' VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd
  obtain ⟨G₂, hG₂, hG₂0, h₂', hB₂', -, hag₂⟩ := hp₂
  obtain ⟨G₁, hG₁, hG₁0, h₁', hB₁', hg₁', hag₁⟩ := hp₁
  exact hasFamilyLawFstC_g3_fstC hκ4 hκ8 hyx hx h₂ h₁ h₂' hB₂' h₁' hB₁' hg₁' hG₁ hG₂ hG₁0 hG₂0
    (fun x' hx' => ⟨fun t => ((hag₁ x' hx').1 t).symm, fun i t => ((hag₁ x' hx').2.1 i t).symm,
      fun j t => ((hag₁ x' hx').2.2.1 j t).symm, (hag₁ x' hx').2.2.2.2.symm⟩)
    (fun y' hy' => ⟨fun t => ((hag₂ y' hy').1 t).symm, fun i t => ((hag₂ y' hy').2.1 i t).symm,
      (hag₂ y' hy').2.2.2.2.symm⟩) hs₁ hs₂ hμ₁ hμ₂ hd

end InteractingSLE.ZhanGT4.A1G3Lg
