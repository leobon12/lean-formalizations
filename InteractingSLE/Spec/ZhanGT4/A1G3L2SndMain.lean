/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndHLaw

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the family law from the frozen time `0` and the record facts

Packet PROVE-A1-G3LAW2. **`hasFamilyLawC_g3_of_zero_stop`**: `G3RectLawSndC`'s conclusion (verbatim, the original
marginals) for regular marginals with patches (the data of `IsPatchOf`: patched regular marginals in the usual
augmentations with continuous Brownian paths, good small samples, agreement on the good sets `G₁`, `G₂`), from three
named inputs only:

* `hgeo0`, `hlaw0`: the geometry and the one-sample laws at the frozen time `σ = 0` (the frozen large curve is
  trivial: the record at height `0` is not a source column, so the column machinery does not apply);
* `hstop`: the per-stop record facts (`ResStopInput`) for the corrected forces and the masked caps.

Everything else is proved: `hD` (PROVE-A1-G3LAW's `measurable_g3SndD`), the geometry and the laws at every positive
frozen time (`g3Snd_hgeo_pos`, `g3Snd_hlaw_pos`), through `hasFamilyLawC_g3_of_inputsC`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

/-- **`G3RectLawSndC`'s conclusion from the `σ = 0` inputs and the record facts.** -/
theorem hasFamilyLawC_g3_of_zero_stop {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
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
    (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁ t x' = W₁' t x') ∧ ζ₁ x' = ζ₁' x')
    (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂ t y' = W₂' t y') ∧ (∀ i t, VL₂ i t y' = VL₂' i t y') ∧ ζ₂ y' = ζ₂' y')
    (hgeo0 : ∀ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' 0 k z →
      SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ 0 z.2) (smallG3RhoL κ) (smallG3RhoR κ)
        (fun t => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁'
            W₂' ζ₂' 0 k z)) z)
        (fun i t => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' 0 k z)) z)
        (fun j t => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' 0 k z)) z)
            (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' 0 k z))
    (hlaw0 : ∀ k, ∀ᵐ y' ∂P₂, y' ∈ G₂ →
      IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' 0 k (x', y'))
        (fun t x' => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) t (x', y'))
        (fun x' => rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) (x', y'))
        (fun i t x' => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x', y'))
        (fun j t x' => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j t (x', y'))
        (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
          (fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) s (x', y'))
          (fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x', y'))
          (fun j s => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x', y')) t)
        (fun k' x' => maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') 0 k' (x', y')) k)
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂)
        (g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂) (maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
      W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
      (smallG3RhoR κ) := by
  have hR := fun k => g3_isRectField hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' k
  have hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k) := fun k => measurable_of_isStoppingTime (hR k).stop₁
  have hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k) := fun k => measurable_of_isStoppingTime (hR k).stop₂
  refine hasFamilyLawC_g3_of_inputsC hκ4 hκ8 hyx h₂ h₁ hS₁ hS₂ hG₁ hG₂ hG₂0
    (fun k => measurable_g3SndD hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' k) (fun σ k z hz1 hz2 hpos => ?_)
    (fun k => ?_) hstop
  · rcases eq_zero_or_pos σ with h0 | hσ
    · subst h0
      exact hgeo0 k z hz1 hz2 hpos
    · exact g3Snd_hgeo_pos hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ hσ k hz1 hz2 hpos
  · filter_upwards [hlaw0 k] with y' h0 hy' σ
    rcases eq_zero_or_pos σ with hσ0 | hσ
    · subst hσ0
      exact h0 hy'
    · exact g3Snd_hlaw_pos hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hag₁ hag₂ hG₁ hG₁0 k hy' hσ

end InteractingSLE.ZhanGT4.A1G3L2
