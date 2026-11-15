/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgMasked

/-!
# G3 large direction: assembly with masked sample laws

The positive-time inputs are `g3Fst_hlaw_pos` and `g3Fst_hgeo_pos`.
The frozen time zero and stopped-record inputs remain separate.
This uses the masked-cap assembly of A1-G3LAW2 so that original processes need
only agree with their regular patches on their measurable conull good sets.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm
  A1EightSeed A1RLaw A1Law A1Patch A1SeedField A1G3Calc A1Common A1EightFin A1G3Law A1G3L2

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- G3's large-direction family law from the geometric, masked-sample, density, and stopped-record inputs. -/
theorem hasFamilyLawFstC_g3_of_inputsC {κ x y : ℝ} (hκ : 0 < κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁' : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (g3FstWord W₁ VL₁ VR₁ σ z.1) ![] (largeG3ImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
          W₁ (fun _ => σ) (min t (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i
          (min t (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j _ => (j.elim0 : ℝ)) (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ x' ∂P₁, x' ∈ G₁ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₂.withDensity fun y' => g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x', y'))
        (fun t y' => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
          W₁ (fun _ => σ) t (x', y'))
        (fun y' => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
          W₁ (fun _ => σ) (x', y'))
        (fun i t y' => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y')) (fun j _ _ => (j.elim0 : ℝ))
        (fun t y' => seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
          (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω))
            y W₁ (fun _ => σ) s (x', y'))
          (fun i s => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y')) (fun j _ => (j.elim0 : ℝ)) t)
        (fun k' y' => maskCap G₁ G₂ (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') σ k' (x', y')) k)
    (hstop : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂)
        (fun _ j _ _ => (j.elim0 : ℝ)) (maskCap G₁ G₂ (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
      (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
      (fun _ _ => ![]) (largeG3ImgRhoL κ) ![] := by
  obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := A1G3Law.g3Fst_facts h₁ h₂
  have hm3 := (measurable_rDrvFst_rLifeFst (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) hlive (fun _ _ h => h) hjc hj0
    hkc hk0 hjm hkm hζj hζk 0 y).1
  exact hasFamilyLawFstC_of_maskedLaw hκ (g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂) (fun _ j _ _ => (j.elim0 : ℝ))
    (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hG₁ hG₂ hG₁0
    hm3 (fun i t => measurable_g3FstVL h₁ h₂ i t) (fun j => j.elim0)
    (fun k => measurable_g3FstCap h₁ h₂ hS₁ hS₂ k) hD hgeo
    (fun σ x' hσ => isSeedWord_g3FstWord hx h₁.path σ x' hσ)
    (fun σ z _ i => g3FstVL_zero y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i z) (fun _ _ _ j => j.elim0) hlaw hstop

end InteractingSLE.ZhanGT4.A1G3Lg
