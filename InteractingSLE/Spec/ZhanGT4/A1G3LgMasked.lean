/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgSample
import InteractingSLE.Spec.ZhanGT4.A1G3LgCongr
import InteractingSLE.Spec.ZhanGT4.A1G3L2Shared
/-!
# G3 large direction: positive-time inputs for original processes

Pointwise agreement on measurable conull good sets transfers the regular
sample law to masked caps and transfers the stopped image geometry.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap drive IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR A1G3Id Girsanov A1G3Row A1LargeDens A1MultiMark A1Family
  A1Forces A1Core A1Canon A1RLaw A1G3L2

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

variable {W₁o : ℝ≥0 → X → ℝ} {VL₁o : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁o : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞}
  {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}
  (hag₁ : ∀ x₀ ∈ G₁, (∀ t, W₁o t x₀ = W₁ t x₀) ∧
    (∀ i t, VL₁o i t x₀ = VL₁ i t x₀) ∧ (∀ j t, VR₁o j t x₀ = VR₁ j t x₀) ∧ ζ₁o x₀ = ζ₁ x₀)
  (hag₂ : ∀ y₀ ∈ G₂, (∀ t, W₂o t y₀ = W₂ t y₀) ∧
    (∀ i t, VL₂o i t y₀ = VL₂ i t y₀) ∧ ζ₂o y₀ = ζ₂ y₀)

include hag₁ hag₂

/-- The large-direction law for the original canonical processes, with masked caps, at every positive frozen time. -/
theorem g3Fst_hlaw_pos (hG₂ : MeasurableSet G₂) (hG₂0 : P₂ G₂ᶜ = 0)
    (k : ℕ) {x₀ : X} (hx₀ : x₀ ∈ G₁) {σ : ℝ≥0} (hσ : 0 < σ) :
    IsSeedSampleLaw (P₂.withDensity fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀))
      (fun t y₀ => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁o ω) 0 W₂o
        (fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) y W₁o (fun _ => σ) t (x₀, y₀))
      (fun y₀ => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁o ω) 0 W₂o
        (fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) y W₁o (fun _ => σ) (x₀, y₀))
      (fun i t y₀ => g3FstVL y W₁o VL₁o VR₁o ζ₁o W₂o VL₂o ζ₂o σ i t (x₀, y₀))
      (fun j _ _ => (j.elim0 : ℝ))
      (fun t y₀ => seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁o ω) 0 W₂o
          (fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) y W₁o (fun _ => σ) t (x₀, y₀))
        (fun i t => g3FstVL y W₁o VL₁o VR₁o ζ₁o W₂o VL₂o ζ₂o σ i t (x₀, y₀))
        (fun j _ => (j.elim0 : ℝ)) t)
      (fun k' y₀ => maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)
        σ k' (x₀, y₀)) k := by
  have hE0 : (P₂.withDensity fun y₀ => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀)) G₂ᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ hG₂0
  obtain ⟨hW₁, hL₁, hR₁, hζ₁⟩ := hag₁ x₀ hx₀
  have hcg := fun y₀ (hy : y₀ ∉ G₂ᶜ) =>
    g3Fst_data_congr (x := x) (y := y) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
      hW₁ hL₁ hR₁ hζ₁ (hag₂ y₀ (not_not.1 hy)).1
      (hag₂ y₀ (not_not.1 hy)).2.1 (hag₂ y₀ (not_not.1 hy)).2.2 σ
  have hbase := g3Fst_isSeedSampleLaw_pos hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ
  refine IsSeedSampleLaw.congr_off hbase hG₂.compl hE0
    (fun y₀ hy => maskCap_of_not_mem (z := (x₀, y₀)) fun h => hy h.2)
    (fun y₀ hy t => (hcg y₀ hy).1 t) (fun y₀ hy => (hcg y₀ hy).2.1)
    (fun y₀ hy i t => (hcg y₀ hy).2.2.1 i t) (fun _ _ j => j.elim0)
    (fun y₀ hy t => ?_) (fun y₀ hy k' => ?_)
  · have eW := funext ((hcg y₀ hy).1)
    have eL := funext fun i => funext ((hcg y₀ hy).2.2.1 i)
    rw [eW, eL]
  · exact (maskCap_of_mem (z := (x₀, y₀)) hx₀ (not_not.1 hy)).trans ((hcg y₀ hy).2.2.2 k')

omit [StandardBorelSpace X] [StandardBorelSpace Y] [IsProbabilityMeasure P₁] in
/-- The original canonical family has the required geometry at every positive frozen time and positive raw cap. -/
theorem g3Fst_hgeo_pos {σ : ℝ≥0} (hσ : 0 < σ) (k : ℕ) {z : X × Y}
    (hz₁ : z.1 ∈ G₁) (hz₂ : z.2 ∈ G₂)
    (hpos : 0 < g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z) :
    SeedImageGeometry (g3FstWord W₁o VL₁o VR₁o σ z.1) ![] (largeG3ImgRhoL κ) ![]
      (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁o ω) 0 W₂o
        (fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) y W₁o (fun _ => σ)
        (min t (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z)) z)
      (fun i t => g3FstVL y W₁o VL₁o VR₁o ζ₁o W₂o VL₂o ζ₂o σ i
        (min t (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z)) z)
      (fun j _ => (j.elim0 : ℝ)) (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k z) := by
  rcases z with ⟨x₀, y₀⟩
  obtain ⟨hW₁, hL₁, hR₁, hζ₁⟩ := hag₁ x₀ hz₁
  obtain ⟨hW₂, hL₂, hζ₂⟩ := hag₂ y₀ hz₂
  have hcg := g3Fst_data_congr (x := x) (y := y) (W₁g := W₁) (ζ₁g := ζ₁)
    (W₂g := W₂) (ζ₂g := ζ₂) hW₁ hL₁ hR₁ hζ₁ hW₂ hL₂ hζ₂ σ
  rw [hcg.2.2.2 k] at hpos ⊢
  have hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀ := by
    by_contra h
    have h0 : g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) = 0 := by
      unfold g3FstCap
      apply capFst_of_nonpos
      simp only [g3FstOwn, h, ↓reduceIte, le_refl]
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  have hword : g3FstWord W₁o VL₁o VR₁o σ x₀ = g3FstWord W₁ VL₁ VR₁ σ x₀ := by
    simp only [g3FstWord, hW₁ σ, hL₁ 0 σ, hR₁ 0 σ, hR₁ 1 σ, hR₁ 2 σ]
  simp only [hword, hcg.1, hcg.2.2.1]
  obtain ⟨a, W', hown⟩ := exists_ownData_g3Fst hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  exact g3Fst_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hσ hσS hown y₀

end InteractingSLE.ZhanGT4.A1G3Lg

