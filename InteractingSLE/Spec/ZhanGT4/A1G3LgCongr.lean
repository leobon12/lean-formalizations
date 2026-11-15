/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2Congr
import InteractingSLE.Spec.ZhanGT4.A1G3LawFstFam

/-!
# G3 large direction: dependence on each sample's data

Pointwise equality on the patches' good sets identifies the canonical families.
The rectangle exits and densities continue to use the patched data.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open A1Ref A1Core A1Forces A1G3Law A1G3L2 A1MultiMark A2X

variable {X Y : Type*}

/-- The large-direction family only reads the two curves at the chosen sample pair. -/
theorem g3Fst_data_congr {x y : ℝ}
    {W₁ W₁' : ℝ≥0 → X → ℝ} {VL₁ VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ VR₁' : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁ ζ₁' : X → ℝ≥0∞}
    {W₂ W₂' : ℝ≥0 → Y → ℝ} {VL₂ VL₂' : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂ ζ₂' : Y → ℝ≥0∞}
    {W₁g : ℝ≥0 → X → ℝ} {ζ₁g : X → ℝ≥0∞} {W₂g : ℝ≥0 → Y → ℝ} {ζ₂g : Y → ℝ≥0∞}
    {x₀ : X} {y₀ : Y}
    (hW₁ : ∀ t, W₁ t x₀ = W₁' t x₀) (hL₁ : ∀ i t, VL₁ i t x₀ = VL₁' i t x₀)
    (hR₁ : ∀ i t, VR₁ i t x₀ = VR₁' i t x₀) (hζ₁ : ζ₁ x₀ = ζ₁' x₀)
    (hW₂ : ∀ t, W₂ t y₀ = W₂' t y₀) (hL₂ : ∀ i t, VL₂ i t y₀ = VL₂' i t y₀)
    (hζ₂ : ζ₂ y₀ = ζ₂' y₀) (σ : ℝ≥0) :
    (∀ t, rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) t (x₀, y₀) =
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁' ω) 0 W₂'
        (fun ω => lifeEnd (W₂' · ω) (VL₂' 0 · ω) (ζ₂' ω)) y W₁' (fun _ => σ) t (x₀, y₀)) ∧
      rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (fun _ => σ) (x₀, y₀) =
      rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁' ω) 0 W₂'
        (fun ω => lifeEnd (W₂' · ω) (VL₂' 0 · ω) (ζ₂' ω)) y W₁' (fun _ => σ) (x₀, y₀) ∧
      (∀ i t, g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y₀) =
        g3FstVL y W₁' VL₁' VR₁' ζ₁' W₂' VL₂' ζ₂' σ i t (x₀, y₀)) ∧
      ∀ k, g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁g ζ₁g W₂g ζ₂g σ k (x₀, y₀) =
        g3FstCap x y W₁' ζ₁' W₂' VL₂' ζ₂' W₁g ζ₁g W₂g ζ₂g σ k (x₀, y₀) := by
  have eW₁ : (W₁ · x₀) = (W₁' · x₀) := funext hW₁
  have eW₂ : (W₂ · y₀) = (W₂' · y₀) := funext hW₂
  have eL₂ : (VL₂ 0 · y₀) = (VL₂' 0 · y₀) := funext (hL₂ 0)
  have eζ : lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) =
      lifeEnd (W₂' · y₀) (VL₂' 0 · y₀) (ζ₂' y₀) := by rw [eW₂, eL₂, hζ₂]
  have hword : g3FstWord W₁ VL₁ VR₁ σ x₀ = g3FstWord W₁' VL₁' VR₁' σ x₀ := by
    simp only [g3FstWord, hW₁ σ, hL₁ 0 σ, hR₁ 0 σ, hR₁ 1 σ, hR₁ 2 σ]
  refine ⟨fun t => ?_, ?_, fun i t => ?_, fun k => ?_⟩
  · simp only [rDrvFst, cImgDrvM, cImgDrv, cImgSrc, eW₂, eW₁, eL₂, hζ₂, hζ₁]
    split_ifs <;> rfl
  · simp only [rLifeFst, cImgLifeM, cImgLife, eW₂, eW₁, eL₂, hζ₂, hζ₁]
    split_ifs <;> rfl
  · by_cases ht : t = 0
    · subst ht
      rw [g3FstVL_zero, g3FstVL_zero, hword]
    · simp only [g3FstVL, ite_eq_right ht]
      exact canonForce_congr_pt
        (L := {z : X × Y | (σ : ℝ≥0∞) < ζ₁ z.1})
        (L' := {z : X × Y | (σ : ℝ≥0∞) < ζ₁' z.1}) (xj := 0) (xk := y)
        (wj := fun z t => W₂ t z.2) (wj' := fun z t => W₂' t z.2)
        (ζj := fun z => lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2))
        (ζj' := fun z => lifeEnd (W₂' · z.2) (VL₂' 0 · z.2) (ζ₂' z.2))
        (wk := fun z t => W₁ t z.1) (wk' := fun z t => W₁' t z.1)
        (τ := fun _ => σ) (τ' := fun _ => σ)
        (p := fun z => largeG3Marks (y - 0) (W₁ · z.1) (fun i t => VL₁ i t z.1)
          (fun j t => VR₁ j t z.1) σ i)
        (p' := fun z => largeG3Marks (y - 0) (W₁' · z.1) (fun i t => VL₁' i t z.1)
          (fun j t => VR₁' j t z.1) σ i) (ω := (x₀, y₀))
        (by simp only [mem_ofPred_eq, hζ₁]) eW₂ eζ eW₁ rfl
        (by simp only [largeG3Marks, hW₁ σ, hL₁ 0 σ, hR₁ 0 σ, hR₁ 1 σ]) t
  · simp only [g3FstCap, capFst, Set.indicator, mem_ofPred_eq, eW₂, eW₁, eL₂, hζ₂, hζ₁]

end InteractingSLE.ZhanGT4.A1G3Lg
