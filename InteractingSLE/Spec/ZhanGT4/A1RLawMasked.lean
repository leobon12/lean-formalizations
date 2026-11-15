/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawAssemble
import InteractingSLE.Spec.ZhanGT4.A1RLawShared

/-!
# Zhan's A.1 under R83: the family law with caps masked off the good samples

Packet PROVE-A1-RECTLAW2 (R83), shared by the four directional laws. The C family laws are stated for the original
regular marginals, while the rectangle densities live on patched versions that agree with them off measurable null
sets `G₁ᶜ ⊆ X`, `G₂ᶜ ⊆ Y` (`A1Asm.IsPatchOf`). Masking raw caps `S₀` by `G₁ ×ˢ G₂` (`maskCap`) confines every
positive cap to samples where the two agree:

* **`hasFamilyLawC_of_masked`** / **`hasFamilyLawFstC_of_masked`**: `hasFamily*C_of_residual` for the masked caps,
  with the geometry asked only at good samples with a positive raw cap, the zero-cap geometry reduced to the
  admissibility of the initial word and the initial values of the forces (`seedImageGeometry_zero_of_isSeedWord`), and
  the one-sample laws asked only at good conditioning samples, with the **raw** caps (`IsSeedSampleLaw.mask` removes
  the bad image samples).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-- **The caps masked off the good samples**: `S₀` on `G₁ ×ˢ G₂`, `0` elsewhere. -/
def maskCap (G₁ : Set X) (G₂ : Set Y) (S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0) (σ : ℝ≥0) (k : ℕ) : X × Y → ℝ≥0 :=
  (G₁ ×ˢ G₂).indicator (S₀ σ k)

omit mX mY in
theorem maskCap_of_mem {G₁ : Set X} {G₂ : Set Y} {S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0} {σ : ℝ≥0} {k : ℕ} {z : X × Y}
    (h₁ : z.1 ∈ G₁) (h₂ : z.2 ∈ G₂) : maskCap G₁ G₂ S₀ σ k z = S₀ σ k z :=
  indicator_of_mem (mk_mem_prod h₁ h₂) _

omit mX mY in
theorem maskCap_of_not_mem {G₁ : Set X} {G₂ : Set Y} {S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0} {σ : ℝ≥0} {k : ℕ}
    {z : X × Y} (h : ¬ (z.1 ∈ G₁ ∧ z.2 ∈ G₂)) : maskCap G₁ G₂ S₀ σ k z = 0 :=
  indicator_of_notMem (fun hz => h (mem_prod.1 hz)) _

theorem measurable_maskCap {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂)
    {S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0} {k : ℕ} (hS₀ : Measurable fun p : ℝ≥0 × (X × Y) => S₀ p.1 k p.2) :
    Measurable fun p : ℝ≥0 × (X × Y) => maskCap G₁ G₂ S₀ p.1 k p.2 := by
  have e : (fun p : ℝ≥0 × (X × Y) => maskCap G₁ G₂ S₀ p.1 k p.2) =
      (Prod.snd ⁻¹' (G₁ ×ˢ G₂)).indicator fun p : ℝ≥0 × (X × Y) => S₀ p.1 k p.2 := by
    funext p
    by_cases hp : p.2 ∈ G₁ ×ˢ G₂
    · rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' (G₁ ×ˢ G₂) from hp)]
      exact indicator_of_mem hp _
    · rw [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' (G₁ ×ˢ G₂) from hp)]
      exact indicator_of_notMem hp _
  rw [e]
  exact hS₀.indicator (measurable_snd (hG₁.prod hG₂))

omit mX mY in
/-- The geometry asked by `hgeo` at a masked cap: positive raw caps at good samples, the initial word otherwise. -/
theorem geometry_maskCap {G₁ : Set X} {G₂ : Set Y} {S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {σ : ℝ≥0} {m : ℕ} {z : X × Y}
    (hpos : z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < S₀ σ m z → SeedImageGeometry xL xR ρL ρR (fun t => w (min t (S₀ σ m z)))
      (fun i t => vL i (min t (S₀ σ m z))) (fun j t => vR j (min t (S₀ σ m z))) (S₀ σ m z))
    (hzero : SeedImageGeometry xL xR ρL ρR (fun t => w (min t 0)) (fun i t => vL i (min t 0))
      (fun j t => vR j (min t 0)) 0) :
    SeedImageGeometry xL xR ρL ρR (fun t => w (min t (maskCap G₁ G₂ S₀ σ m z)))
      (fun i t => vL i (min t (maskCap G₁ G₂ S₀ σ m z))) (fun j t => vR j (min t (maskCap G₁ G₂ S₀ σ m z)))
      (maskCap G₁ G₂ S₀ σ m z) := by
  by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
  · rw [maskCap_of_mem hG.1 hG.2]
    rcases eq_zero_or_pos (S₀ σ m z) with h0 | h0
    · rw [h0]; exact hzero
    · exact hpos hG.1 hG.2 h0
  · rw [maskCap_of_not_mem hG]
    exact hzero

/-! ### Conditioning curve on `Y` -/

/-- **The C family input with masked caps** (conditioning curve on `Y`). -/
theorem hasFamilyLawC_of_masked {a : ℝ} (ha : 0 < a) {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] {𝓕k : Filtration ℝ≥0 mY} {live : ℝ≥0 → Y → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {ΘL : ℝ≥0 → Y → Fin nL → ℝ}
    {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞) {G₁ : Set X} {G₂ : Set Y}
    (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hS₀ : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S₀ p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hgeo : ∀ σ m z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < S₀ σ m z → SeedImageGeometry (ΘL σ z.2) (ΘR σ z.2) ρL ρR
      (fun t => rDrv live xj Wj ζj xk Wk (fun _ => σ) (min t (S₀ σ m z)) z)
      (fun i t => VL σ i (min t (S₀ σ m z)) z) (fun j t => VR σ j (min t (S₀ σ m z)) z) (S₀ σ m z))
    (hword : ∀ σ y, live σ y → IsSeedWord (ΘL σ y) (ΘR σ y) ρL ρR)
    (hVL0 : ∀ σ z, live σ z.2 → ∀ i, VL σ i 0 z = ΘL σ z.2 i)
    (hVR0 : ∀ σ z, live σ z.2 → ∀ j, VR σ j 0 z = ΘR σ z.2 j)
    (hlaw : ∀ m, ∀ᵐ y ∂P₂, y ∈ G₂ → ∀ σ : ℝ≥0, IsSeedSampleLaw (P₁.withDensity fun x => D σ m (x, y))
      (fun t x => rDrv live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun x => rLife live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t x => VL σ i t (x, y))
      (fun j t x => VR σ j t (x, y))
      (fun t x => seedCapacityNoise a ρL ρR (fun s => rDrv live xj Wj ζj xk Wk (fun _ => σ) s (x, y))
        (fun i s => VL σ i s (x, y)) (fun j s => VR σ j s (x, y)) t)
      (fun k x => S₀ σ k (x, y)) m)
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ live xj Wj ζj xk Wk VL VR (maskCap G₁ G₂ S₀) D τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  refine hasFamilyLawC_of_residual ha VL VR (maskCap G₁ G₂ S₀) D hm3 hVL hVR
    (fun m => measurable_maskCap hG₁ hG₂ (hS₀ m)) hD (fun σ m z hz => ?_) (fun m => ?_) hstop
  · by_cases hl : live σ z.2
    · exact geometry_maskCap (w := fun t => rDrv live xj Wj ζj xk Wk (fun _ => σ) t z)
        (vL := fun i t => VL σ i t z) (vR := fun j t => VR σ j t z) (hgeo σ m z)
        (seedImageGeometry_zero_of_isSeedWord (hword σ z.2 hl)
        (w := fun t => rDrv live xj Wj ζj xk Wk (fun _ => σ) t z) (vL := fun i t => VL σ i t z)
        (vR := fun j t => VR σ j t z) (cImgDrvM_zero _ _ _ _ _ _ _ z) (hVL0 σ z hl) (hVR0 σ z hl))
    · have hpos : 0 < maskCap G₁ G₂ S₀ σ m z := hz.resolve_right hl
      by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
      · rw [maskCap_of_mem hG.1 hG.2] at hpos ⊢
        exact hgeo σ m z hG.1 hG.2 hpos
      · rw [maskCap_of_not_mem hG] at hpos
        exact absurd hpos (lt_irrefl 0)
  · have hG₂ae : ∀ᵐ y ∂P₂, y ∈ G₂ := by
      rw [ae_iff]; simpa only [compl_def] using hG₂0
    filter_upwards [hlaw m, hG₂ae] with y hy hyG σ
    refine IsSeedSampleLaw.mask (hy hyG σ) (E := G₁ᶜ) hG₁.compl ?_ (fun x hx k => ?_) (fun x hx => ?_)
    · exact withDensity_absolutelyContinuous _ _ hG₁0
    · exact maskCap_of_mem (z := (x, y)) (not_not.1 hx) hyG
    · exact maskCap_of_not_mem (z := (x, y)) fun h => hx h.1

/-! ### Conditioning curve on `X` -/

/-- **The C family input with masked caps** (conditioning curve on `X`, mirror of `hasFamilyLawC_of_masked`). -/
theorem hasFamilyLawFstC_of_masked {a : ℝ} (ha : 0 < a) {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁]
    [SFinite P₂] {μ : Measure (X × Y)} [IsFiniteMeasure μ] {𝓕k : Filtration ℝ≥0 mX} {live : ℝ≥0 → X → Prop}
    {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {ΘL : ℝ≥0 → X → Fin nL → ℝ}
    {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞) {G₁ : Set X} {G₂ : Set Y}
    (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hS₀ : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S₀ p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hgeo : ∀ σ m z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < S₀ σ m z → SeedImageGeometry (ΘL σ z.1) (ΘR σ z.1) ρL ρR
      (fun t => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) (min t (S₀ σ m z)) z)
      (fun i t => VL σ i (min t (S₀ σ m z)) z) (fun j t => VR σ j (min t (S₀ σ m z)) z) (S₀ σ m z))
    (hword : ∀ σ x, live σ x → IsSeedWord (ΘL σ x) (ΘR σ x) ρL ρR)
    (hVL0 : ∀ σ z, live σ z.1 → ∀ i, VL σ i 0 z = ΘL σ z.1 i)
    (hVR0 : ∀ σ z, live σ z.1 → ∀ j, VR σ j 0 z = ΘR σ z.1 j)
    (hlaw : ∀ m, ∀ᵐ x ∂P₁, x ∈ G₁ → ∀ σ : ℝ≥0, IsSeedSampleLaw (P₂.withDensity fun y => D σ m (x, y))
      (fun t y => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun y => rLifeFst live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t y => VL σ i t (x, y))
      (fun j t y => VR σ j t (x, y))
      (fun t y => seedCapacityNoise a ρL ρR (fun s => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) s (x, y))
        (fun i s => VL σ i s (x, y)) (fun j s => VR σ j s (x, y)) t)
      (fun k y => S₀ σ k (x, y)) m)
    (hstop : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ live xj Wj ζj xk Wk VL VR (maskCap G₁ G₂ S₀) D τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  refine hasFamilyLawFstC_of_residual ha VL VR (maskCap G₁ G₂ S₀) D hm3 hVL hVR
    (fun m => measurable_maskCap hG₁ hG₂ (hS₀ m)) hD (fun σ m z hz => ?_) (fun m => ?_) hstop
  · by_cases hl : live σ z.1
    · exact geometry_maskCap (w := fun t => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t z)
        (vL := fun i t => VL σ i t z) (vR := fun j t => VR σ j t z) (hgeo σ m z)
        (seedImageGeometry_zero_of_isSeedWord (hword σ z.1 hl)
        (w := fun t => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t z) (vL := fun i t => VL σ i t z)
        (vR := fun j t => VR σ j t z) (cImgDrvM_zero _ _ _ _ _ _ _ z) (hVL0 σ z hl) (hVR0 σ z hl))
    · have hpos : 0 < maskCap G₁ G₂ S₀ σ m z := hz.resolve_right hl
      by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
      · rw [maskCap_of_mem hG.1 hG.2] at hpos ⊢
        exact hgeo σ m z hG.1 hG.2 hpos
      · rw [maskCap_of_not_mem hG] at hpos
        exact absurd hpos (lt_irrefl 0)
  · have hG₁ae : ∀ᵐ x ∂P₁, x ∈ G₁ := by
      rw [ae_iff]; simpa only [compl_def] using hG₁0
    filter_upwards [hlaw m, hG₁ae] with x hx hxG σ
    refine IsSeedSampleLaw.mask (hx hxG σ) (E := G₂ᶜ) hG₂.compl ?_ (fun y hy k => ?_) (fun y hy => ?_)
    · exact withDensity_absolutelyContinuous _ _ hG₂0
    · exact maskCap_of_mem (z := (x, y)) hxG (not_not.1 hy)
    · exact maskCap_of_not_mem (z := (x, y)) fun h => hy h.2

end InteractingSLE.ZhanGT4.A1RLaw
