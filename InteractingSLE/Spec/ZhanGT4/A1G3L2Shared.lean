/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawMasked

/-!
# Zhan's A.1 under R83: one-sample laws with masked caps

Packet PROVE-A1-G3LAW2. A1-RECTLAW2's masked assemblies (`hasFamilyLawC_of_masked`, `…Fst…`) ask for the one-sample
laws with the **raw** caps at every image sample, including the null set of image samples where the original marginal
differs from its patch. There the original image data need not be regular, and the law asks for the measurability of
cap events cut by their generators, which is not available. The family only uses the **masked** caps (`maskCap`,
zero off the good sets), and A1-RECTLAW2's proof only uses the raw-cap laws to derive the masked-cap ones
(`IsSeedSampleLaw.mask`). This file:

* **`IsSeedSampleLaw.congr_off`**: a one-sample law transfers to data that agree off a measurable null set `E`
  provided the new cap `m` vanishes on `E` — no measurability of the new data is needed (every cap event misses `E`);
* **`hasFamilyLawC_of_maskedLaw`**, **`hasFamilyLawFstC_of_maskedLaw`**: the masked assemblies with the one-sample
  laws stated for the masked caps.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open A1Frozen A1Family A1Core A1RLaw A1SeedGeom

section CongrOff

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

/-- **A one-sample law transfers to data agreeing off a measurable null set on which the new cap vanishes.** No
measurability of the new data is needed: every new cap event misses `E`, and off `E` the new generators are the old
ones. -/
theorem IsSeedSampleLaw.congr_off {Q : Measure Ω} {W W' : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {N N' : ℝ≥0 → Ω → ℝ}
    {Scap Scap' : ℕ → Ω → ℝ≥0} {m : ℕ} (h : IsSeedSampleLaw Q W ζ VL VR N Scap m) {E : Set Ω}
    (hE : MeasurableSet E) (hE0 : Q E = 0) (hS0 : ∀ ω ∈ E, Scap' m ω = 0)
    (hW : ∀ ω ∉ E, ∀ t, W' t ω = W t ω) (hζ : ∀ ω ∉ E, ζ' ω = ζ ω)
    (hVL : ∀ ω ∉ E, ∀ i t, VL' i t ω = VL i t ω) (hVR : ∀ ω ∉ E, ∀ j t, VR' j t ω = VR j t ω)
    (hN : ∀ ω ∉ E, ∀ t, N' t ω = N t ω) (hS : ∀ ω ∉ E, ∀ k, Scap' k ω = Scap k ω) :
    IsSeedSampleLaw Q W' ζ' VL' VR' N' Scap' m := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  set 𝓗' := usualAugmentation 𝓗 Q with h𝓗'
  have hle : ∀ t, 𝓗 t ≤ 𝓗' t := fun t => Ito.le_usualAugmentation 𝓗 Q t
  have hEm : ∀ t, MeasurableSet[𝓗' t] E := fun t => Ito.measurableSet_usualAugmentation_of_null hE hE0 t
  have hcapE : ∀ s : ℝ≥0, {ω | s < Scap' m ω} = {ω | s < Scap m ω} \ E := fun s => by
    ext ω
    by_cases hω : ω ∈ E
    · simp only [mem_ofPred_eq, Set.mem_sdiff, hω, not_true_eq_false, and_false, hS0 ω hω, not_lt_zero]
    · simp only [mem_ofPred_eq, Set.mem_sdiff, hω, not_false_eq_true, and_true, hS ω hω m]
  have hC' : ∀ s : ℝ≥0, MeasurableSet[𝓗' s] {ω | s < Scap' m ω} := fun s => by
    rw [hcapE s]
    exact (hle s _ (hC s)).diff (hEm s)
  refine ⟨𝓗', B, Ito.isFilteredBrownianReal_usualAugmentation hB, hBc, hC', fun s => ?_, ?_⟩
  · have key : ∀ (g g' : Set Ω), (∀ ω ∉ E, ω ∈ g' ↔ ω ∈ g) → g ∈ imageGen W ζ VL VR N Scap s →
        MeasurableSet[𝓗' s] (g' ∩ {ω | s < Scap' m ω}) := fun g g' hgg hg => by
      have e : g' ∩ {ω | s < Scap' m ω} = (g ∩ {ω | s < Scap m ω}) \ E := by
        rw [hcapE s]
        ext ω
        by_cases hω : ω ∈ E
        · simp only [mem_inter_iff, Set.mem_sdiff, hω, not_true_eq_false, and_false]
        · simp only [mem_inter_iff, Set.mem_sdiff, hω, not_false_eq_true, and_true, hgg ω hω]
      rw [e]
      exact (hle s _ (hG s g hg)).diff (hEm s)
    refine forall_imageGen (p := fun g => MeasurableSet[𝓗' s] (g ∩ {ω | s < Scap' m ω}))
      (fun r hr U hU => key (W r ⁻¹' U) _ (fun ω hω => by simp only [mem_preimage, hW ω hω r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩)
      (fun r hr U hU i => key (VL i r ⁻¹' U) _ (fun ω hω => by simp only [mem_preimage, hVL ω hω i r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
      (fun r hr U hU j => key (VR j r ⁻¹' U) _ (fun ω hω => by simp only [mem_preimage, hVR ω hω j r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩)
      (fun r hr U hU => key (N r ⁻¹' U) _ (fun ω hω => by simp only [mem_preimage, hN ω hω r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩)
      (fun r hr k => key {ω | Scap k ω ≤ r} _ (fun ω hω => by simp only [mem_ofPred_eq, hS ω hω k])
        ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩)
      (fun r hr => key {ω | (r : ℝ≥0∞) < ζ ω} _ (fun ω hω => by simp only [mem_ofPred_eq, hζ ω hω])
        ⟨r, hr, Or.inr (Or.inr rfl)⟩)
  · have hE' : ∀ᵐ ω ∂Q, ω ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
    filter_upwards [heq, hE'] with ω hω hωE t ht
    rw [hS ω hωE m] at ht
    rw [hω t ht, hN ω hωE t]

end CongrOff

/-! ### The masked assemblies with masked-cap laws -/

section Masked

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-- **The C family input from masked-cap laws** (conditioning curve on `Y`): `hasFamilyLawC_of_masked` with the
one-sample laws stated for the masked caps. -/
theorem hasFamilyLawC_of_maskedLaw {a : ℝ} (ha : 0 < a) {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁]
    [SFinite P₂] {μ : Measure (X × Y)} [IsFiniteMeasure μ] {𝓕k : Filtration ℝ≥0 mY} {live : ℝ≥0 → Y → Prop}
    {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {ΘL : ℝ≥0 → Y → Fin nL → ℝ}
    {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞) {G₁ : Set X} {G₂ : Set Y}
    (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₂0 : P₂ G₂ᶜ = 0)
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
      (fun k x => maskCap G₁ G₂ S₀ σ k (x, y)) m)
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
    exact hy hyG σ

/-- **The C family input from masked-cap laws** (conditioning curve on `X`, mirror). -/
theorem hasFamilyLawFstC_of_maskedLaw {a : ℝ} (ha : 0 < a) {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁]
    [SFinite P₂] {μ : Measure (X × Y)} [IsFiniteMeasure μ] {𝓕k : Filtration ℝ≥0 mX} {live : ℝ≥0 → X → Prop}
    {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {ΘL : ℝ≥0 → X → Fin nL → ℝ}
    {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (S₀ : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞) {G₁ : Set X} {G₂ : Set Y}
    (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
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
      (fun k y => maskCap G₁ G₂ S₀ σ k (x, y)) m)
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
    exact hx hxG σ

end Masked

end InteractingSLE.ZhanGT4.A1G3L2
