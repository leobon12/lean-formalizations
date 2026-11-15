/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EFamZero
import InteractingSLE.Spec.ZhanGT4.A1RLawStmt

/-!
# Zhan's A.1 under R83, (Eight), large-curve direction: the family law from the record facts

Packet PROVE-A1-EIGHTFAM.

* **`IsSeedSampleLaw.congr_offNull`**: a one-sample law transfers to data agreeing off a measurable null set on which
  the new cap vanishes (no measurability of the new data; the same statement as PROVE-A1-G3LAW2's in-flight
  `A1G3L2.IsSeedSampleLaw.congr_off`, not yet landed when this file was written);
* `eightFst_congr`: the canonical driver, lifetime, forces and raw caps read only the two sample paths;
* **`eightFst_law_all`**, **`eightFst_geom_all`**: the one-sample laws at every frozen time and the deterministic
  geometry at every positive raw cap, for the patched marginals;
* **`hasFamilyLawFstC_eight_of_maskedLaw`**: A1-RECTLAW2's `hasFamilyLawFstC_eight_of_inputs` with the one-sample
  laws stated for the masked caps (which vanish off the good sets of the patches);
* **`EightFstRecordStatement`** (the remaining input: the record facts `hSm`, `hstop`, `hgW`, `hgVL`, `hgS`, `hcov` of
  A1-RECTLAW2's `eightFstResStop`) and **`eightRectLawFstC_of_records : EightFstRecordStatement κ →
  EightRectLawFstC κ`**.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1EFam
open QuantumZipper (H fwdMap fwdHull drive IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm A1Forces A1MultiMark A1Family A1RLaw A1Frozen


section CongrOff

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

/-- **A one-sample law transfers to data agreeing off a measurable null set on which the new cap vanishes** (no
measurability of the new data: off `E` the new generators are the old ones, and every new cap event misses `E`). -/
theorem IsSeedSampleLaw.congr_offNull {Q : Measure Ω} {W W' : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
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
    · simp only [Set.mem_ofPred_eq, Set.mem_sdiff, hω, not_true_eq_false, and_false, hS0 ω hω, not_lt_zero]
    · simp only [Set.mem_ofPred_eq, Set.mem_sdiff, hω, not_false_eq_true, and_true, hS ω hω m]
  refine ⟨𝓗', B, Ito.isFilteredBrownianReal_usualAugmentation hB, hBc, fun s => ?_, fun s => ?_, ?_⟩
  · rw [hcapE s]
    exact (hle s _ (hC s)).diff (hEm s)
  · have key : ∀ (g g' : Set Ω), (∀ ω ∉ E, ω ∈ g' ↔ ω ∈ g) → g ∈ imageGen W ζ VL VR N Scap s →
        MeasurableSet[𝓗' s] (g' ∩ {ω | s < Scap' m ω}) := fun g g' hgg hg => by
      have e : g' ∩ {ω | s < Scap' m ω} = (g ∩ {ω | s < Scap m ω}) \ E := by
        rw [hcapE s]
        ext ω
        by_cases hω : ω ∈ E
        · simp only [Set.mem_inter_iff, Set.mem_sdiff, hω, not_true_eq_false, and_false]
        · simp only [Set.mem_inter_iff, Set.mem_sdiff, hω, not_false_eq_true, and_true, hgg ω hω]
      rw [e]
      exact (hle s _ (hG s g hg)).diff (hEm s)
    refine forall_imageGen (p := fun g => MeasurableSet[𝓗' s] (g ∩ {ω | s < Scap' m ω}))
      (fun r hr U hU => key (W r ⁻¹' U) _ (fun ω hω => by simp only [Set.mem_preimage, hW ω hω r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩)
      (fun r hr U hU i => key (VL i r ⁻¹' U) _ (fun ω hω => by simp only [Set.mem_preimage, hVL ω hω i r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
      (fun r hr U hU j => key (VR j r ⁻¹' U) _ (fun ω hω => by simp only [Set.mem_preimage, hVR ω hω j r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩)
      (fun r hr U hU => key (N r ⁻¹' U) _ (fun ω hω => by simp only [Set.mem_preimage, hN ω hω r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩)
      (fun r hr k => key {ω | Scap k ω ≤ r} _ (fun ω hω => by simp only [Set.mem_ofPred_eq, hS ω hω k])
        ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩)
      (fun r hr => key {ω | (r : ℝ≥0∞) < ζ ω} _ (fun ω hω => by simp only [Set.mem_ofPred_eq, hζ ω hω])
        ⟨r, hr, Or.inr (Or.inr rfl)⟩)
  · have hE' : ∀ᵐ ω ∂Q, ω ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
    filter_upwards [heq, hE'] with ω hω hωE t ht
    rw [hS ω hωE m] at ht
    rw [hω t ht, hN ω hωE t]

end CongrOff

section Congr

variable {X Y : Type*}

/-- **The large direction's canonical data read only the two sample paths**: original and patched marginals agreeing
at a sample `z` (drivers, marks, lifetimes) have the same canonical driver, lifetime, forces and raw caps there. -/
theorem eightFst_congr {x : ℝ} {W₁ W₁' : ℝ≥0 → X → ℝ} {VL₁ VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ VR₁' : Fin 2 → ℝ≥0 → X → ℝ} {ζ₁ ζ₁' : X → ℝ≥0∞} {W₂ W₂' : ℝ≥0 → Y → ℝ}
    {VL₂ VL₂' : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂ ζ₂' : Y → ℝ≥0∞} {z : X × Y}
    (hW₁ : ∀ t, W₁ t z.1 = W₁' t z.1) (hVL₁ : ∀ i t, VL₁ i t z.1 = VL₁' i t z.1)
    (hVR₁ : ∀ i t, VR₁ i t z.1 = VR₁' i t z.1) (hζ₁ : ζ₁ z.1 = ζ₁' z.1)
    (hW₂ : ∀ t, W₂ t z.2 = W₂' t z.2) (hVL₂ : ∀ i t, VL₂ i t z.2 = VL₂' i t z.2) (hζ₂ : ζ₂ z.2 = ζ₂' z.2) :
    (∀ σ t, rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) t z =
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁' ω) 0 W₂' (fun ω => lifeEnd (W₂' · ω) (VL₂' 0 · ω) (ζ₂' ω)) x W₁'
        (fun _ => σ) t z) ∧
    (∀ σ, rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) z =
      rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁' ω) 0 W₂' (fun ω => lifeEnd (W₂' · ω) (VL₂' 0 · ω) (ζ₂' ω)) x W₁'
        (fun _ => σ) z) ∧
    (∀ σ i t, eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t z = eightFstVL x W₁' VL₁' VR₁' ζ₁' W₂' VL₂' ζ₂' σ i t z) ∧
    ∀ (A : ℝ≥0 → X → ℝ) (B : X → ℝ≥0∞) (C : ℝ≥0 → Y → ℝ) (D : Y → ℝ≥0∞) σ k,
      eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ A B C D σ k z = eightFstCap x W₁' ζ₁' W₂' VL₂' ζ₂' A B C D σ k z := by
  obtain ⟨z₁, z₂⟩ := z
  dsimp only at hW₁ hVL₁ hVR₁ hζ₁ hW₂ hVL₂ hζ₂
  have e1 : (fun t => W₁ t z₁) = fun t => W₁' t z₁ := funext hW₁
  have e2 : (fun t => W₂ t z₂) = fun t => W₂' t z₂ := funext hW₂
  have e3 : (fun t => VL₂ 0 t z₂) = fun t => VL₂' 0 t z₂ := funext (hVL₂ 0)
  refine ⟨fun σ t => ?_, fun σ => ?_, fun σ i t => ?_, fun A B C D σ k => ?_⟩
  · simp only [rDrvFst, A1Ref.cImgDrvM, A1Ref.cImgDrv, A1Ref.cImgSrc]
    simp only [e1, e2, e3, hζ₁, hζ₂]
    split_ifs <;> rfl
  · simp only [rLifeFst, A1Ref.cImgLifeM, A1Ref.cImgLife]
    simp only [e1, e2, e3, hζ₁, hζ₂]
    split_ifs <;> rfl
  · simp only [eightFstVL, eightFstWord, rForceFst, canonForce, largeEightMarks, Set.mem_ofPred_eq]
    simp only [e2, e3, hζ₁, hζ₂, hW₁, hVL₁, hVR₁]
    split_ifs <;> rfl
  · simp only [eightFstCap, capFst, Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [e1, e2, e3, hζ₁, hζ₂]

end Congr

section Frame
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}


/-- **The one-sample laws of the large Eight direction at every frozen time** (patched data, raw caps, residual
noise): `σ = 0` (`eightFst_law_zero`), protected `σ` (`eightFst_law_prot`), unprotected `σ` (`eightFst_law_unprot`). -/
theorem eightFst_law_all [𝓖₂.IsRightContinuous] (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (σ : ℝ≥0) :
    IsSeedSampleLaw (P₂.withDensity fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ m (x₀, y))
      (fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) t (x₀, y))
      (fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) (x₀, y))
      (fun i t y => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
        (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
          W₁ (fun _ => σ) s (x₀, y))
        (fun i s => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x₀, y)) (fun j _ => (j.elim0 : ℝ)) t)
      (fun k y => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y)) m := by
  by_cases h0 : σ = 0
  · subst h0
    exact eightFst_law_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀
  by_cases hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀
  · exact eightFst_law_prot hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (pos_iff_ne_zero.2 h0) hσ
  · exact eightFst_law_unprot hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (not_le.1 hσ)

/-- **The deterministic geometry of the large Eight direction at every positive raw cap** (patched data). -/
theorem eightFst_geom_all [𝓖₂.IsRightContinuous] (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (σ : ℝ≥0) (m : ℕ) (x₀ : X) (y : Y)
    (hpos : 0 < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y)) :
    SeedImageGeometry (eightFstWord W₁ VL₁ VR₁ σ x₀) ![] (largeEightImgRhoL κ) ![]
      (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) (min t (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y))) (x₀, y))
      (fun i t => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i
        (min t (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y))) (x₀, y))
      (fun j _ => (j.elim0 : ℝ)) (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y)) := by
  by_cases h0 : σ = 0
  · subst h0
    have hc := (eightFst_zero_ident hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y).2.2.2 m
    have hL := eightFst_lt_lifeEnd hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y
    rw [← hc] at hL
    exact eightFst_geom_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y hL
  by_cases hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀
  · obtain ⟨a, W', haW, hCc, hCs, ⟨c, hc, hClb⟩, hv⟩ :=
      eightFst_seed hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (pos_iff_ne_zero.2 h0) hσ
    obtain ⟨-, -, -, hI5, hgeo⟩ := eightFst_ident hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hσ haW hCc hCs hc hClb hv y
    have hcap : eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y) =
        seedCapacityHorizon (eightFstSeed κ B₂ a W' (physMap x (Strip.extPath (W₁ · x₀)) σ)) (eightS₂ x W₂ ζ₂ m)
          y := hI5 _ (by simp only [eightFstOwn, hσ, ↓reduceIte])
    exact hgeo _ hcap.le
  · exfalso
    have h : eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ m (x₀, y) = 0 := by
      unfold eightFstCap
      exact capFst_of_nonpos (by simp only [eightFstOwn, hσ, ↓reduceIte, le_refl])
    rw [h] at hpos
    exact lt_irrefl 0 hpos

end Frame

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **`EightRectLawFstC`'s conclusion from the concrete families with masked-cap laws** (A1-RECTLAW2's
`hasFamilyLawFstC_eight_of_inputs` with the one-sample laws stated for the masked caps `maskCap G₁ G₂ eightFstCap`,
which vanish off the good sets; the law at a null set of image samples then asks nothing of the original data there). -/
theorem hasFamilyLawFstC_eight_of_maskedLaw {κ xs : ℝ} (hκ : 0 < κ) (hxs : xs < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![xs] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -xs] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁' : Fin 2 → ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (hS₁ : ∀ k, Measurable (eightS₁ xs W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (eightS₂ xs W₂' ζ₂' k))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (eightFstWord W₁ VL₁ VR₁ σ z.1) ![] (largeEightImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs
          W₁ (fun _ => σ) (min t (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun i t => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i
          (min t (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j _ => (j.elim0 : ℝ)) (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ x ∂P₁, x ∈ G₁ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₂.withDensity fun y => eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x, y))
        (fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs
          W₁ (fun _ => σ) t (x, y))
        (fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs
          W₁ (fun _ => σ) (x, y))
        (fun i t y => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x, y)) (fun j _ _ => (j.elim0 : ℝ))
        (fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
          (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω))
            xs W₁ (fun _ => σ) s (x, y))
          (fun i s => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x, y)) (fun j _ => (j.elim0 : ℝ)) t)
        (fun k' y => maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') σ k' (x, y)) k)
    (hstop : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs W₁ (eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂)
        (fun _ j _ _ => (j.elim0 : ℝ)) (maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs W₁
      (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
      (fun _ _ => ![]) (largeEightImgRhoL κ) ![] := by
  obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightFst_facts h₁ h₂
  have hm3 := (measurable_rDrvFst_rLifeFst (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) hlive (fun _ _ h => h) hjc hj0
    hkc hk0 hjm hkm hζj hζk 0 xs).1
  have hG₁ae : ∀ᵐ x ∂P₁, x ∈ G₁ := by
    rw [ae_iff]; simpa only [compl_def] using hG₁0
  refine hasFamilyLawFstC_of_residual hκ (eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂) (fun _ j _ _ => (j.elim0 : ℝ))
    (maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂')) (eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hm3
    (fun i t => measurable_eightFstVL h₁ h₂ i t) (fun j => j.elim0)
    (fun m => measurable_maskCap hG₁ hG₂ (measurable_eightFstCap h₁ h₂ hS₁ hS₂ m)) hD (fun σ m z hz => ?_)
    (fun m => (hlaw m).mp (hG₁ae.mono fun x hx h σ => h hx σ)) hstop
  by_cases hl : (σ : ℝ≥0∞) < ζ₁ z.1
  · exact geometry_maskCap (w := fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs W₁ (fun _ => σ) t z)
      (vL := fun i t => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t z) (vR := fun j _ => (j.elim0 : ℝ))
      (hgeo σ m z)
      (seedImageGeometry_zero_of_isSeedWord (isSeedWord_eightFstWord hxs h₁.path σ z.1 hl)
        (w := fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω))
          xs W₁ (fun _ => σ) t z)
        (vL := fun i t => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t z) (vR := fun j _ => (j.elim0 : ℝ))
        (cImgDrvM_zero _ _ _ _ _ _ _ z) (fun i => eightFstVL_zero xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i z) fun j => j.elim0)
  · have hpos : 0 < maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') σ m z := hz.resolve_right hl
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [maskCap_of_mem hG.1 hG.2] at hpos ⊢
      exact hgeo σ m z hG.1 hG.2 hpos
    · rw [maskCap_of_not_mem hG] at hpos
      exact absurd hpos (lt_irrefl 0)

end Assembly

section Final

/-- **The record facts of the large Eight direction** (the remaining input of `EightRectLawFstC`): the binders of
`EightRectLawFstC` and the good sets `G₁`, `G₂` of the two patches; at every stopping time `τ` of the small curve's
usual augmentation, the masked raw caps, the canonical driver and the forces read, before the cap, only the records
`(τ ∧ S₁ᵐ, S₂ᵐ)` of the patched exits, and the caps exhaust the pre-contact clock almost surely (the inputs `hSm`,
`hstop`, `hgW`, `hgVL`, `hgS`, `hcov` of A1-RECTLAW2's `eightFstResStop`). -/
def EightFstRecordStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∀ (W₂' : ℝ≥0 → Y → ℝ) (VL₂' : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂' : Fin 0 → ℝ≥0 → Y → ℝ) (B₂' : ℝ≥0 → Y → ℝ)
        (ζ₂' : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 2 → ℝ≥0 → X → ℝ)
        (B₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞),
      IsPatchOf κ ![x] ![] ![0] ![] (fun _ _ _ _ _ => True) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₂' VL₂' VR₂' B₂' ζ₂' →
      IsPatchOf (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) GoodSmallEight P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁
        W₁' VL₁' VR₁' B₁' ζ₁' →
      ∀ (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁' ζ₁' m ω : WithTop ℝ≥0))
        (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂' ζ₂' m ω : WithTop ℝ≥0))
        (μ : Measure (X × Y)), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
        (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
          ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁' VL₁' VR₁' W₂' (eightS₁ x W₁' ζ₁') m) ω
            (eightS₁ x W₁' ζ₁' m ω.1) (eightS₂ x W₂' ζ₂' m ω.2))) →
        ∀ (G₁ : Set X) (G₂ : Set Y), MeasurableSet G₁ → MeasurableSet G₂ → P₁ G₁ᶜ = 0 → P₂ G₂ᶜ = 0 →
        (∀ x₀ ∈ G₁, (∀ t, W₁' t x₀ = W₁ t x₀) ∧ (∀ i t, VL₁' i t x₀ = VL₁ i t x₀) ∧
          (∀ i t, VR₁' i t x₀ = VR₁ i t x₀) ∧ (∀ t, B₁' t x₀ = B₁ t x₀) ∧ ζ₁' x₀ = ζ₁ x₀) →
        (∀ y₀ ∈ G₂, (∀ t, W₂' t y₀ = W₂ t y₀) ∧ (∀ i t, VL₂' i t y₀ = VL₂ i t y₀) ∧
          (∀ i t, VR₂' i t y₀ = VR₂ i t y₀) ∧ (∀ t, B₂' t y₀ = B₂ t y₀) ∧ ζ₂' y₀ = ζ₂ y₀) →
        ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x₀ => (τ x₀ : WithTop ℝ≥0)),
          (∀ m, Measurable[@Prod.instMeasurableSpace X Y
            (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
            fun z => maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z) ∧
          (∀ m (s : ℝ≥0) (B : Set X), MeasurableSet[hτ.measurableSpace] B →
            MeasurableSet[@Prod.instMeasurableSpace X Y
            (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
              (Prod.fst ⁻¹' B ∩ {z | s < maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z})) ∧
          (∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y
            (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace] f ∧
            ∀ z, r < maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z →
              rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
                τ r z = f z) ∧
          (∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y
            (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace] f ∧
            ∀ z, r < maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z →
              eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ (τ z.1) i r z = f z) ∧
          (∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y
            (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
            ({z | maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) k z ≤ r} ∩
              {z | r < maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z})) ∧
          ∀ᵐ z ∂μ, (τ z.1 : ℝ≥0∞) < ζ₁ z.1 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime 0
              (Strip.extPath (W₂ · z.2)) (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) x (Strip.extPath (W₁ · z.1))
              (τ z.1) →
            ∃ m, A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) x (Strip.extPath (W₁ · z.1)) (τ z.1) s ≤
              maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z

/-- **Zhan's A.1 (Eight), the large-curve direction, from its record facts**: `EightRectLawFstC κ` follows from
`EightFstRecordStatement κ`. Proved here: the one-sample laws at every frozen time (protected, unprotected and `σ = 0`)
and the deterministic geometry, both for the patched marginals and transferred to the original ones off the null sets
of the patches (masked caps). -/
theorem eightRectLawFstC_of_records {κ : ℝ} (hrec : EightFstRecordStatement κ) : EightRectLawFstC κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂'
    ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd
  have hκ : 0 < κ := by linarith
  obtain ⟨G₂, hG₂, hG₂0, h₂', hB₂', -, hag₂⟩ := id hp₂
  obtain ⟨G₁, hG₁, hG₁0, h₁', hB₁', hg₁', hag₁⟩ := id hp₁
  have hrec' := hrec hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
    VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd G₁ G₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂
  -- original = patched at good samples
  have hc : ∀ z : X × Y, z.1 ∈ G₁ → z.2 ∈ G₂ → _ := fun z hz₁ hz₂ =>
    eightFst_congr (x := x) (z := z) (fun t => ((hag₁ z.1 hz₁).1 t).symm) (fun i t => ((hag₁ z.1 hz₁).2.1 i t).symm)
      (fun i t => ((hag₁ z.1 hz₁).2.2.1 i t).symm) (hag₁ z.1 hz₁).2.2.2.2.symm
      (fun t => ((hag₂ z.2 hz₂).1 t).symm) (fun i t => ((hag₂ z.2 hz₂).2.1 i t).symm) (hag₂ z.2 hz₂).2.2.2.2.symm
  have hword : ∀ σ x₀, x₀ ∈ G₁ → eightFstWord W₁ VL₁ VR₁ σ x₀ = eightFstWord W₁' VL₁' VR₁' σ x₀ := fun σ x₀ hx₀ => by
    simp only [eightFstWord, (hag₁ x₀ hx₀).1, (hag₁ x₀ hx₀).2.1, (hag₁ x₀ hx₀).2.2.1]
  have hS₁m : ∀ k, Measurable (eightS₁ x W₁' ζ₁' k) := fun k => measurable_of_isStoppingTime (hs₁ k)
  have hS₂m : ∀ k, Measurable (eightS₂ x W₂' ζ₂' k) := fun k => measurable_of_isStoppingTime (hs₂ k)
  refine hasFamilyLawFstC_eight_of_maskedLaw hκ hx h₂ h₁ hS₁m hS₂m hG₁ hG₂ hG₁0
    (fun k => measurable_eightFstD hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' k) (fun σ k z hz₁ hz₂ hpos => ?_)
    (fun k => Eventually.of_forall fun x₀ hx₀ σ => ?_) (fun τ hτ => ?_)
  · -- the geometry at good samples
    obtain ⟨hc1, -, hc3, hc4⟩ := hc z hz₁ hz₂
    rw [hc4] at hpos
    have hg := eightFst_geom_all hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' σ k z.1 z.2 hpos
    simp only [hc1, hc3, hc4, hword σ z.1 hz₁]
    exact hg
  · -- the one-sample laws at good small samples, transferred off the null set `G₂ᶜ`
    have hL := eightFst_law_all hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' k x₀ σ
    refine IsSeedSampleLaw.congr_offNull hL (E := G₂ᶜ) hG₂.compl (withDensity_absolutelyContinuous _ _ hG₂0)
      (fun y hy => maskCap_of_not_mem (z := (x₀, y)) fun h => hy h.2) (fun y hy t => ?_) (fun y hy => ?_)
      (fun y hy i t => ?_) (fun y hy j => j.elim0) (fun y hy t => ?_) (fun y hy k' => ?_)
    · exact ((hc (x₀, y) hx₀ (not_not.1 hy)).1 σ t)
    · exact ((hc (x₀, y) hx₀ (not_not.1 hy)).2.1 σ)
    · exact ((hc (x₀, y) hx₀ (not_not.1 hy)).2.2.1 σ i t)
    · obtain ⟨hc1, -, hc3, -⟩ := hc (x₀, y) hx₀ (not_not.1 hy)
      simp only [hc1, hc3]
    · rw [maskCap_of_mem (z := (x₀, y)) hx₀ (not_not.1 hy)]
      exact (hc (x₀, y) hx₀ (not_not.1 hy)).2.2.2 W₁' ζ₁' W₂' ζ₂' σ k'
  · -- the per-stop inputs: A1-RECTLAW2's `eightFstResStop` with the record facts
    obtain ⟨hSm, hstop, hgW, hgVL, hgS, hcov⟩ := hrec' τ hτ
    exact ⟨eightFstResStop hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hd hτ hSm hstop hgW hgVL
      (fun m j r => j.elim0) hgS (eightFst_hgζ x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' G₁ G₂ τ) hcov⟩

end Final

end InteractingSLE.ZhanGT4.A1EFam
