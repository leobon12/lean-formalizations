/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawNoise
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomWord
import InteractingSLE.Spec.ZhanGT4.A1CanonFactor

/-!
# Zhan's A.1 under R83: shared helpers for the directional laws

Packet PROVE-A1-RECTLAW2 (R83), shared by the four directional laws (Eight and G3, both directions):

* **`seedImageGeometry_zero_of_isSeedWord`**: at a live sample with a zero cap, the geometry required by
  `hasFamilyLawC_of_residual`'s `hgeo` is the admissibility of the initial word (SEEDGEOM's `*_isSeedWord`) and the
  initial values of the data (the forces at time `0` must be the word, also where the image lifetime vanishes);
* **`IsSeedSampleLaw.congr_ae`**: the one-sample law only depends on the image data outside a null set (the patched
  marginals agree with the original ones off null sets), for measurable data, through the usual augmentation of the
  law's filtration.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom

/-! ### The geometry at a zero cap -/

section Zero

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}

/-- **The geometry of data stopped at a zero cap** is the admissibility of the initial word and the initial values. -/
theorem seedImageGeometry_zero_of_isSeedWord (hword : IsSeedWord xL xR ρL ρR) (hw0 : w 0 = 0)
    (hL0 : ∀ i, vL i 0 = xL i) (hR0 : ∀ j, vR j 0 = xR j) :
    SeedImageGeometry xL xR ρL ρR (fun t => w (min t 0)) (fun i t => vL i (min t 0)) (fun j t => vR j (min t 0))
      0 := by
  have hm : ∀ t : ℝ≥0, min t 0 = 0 := fun t => min_eq_right bot_le
  have h0 : ∀ t : ℝ≥0, t ≤ 0 → t = 0 := fun t ht => le_antisymm ht bot_le
  refine seedImageGeometry_of_isSeedWord hword (by simp only [hm, hw0]) (fun i => by simp only [hm, hL0])
    (fun j => by simp only [hm, hR0]) (by simp only [hm]; exact continuous_const)
    (fun i => by simp only [hm]; exact continuous_const) (fun j => by simp only [hm]; exact continuous_const)
    (fun t ht i => ?_) (fun t ht j => ?_) (fun t ht i => ?_) (fun t ht j => ?_)
    (fun t ht ht' => absurd ht (not_lt.2 ht')) (fun t ht ht' => absurd ht (not_lt.2 ht'))
  · rw [h0 t ht, NNReal.coe_zero]
  · rw [h0 t ht, NNReal.coe_zero]
  · rw [h0 t ht, NNReal.coe_zero, intervalIntegral.integral_same, add_zero, hm, hL0]
  · rw [h0 t ht, NNReal.coe_zero, intervalIntegral.integral_same, add_zero, hm, hR0]

end Zero

/-! ### The one-sample law ignores null sets -/

section CongrAE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

/-- **The one-sample law only depends on the image data outside a null set.** If the primed data are measurable and
agree with the unprimed ones outside a `Q`-null set `E`, the one-sample law transfers (in the usual
augmentation of the law's filtration, which contains the null sets). -/
theorem IsSeedSampleLaw.congr_ae {Q : Measure Ω} {W W' : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {N N' : ℝ≥0 → Ω → ℝ}
    {Scap Scap' : ℕ → Ω → ℝ≥0} {m : ℕ} (h : IsSeedSampleLaw Q W ζ VL VR N Scap m) {E : Set Ω}
    (hE0 : Q E = 0)
    (hW : ∀ ω ∉ E, ∀ t, W' t ω = W t ω) (hζ : ∀ ω ∉ E, ζ' ω = ζ ω)
    (hVL : ∀ ω ∉ E, ∀ i t, VL' i t ω = VL i t ω) (hVR : ∀ ω ∉ E, ∀ j t, VR' j t ω = VR j t ω)
    (hN : ∀ ω ∉ E, ∀ t, N' t ω = N t ω) (hS : ∀ ω ∉ E, ∀ k, Scap' k ω = Scap k ω)
    (hW'm : ∀ t, Measurable (W' t)) (hζ'm : Measurable ζ') (hVL'm : ∀ i t, Measurable (VL' i t))
    (hVR'm : ∀ j t, Measurable (VR' j t)) (hN'm : ∀ t, Measurable (N' t)) (hS'm : ∀ k, Measurable (Scap' k)) :
    IsSeedSampleLaw Q W' ζ' VL' VR' N' Scap' m := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  set 𝓗' := usualAugmentation 𝓗 Q with h𝓗'
  have hle : ∀ t, 𝓗 t ≤ 𝓗' t := fun t => Ito.le_usualAugmentation 𝓗 Q t
  have hN0 : ∀ t, Ito.nullSets Q ≤ 𝓗' t := fun t => Ito.nullSets_le_usualAugmentation 𝓗 Q t
  -- two sets agreeing off `E` are a.e. equal
  have hae : ∀ {s s' : Set Ω}, (∀ ω ∉ E, ω ∈ s' ↔ ω ∈ s) → s' =ᵐ[Q] s := fun {s s'} hss => by
    have hE' : ∀ᵐ ω ∂Q, ω ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
    filter_upwards [hE'] with ω hω
    exact propext (hss ω hω)
  have hcap : ∀ s : ℝ≥0, MeasurableSet {ω | s < Scap' m ω} := fun s =>
    measurableSet_lt measurable_const (hS'm m)
  have hcapE : ∀ (s : ℝ≥0) ω, ω ∉ E → (ω ∈ {ω | s < Scap' m ω} ↔ ω ∈ {ω | s < Scap m ω}) := fun s ω hω => by
    simp only [mem_ofPred_eq, hS ω hω m]
  have hC' : ∀ s : ℝ≥0, MeasurableSet[𝓗' s] {ω | s < Scap' m ω} := fun s =>
    measurableSet_of_ae_eq_of_nullSets_le (𝓗'.le s) (hN0 s) (hcap s) (hle s _ (hC s)) (hae (hcapE s · ·))
  refine ⟨𝓗', B, Ito.isFilteredBrownianReal_usualAugmentation hB, hBc, hC', fun s => ?_, ?_⟩
  · -- every primed generator, cut down to the cap event, is a.e. equal to the unprimed one
    have key : ∀ (g g' : Set Ω), MeasurableSet g' → (∀ ω ∉ E, ω ∈ g' ↔ ω ∈ g) →
        g ∈ imageGen W ζ VL VR N Scap s → MeasurableSet[𝓗' s] (g' ∩ {ω | s < Scap' m ω}) :=
      fun g g' hg' hgg hg => measurableSet_of_ae_eq_of_nullSets_le (𝓗'.le s) (hN0 s) (hg'.inter (hcap s))
        (hle s _ (hG s g hg)) (hae fun ω hω => by
          simp only [mem_inter_iff]
          rw [hgg ω hω, hcapE s ω hω])
    refine forall_imageGen (p := fun g => MeasurableSet[𝓗' s] (g ∩ {ω | s < Scap' m ω}))
      (fun r hr U hU => key (W r ⁻¹' U) _ (hW'm r hU) (fun ω hω => by simp only [mem_preimage, hW ω hω r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩)
      (fun r hr U hU i => key (VL i r ⁻¹' U) _ (hVL'm i r hU)
        (fun ω hω => by simp only [mem_preimage, hVL ω hω i r]) ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
      (fun r hr U hU j => key (VR j r ⁻¹' U) _ (hVR'm j r hU)
        (fun ω hω => by simp only [mem_preimage, hVR ω hω j r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩)
      (fun r hr U hU => key (N r ⁻¹' U) _ (hN'm r hU) (fun ω hω => by simp only [mem_preimage, hN ω hω r])
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩)
      (fun r hr k => key {ω | Scap k ω ≤ r} _ (measurableSet_le (hS'm k) measurable_const)
        (fun ω hω => by simp only [mem_ofPred_eq, hS ω hω k]) ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩)
      (fun r hr => key {ω | (r : ℝ≥0∞) < ζ ω} _ (measurableSet_lt measurable_const hζ'm)
        (fun ω hω => by simp only [mem_ofPred_eq, hζ ω hω]) ⟨r, hr, Or.inr (Or.inr rfl)⟩)
  · have hE' : ∀ᵐ ω ∂Q, ω ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
    filter_upwards [heq, hE'] with ω hω hωE t ht
    rw [hS ω hωE m] at ht
    rw [hω t ht, hN ω hωE t]

end CongrAE

/-! ### Masking the caps on a null set -/

section Mask

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

/-- **Masking the caps on a measurable null set keeps the one-sample law.** If the caps `Scap'` agree with `Scap`
outside a measurable `Q`-null set `E` and the cap `Scap' m` vanishes on `E`, the one-sample law transfers (no
measurability of the image data is needed: the primed cap event misses `E`). -/
theorem IsSeedSampleLaw.mask {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {N : ℝ≥0 → Ω → ℝ} {Scap Scap' : ℕ → Ω → ℝ≥0} {m : ℕ}
    (h : IsSeedSampleLaw Q W ζ VL VR N Scap m) {E : Set Ω} (hE : MeasurableSet E) (hE0 : Q E = 0)
    (hS : ∀ ω ∉ E, ∀ k, Scap' k ω = Scap k ω) (hS0 : ∀ ω ∈ E, Scap' m ω = 0) :
    IsSeedSampleLaw Q W ζ VL VR N Scap' m := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  set 𝓗' := usualAugmentation 𝓗 Q with h𝓗'
  have hle : ∀ t, 𝓗 t ≤ 𝓗' t := fun t => Ito.le_usualAugmentation 𝓗 Q t
  have hEm : ∀ t, MeasurableSet[𝓗' t] E := fun t => Ito.measurableSet_usualAugmentation_of_null hE hE0 t
  -- the primed cap event is the unprimed one off `E`
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
      (fun r hr U hU => key _ _ (fun _ _ => Iff.rfl) ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩)
      (fun r hr U hU i => key _ _ (fun _ _ => Iff.rfl) ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
      (fun r hr U hU j => key _ _ (fun _ _ => Iff.rfl)
        ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩)
      (fun r hr U hU => key _ _ (fun _ _ => Iff.rfl) ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩)
      (fun r hr k => key {ω | Scap k ω ≤ r} _ (fun ω hω => by simp only [mem_ofPred_eq, hS ω hω k])
        ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩)
      (fun r hr => key _ _ (fun _ _ => Iff.rfl) ⟨r, hr, Or.inr (Or.inr rfl)⟩)
  · have hE' : ∀ᵐ ω ∂Q, ω ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
    filter_upwards [heq, hE'] with ω hω hωE t ht
    rw [hS ω hωE m] at ht
    exact hω t ht

end Mask

end InteractingSLE.ZhanGT4.A1RLaw
