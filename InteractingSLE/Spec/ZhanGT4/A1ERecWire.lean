/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ERecCov

/-!
# Zhan's A.1 (Eight), large direction: the record facts, and `EightRectLawFstC`

Packet PROVE-A1-EIGHTREC. A1-EIGHTFAM reduced the large direction `EightRectLawFstC` to its record facts
(`A1EFam.EightFstRecordStatement`: `hSm`, `hstop`, `hgW`, `hgVL`, `hgS`, `hcov` of A1-RECTLAW2's `eightFstResStop`, for
the original marginals with the caps masked off the good sets `G₁ × G₂`). Here they are proved:

* on `G₁ × G₂` the original data are the patched data (A1-EIGHTFAM's `eightFst_congr`), so the masked cap is the
  indicator of `G₁ × G₂` times the patched raw cap; `G₁ × G₂` is an event of the records (the stopped σ-algebras of
  the usual augmentations contain the conull measurable sets, `measurableSet_stop_of_null`);
* the patched facts are `A1ERecMeas`'s `eightRec_hSm`, `eightRec_hgS`, `eightRec_hgW`, `eightRec_hgVL`, MULTIMARK's
  `measurableSet_fst_inter_cap` (`hstop`) and `A1ERecCov`'s `eightRec_hcov` (`μ`-almost every sample lies in
  `G₁ × G₂`, since the marginals of `μ` are `P₁`, `P₂`).

Main results: **`eightFstRecordStatement`** and **`eightRectLawFstC`** (Eight's large direction of Zhan's A.1, R83).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ERec

open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm A1Forces A1MultiMark A1Family A1RLaw A1Frozen A1SeedGeom A1RectLaw A1EFam

/-- **Zhan's A.1 (Eight), the large direction's record facts** (`A1EFam.EightFstRecordStatement`): PROVED for every
`κ`. -/
theorem eightFstRecordStatement (κ : ℝ) : EightFstRecordStatement κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂'
    ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd G₁ G₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ τ hτ
  obtain ⟨-, -, -, h₂', hB₂', -, -⟩ := id hp₂
  obtain ⟨-, -, -, h₁', hB₁', hg₁', -⟩ := id hp₁
  -- original = patched on `G₁ × G₂`
  have hc : ∀ z : X × Y, z.1 ∈ G₁ → z.2 ∈ G₂ → _ := fun z hz₁ hz₂ =>
    eightFst_congr (x := x) (z := z) (fun t => ((hag₁ z.1 hz₁).1 t).symm) (fun i t => ((hag₁ z.1 hz₁).2.1 i t).symm)
      (fun i t => ((hag₁ z.1 hz₁).2.2.1 i t).symm) (hag₁ z.1 hz₁).2.2.2.2.symm
      (fun t => ((hag₂ z.2 hz₂).1 t).symm) (fun i t => ((hag₂ z.2 hz₂).2.1 i t).symm) (hag₂ z.2 hz₂).2.2.2.2.symm
  -- the masked cap is the indicator of `G₁ × G₂` times the patched raw cap
  have hmask : ∀ m z, maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z =
      (G₁ ×ˢ G₂).indicator (fun z => eightFstCap x W₁' ζ₁' W₂' VL₂' ζ₂' W₁' ζ₁' W₂' ζ₂' (τ z.1) m z) z := by
    intro m z
    by_cases hz : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [maskCap_of_mem hz.1 hz.2, indicator_of_mem (mk_mem_prod hz.1 hz.2)]
      exact (hc z hz.1 hz.2).2.2.2 W₁' ζ₁' W₂' ζ₂' (τ z.1) m
    · rw [maskCap_of_not_mem hz, indicator_of_notMem fun h => hz (mem_prod.1 h)]
  have hmask' : ∀ m, (fun z => maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z) =
      (G₁ ×ˢ G₂).indicator (fun z => eightFstCap x W₁' ζ₁' W₂' VL₂' ζ₂' W₁' ζ₁' W₂' ζ₂' (τ z.1) m z) :=
    fun m => funext (hmask m)
  have hpos : ∀ m (r : ℝ≥0) z, r < maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z →
      (z.1 ∈ G₁ ∧ z.2 ∈ G₂) ∧ r < eightFstCap x W₁' ζ₁' W₂' VL₂' ζ₂' W₁' ζ₁' W₂' ζ₂' (τ z.1) m z := by
    intro m r z hz
    rw [hmask m z] at hz
    by_cases hzG : z ∈ G₁ ×ˢ G₂
    · rw [indicator_of_mem hzG] at hz
      exact ⟨mem_prod.1 hzG, hz⟩
    · rw [indicator_of_notMem hzG] at hz
      exact absurd hz (not_lt.2 (_root_.zero_le : (0 : ℝ≥0) ≤ r))
  -- `G₁ × G₂` is an event of the records
  have hGG : ∀ m, MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] (G₁ ×ˢ G₂) := fun m =>
    ((@measurable_fst X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace)
      (measurableSet_stop_of_null (hτ.min (hs₁ m)) hG₁ hG₁0)).inter
    ((@measurable_snd X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace)
      (measurableSet_stop_of_null (hs₂ m) hG₂ hG₂0))
  have hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace]
      fun z => maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z := fun m => by
    rw [hmask' m]
    exact (eightRec_hSm hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ m).indicator (hGG m)
  refine ⟨hSm, fun m s B hB => ?_, fun m r => ?_, fun m i r => ?_, fun m k r => ?_, ?_⟩
  · -- `hstop`
    refine measurableSet_fst_inter_cap hτ (hs₁ m) (𝓑 := (hs₂ m).measurableSpace)
      (cap := fun z => maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z)
      (measurableSet_lt measurable_const (hSm m)) (fun z hz => ?_) hB
    exact WithTop.coe_le_coe.2
      (eightFstCap_pos (lt_of_le_of_lt (_root_.zero_le : (0 : ℝ≥0) ≤ s) (hpos m s z hz).2)).1
  · -- `hgW`
    obtain ⟨f, hf, hfe⟩ := eightRec_hgW hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ m r
    refine ⟨f, hf, fun z hz => ?_⟩
    obtain ⟨⟨hz₁, hz₂⟩, hz'⟩ := hpos m r z hz
    rw [rDrvFst_congr_stop (τ' := fun _ => τ z.1) rfl, (hc z hz₁ hz₂).1 (τ z.1) r,
      ← rDrvFst_congr_stop (τ := τ) (τ' := fun _ => τ z.1) rfl]
    exact hfe z hz'
  · -- `hgVL`
    obtain ⟨f, hf, hfe⟩ := eightRec_hgVL hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ m i r
    refine ⟨f, hf, fun z hz => ?_⟩
    obtain ⟨⟨hz₁, hz₂⟩, hz'⟩ := hpos m r z hz
    rw [(hc z hz₁ hz₂).2.2.1 (τ z.1) i r]
    exact hfe z hz'
  · -- `hgS`
    have e : {z | maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) k z ≤ r} ∩
        {z | r < maskCap G₁ G₂ (eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z} =
        (G₁ ×ˢ G₂) ∩ ({z | eightFstCap x W₁' ζ₁' W₂' VL₂' ζ₂' W₁' ζ₁' W₂' ζ₂' (τ z.1) k z ≤ r} ∩
          {z | r < eightFstCap x W₁' ζ₁' W₂' VL₂' ζ₂' W₁' ζ₁' W₂' ζ₂' (τ z.1) m z}) := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, hmask k z, hmask m z]
      by_cases hzG : z ∈ G₁ ×ˢ G₂
      · simp only [indicator_of_mem hzG, hzG, true_and]
      · simp only [indicator_of_notMem hzG, hzG, false_and, iff_false, not_and, not_lt]
        exact fun _ => _root_.zero_le
    rw [e]
    exact (hGG m).inter (eightRec_hgS hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hτ m k r)
  · -- `hcov`: almost every sample lies in `G₁ × G₂`
    have h₁G : ∀ᵐ z ∂μ, z.1 ∈ G₁ := by
      have h0 : μ (Prod.fst ⁻¹' G₁ᶜ) = 0 := by
        rw [← Measure.map_apply measurable_fst hG₁.compl, hμ₁]; exact hG₁0
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz
      simpa only [mem_preimage, mem_compl_iff, not_not] using hz
    have h₂G : ∀ᵐ z ∂μ, z.2 ∈ G₂ := by
      have h0 : μ (Prod.snd ⁻¹' G₂ᶜ) = 0 := by
        rw [← Measure.map_apply measurable_snd hG₂.compl, hμ₂]; exact hG₂0
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz
      simpa only [mem_preimage, mem_compl_iff, not_not] using hz
    filter_upwards [h₁G, h₂G] with z hz₁ hz₂ hlive s hs
    have e1 : (fun t => W₁ t z.1) = fun t => W₁' t z.1 := funext fun t => ((hag₁ z.1 hz₁).1 t).symm
    have e2 : (fun t => W₂ t z.2) = fun t => W₂' t z.2 := funext fun t => ((hag₂ z.2 hz₂).1 t).symm
    have e3 : (fun t => VL₂ 0 t z.2) = fun t => VL₂' 0 t z.2 := funext fun t => ((hag₂ z.2 hz₂).2.1 0 t).symm
    have hζ₁ : ζ₁ z.1 = ζ₁' z.1 := (hag₁ z.1 hz₁).2.2.2.2.symm
    have hζ₂ : ζ₂ z.2 = ζ₂' z.2 := (hag₂ z.2 hz₂).2.2.2.2.symm
    simp only [hmask _ z, indicator_of_mem (mk_mem_prod hz₁ hz₂)]
    rw [hζ₁] at hlive
    simp only [e1, e2, e3, hζ₂] at hs ⊢
    exact eightRec_hcov hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' τ z hlive s hs

/-- **Zhan's A.1 (Eight), the large-curve direction `EightRectLawFstC`: PROVED** (A1-EIGHTFAM's
`eightRectLawFstC_of_records` with the record facts `eightFstRecordStatement`). -/
theorem eightRectLawFstC (κ : ℝ) : EightRectLawFstC κ :=
  eightRectLawFstC_of_records (eightFstRecordStatement κ)

end InteractingSLE.ZhanGT4.A1ERec
