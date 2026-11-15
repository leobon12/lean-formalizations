/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepReg
import InteractingSLE.Spec.ZhanGT4.A2Part1Crosscut

/-!
# A.2, part 2: the image endpoint alternative for evolutions of a deterministic image word

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L527–L551 (R38, R53).

For a **deterministic** image word (left seed `0`, right seed `0`, marks `0 < a < b`), every integrated evolution
satisfies the image endpoint alternative `ImageEndpointAlt` at its lifetime **and at every earlier truncation**,
almost surely: at the lifetime, the small strip endpoint theorem (A2P1's `a2SmallCrosscutG3Statement`, the word of the
small curve from `y = −b` with marks `x = a − b`, `0`) gives the crosscut alternative; at an earlier time the trace up
to it is a simple arc in `ℍ ∪ {0}`, which is the premature alternative.

* `imgU_eq_trace`: the union of the hulls before `ζ' ≤ ζ` of a small crosscut's driver is its trace on `(0, ζ')`;
* `imageEndpointAlt_of_isSmallCrosscut`: the pathwise alternative at every truncation;
* `ae_imageEndpointAlt_G3`, `ae_imageEndpointAlt_eight`: the almost sure statements for integrated evolutions of the
  deterministic (G3) / (Eight) image word.

`ImageEndpointG3Statement` / `ImageEndpointEightStatement` (`A2TipSepAug.lean`) ask the same for **local** evolutions of
the **random** word given by the conditional image law; their remaining content is the transfer from these
deterministic-word statements (disintegration over the `𝓔`-measurable word, independent of the image Brownian motion,
and the identification of a local evolution with the integrated one before its stop).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

theorem ofReal_not_mem_H (u : ℝ) : (u : ℂ) ∉ H := fun h => by
  have : (0 : ℝ) < (u : ℂ).im := h
  simp at this

theorem zero_not_mem_H : (0 : ℂ) ∉ H := by simpa using ofReal_not_mem_H 0

section Path

variable {y : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ → ℂ} {η : ℝ≥0 → ℂ}

/-- **The hulls before `ζ' ≤ ζ` of the small curve form its trace on `(0, ζ')`.** -/
theorem imgU_eq_trace (hγ : IsRealCrosscut γ) (hγ0 : (γ 0).re = y) (hlt : y < (γ 1).re)
    (hη : IsGeneratingTrace w ζ η)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ}))
    {ζ' : ℝ≥0∞} (hζ' : ζ' ≤ ζ) : imgU (Strip.extPath w) ζ' = η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ'} := by
  ext z
  simp only [imgU, mem_iUnion]
  constructor
  · rintro ⟨t, ht, hz⟩
    have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le hζ'
    obtain ⟨r, hr, rfl⟩ := fwdHull_subset_trace hγ hγ0 hlt hη himg htζ hz
    have hr0 : 0 < r := by
      rcases eq_or_lt_of_le (zero_le (a := r)) with h | h
      · exfalso; have := hz.1; rw [← h, hη.1] at this; exact zero_not_mem_H this
      · exact h
    exact ⟨r, ⟨hr0, (ENNReal.coe_le_coe.2 hr.2).trans_lt ht⟩, rfl⟩
  · rintro ⟨r, ⟨hr0, hr⟩, rfl⟩
    have hrζ : (r : ℝ≥0∞) < ζ := hr.trans_le hζ'
    exact ⟨r, hr, trace_mem_fwdHull hη hrζ (trace_mem_H hγ himg hr0 hrζ)⟩

/-- **The image endpoint alternative for a small crosscut's driver, at every truncation `ζ' ≤ ζ`** (in the coordinates
of the source: the crosscut runs from `0`, and its end point is beyond `−y`). -/
theorem imageEndpointAlt_of_isSmallCrosscut (hy : y < 0) (hγ : IsSmallCrosscut y w ζ γ) {ζ' : ℝ≥0∞}
    (hζ' : ζ' ≤ ζ) : ImageEndpointAlt (Strip.extPath w) ζ' (-y) := by
  obtain ⟨hγc, hγ0, hγ1, η, hη, himg⟩ := hγ
  have hlt : y < (γ 1).re := by linarith
  rw [ImageEndpointAlt, imgU_eq_trace hγc hγ0 hlt hη himg hζ']
  rcases hζ'.eq_or_lt with h | h
  · -- at the lifetime: the crosscut
    left
    subst h
    have h0 : γ 0 = (y : ℂ) := Complex.ext (by simp [hγ0]) (by simp [hγc.2.2.2.1])
    refine ⟨fun s => γ s - y, isRealCrosscut_sub hγc y, by simp [h0], ?_, ?_⟩
    · simp only [sub_re, ofReal_re]; linarith
    · have e : (fun s => γ s - (y : ℂ)) '' Ioo 0 1 = (fun z : ℂ => z - y) '' (γ '' Ioo 0 1) := by
        rw [image_image]
      rw [e, himg, image_image]
      simp
  · -- before the lifetime: a simple arc in `ℍ ∪ {0}`
    right
    have hζ'top : ζ' ≠ ⊤ := ne_top_of_lt h
    set T : ℝ≥0 := ζ'.toNNReal with hT
    have hTζ' : (T : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hζ'top
    have hTζ : (T : ℝ≥0∞) < ζ := hTζ' ▸ h
    have hcont : ∀ t₀ : ℝ≥0, t₀ ≤ T → ContinuousOn η (Icc t₀ T) := fun t₀ _ =>
      hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hTζ.le
    have hsub : η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ'} ⊆ η '' Icc 0 T := by
      rintro _ ⟨r, ⟨-, hr⟩, rfl⟩
      exact ⟨r, ⟨zero_le (a := r), by rw [← hTζ'] at hr; exact (ENNReal.coe_lt_coe.1 hr).le⟩, rfl⟩
    have hEc : IsCompact (η '' Icc 0 T) := isCompact_Icc.image_of_continuousOn (hcont 0 (zero_le (a := T)))
    have hmemH : ∀ r : ℝ≥0, 0 < r → r ≤ T → η r ∈ H := fun r hr0 hrT =>
      trace_mem_H hγc himg hr0 ((ENNReal.coe_le_coe.2 hrT).trans_lt hTζ)
    refine ⟨hEc.isBounded.subset hsub, fun u hu => ?_, fun t ht => ?_⟩
    · obtain ⟨r, hr, hru⟩ := (closure_minimal hsub hEc.isClosed) hu
      rcases eq_or_lt_of_le (zero_le (a := r)) with h0 | h0
      · rw [← h0, hη.1] at hru; exact_mod_cast hru.symm
      · exfalso
        have := hmemH r h0 hr.2
        rw [hru] at this
        exact ofReal_not_mem_H u this
    · by_cases htT : (T : ℝ) ≤ t
      · refine ⟨1, one_pos, fun z hz => ?_⟩
        obtain ⟨⟨r, ⟨hr0, hr⟩, rfl⟩, -⟩ := hz
        have hrT : (r : ℝ) ≤ t := by
          rw [← hTζ'] at hr; exact (NNReal.coe_le_coe.2 (ENNReal.coe_lt_coe.1 hr).le).trans htT
        exact fwdHull_subset_of_le hrT
          (trace_mem_fwdHull hη (hr.trans h) (hmemH r hr0 (by rw [← hTζ'] at hr; exact (ENNReal.coe_lt_coe.1 hr).le)))
      · push Not at htT
        set E := η '' Icc t.toNNReal T with hE
        have hEc' : IsCompact E := isCompact_Icc.image_of_continuousOn (hcont _ (Real.toNNReal_le_iff_le_coe.2 htT.le))
        have h0E : (0 : ℂ) ∉ E := by
          rintro ⟨r, hr, hr0⟩
          have hrpos : 0 < r := lt_of_lt_of_le (Real.toNNReal_pos.2 ht) hr.1
          have := hmemH r hrpos hr.2
          rw [hr0] at this
          exact zero_not_mem_H this
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hEc'.isClosed.isOpen_compl 0 h0E
        refine ⟨δ, hδ, fun z hz => ?_⟩
        obtain ⟨⟨r, ⟨hr0, hr⟩, rfl⟩, hzδ⟩ := hz
        have hrT : r ≤ T := by rw [← hTζ'] at hr; exact (ENNReal.coe_lt_coe.1 hr).le
        have hrt : (r : ℝ) < t := by
          by_contra hcon
          push Not at hcon
          exact hball hzδ ⟨r, ⟨Real.toNNReal_le_iff_le_coe.2 hcon, hrT⟩, rfl⟩
        exact fwdHull_subset_of_le hrt.le (trace_mem_fwdHull hη (hr.trans h) (hmemH r hr0 hrT))

end Path

/-- **The image endpoint alternative for the deterministic (G3) image word** (L527–L551): every integrated evolution
of the word (left seed `0`, right seed `0`, marks `0 < a < b`) satisfies `ImageEndpointAlt` almost surely at its
lifetime and at every earlier truncation. -/
theorem ae_imageEndpointAlt_G3 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 3 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution (kh κ) ![0] ![0, a, b] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ ζ' ≤ ζ ω, ImageEndpointAlt (Strip.extPath (W · ω)) ζ' b := by
  have hword : (![0, (a - b) - (-b), -(-b)] : Fin 3 → ℝ) = ![0, a, b] := by
    ext i; fin_cases i <;> simp
  have h := A2P1.a2SmallCrosscutG3Statement.{u} κ hκ4 hκ8 (-b) (a - b) (by linarith) (by linarith) P 𝓕 W VL VR B ζ
    (by rw [hword]; exact hE)
  filter_upwards [h] with ω ⟨γ, hγ⟩ ζ' hζ'
  have := imageEndpointAlt_of_isSmallCrosscut (by linarith) hγ hζ'
  rwa [neg_neg] at this

/-- **The image endpoint alternative for the deterministic (Eight) image word** (left seed `0`, right seed `0`, the
mark `b > 0`). -/
theorem ae_imageEndpointAlt_eight {κ : ℝ} (hκ8 : 8 ≤ κ) {b : ℝ} (hb : 0 < b)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution (kh κ) ![0] ![0, b] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ ζ' ≤ ζ ω, ImageEndpointAlt (Strip.extPath (W · ω)) ζ' b := by
  have hword : (![0, -(-b)] : Fin 2 → ℝ) = ![0, b] := by
    ext i; fin_cases i <;> simp
  have h := A2P1.a2SmallCrosscutEightStatement.{u} κ hκ8 (-b) (by linarith) P 𝓕 W VL VR B ζ
    (by rw [hword]; exact hE)
  filter_upwards [h] with ω ⟨γ, hγ⟩ ζ' hζ'
  have := imageEndpointAlt_of_isSmallCrosscut (by linarith) hγ hζ'
  rwa [neg_neg] at this

end InteractingSLE.ZhanGT4.A2TipSep
