/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinGeom
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc

/-!
# The small prefix as a compact arc

Packet PROVE-ZHAN-A2P3-PC. Specializations of the proved A.2 part 1 retain the
simple generating trace, and its finite prefixes give the arc required by the
first-contact lemma.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-- A simple interior generating prefix, translated to its physical root, is
a compact arc whose image is the closure of the physical hull. -/
theorem exists_arc_of_simple_generatingTrace
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ζ η) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → η t ∈ H)
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < ζ) (x : ℝ) :
    ∃ α : ℝ → ℂ, ContinuousOn α (Icc 0 (q : ℝ)) ∧ α 0 = (x : ℂ) ∧
      MapsTo α (Ioc 0 (q : ℝ)) H ∧
      closure (physHull x (Strip.extPath w) q) = α '' Icc 0 (q : ℝ) := by
  let β : ℝ → ℂ := fun t => η (min t.toNNReal q)
  have hβc : Continuous β := hη.2.1.comp_continuous
    (continuous_real_toNNReal.min continuous_const) fun t =>
      (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans hq.le
  have hβeq : ∀ t ∈ Icc (0 : ℝ) q, β t = η t.toNNReal := by
    intro t ht
    exact congrArg η (min_eq_left ((Real.toNNReal_le_iff_le_coe).2 ht.2))
  have hβ0 : β 0 = 0 := by simp only [β, Real.toNNReal_zero, zero_min, hη.1]
  have hβH : MapsTo β (Ioc 0 (q : ℝ)) H := by
    intro t ht
    rw [hβeq t ⟨ht.1.le, ht.2⟩]
    exact hH _ (Real.toNNReal_pos.2 ht.1)
      ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)).trans_lt hq)
  have hβinj : InjOn β (Icc (0 : ℝ) q) := by
    intro s hs t ht he
    rw [hβeq s hs, hβeq t ht] at he
    have he' := hinj
      ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hq.le)
      ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)).trans hq.le) he
    have hh := congrArg (fun r : ℝ≥0 => (r : ℝ)) he'
    simpa only [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ ht.1] using hh
  have himg : β '' Icc (0 : ℝ) q = η '' Icc 0 q := by
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t.toNNReal, ⟨bot_le, Real.toNNReal_le_iff_le_coe.2 ht.2⟩, (hβeq t ht).symm⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.2⟩,
        by rw [hβeq t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.2⟩, Real.toNNReal_coe]⟩
  have hK : fwdHull (Strip.extPath w) q = β '' Ioc (0 : ℝ) q := by
    rw [show Strip.extPath w = (fun t => w t.toNNReal) from rfl,
      Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hη hq, ← himg,
      YuanCharacterisation.fillH_image_eq q.coe_nonneg hβc.continuousOn hβinj
        (by rw [hβ0]; rfl) hβH]
  let α : ℝ → ℂ := fun t => β t + x
  have hαc : Continuous α := hβc.add continuous_const
  refine ⟨α, hαc.continuousOn, ?_, ?_, ?_⟩
  · change β 0 + x = (x : ℂ)
    rw [hβ0, zero_add]
  · intro t ht
    have hh := hβH ht
    change 0 < (β t).im at hh
    change 0 < (β t + x).im
    simpa only [add_im, ofReal_im, add_zero] using hh
  · have hphys : physHull x (Strip.extPath w) q = α '' Ioc (0 : ℝ) q := by
      rw [physHull, hK, image_image]
    rw [hphys]
    apply Subset.antisymm
    · exact closure_minimal (image_mono Ioc_subset_Icc_self)
        (isCompact_Icc.image hαc).isClosed
    · have hh := image_closure_subset_closure_image hαc (s := Ioc (0 : ℝ) q)
      rwa [closure_Ioc (NNReal.coe_pos.2 hq0).ne] at hh

/-- Retain the simple trace in A.2 part 1, G3. -/
theorem ae_smallG3_simple_trace {κ y x : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hyx : y < x) (hx : x < 0) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR : Fin 3 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y]
      (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) (ζ ω) η ∧
      InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω} ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → η t ∈ H := by
  obtain ⟨hk2, hk4⟩ := kh_bounds_G3 hκ4 hκ8
  have hk0 : 0 < kh κ := by linarith only [hk2]
  have h := A2P1.ae_exit_trace (ρL' := ![2 - kh κ / 2, kh κ - 4, 0]) hk0 hk4.le
    (A2P1.g3_ordered hyx hx) (A2P1.g3_strictAnti hyx hx) (by rw [A2P1.g3_last]; linarith)
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
    (A2P1.g3_adm hk2.le hk4.le hx) (A2P1.g3_sum _) (A2P1.g3_preL hk0 hk4)
    (A2P1.one_preR (by linarith)) (A2P1.g3_pre hk2.le hk4.le) (A2P1.g3_q hk0 hk4) hE.reflect
  filter_upwards [h] with ω hgood
  obtain ⟨_hpos, _hfin, η, hη, hi, hH, _hend⟩ := hgood
  have hη' := LP.isGeneratingTrace_reflect hη
  have he : (-fun t => (-W) t ω) = (fun t => W t ω) := by funext t; simp
  rw [he] at hη'
  exact ⟨fun t => LP.reflectC (η t), hη', fun s hs t ht he =>
    hi hs ht (LP.reflectC_injective he), fun t ht htz => LP.reflectC_mem_H_iff.2 (hH t ht htz)⟩

/-- Retain the simple trace in A.2 part 1, Eight. -/
theorem ae_smallEight_simple_trace {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR : Fin 2 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x]
      (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) (ζ ω) η ∧
      InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω} ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → η t ∈ H := by
  obtain ⟨hk0, hk2⟩ := kh_bounds_eight hκ8
  have h := A2P1.ae_exit_trace (ρL' := ![kh κ / 2 - 2, 0]) hk0 (by linarith)
    (A2P1.e8_ordered hx) (A2P1.e8_strictAnti hx) (by rw [A2P1.e8_last]; exact hx)
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
    (A2P1.e8_adm hk2) (A2P1.e8_sum _) (A2P1.e8_preL hk0)
    (A2P1.one_preR (by linarith)) (A2P1.e8_pre hk2) (A2P1.e8_q hk0 (by linarith)) hE.reflect
  filter_upwards [h] with ω hgood
  obtain ⟨_hpos, _hfin, η, hη, hi, hH, _hend⟩ := hgood
  have hη' := LP.isGeneratingTrace_reflect hη
  have he : (-fun t => (-W) t ω) = (fun t => W t ω) := by funext t; simp
  rw [he] at hη'
  exact ⟨fun t => LP.reflectC (η t), hη', fun s hs t ht he =>
    hi hs ht (LP.reflectC_injective he), fun t ht htz => LP.reflectC_mem_H_iff.2 (hH t ht htz)⟩

end InteractingSLE.ZhanGT4.A2X.P3
