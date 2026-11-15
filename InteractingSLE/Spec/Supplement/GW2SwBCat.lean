/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwBConcat

/-!
# Loewner concatenation of a generating continuation that may touch the boundary

Packet PROVE-GW2-SWITCH (round 2). The proof of `LoewnerConcat.isGeneratingTrace_catPath`, with its
two uses of the `ℍ`-avoidance premise replaced by `continuous_joinedTrace_bdry` and
`joinedTrace_inter_domain_bdry` (`GW2SwBConcat`), and the time-`0` case by the boundary extension of
the identity at a point of `ℍ̄`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.Sec7.StripSideHeightProb

namespace InteractingSLE.LoewnerConcat

variable {w₀ w₁ : ℝ≥0 → ℝ} {η₀ η₁ : ℝ≥0 → ℂ} {a : ℝ≥0}

/-- **Loewner concatenation, boundary hits allowed.** A closed continuous generating prefix followed by
ANY generating trace of the continuation generates the concatenated driver, with the joined trace. -/
theorem isGeneratingTrace_catPath_bdry (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ a η₀) (hη₁ : IsGeneratingTrace w₁ ⊤ η₁) :
    IsGeneratingTrace (catPath w₀ a w₁) ⊤ (joinedTrace w₀ η₀ a η₁) := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hV : Continuous (Ito.rpath w₁) := h₁.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hc := continuous_joinedTrace_bdry h₀ h00 h₁ h10 hη₀ hη₁
  rcases eq_or_lt_of_le (show 0 ≤ a from bot_le) with ha | ha
  · subst a
    have hw : catPath w₀ 0 w₁ = w₁ := by
      funext t
      by_cases ht : t ≤ 0
      · have ht0 : t = 0 := le_antisymm ht bot_le
        rw [ht0, catPath_zero h00, h10]
      · simp only [catPath, ht, ↓reduceIte, h00, zero_add, tsub_zero]
    have hη : joinedTrace w₀ η₀ 0 η₁ = η₁ := by
      funext t
      rcases eq_or_lt_of_le (show 0 ≤ t from bot_le) with ht | ht
      · rw [← ht, joinedTrace_of_le le_rfl, hη₀.1, hη₁.1]
      · rw [show t = 0 + t by rw [zero_add], joinedTrace_add ht, NNReal.coe_zero, zero_add]
        refine extendFrom_eq (by rw [closure_H]; exact trace_mem_Hbar_bdry h₁ h10 hη₁ t) ?_
        refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (fwdMapInv_zero_time hW hW0 hz).symm
    rw [hw, hη]
    exact hη₁
  · have haR : 0 < (a : ℝ) := ha
    have hK : fwdHull (Ito.rpath w₀) a = fillH (η₀ '' Icc 0 a) := by
      have h := TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT
        (isLoewnerTraceLT_prefix hη₀) hW hW0 haR (continuousOn_prefix hη₀)
      rwa [image_toNNReal_Icc η₀ a.coe_nonneg, Real.toNNReal_coe] at h
    refine ⟨(joinedTrace_of_le (show 0 ≤ a from bot_le)).trans hη₀.1,
      hc.continuousOn, fun t _ => ?_⟩
    have hP : IsCompact (joinedTrace w₀ η₀ a η₁ '' Icc 0 t) := isCompact_Icc.image hc
    apply (fillH_eq_iff_isFilling_of_isClosed hP.isBounded hP.isClosed
      (QuantumZipper.fwdHull_mono.2 _)).2
    change fwdHull (Ito.rpath (catPath w₀ a w₁)) t = _
    by_cases hta : t ≤ a
    · have hKh : fwdHull (Ito.rpath (catPath w₀ a w₁)) t = fwdHull (Ito.rpath w₀) t :=
        YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_rpath_catPath h₀ h₁ h10) hW t.coe_nonneg
          (fun r hr => rpath_catPath_eqOn ⟨hr.1, hr.2.trans (by exact_mod_cast hta)⟩)
      rw [hKh, (EqOn.image_eq (fun r hr => joinedTrace_of_le (hr.2.trans hta)))]
      rcases hta.eq_or_lt with heq | hlt
      · rw [heq]; exact hK
      · have ht' : (t : ℝ≥0∞) < a := ENNReal.coe_lt_coe.2 hlt
        have hPt : IsCompact (η₀ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn
          (hη₀.2.1.mono (fun r hr => ENNReal.coe_le_coe.2 (hr.2.trans hta)))
        exact (fillH_eq_iff_isFilling_of_isClosed hPt.isBounded hPt.isClosed
          (QuantumZipper.fwdHull_mono.2 _)).1 (hη₀.2.2 t ht')
    · let s := t - a
      have hts : a + s = t := add_tsub_cancel_of_le (not_le.1 hta).le
      have hc₁ : Continuous η₁ := continuousOn_univ.1
        (hη₁.2.1.mono (fun r _ => show (r : ℝ≥0∞) ≤ ⊤ from le_top))
      have hB : IsCompact (η₁ '' Icc 0 s) := isCompact_Icc.image hc₁
      have hAP : η₀ '' Icc 0 a ⊆ joinedTrace w₀ η₀ a η₁ '' Icc 0 t := by
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨r, ⟨hr.1, hr.2.trans (not_le.1 hta).le⟩, joinedTrace_of_le hr.2⟩
      have hPB := joinedTrace_inter_domain_bdry h₀ h00 h₁ h10 hη₀ hη₁ hK s
      rw [hts] at hPB
      have hcomp := compl_fillH_eq_image hW hW0 a.coe_nonneg hK hAP hB hP hPB
      have hBfill := (fillH_eq_iff_isFilling_of_isClosed hB.isBounded hB.isClosed
        (QuantumZipper.fwdHull_mono.2 _)).1 (hη₁.2.2 s ENNReal.coe_lt_top)
      change fwdHull (Ito.rpath w₁) s = _ at hBfill
      rw [← hBfill, ← QuantumZipper.RS.image_fwdMapInv_H hV
        (by simpa only [Ito.rpath, Real.toNNReal_zero] using h10) s.coe_nonneg,
        image_image] at hcomp
      have himg : (fun z => fwdMapInv (Ito.rpath w₀) a (fwdMapInv (Ito.rpath w₁) s z)) '' H =
          fwdMapInv (Ito.rpath (catPath w₀ a w₁)) t '' H := by
        rw [← hts]
        exact image_congr (fun z hz => twoChart_inv_eq h₀ h00 h₁ h10 hz)
      rw [himg,
        QuantumZipper.RS.image_fwdMapInv_H (continuous_rpath_catPath h₀ h₁ h10)
          (rpath_catPath_zero h00) t.coe_nonneg] at hcomp
      ext z
      by_cases hzH : z ∈ H
      · have heq := Set.ext_iff.1 hcomp z
        simp only [Set.mem_sdiff, hzH, true_and] at heq
        exact not_iff_not.mp heq.symm
      · exact iff_of_false (fun hz => hzH hz.1) (fun hz => hzH hz.1)

end InteractingSLE.LoewnerConcat
