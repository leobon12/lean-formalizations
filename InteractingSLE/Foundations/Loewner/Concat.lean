import InteractingSLE.Foundations.Loewner.ConcatTransport
import InteractingSLE.Foundations.Loewner.TraceClose
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Sec7.StripSideHeightProb

/-!
# Concatenating two continuous generating Loewner traces

The continuation is read through the continuous boundary extension of the centered inverse
prefix map. Thus this extension already incorporates the translation by the prefix driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.Sec7.StripSideHeightProb

namespace InteractingSLE.LoewnerConcat

variable {w₀ w₁ : ℝ≥0 → ℝ} {η₀ η₁ : ℝ≥0 → ℂ} {a : ℝ≥0}

/-- The joined trace, using the centered inverse prefix map. -/
def joinedTrace (w₀ : ℝ≥0 → ℝ) (η₀ : ℝ≥0 → ℂ) (a : ℝ≥0)
    (η₁ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  if t ≤ a then η₀ t else extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ (t - a))

theorem joinedTrace_of_le {t : ℝ≥0} (ht : t ≤ a) :
    joinedTrace w₀ η₀ a η₁ t = η₀ t := by
  simp only [joinedTrace, ht, ↓reduceIte]

theorem joinedTrace_add {s : ℝ≥0} (hs : 0 < s) :
    joinedTrace w₀ η₀ a η₁ (a + s) =
      extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ s) := by
  have h : ¬ a + s ≤ a := not_le.2 (lt_add_of_pos_right a hs)
  simp only [joinedTrace, h, ↓reduceIte, add_tsub_cancel_left]

theorem continuousOn_prefix (hη : IsGeneratingTrace w₀ a η₀) :
    ContinuousOn (fun t : ℝ => η₀ t.toNNReal) (Icc 0 (a : ℝ)) := by
  refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun t ht => ?_
  exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)

/-- A finite frozen generating trace, read on real times, generates before its horizon. -/
theorem isLoewnerTraceLT_prefix (hη : IsGeneratingTrace w₀ a η₀) :
    IsLoewnerTraceLT (Ito.rpath w₀) a (fun t : ℝ => η₀ t.toNNReal) := by
  refine ⟨by simpa only [Real.toNNReal_zero] using hη.1,
    (continuousOn_prefix hη).mono Ico_subset_Icc_self, fun t ht hta => ?_⟩
  have ht' : (t.toNNReal : ℝ≥0∞) < a := by
    rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht]
    exact hta
  have hc : IsCompact (η₀ '' Icc 0 t.toNNReal) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht'.le)
  have hf := hη.2.2 t.toNNReal ht'
  rw [Real.coe_toNNReal _ ht] at hf
  rw [image_toNNReal_Icc η₀ ht]
  exact (fillH_eq_iff_isFilling_of_isClosed hc.isBounded hc.isClosed
    (QuantumZipper.fwdHull_mono.2 _)).1 hf

/-- The inverse prefix map has a continuous extension to the closed half-plane, including at
the final prefix time (where the definition of a generating trace only specifies continuity). -/
theorem prefix_boundary (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (hη : IsGeneratingTrace w₀ a η₀) :
    HasBdryLimits (fwdMapInv (Ito.rpath w₀) a) ∧
      extendFrom H (fwdMapInv (Ito.rpath w₀) a) 0 = η₀ a := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  rcases eq_or_lt_of_le a.coe_nonneg with ha | ha
  · have ha' : a = 0 := NNReal.coe_eq_zero.1 ha.symm
    subst a
    have hb : HasBdryLimits (fwdMapInv (Ito.rpath w₀) 0) := by
      intro x hx
      refine ⟨x, (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (fwdMapInv_zero_time hW hW0 hz).symm
    refine ⟨hb, ?_⟩
    rw [hη.1]
    apply extendFrom_eq (by rw [closure_H]; exact zero_mem_Hbar)
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (fwdMapInv_zero_time hW hW0 hz).symm
  · have hc := continuousOn_prefix hη
    have hLT := isLoewnerTraceLT_prefix hη
    refine ⟨TraceClose.hasBdryLimits_of_isLoewnerTraceLT hLT hW hW0 ha hc, ?_⟩
    simpa only [Real.toNNReal_coe] using TraceClose.extendFrom_zero_eq hLT hW hW0 ha hc

theorem continuous_joinedTrace (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ a η₀) (hη₁ : IsGeneratingTrace w₁ ⊤ η₁)
    (hH : ∀ s, 0 < s → η₁ s ∈ H) : Continuous (joinedTrace w₀ η₀ a η₁) := by
  obtain ⟨hb, htip⟩ := prefix_boundary h₀ h00 hη₀
  have hc₁ : Continuous η₁ := continuousOn_univ.1
    (hη₁.2.1.mono (fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top))
  have hbar : ∀ s, η₁ s ∈ Hbar := by
    intro s
    rcases eq_or_lt_of_le (show 0 ≤ s from bot_le) with hs | hs
    · rw [← hs, hη₁.1]; exact zero_mem_Hbar
    · exact H_subset_Hbar (hH s hs)
  have hleft : Continuous (fun t : ℝ≥0 => η₀ (min t a)) :=
    hη₀.2.1.comp_continuous (continuous_id.min continuous_const)
      (fun _ => ENNReal.coe_le_coe.2 (min_le_right _ _))
  have hright : Continuous (fun t : ℝ≥0 =>
      extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ (t - a))) :=
    hb.continuousOn.comp_continuous (hc₁.comp (continuous_id.sub continuous_const))
      (fun t => hbar (t - a))
  have hc := Continuous.if_le hleft hright continuous_id (continuous_const (y := a))
    (fun t (ht : t = a) => by rw [ht, min_self, tsub_self, hη₁.1, htip])
  refine hc.congr fun t => ?_
  by_cases ht : t ≤ a
  · simp only [joinedTrace, id_eq, ht, ↓reduceIte, min_eq_left ht]
  · simp only [joinedTrace, id_eq, ht, ↓reduceIte]

/-- The part of the joined path inside the prefix domain is exactly the inverse image of
the positive-time continuation. -/
theorem joinedTrace_inter_domain (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (hη₁ : IsGeneratingTrace w₁ ⊤ η₁)
    (hH : ∀ s, 0 < s → η₁ s ∈ H)
    (hK : fwdHull (Ito.rpath w₀) a = fillH (η₀ '' Icc 0 a)) (s : ℝ≥0) :
    (joinedTrace w₀ η₀ a η₁ '' Icc 0 (a + s)) ∩ (H \ fwdHull (Ito.rpath w₀) a) =
      fwdMapInv (Ito.rpath w₀) a '' ((η₁ '' Icc 0 s) ∩ H) := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hF : ∀ z ∈ H, extendFrom H (fwdMapInv (Ito.rpath w₀) a) z =
      fwdMapInv (Ito.rpath w₀) a z := fun z hz =>
    extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 a.coe_nonneg) hz
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    by_cases hta : t ≤ a
    · rw [joinedTrace_of_le hta] at hz
      exact False.elim (hz.2 (hK ▸ ⟨hz.1, Or.inl (subset_closure ⟨t, ⟨ht.1, hta⟩, rfl⟩)⟩))
    · have hp : 0 < t - a := tsub_pos_iff_lt.2 (not_le.1 hta)
      have heq : joinedTrace w₀ η₀ a η₁ t = fwdMapInv (Ito.rpath w₀) a (η₁ (t - a)) := by
        simp only [joinedTrace, hta, ↓reduceIte]
        exact hF _ (hH _ hp)
      exact ⟨η₁ (t - a), ⟨⟨t - a, ⟨bot_le,
        tsub_le_iff_right.2 (by simpa only [add_comm] using ht.2)⟩, rfl⟩,
        hH _ hp⟩, heq.symm⟩
  · rintro ⟨v, ⟨⟨t, ht, rfl⟩, hvH⟩, rfl⟩
    have htpos : 0 < t := by
      by_contra h
      have ht0 : t = 0 := le_antisymm (not_lt.1 h) bot_le
      rw [ht0, hη₁.1] at hvH
      exact lt_irrefl 0 (show 0 < (0 : ℂ).im from hvH)
    refine ⟨⟨a + t, ⟨bot_le, add_le_add_right ht.2 a⟩, ?_⟩,
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 a.coe_nonneg hvH⟩
    rw [joinedTrace_add htpos, hF _ hvH]

/-- **Loewner concatenation.** A closed continuous generating prefix followed by a generating
trace that stays in `ℍ` generates the concatenated driver. -/
theorem isGeneratingTrace_catPath (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ a η₀) (hη₁ : IsGeneratingTrace w₁ ⊤ η₁)
    (hH : ∀ s, 0 < s → η₁ s ∈ H) :
    IsGeneratingTrace (catPath w₀ a w₁) ⊤ (joinedTrace w₀ η₀ a η₁) := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hV : Continuous (Ito.rpath w₁) := h₁.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hc := continuous_joinedTrace h₀ h00 hη₀ hη₁ hH
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
      · rw [show t = 0 + t by rw [zero_add], joinedTrace_add ht, NNReal.coe_zero,
          extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 le_rfl) (hH t ht),
          fwdMapInv_zero_time hW hW0 (hH t ht)]
        rw [zero_add]
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
      have hPB := joinedTrace_inter_domain h₀ h00 hη₁ hH hK s
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
