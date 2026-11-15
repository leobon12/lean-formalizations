/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCLPositivityPath
import InteractingSLE.Spec.Supplement.GB7aCmpLoewner

/-!
# The final interior approach in Lemma G8

Packet PROVE-G8-DET. Before the first swallowing of `1`, every real trace point is
strictly to the left of `1`. Consequently, a trace landing at a real `q > 1` has
a final interior segment outside the individual hull of a prefix in `B(0, 1/2)`.
This proves the approach part of `RLC.G8DetFrameStatement` without any new input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull IsForwardSol)

namespace InteractingSLE.RLC.G8Det

/-- A real trace point visited before `T` cannot still be alive at `T`. The trace
has interior points arbitrarily soon after the visit, whereas an alive real
point has a whole ball disjoint from the hull at `T`. -/
theorem not_alive_of_real_visit {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {t T : ℝ≥0} (htT : t < T)
    {y : ℝ} (hy : α t = y) :
    ¬ ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) T v := by
  rintro ⟨v, hv⟩
  obtain ⟨δ, hδ, hnot⟩ := GB7a.exists_ball_notMem_fwdHull
    (hw.comp continuous_real_toNNReal) T.coe_nonneg hv
  have hev : ∀ᶠ s in 𝓝[>] t, α s ∈ ball (y : ℂ) δ :=
    (hy ▸ hα.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      |>.eventually (ball_mem_nhds _ hδ)
  obtain ⟨b, htb, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  obtain ⟨s, hs, hsH⟩ := Supp9D.exists_mem_H_of_isGeneratingTrace hgen hw.continuousOn hw0
    (lt_min htb htT) ENNReal.coe_lt_top
  have hdist : ‖α s - y‖ < δ := by
    have hb : α s ∈ ball (y : ℂ) δ :=
      hsub (show s ∈ Ioo t b from ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩)
    simpa only [mem_ball, dist_eq_norm] using hb
  have hsK : α s ∈ fwdHull (fun s : ℝ => w s.toNNReal) s := by
    have htrace := isLoewnerTrace_of_isGeneratingTrace hgen
    rw [htrace.2.2 s s.coe_nonneg]
    exact ⟨hsH, Or.inl (subset_closure
      ⟨(s : ℝ), ⟨s.coe_nonneg, le_rfl⟩, by simp only [Real.toNNReal_coe]⟩)⟩
  exact hnot _ hdist (QuantumZipper.fwdHull_mono.1
    (show (s : ℝ) ≤ T from (hs.2.trans_le (min_le_right _ _)).le) hsK)

/-- Until the first swallow of `1`, no real trace point is at or to its right. -/
theorem re_lt_one_of_real_before_swallow {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {σ t : ℝ≥0}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (ht : t < σ)
    (him : (α t).im = 0) : (α t).re < 1 := by
  by_contra hle
  have hy : α t = ((α t).re : ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using him)
  obtain ⟨T, htT, hTσ⟩ := exists_between ht
  have hdead := not_alive_of_real_visit hα hw hw0 hgen htT hy
  have hdead1 := RLCJ.isSwallowedBy_of_le (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0)
    T.coe_nonneg one_pos (not_lt.1 hle) hdead
  exact hdead1 (hsw.2.1 T ⟨T.coe_nonneg, by exact_mod_cast hTσ⟩)

/-- A landing at `q > 1` has a final interval of interior tips outside the
individual filled hull of the retained small prefix. -/
theorem exists_final_approach {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hα : Continuous α) (hαH : ∀ t, 0 ≤ (α t).im) (hβ : Continuous β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r : ℝ≥0} {q : ℝ}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ)
    (hq : 1 < q) (hασ : α σ = q) (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2) :
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ u : ℝ≥0, t₀ < u → u < σ →
      1 < (α u).re ∧ α u ∈ H \ fillH (β '' Icc 0 r) ∧ α u ∉ β '' Icc 0 r := by
  have hσ : (0 : ℝ≥0) < σ := by exact_mod_cast hsw.1
  have hq' : 1 < (α σ).re := by simpa only [hασ, ofReal_re] using hq
  have hev : ∀ᶠ u in 𝓝[<] σ, 1 < (α u).re :=
    ((continuous_re.comp hα).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (lt_mem_nhds hq')
  obtain ⟨t₀, ht₀, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hσ).1 hev
  have hc : IsCompact (β '' Icc 0 r) := isCompact_Icc.image hβ
  have hball : β '' Icc 0 r ⊆ ball 0 (1 / 2) := by
    rintro _ ⟨t, ht, rfl⟩
    simpa only [mem_ball, dist_zero_right] using hsmall t ht.2
  refine ⟨t₀, ht₀, fun u htu huσ => ?_⟩
  have hre : 1 < (α u).re := hsub ⟨htu, huσ⟩
  have him : 0 < (α u).im := lt_of_le_of_ne (hαH u) fun h =>
    (re_lt_one_of_real_before_swallow hα hw hw0 hgen hsw huσ h.symm).not_gt hre
  have hnorm : 1 / 2 ≤ ‖α u‖ := by
    have := Complex.re_le_norm (α u)
    linarith only [hre, this]
  have hout := HalfPlaneSep.mem_H_diff_fillH_of_le_norm hc.isClosed
    (by norm_num : (0 : ℝ) < 1 / 2) hball him hnorm
  exact ⟨hre, hout, fun h => (not_lt_of_ge hnorm) (by
    simpa only [mem_ball, dist_zero_right] using hball h)⟩

/-- All real points of the retained union are left of `1` before its swallow. -/
theorem real_prefix_re_lt_one {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {σ u r : ℝ≥0}
    (hsw : RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ) (hu : u < σ)
    (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2) :
    ∀ z ∈ Restart.prefixSet α u β r, z.im = 0 → z.re < 1 := by
  rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) him
  · exact re_lt_one_of_real_before_swallow hα hw hw0 hgen hsw (ht.2.trans_lt hu) him
  · have hnorm := hsmall t ht.2
    exact (Complex.re_le_norm _).trans_lt (hnorm.trans (by norm_num))

/-- The untouched point `1` is adherent to the joint unbounded domain. This is
the existing compact-set real-collar lemma of Lemma 7.6. -/
theorem one_mem_closure_activeDomain {α β : ℝ≥0 → ℂ} {u r : ℝ≥0}
    (hα : Continuous α) (hβ : Continuous β)
    (hreal : ∀ z ∈ Restart.prefixSet α u β r, z.im = 0 → z.re < 1) :
    (1 : ℂ) ∈ closure (activeDomain α u β r) := by
  have hc : IsCompact (Restart.prefixSet α u β r) :=
    (isCompact_Icc.image hα).union (isCompact_Icc.image hβ)
  rw [Restart.activeDomain_eq hc.isClosed]
  exact Supp9D.mem_closure_of_isFreeAt
    (Sec7.Lemma76E.isFreeAt_of_forall_re_lt hc hreal) (by norm_num)

/-- Aux. 90 for the complete ordered pair itself, with no new planar argument. -/
theorem tips_mem_closure_of_opposite_hulls {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    {u r : ℝ≥0} :
    (α u ∈ H \ fillH (β '' Icc 0 r) →
      α u ∈ closure (activeDomain α u β r)) ∧
    (β r ∈ H \ fillH (α '' Icc 0 u) →
      β r ∈ closure (activeDomain α u β r)) := by
  obtain ⟨hα, hiα, hHα, hpα, hβ, hiβ, hHβ, hpβ, hord⟩ := hcop
  have hc : IsCompact (Restart.prefixSet α u β r) :=
    (isCompact_Icc.image hα).union (isCompact_Icc.image hβ)
  rw [Restart.activeDomain_eq hc.isClosed]
  exact Supp9D.aux90 ⟨hα, hiα, hHα, hpα, fun _ _ => rfl⟩
    ⟨hβ, hiβ, hHβ, hpβ, fun _ _ => rfl⟩ hord
    (by rw [hα0]; exact zero_im) (by rw [hβ0]; exact zero_im)
    (by rw [hα0, hβ0])

end InteractingSLE.RLC.G8Det
