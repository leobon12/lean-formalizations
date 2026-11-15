/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKillMeas
import InteractingSLE.Spec.Sec5.Aux8Inf
import InteractingSLE.Spec.Sec7.Lemma71PinNull
import InteractingSLE.Spec.Supplement.GB6Disjoint
import InteractingSLE.Spec.Sec5.GlueCondUnionHull
import InteractingSLE.WangWu.ReverseContactMartGlue

/-!
# Lemma 4.7 in the chart `Q`: the image of the counterflow before its first contact is a killed curve

Packet PROVE-CFRESTART4, item D1 (deterministic part). In the chart `R` the counterflow `α` (driver `Wc`, a continuous
Loewner trace staying in `ℍ` at positive times; parameter `16/κ > 4`, **not simple**) is read in the chart
`Ψ = revChart Wf q = R ∘ f_q ∘ R` of `ℍ ∖ G`, `G = R(K_q)` the reflected flow line prefix. Before the first contact of
`α` with `G` (`WangWu.preContact α G`) the image `Ψ ∘ α` is a killed curve (`KernelQ.IsKilledCurve`):
**`isKilledCurve_imgCurve`**. The local drivers come from `Aux8Inf.exists_loewner_revChart_trace` (the relative
Loewner chain of the image hulls `Ψ(K′_u)`), whose filling clause identifies the image hulls with the filled image
prefixes; the separation of the closed hulls before contact is a hypothesis here (it follows from GB6's
`disjoint_closure_fwdHull_inv_image` on good samples).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu (imgCurve imgCurve_zero imgCurve_of_pos preContact Icc_subset_preContact exists_gt_forall_notMem
  negInv revChart revChart_mem_H isOpen_H_diff_negInv_fwdHull continuousOn_revChart tendsto_revChart_zero)

theorem H_diff_insert_zero (X : Set ℂ) : H \ insert 0 X = H \ X := by
  ext z
  simp only [Set.mem_sdiff, mem_insert_iff, not_or]
  constructor
  · rintro ⟨hz, -, hX⟩; exact ⟨hz, hX⟩
  · rintro ⟨hz, hX⟩
    refine ⟨hz, fun h => ?_, hX⟩
    rw [h] at hz
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)

theorem fillH_singleton_zero : fillH ({0} : Set ℂ) = ∅ := by
  rw [← Sec7.Lemma71S.fillH_empty]
  refine fillH_congr ?_
  rw [closure_singleton, closure_empty, empty_inter]
  ext z
  simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
  rintro rfl hz
  exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)

variable {Wf Wc : ℝ → ℝ} {q : ℝ} {α : ℝ → ℂ}

/-- **The image of the counterflow before its first contact with `G = R(K_q)` is a killed curve.** -/
theorem isKilledCurve_imgCurve (hWf : Continuous Wf) (hWf0 : Wf 0 = 0) (hq : 0 ≤ q)
    (hG : IsClosed (negInv '' fwdHull Wf q)) (hKq : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wf q))
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hα : IsLoewnerTrace Wc α) (hαH : ∀ u, 0 < u → α u ∈ H)
    (hdis : ∀ S ∈ preContact α (negInv '' fwdHull Wf q),
      Disjoint (closure (fwdHull Wc S)) (closure (negInv '' fwdHull Wf q))) :
    IsKilledCurve (imgCurve Wf q α) (preContact α (negInv '' fwdHull Wf q)) := by
  set G := negInv '' fwdHull Wf q with hGdef
  have hα0 : α 0 = 0 := hα.1
  have hαc : ContinuousOn α (Ici 0) := hα.2.1
  have hGH : G ⊆ H := fun z ⟨w, hw, e⟩ => e ▸ WangWu.negInv_mem_H hw.1
  have hmem : ∀ u ∈ preContact α G, 0 < u → α u ∈ H \ G := fun u hu hpos =>
    ⟨hαH u hpos, hu.2 u ⟨hu.1, le_rfl⟩⟩
  have h0P : (0 : ℝ) ∈ preContact α G := by
    refine ⟨le_rfl, fun u hu hu' => ?_⟩
    obtain rfl : u = 0 := le_antisymm hu.2 hu.1
    have := hGH hu'
    rw [hα0] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  -- continuity of the image curve on the pre-contact interval
  have hcont : ContinuousOn (imgCurve Wf q α) (preContact α G) := by
    intro u hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · rw [← h0, Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hR⟩ := Metric.tendsto_nhdsWithin_nhds.1 (tendsto_revChart_zero hWf hWf0 hq) ε hε
      obtain ⟨δ₂, hδ₂, hαδ⟩ := Metric.continuousWithinAt_iff.1 (hαc 0 self_mem_Ici) δ₁ hδ₁
      refine ⟨δ₂, hδ₂, fun {v} hv hvd => ?_⟩
      rw [imgCurve_zero, dist_zero_right]
      rcases hv.1.eq_or_lt with hv0 | hvpos
      · rw [← hv0, imgCurve_zero, norm_zero]; exact hε
      · rw [imgCurve_of_pos hvpos]
        have h1 := hαδ (mem_Ici.2 hv.1) hvd
        rw [hα0] at h1
        have h2 := hR (hmem v hv hvpos) h1
        rwa [dist_zero_right] at h2
    · have hcα : ContinuousAt α u := hαc.continuousAt (Ici_mem_nhds hpos)
      have hcR : ContinuousAt (revChart Wf q) (α u) :=
        (continuousOn_revChart hWf hq).continuousAt
          ((isOpen_H_diff_negInv_fwdHull hWf hq).mem_nhds (hmem u hu hpos))
      have hcA : ContinuousAt (fun v => revChart Wf q (α v)) u := hcR.comp hcα
      refine (hcA.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hpos] with v hv
      exact (imgCurve_of_pos hv).symm
  refine ⟨h0P, fun u hu => hu.1, fun S hS => Icc_subset_preContact hS, fun S hS => ?_, imgCurve_zero, hcont,
    fun u hu hpos => ?_, fun S hS hS0 => ?_⟩
  · obtain ⟨S', hSS', hS'⟩ := exists_gt_forall_notMem hG hαc hS.2
    exact ⟨S', ⟨(hS.1.trans hSS'.le), hS'⟩, hSS'⟩
  · rw [imgCurve_of_pos hpos]
    exact revChart_mem_H hWf hq (hmem u hu hpos)
  -- the local drivers: the relative Loewner chain of the image hulls
  have hsub : Icc 0 S ⊆ preContact α G := Icc_subset_preContact hS
  obtain ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK, hfill, -⟩ :=
    Aux8Inf.exists_loewner_revChart_trace (Wα := Wf) (Wβ := Wc) hWf hWf0 hq hKq hWc hWc0 hS0.le (hdis S hS)
      hα0 (hαc.mono Icc_subset_Ici_self) (fun t ht => Or.inl (hαH t ht.1)) fun t ht => by
        rw [hα.2.2 t ht.1.le]
        exact isFilling_fillH (isCompact_Icc.image_of_continuousOn (hαc.mono fun v hv => hv.1))
  have hτnn : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ τ t := fun t ht => by
    rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, hS0.le⟩ ht ht.1
  have hfill0 : fillH (α '' Icc 0 0) = ∅ := by
    rw [Icc_self, image_singleton, hα0, fillH_singleton_zero]
  -- the filled image prefixes are the image hulls
  have key : ∀ t ∈ Icc (0 : ℝ) S, fillH (imgCurve Wf q α '' Icc 0 t) = fwdHull W' (τ t) := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0, Icc_self, image_singleton, imgCurve_zero, fillH_singleton_zero, (hK 0 ⟨le_rfl, hS0.le⟩).2,
        hα.2.2 0 le_rfl, hfill0, image_empty]
    · have himg : imgCurve Wf q α '' Icc 0 t = insert 0 (revChart Wf q '' (α '' Icc 0 t ∩ H)) := by
        ext z
        constructor
        · rintro ⟨v, hv, rfl⟩
          rcases hv.1.eq_or_lt with hv0 | hvpos
          · rw [← hv0, imgCurve_zero]; exact mem_insert _ _
          · rw [imgCurve_of_pos hvpos]
            exact mem_insert_of_mem _ ⟨α v, ⟨⟨v, hv, rfl⟩, hαH v hvpos⟩, rfl⟩
        · rintro (rfl | ⟨w, ⟨⟨v, hv, rfl⟩, hwH⟩, rfl⟩)
          · exact ⟨0, ⟨le_rfl, ht.1⟩, imgCurve_zero⟩
          · rcases hv.1.eq_or_lt with hv0 | hvpos
            · rw [← hv0, hα0] at hwH
              exact absurd (show (0 : ℝ) < (0 : ℂ).im from hwH) (lt_irrefl _)
            · exact ⟨v, hv, imgCurve_of_pos hvpos⟩
      have hcpt : IsCompact (imgCurve Wf q α '' Icc 0 t) :=
        isCompact_Icc.image_of_continuousOn (hcont.mono fun v hv => hsub ⟨hv.1, hv.2.trans ht.2⟩)
      have hF : IsFilling (fwdHull W' (τ t)) (imgCurve Wf q α '' Icc 0 t) := by
        have h := hfill t ⟨hpos, ht.2⟩
        unfold IsFilling at h ⊢
        rwa [himg, H_diff_insert_zero]
      have h2 := (isFilling_iff_inter_H_eq_fillH hcpt.isBounded hcpt.isClosed).1 hF
      rw [← h2, inter_eq_left.2 (fun z hz => hz.1)]
  have hcap : EqOn (capClock (imgCurve Wf q α)) τ (Icc 0 S) := fun t ht => by
    have := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW'c hW'0 (hτnn t ht) (key t ht).symm
    simp only [capClock, this]
    ring
  refine ⟨W', hW'c, hW'0, by rw [hcap ⟨le_rfl, hS0.le⟩, hτ0], hτm.congr hcap.symm, hτc.congr hcap,
    fun t ht => ⟨by rw [hcap ht]; exact hτnn t ht, by rw [hcap ht, key t ht]⟩⟩

/-- **The counterflow image from generating traces**: for continuous drivers `wf` (flow) and `wc` (counterflow), both
started at `0`, with generating traces on `[0, ∞)` staying in `ℍ` at positive times, the image of the counterflow in
the chart `Ψ = revChart wf q` before its first contact with `R(K_q)` is a killed curve. -/
theorem isKilledCurve_imgCurve_of_traces {wf wc : ℝ≥0 → ℝ} {ηf ηc : ℝ≥0 → ℂ} (hwf : Continuous wf)
    (hwf0 : wf 0 = 0) (hηf : IsGeneratingTrace wf ⊤ ηf) (hηfH : ∀ t : ℝ≥0, 0 < t → ηf t ∈ H)
    (hwc : Continuous wc) (hwc0 : wc 0 = 0) (hηc : IsGeneratingTrace wc ⊤ ηc)
    (hηcH : ∀ t : ℝ≥0, 0 < t → ηc t ∈ H) (q : ℝ≥0) :
    IsKilledCurve (imgCurve (fun r : ℝ => wf r.toNNReal) q (fun s : ℝ => ηc s.toNNReal))
      (preContact (fun s : ℝ => ηc s.toNNReal) (negInv '' fwdHull (fun r : ℝ => wf r.toNNReal) q)) := by
  have hWf : Continuous fun r : ℝ => wf r.toNNReal := hwf.comp continuous_real_toNNReal
  have hWc : Continuous fun r : ℝ => wc r.toNNReal := hwc.comp continuous_real_toNNReal
  have hqT : ((q : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hH : ∀ r : ℝ≥0, 0 < r → r ≤ q → ηf r ∈ H := fun r hr _ => hηfH r hr
  refine isKilledCurve_imgCurve hWf (by simpa using hwf0) q.coe_nonneg
    (GlueCond.isClosed_image_negInv_fwdHull hWf hηf hqT hH)
    (fun x hx => GlueCond.ofReal_notMem_closure_fwdHull hWf hηf hqT hH hx) hWc (by simpa using hwc0)
    (isLoewnerTrace_of_isGeneratingTrace hηc) (fun u hu => hηcH _ (Real.toNNReal_pos.2 hu)) fun S hS => ?_
  have hS0 : 0 ≤ S := hS.1
  have hsep : ∀ t ∈ Icc (0 : ℝ≥0) q, ηf t ≠ 0 → -(ηf t)⁻¹ ∉ ηc '' Icc 0 S.toNNReal := by
    rintro t ht hne ⟨u, hu, hue⟩
    have ht0 : 0 < t := by
      refine pos_iff_ne_zero.2 fun h => hne ?_
      rw [h, hηf.1]
    have hmemK : ηf t ∈ fwdHull (fun r : ℝ => wf r.toNNReal) q :=
      CrossRestart.inter_H_subset_of_isFilling (hηf.2.2 q hqT) ⟨⟨t, ht, rfl⟩, hηfH t ht0⟩
    have huS : (u : ℝ) ≤ S := by
      have := NNReal.coe_le_coe.2 hu.2
      rwa [Real.coe_toNNReal _ hS0] at this
    refine hS.2 u ⟨u.coe_nonneg, huS⟩ ⟨ηf t, hmemK, ?_⟩
    show -(ηf t)⁻¹ = ηc (u : ℝ).toNNReal
    rw [Real.toNNReal_coe, hue]
  have h := Supp8.GB6.disjoint_closure_fwdHull_inv_image hηc hwc.continuousOn hwc0 hηf hwf.continuousOn hwf0
    (s := S.toNNReal) ENNReal.coe_lt_top hqT hsep
  rwa [Real.coe_toNNReal _ hS0] at h

/-- **A killed arc is a killed curve.** -/
theorem _root_.InteractingSLE.WangWu.IsKilledArc.isKilledCurve {γ : ℝ → ℂ} {P : Set ℝ}
    (hγ : WangWu.IsKilledArc γ P) : IsKilledCurve γ P where
  zero_mem := hγ.zero_mem
  nonneg := hγ.nonneg
  icc := hγ.icc
  exists_gt := hγ.exists_gt
  zero := hγ.zero
  cont := hγ.cont
  mem_H := hγ.mem_H
  localDriver S hS hS0 := by
    obtain ⟨W, hW, hW0, hc0, hm, hc, hK⟩ := hγ.exists_localDriver hS hS0
    refine ⟨W, hW, hW0, hc0, hm, hc, fun t ht => ⟨(hK t ht).1, ?_⟩⟩
    rw [(hK t ht).2, hγ.fillH_eq (hγ.icc S hS ht)]

/-- The vertical ray is a killed curve on `[0, ∞)`. -/
theorem isKilledCurve_vRay : IsKilledCurve WangWu.ImgWord.vRay (Ici 0) := WangWu.isKilledArc_vRay.isKilledCurve

end InteractingSLE.Sec5.CrossRestart.KernelQ
