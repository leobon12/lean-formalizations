/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailBookkeeping

/-!
# The orientation of two proper arcs with reverse ranges

Packet PROVE-WW-B27. Equality of the positive ranges under `z ↦ -1/z`
determines a continuous, strictly decreasing, onto height map. Thus the reverse
prefixes are forward tails and the positive rational reverse times give dense heights.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.WangWu.SeedTail

/-- Inversion preserves closed sets that contain its exceptional point. -/
theorem isClosed_image_negInv_of_zero_mem {S : Set ℂ} (hS : IsClosed S) (h0 : (0 : ℂ) ∈ S) :
    IsClosed (negInv '' S) := by
  apply isOpen_compl_iff.1
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz0 : z ≠ 0 := by
    intro he
    exact hz ⟨0, h0, by simp only [negInv, inv_zero, neg_zero, he]⟩
  have hRz : negInv z ∉ S := fun h => hz ⟨negInv z, h, negInv_negInv z⟩
  have hn := (continuousAt_negInv hz0).preimage_mem_nhds (hS.isOpen_compl.mem_nhds hRz)
  refine mem_of_superset hn ?_
  rintro w hw ⟨v, hv, rfl⟩
  exact hw (by simpa only [mem_preimage, negInv_negInv] using hv)

/-- A positive-time continuous curve visits an open set at a positive rational
time whenever it visits that set at a positive real time. -/
theorem exists_rat_of_continuousAt {f : ℝ → ℂ} {s : ℝ} (hs : 0 < s)
    (hc : ContinuousAt f s) {U : Set ℂ} (hU : IsOpen U) (hsU : f s ∈ U) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ f q ∈ U := by
  have hn := inter_mem (Ioi_mem_nhds hs) (hc.preimage_mem_nhds (hU.mem_nhds hsU))
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hn
  obtain ⟨q, hlq, hqr⟩ := exists_rat_btwn (hl.trans hr)
  exact ⟨q, hsub ⟨hlq, hqr⟩⟩

/-- The hitting-code range identity also determines the positive reverse range,
although the reflected reverse line is discontinuous at time zero. -/
theorem image_Ioi_eq_of_hitCode {β γ : ℝ → ℂ} (hβ : IsProperArc β) (hγ : IsProperArc γ)
    (hcode : hitCode β = hitCode (fun s => negInv (γ s))) :
    β '' Ioi 0 = negInv '' (γ '' Ioi 0) := by
  classical
  have hzero : (0 : ℂ) ∈ arcRange γ := ⟨0, self_mem_Ici, hγ.zero⟩
  have hSc : IsClosed (negInv '' arcRange γ) :=
    isClosed_image_negInv_of_zero_mem hγ.isClosed_arcRange hzero
  have hsub : arcRange β ⊆ negInv '' arcRange γ := by
    intro z hz
    by_contra hn
    obtain ⟨i, hiU, hi⟩ := (arcRange_inter_nonempty_iff_hitCode hβ.cont hSc.isOpen_compl).1 ⟨z, hz, hn⟩
    rw [hcode, hitCode] at hi
    split_ifs at hi with hex
    · obtain ⟨q, hq, hqi⟩ := hex
      exact hiU hqi ⟨γ q, ⟨q, hq, rfl⟩, rfl⟩
    · norm_num at hi
  have hsub' : negInv '' arcRange γ ⊆ arcRange β := by
    rintro z ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    by_cases hs0 : s = 0
    · rw [hs0, hγ.zero]
      exact ⟨0, self_mem_Ici, by simp only [negInv, inv_zero, neg_zero, hβ.zero]⟩
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      by_contra hn
      let U := (arcRange β)ᶜ
      have hU : IsOpen U := hβ.isClosed_arcRange.isOpen_compl
      obtain ⟨i, hi, hiU⟩ := exists_ratBall_subset hU hn
      have hc : ContinuousAt (fun t => negInv (γ t)) s :=
        (continuousAt_negInv (ne_zero_of_mem_H (hγ.mem_H s hspos))).comp
          ((hγ.cont s hs).continuousAt (Ici_mem_nhds hspos))
      obtain ⟨q, hq, hqi⟩ := exists_rat_of_continuousAt hspos hc Metric.isOpen_ball hi
      have hci : hitCode (fun t => negInv (γ t)) i = 1 := by
        exact ite_eq_left (show ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ negInv (γ q) ∈ ratBall i from ⟨q, hq.le, hqi⟩)
      rw [← hcode] at hci
      obtain ⟨_, hw, hwU⟩ := (arcRange_inter_nonempty_iff_hitCode hβ.cont hU).2 ⟨i, hiU, hci⟩
      exact hwU hw
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    change 0 < s at hs
    obtain ⟨_, ⟨t, ht, rfl⟩, he⟩ := hsub ⟨s, hs.le, rfl⟩
    refine ⟨γ t, ⟨t, mem_Ioi.2 (lt_of_le_of_ne ht ?_), rfl⟩, he⟩
    intro he0
    rw [← he0, hγ.zero] at he
    exact ne_zero_of_mem_H (hβ.mem_H s hs) (by simpa only [negInv, inv_zero, neg_zero] using he.symm)
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    change 0 < s at hs
    obtain ⟨t, ht, he⟩ := hsub' ⟨γ s, ⟨s, hs.le, rfl⟩, rfl⟩
    refine ⟨t, mem_Ioi.2 (lt_of_le_of_ne ht ?_), he⟩
    intro he0
    rw [← he0, hβ.zero] at he
    exact ne_zero_of_mem_H (negInv_mem_H (hγ.mem_H s hs)) he.symm

/-- Reverse equality of positive ranges determines the reverse orientation. -/
theorem exists_isTailReversal {β γ : ℝ → ℂ} (hβ : IsProperArc β) (hγ : IsProperArc γ)
    (hR : β '' Ioi 0 = negInv '' (γ '' Ioi 0)) :
    ∃ a : ℝ → ℝ, IsTailReversal β γ a := by
  let a : ℝ → ℝ := fun s => Function.invFunOn β (Ici 0) (negInv (γ s))
  have hex : ∀ s, 0 < s → negInv (γ s) ∈ β '' Ici 0 := by
    intro s hs
    exact image_mono Ioi_subset_Ici_self (hR.symm ▸ ⟨γ s, ⟨s, hs, rfl⟩, rfl⟩)
  have ha0 : ∀ s, 0 < s → 0 ≤ a s := fun s hs => Function.invFunOn_mem (hex s hs)
  have hae : ∀ s, 0 < s → β (a s) = negInv (γ s) := fun s hs => Function.invFunOn_eq (hex s hs)
  have hap : ∀ s, 0 < s → 0 < a s := by
    intro s hs
    refine lt_of_le_of_ne (ha0 s hs) ?_
    intro he
    have he' := hae s hs
    rw [← he, hβ.zero] at he'
    exact ne_zero_of_mem_H (negInv_mem_H (hγ.mem_H s hs)) he'.symm
  have hai : InjOn a (Ioi 0) := by
    intro s hs t ht he
    change 0 < s at hs
    change 0 < t at ht
    apply hγ.inj hs.le ht.le
    apply negInv_involutive.injective
    rw [← hae s hs, ← hae t ht, he]
  have hacI : ∀ l r : ℝ, 0 < l → ContinuousOn a (Icc l r) := by
    intro l r hl
    have hd : ContinuousOn (fun s => negInv (γ s)) (Icc l r) :=
      continuousOn_negInv.comp (hγ.cont.mono fun s hs => (hl.trans_le hs.1).le)
        (fun s hs => hγ.mem_H s (hl.trans_le hs.1))
    rw [continuousOn_iff_isClosed]
    intro F hF
    refine ⟨Icc l r ∩ (fun s => negInv (γ s)) ⁻¹' (β '' (F ∩ Ici 0)),
      hd.preimage_isClosed_of_isClosed isClosed_Icc
        (hβ.isClosed_image (hF.inter isClosed_Ici) inter_subset_right), ?_⟩
    ext s
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hsF, hs⟩
      exact ⟨⟨hs, a s, ⟨hsF, ha0 s (hl.trans_le hs.1)⟩, hae s (hl.trans_le hs.1)⟩, hs⟩
    · rintro ⟨⟨-, t, ⟨htF, ht0⟩, he⟩, hs⟩
      have hat : a s = t := hβ.inj (ha0 s (hl.trans_le hs.1)) ht0
        ((hae s (hl.trans_le hs.1)).trans he.symm)
      exact ⟨hat.symm ▸ htF, hs⟩
  have hac : ContinuousOn a (Ioi 0) := by
    intro s hs
    change 0 < s at hs
    exact ((hacI (s / 2) (s + 1) (by linarith)).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt
  have hnorm : Tendsto (fun s => ‖negInv (γ s)‖) (𝓝[>] 0) atTop := by
    have hc : Tendsto (fun s => ‖γ s‖) (𝓝[>] 0) (𝓝 0) := by
      have hc := ((hγ.cont 0 self_mem_Ici).mono Ioi_subset_Ici_self).norm
      change Tendsto (fun s => ‖γ s‖) (𝓝[>] 0) (𝓝 ‖γ 0‖) at hc
      simpa only [hγ.zero, norm_zero] using hc
    have hc' : Tendsto (fun s => ‖γ s‖) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hc, by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact norm_pos_iff.2 (ne_zero_of_mem_H (hγ.mem_H s hs))⟩
    simpa only [norm_negInv, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hc'
  have halim : Tendsto a (𝓝[>] 0) atTop := by
    refine tendsto_atTop.2 fun M => ?_
    let M' := max M 0
    have hbnd := (isCompact_Icc.image_of_continuousOn
      (hβ.cont.mono (show Icc 0 M' ⊆ Ici 0 from Icc_subset_Ici_self))).isBounded
    obtain ⟨K, hK⟩ := hbnd.exists_norm_le
    filter_upwards [hnorm.eventually (eventually_gt_atTop K), self_mem_nhdsWithin] with s hKs hs
    by_contra hle
    have has : a s ∈ Icc 0 M' := ⟨ha0 s hs, (lt_of_not_ge hle).le.trans (le_max_left _ _)⟩
    have hbound := hK (β (a s)) ⟨a s, has, rfl⟩
    rw [hae s hs] at hbound
    exact (not_lt_of_ge hbound) hKs
  have haa : StrictAntiOn a (Ioi 0) := by
    intro s hs t ht hst
    change 0 < s at hs
    change 0 < t at ht
    have hev : {r | 0 < r ∧ r < s ∧ a t < a r} ∈ 𝓝[>] 0 :=
      inter_mem self_mem_nhdsWithin (inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs))
        (halim.eventually (eventually_gt_atTop (a t))))
    obtain ⟨r, hr, hrs, har⟩ := Filter.Eventually.exists hev
    have hsub : Icc r t ⊆ Ioi 0 := fun u hu => hr.trans_le hu.1
    have hanti := ContinuousOn.strictAntiOn_of_injOn_Icc (hrs.trans hst).le har.le
      (hac.mono hsub) (hai.mono hsub)
    exact hanti ⟨hrs.le, hst.le⟩ ⟨(hrs.trans hst).le, le_rfl⟩ hst
  refine ⟨a, hac, haa, hap, ?_, hae⟩
  intro b hb
  change 0 < b at hb
  have hbR : β b ∈ negInv '' (γ '' Ioi 0) := hR ▸ ⟨b, hb, rfl⟩
  obtain ⟨_, ⟨s, hs, rfl⟩, he⟩ := hbR
  exact ⟨s, hs, hβ.inj (ha0 s hs) hb.le ((hae s hs).trans he)⟩

end InteractingSLE.WangWu.SeedTail
