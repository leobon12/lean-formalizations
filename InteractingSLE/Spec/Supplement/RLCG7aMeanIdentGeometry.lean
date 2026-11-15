/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenKernel
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# Boundary geometry for G7a's pocket mean identity

Packet PROVE-G7A-MEANIDENT. Accessible boundary points of a filled trace that
are not alive real points lie in the trace buffer. Their chart coordinates
lie between the two geometric images of the seed, including when some initial
marks have been swallowed.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI
open MartChar.RealFlow

/-- A non-alive boundary access lies in the buffer containing the trace range.
The filled hull itself need not lie in the buffer. -/
theorem extension_mem_buffer_of_not_alive {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {η : ℝ → ℂ}
    (hη : ContinuousOn η (Icc 0 t)) (hfill : fwdHull w t = fillH (η '' Icc 0 t))
    {N : Set ℂ} (h0N : (0 : ℂ) ∈ N) (hηN : ∀ s ∈ Icc 0 t, η s ∈ N)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv w t) H) (hFc : ContinuousOn F Hbar)
    (hFR : ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull w t) {x : ℝ}
    (hna : ¬ ∃ a : ℝ, F x = a ∧ ∃ u, IsForwardSol w (a : ℂ) t u) : F x ∈ N := by
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hxne : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact hxH
  have hFt : Tendsto F (𝓝[H] (x : ℂ)) (𝓝 (F x)) :=
    ((hFc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
  have hFΩ : ∀ᶠ z in 𝓝[H] (x : ℂ), F z ∈ H \ fwdHull w t := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFeq hz]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hz
  have hcl : F x ∈ closure (H \ fwdHull w t) := mem_closure_of_tendsto hFt hFΩ
  have hfr : F x ∈ frontier (H \ fwdHull w t) := by
    rw [(QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht).frontier_eq]
    exact ⟨hcl, hFR x (by simp)⟩
  have hFH : F x ∈ Hbar := by
    refine (isClosed_le continuous_const Complex.continuous_im).mem_of_tendsto hFt ?_
    filter_upwards [hFΩ] with z hz using hz.1.le
  have hηclosed : IsClosed (η '' Icc 0 t) := (isCompact_Icc.image_of_continuousOn hη).isClosed
  have hmemN : F x ∈ η '' Icc 0 t → F x ∈ N := by
    rintro ⟨s, hs, he⟩
    exact he ▸ hηN s hs
  rcases (show (0 : ℝ) ≤ (F x).im from hFH).lt_or_eq with hpos | hzero
  · have hK : F x ∈ fwdHull w t := by
      by_contra hK
      exact hFR x (by simp) ⟨hpos, hK⟩
    rw [hfill] at hK hcl
    exact hmemN (by
      rw [← hηclosed.closure_eq]
      exact YuanCorollary13.mem_closure_of_mem_fillH_of_mem_closure hK hcl)
  · have hFx : F x = ((F x).re : ℂ) := Complex.ext (by simp) (by simp [hzero.symm])
    by_cases h0 : (F x).re = 0
    · rw [hFx, h0, Complex.ofReal_zero]
      exact h0N
    by_cases hK : F x ∈ closure (fwdHull w t)
    · rw [hfill] at hK hfr
      exact hmemN (YuanCharacterisation.mem_of_mem_closure_of_mem_frontier
        hηclosed hzero.symm hK hfr)
    · exfalso
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hK
      have hd : Disjoint (ball ((F x).re : ℂ) r) (fwdHull w t) := by
        rw [← hFx]
        exact disjoint_left.2 fun z hz hzK => hball hz (subset_closure hzK)
      obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hw hw0 h0 ht hr hd
      exact hna ⟨(F x).re, hFx, u, hu⟩

/-- A non-alive boundary access is between the two geometric seed images. -/
theorem geom_seed_bounds_of_not_alive {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv w t) H) (hFc : ContinuousOn F Hbar) {x : ℝ}
    (hna : ¬ ∃ a : ℝ, F x = a ∧ ∃ u, IsForwardSol w (a : ℂ) t u) :
    geomL w t 0 ≤ x ∧ x ≤ geomR w t 0 := by
  constructor
  · by_contra hlt
    have hlt' : x < geomL w t 0 := not_le.1 hlt
    obtain ⟨a, -, ha, hga⟩ := FCAux79.exists_alive_gImg_eq hw.neg ht
      (show rightImg (fun s => -w s) 0 t < -x - w t by
        simp only [geomL, neg_zero] at hlt'; linarith)
    obtain ⟨u, hu, hut⟩ := FCAux79.exists_isForwardSol_of_alive hw.neg (by simp [hw0]) ht ha
    have hun := QuantumZipper.RS.isForwardSol_neg hu
    have he : (fun s => -(-w) s) = w := by funext s; exact neg_neg _
    rw [he, ← Complex.ofReal_neg] at hun
    have hval : -u t = (x : ℂ) := by
      rw [hut, hga]
      simp only [Pi.neg_apply]
      push_cast
      ring
    have hf := GB7a.extension_fwdMap_real hw hw0 ht hFeq hFc hun
    rw [Zhan.fwdMap_ofReal_eq hw ht hun, hval] at hf
    exact hna ⟨-a, by simpa only [Complex.ofReal_neg] using hf, _, hun⟩
  · by_contra hlt
    have hlt' : geomR w t 0 < x := not_le.1 hlt
    obtain ⟨a, -, ha, hga⟩ := FCAux79.exists_alive_gImg_eq hw ht
      (show rightImg w 0 t < x + w t by simp only [geomR] at hlt'; linarith)
    obtain ⟨u, hu, hut⟩ := FCAux79.exists_isForwardSol_of_alive hw hw0 ht ha
    have hval : u t = (x : ℂ) := by rw [hut, hga]; push_cast; ring
    have hf := GB7a.extension_fwdMap_real hw hw0 ht hFeq hFc hu
    rw [Zhan.fwdMap_ofReal_eq hw ht hu, hval] at hf
    exact hna ⟨a, hf, u, hu⟩

/-- The geometric image of a real mark, on its original side of the seed. -/
def geomImage (w : ℝ → ℝ) (t p : ℝ) : ℝ :=
  if p < 0 then geomL w t p else geomR w t p

/-- An alive real preimage determines its chart coordinate uniquely. -/
theorem chart_eq_of_extension_eq_of_alive {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv w t) H) (hFc : ContinuousOn F Hbar) {x a : ℝ}
    (hFa : F x = a) {u : ℝ → ℂ} (hu : IsForwardSol w (a : ℂ) t u) :
    u t = (x : ℂ) := by
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hxne : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact hxH
  have hFt : Tendsto F (𝓝[H] (x : ℂ)) (𝓝[H] (a : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hFa ▸
      ((hFc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFeq hz]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hz).1
  have hlim := (tendsto_fwdMap_of_isForwardSol hw ht hu).comp hFt
  have heq : (fun z => fwdMap w t (F z)) =ᶠ[𝓝[H] (x : ℂ)] id := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFeq hz, QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 ht hz]
    rfl
  exact tendsto_nhds_unique (hlim.congr' heq)
    (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- The order relative to a geometric mark is preserved at every alive real point.
This includes marks swallowed before `t`. -/
theorem geomImage_order_of_alive {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {a x p : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol w (a : ℂ) t u) (hut : u t = (x : ℂ))
    (hxp : x ≠ geomImage w t p) : x < geomImage w t p ↔ a < p := by
  have hpa : p ≠ a := by
    intro he
    subst p
    have hg : (geomImage w t a : ℂ) = u t := by
      unfold geomImage
      split_ifs with ha
      · exact (geomL_eq_fwdMap hw hw0 ht ha hu).trans (Zhan.fwdMap_ofReal_eq hw ht hu)
      · have ha0 : a ≠ 0 := by
          have hn := GB7a.ne_zero_of_isForwardSol hw0 ht hu
          exact fun h => hn (by rw [h, Complex.ofReal_zero])
        exact (geomR_eq_fwdMap hw hw0 ht (lt_of_le_of_ne (not_lt.1 ha) ha0.symm) hu).trans
          (Zhan.fwdMap_ofReal_eq hw ht hu)
    exact hxp (Complex.ofReal_injective (hg.trans hut)).symm
  rcases FCAux79.isForwardSol_real_cases hw hw0 ht hu with
    ⟨ha0, ha, hga⟩ | ⟨ha0, ha, hga⟩
  · have hxt : x = gImg w a t - w t := (Complex.ofReal_injective (hut.symm.trans hga))
    have hxpos : 0 < x := by
      rw [hxt]
      linarith [ha.lt_gImg hw ⟨ht, le_rfl⟩]
    by_cases hp : p < 0
    · rw [geomImage, ite_eq_left hp]
      have hg := geomL_nonpos hw ht p
      constructor <;> intro h <;> linarith
    · rw [geomImage, ite_eq_right hp] at hxp ⊢
      have hkey := FCAux79.rightImg_le_gImg_iff hw ht ha hpa
      constructor
      · intro h
        by_contra hnot
        have hlt : p < a := lt_of_le_of_ne (not_lt.1 hnot) hpa
        have hk := hkey.2 hlt
        simp only [geomR, hxt] at h
        linarith
      · intro h
        by_contra hnot
        have hk : rightImg w p t ≤ gImg w a t := by
          simp only [geomR, hxt] at hnot
          linarith
        exact (not_lt_of_gt h) (hkey.1 hk)
  · have hxt : x = -gImg (fun s => -w s) (-a) t - w t :=
      Complex.ofReal_injective (hut.symm.trans hga)
    have hxneg : x < 0 := by
      rw [hxt]
      have hg := ha.lt_gImg hw.neg ⟨ht, le_rfl⟩
      change -w t < gImg (fun s => -w s) (-a) t at hg
      linarith
    by_cases hp : p < 0
    · rw [geomImage, ite_eq_left hp] at hxp ⊢
      have hkey := FCAux79.rightImg_le_gImg_iff hw.neg ht ha
        (show -p ≠ -a from fun h => hpa (neg_injective h))
      constructor
      · intro h
        have hk : rightImg (fun s => -w s) (-p) t ≤ gImg (fun s => -w s) (-a) t := by
          simp only [geomL, hxt] at h
          linarith
        have hk' := hkey.1 hk
        linarith
      · intro h
        have hk := hkey.2 (show -p < -a by linarith)
        change rightImg (fun s => -w s) (-p) t ≤ gImg (fun s => -w s) (-a) t at hk
        have hle : x ≤ geomL w t p := by simp only [geomL, hxt]; linarith
        exact lt_of_le_of_ne hle hxp
    · rw [geomImage, ite_eq_right hp]
      have hg := geomR_nonneg hw ht p
      constructor <;> intro h <;> linarith

end InteractingSLE.Restart.FlowLocalityGen
