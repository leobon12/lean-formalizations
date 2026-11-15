/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PBranch

/-!
# Lemma 7.1's (CS), geometric half: the side of approach along the middle curve

Packet PROVE-LEMMA71P. In the setting `IsTSetting` at capacity time `t`, with `T` the curve time of the capacity stop:
the boundary transition `x ↦ lim g^γ_T(ψ_t⁻¹(y))` (`y → x`) from the chart of the active component to the Loewner map
of the stopped middle prefix is real on the middle chart points, strictly increasing on each side of the slit (its
Schwarz reflection has positive derivative, `R16.IsRealBoundaryConformal.deriv_schwarzReflect_pos`), and tends to `0`
at the tip (the tip lands on `γ(T)`, a single prime end of `γ([0, T])`). Hence (**`IsTSetting.exists_sign_tendsto`**)
the real limit of the centred map `g^γ_T ∘ ψ_t⁻¹` is negative on `(L_t − W_t, 0)` and positive on `(0, R_t − W_t)`:
the inverse chart approaches the middle curve from its left side on the left of the slit and from its right side on
the right (in the sense of `Lemma71N.exists_neg_tendsto_of_leftSideOf`, `Lemma613.exists_pos_tendsto_of_rightSideOf`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (schwarzReflect)
open Lemma71O (land)
open Lemma71C (IsSegCurve capLife capInv segDriver)

/-- On the real line a real-boundary-conformal map has a positive derivative (that of its Schwarz reflection). -/
theorem hasDerivAt_re_of_isRealBoundaryConformal {φ : ℂ → ℂ} {x r : ℝ} (h : R16.IsRealBoundaryConformal φ x r)
    (hr : 0 < r) : ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun v : ℝ => (φ v).re) d x := by
  have hx : ((x : ℝ) : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hd := (h.differentiableOn_schwarzReflect.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  refine ⟨(deriv (schwarzReflect φ) x).re, (h.deriv_schwarzReflect_pos hx).2, ?_⟩
  have e : (fun v : ℝ => (φ v).re) = fun v : ℝ => (schwarzReflect φ v).re := by
    funext v
    simp [schwarzReflect]
  rw [e]
  exact hd.real_of_complex

namespace IsTSetting

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ} {n : ℤ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ≥0}

/-- **The side of approach along the middle curve**: at every middle chart point `x ≠ 0`, the centred Loewner map of
the stopped middle prefix `γ([0, T])` along the inverse chart of the active component has a real limit, negative for
`x < 0` and positive for `x > 0`. -/
theorem exists_sign_tendsto (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wγ : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace Wγ ⊤ γ) {x : ℝ} (hxL : midL W t < x) (hxR : x < midR W t) (hx0 : x ≠ 0) :
    ∃ y : ℝ, (x < 0 → y < 0) ∧ (0 < x → 0 < y) ∧
      Tendsto (fun z => fwdMap (fun r : ℝ => Wγ r.toNNReal) hS.capT ((tChart c n W t).2.1 z)) (𝓝[H] (x : ℂ))
        (𝓝 (y : ℂ)) := by
  obtain ⟨hWc, hW0⟩ := rdriver_spec htr
  have hWγ := Lemma71O.continuous_of_isGeneratingTrace_top htr
  have hWγ0 : Wγ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htr (by simp)
  set q : ℝ := (hS.capT : ℝ) with hq
  have hq0 : 0 ≤ q := hS.capT.2
  set Tf : ℂ → ℂ := fun z => fwdMap (fun r : ℝ => Wγ r.toNNReal) q ((tChart c n W t).2.1 z) with hTf
  set φ : ℂ → ℂ := extendFrom H Tf with hφ
  have hCt := hS.subset_H_diff_fwdHull htr le_rfl
  have hηγ := isLoewnerTrace_of_isGeneratingTrace htr
  -- real limits at the middle points
  have hreal : ∀ z : ℝ, midL W t < z → z < midR W t → z ≠ 0 →
      ∃ v : ℂ, v.im = 0 ∧ Tendsto Tf (𝓝[H] (z : ℂ)) (𝓝 v) := fun z hzL hzR hz0 => by
    obtain ⟨σ, hσ, hT, -⟩ := hS.exists_land hzL hzR hz0
    exact Lemma71O.exists_real_tendsto_wall htr hWγ hWγ0 hS.hc' hCt (mem_Hbar_of_im_eq_zero (by simp)) hσ.le hT
  have hφz : ∀ z : ℝ, midL W t < z → z < midR W t → z ≠ 0 →
      Tendsto Tf (𝓝[H] (z : ℂ)) (𝓝 (((φ z).re : ℝ) : ℂ)) := fun z hzL hzR hz0 => by
    obtain ⟨v, hv, hT⟩ := hreal z hzL hzR hz0
    have hφv : φ z = v := extendFrom_eq (by rw [closure_H]; exact mem_Hbar_of_im_eq_zero (by simp)) hT
    rwa [hφv, ← eq_ofReal_re_of_im_eq_zero hv]
  -- the derivative on the middle points
  have hder : ∀ u : ℝ, midL W t < u → u < midR W t → u ≠ 0 →
      ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun v : ℝ => (φ v).re) d u := by
    intro u huL huR hu0
    set r := min (min (u - midL W t) (midR W t - u)) |u| with hr
    have hr0 : 0 < r := lt_min (lt_min (by linarith) (by linarith)) (abs_pos.2 hu0)
    refine hasDerivAt_re_of_isRealBoundaryConformal ?_ hr0
    refine Lemma71O.isRealBoundaryConformal_extendFrom hS.hc' rfl hCt
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWc hq0) (QuantumZipper.FwdHolo.injOn_fwdMap hWc hq0)
      (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hWc hq0 hz) fun z hz hz0 => ?_
    have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    have hd : |z.re - u| < r := by
      rw [hzx, mem_ball, Lemma71O.dist_ofReal_ofReal, Real.dist_eq] at hz; exact hz
    have h1 := lt_of_lt_of_le hd (min_le_left _ _)
    have h2 := lt_of_lt_of_le hd (min_le_right _ _)
    rw [abs_lt] at h1
    rw [hzx]
    exact hreal z.re (by linarith [min_le_left (u - midL W t) (midR W t - u), h1.1])
      (by linarith [min_le_right (u - midL W t) (midR W t - u), h1.2])
      (fun h => by rw [h, zero_sub, abs_neg] at h2; exact lt_irrefl _ h2)
  -- strictly increasing on each side
  have hmono : ∀ I : Set ℝ, I = Ioo (midL W t) 0 ∨ I = Ioo 0 (midR W t) →
      StrictMonoOn (fun v : ℝ => (φ v).re) I := by
    intro I hI
    have hIm : ∀ u ∈ I, midL W t < u ∧ u < midR W t ∧ u ≠ 0 := by
      have hmL := midL_nonpos hS.hW hS.ht0
      have hmR := midR_nonneg hS.hW hS.ht0
      rcases hI with rfl | rfl
      · exact fun u hu => ⟨hu.1, by linarith [hu.2], hu.2.ne⟩
      · exact fun u hu => ⟨by linarith [hu.1], hu.2, hu.1.ne'⟩
    have hconv : Convex ℝ I := by rcases hI with rfl | rfl <;> exact convex_Ioo _ _
    have hopen : IsOpen I := by rcases hI with rfl | rfl <;> exact isOpen_Ioo
    refine strictMonoOn_of_deriv_pos hconv (fun u hu => ?_) fun u hu => ?_
    · obtain ⟨d, -, hd⟩ := hder u (hIm u hu).1 (hIm u hu).2.1 (hIm u hu).2.2
      exact hd.continuousAt.continuousWithinAt
    · rw [hopen.interior_eq] at hu
      obtain ⟨d, hd0, hd⟩ := hder u (hIm u hu).1 (hIm u hu).2.1 (hIm u hu).2.2
      rw [hd.deriv]; exact hd0
  -- the limit at the tip
  have htip : Tendsto Tf (𝓝[H] (0 : ℂ)) (𝓝 0) := by
    have hland0 := tendsto_tChart_inv (t := t) hS.seg.frame hS.hη hS.hW hS.hW0 n
      (mem_Hbar_of_im_eq_zero (z := (0 : ℂ)) (by simp))
    have hF0 : extendFrom H (fwdMapInv W t) 0 = γ' (capInv γ' t) := by
      rw [ZhanGT4.extendFrom_zero_eq hS.hη hS.hW hS.hW0 t.coe_nonneg, hS.hηe t t.coe_nonneg le_rfl]
    rw [hF0, hS.seg.land_seg (Lemma71C.capInv_nonneg γ' t)] at hland0
    obtain ⟨v, hv, hFv, hT⟩ := Lemma71O.exists_tendsto_fwdMap_comp hηγ hWc hW0 hq0 hS.hc' hCt
      (mem_Hbar_of_im_eq_zero (z := (0 : ℂ)) (by simp)) hland0
    have hvim : v.im = 0 := Lemma71O.im_eq_zero_of_land hWc hW0 hq0 hv hFv
      (Lemma71O.notMem_H_diff_fwdHull htr le_rfl)
    have hvx : v = ((v.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hvim
    have hinj : InjOn (fun s : ℝ => γ s.toNNReal) (Icc 0 q) := fun s hs s' hs' h => by
      have := hS.seg.hγ.2.1 h
      rw [← Real.coe_toNNReal s hs.1, ← Real.coe_toNNReal s' hs'.1, this]
    have htipe : extendFrom H (fwdMapInv (fun r : ℝ => Wγ r.toNNReal) q) ((v.re : ℝ) : ℂ) =
        (fun s : ℝ => γ s.toNNReal) q := by
      rw [← hvx, hFv]
      show γ (κ (capInv γ' t)).toNNReal = γ (q.toNNReal)
      rw [hq, Real.toNNReal_coe]
      rfl
    have hre := eq_zero_of_extendFrom_eq_tip hηγ hWc hW0 hq0 hinj htipe
    rw [hvx, hre, ofReal_zero] at hT
    exact hT
  have hsmall : ∀ ε > 0, ∃ δ > 0, ∀ z : ℝ, midL W t < z → z < midR W t → z ≠ 0 → |z| < δ →
      |(φ z).re| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδT⟩ := Metric.tendsto_nhdsWithin_nhds.1 htip ε hε
    refine ⟨δ, hδ, fun z hzL hzR hz0 hzδ => ?_⟩
    have hT := hφz z hzL hzR hz0
    have := Lemma71O.nhdsWithin_H_ofReal_neBot z
    have hev : ∀ᶠ y in 𝓝[H] (z : ℂ), ‖Tf y‖ ≤ ε := by
      have hb : ball (0 : ℂ) δ ∈ 𝓝 (z : ℂ) := isOpen_ball.mem_nhds (by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hzδ)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hb] with y hy hyb
      have := hδT hy (by rwa [mem_ball] at hyb)
      rw [dist_zero_right] at this
      exact this.le
    have := le_of_tendsto hT.norm hev
    rwa [Complex.norm_real, Real.norm_eq_abs] at this
  refine ⟨(φ x).re, fun hneg => ?_, fun hpos => ?_, hφz x hxL hxR hx0⟩
  · have hmL : midL W t < 0 := hxL.trans hneg
    have hmono' := hmono _ (Or.inl rfl)
    have hle : ∀ w, x < w → w < 0 → (φ w).re ≤ 0 := by
      intro w hxw hw
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨δ, hδ, hδφ⟩ := hsmall ε hε
      set w' := max (w / 2) (-(δ / 2)) with hw'
      have hww' : w < w' := lt_max_of_lt_left (by linarith)
      have hw'0 : w' < 0 := max_lt (by linarith) (by linarith)
      have h1 := hmono' ⟨by linarith, hw⟩ ⟨by linarith, hw'0⟩ hww'
      have h2 := hδφ w' (by linarith) (by linarith [midR_nonneg hS.hW hS.ht0]) hw'0.ne (by
        rw [abs_of_neg hw'0]; linarith [le_max_right (w / 2) (-(δ / 2))])
      linarith [le_abs_self (φ w').re]
    have h1 := hmono' ⟨hxL, hneg⟩ ⟨by linarith, by linarith⟩ (show x < x / 2 by linarith)
    linarith [hle (x / 2) (by linarith) (by linarith)]
  · have hmono' := hmono _ (Or.inr rfl)
    have hge : ∀ w, 0 < w → w < x → 0 ≤ (φ w).re := by
      intro w hw hwx
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨δ, hδ, hδφ⟩ := hsmall ε hε
      set w' := min (w / 2) (δ / 2) with hw'
      have hw'w : w' < w := min_lt_of_left_lt (by linarith)
      have hw'0 : 0 < w' := lt_min (by linarith) (by linarith)
      have h1 := hmono' ⟨hw'0, by linarith⟩ ⟨hw, by linarith⟩ hw'w
      have h2 := hδφ w' (by linarith [midL_nonpos hS.hW hS.ht0]) (by linarith) hw'0.ne' (by
        rw [abs_of_pos hw'0]; linarith [min_le_right (w / 2) (δ / 2)])
      linarith [neg_abs_le (φ w').re]
    have h1 := hmono' ⟨by linarith, by linarith⟩ ⟨hpos, hxR⟩ (show x / 2 < x by linarith)
    linarith [hge (x / 2) (by linarith) (by linarith)]

end IsTSetting

end InteractingSLE.Sec7.Lemma71P
