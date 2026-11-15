/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelObst
import InteractingSLE.Spec.Sec5.GlueCondUnionImgBase
import InteractingSLE.Spec.Sec5.Prop49QExitMainNR
import InteractingSLE.Spec.Supplement.CounterflowNoReturnBack

/-!
# Base points of a nonsimple image hull

The real inverse boundary values at both ends of the base interval are zero, provided
the trace stays in the upper half-plane at positive times. No simplicity is needed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- A nonzero real inverse boundary value has its usual real forward image. -/
theorem eq_realFlow_of_extendFrom_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W T) x = r) :
    (r < 0 ∧ x = -gImg (fun s => -W s) (-r) T - W T) ∨
      (0 < r ∧ x = gImg W r T - W T) := by
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hη hηH hW hW0 hr hT
  have hxH : (x : ℂ) ∈ Hbar := by simp [Hbar]
  have he := eq_of_extendFrom_eq_of_isForwardSol hW hW0 hT hv hη hxH hF
  rcases isForwardSol_real_cases hW hW0 hT hv with ⟨hpos, -, hvT⟩ | ⟨hneg, -, hvT⟩
  · right
    refine ⟨hpos, ?_⟩
    rw [hvT] at he
    exact_mod_cast he
  · left
    refine ⟨hneg, ?_⟩
    rw [hvT] at he
    exact_mod_cast he

/-- A nonzero real inverse value occurs strictly outside the hull's base interval. -/
theorem outside_base_of_extendFrom_real_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W T) x = r) :
    (r < 0 ∧ x < chartAL W T) ∨ (0 < r ∧ chartAR W T < x) := by
  rcases eq_realFlow_of_extendFrom_of_mem_H hη hηH hW hW0 hT hr hF with
    ⟨hneg, he⟩ | ⟨hpos, he⟩
  · have hlt := GlueImg.rightImg_lt_gImg_of_lt hW.neg hT
      (alive_neg_of_mem_H hη hηH hW hW0 hT) le_rfl (neg_pos.2 hneg)
    have hlt' : rightImg (fun s => -W s) 0 T < gImg (fun s => -W s) (-r) T := hlt
    left
    refine ⟨hneg, ?_⟩
    rw [he, chartAL]
    linarith only [hlt']
  · have hlt := GlueImg.rightImg_lt_gImg_of_lt hW hT
      (alive_of_mem_H hη hηH hW hW0 hT) le_rfl hpos
    right
    refine ⟨hpos, ?_⟩
    rw [he, chartAR]
    linarith only [hlt]

/-- Both base points have inverse boundary value zero, even for a nonsimple trace. -/
theorem extendFrom_base_eq_zero_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    {x : ℝ} (hx : x = chartAL W T ∨ x = chartAR W T) :
    extendFrom H (fwdMapInv W T) x = 0 := by
  have hxL : chartAL W T ≤ x := by
    rcases hx with h | h
    · exact h.ge
    · rw [h]
      exact (chartAL_nonpos hW hT).trans (chartAR_nonneg hW hT)
  have hxR : x ≤ chartAR W T := by
    rcases hx with h | h
    · rw [h]
      exact (chartAL_nonpos hW hT).trans (chartAR_nonneg hW hT)
    · exact h.le
  have him : (extendFrom H (fwdMapInv W T) x).im = 0 := by
    rcases (GlueImg.extendFrom_im_nonneg hη hW hW0 hT x).eq_or_lt with he | hpos
    · exact he.symm
    · have hi := GlueImg.chartAL_lt_of_extendFrom_mem_H hη hW hW0 hT hpos
      rcases hx with h | h
      · exact False.elim (hi.1.ne' h)
      · exact False.elim (hi.2.ne h)
  have hreal : extendFrom H (fwdMapInv W T) x =
      ((extendFrom H (fwdMapInv W T) x).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  have hre : (extendFrom H (fwdMapInv W T) x).re = 0 := by
    by_contra hn
    rcases outside_base_of_extendFrom_real_of_mem_H hη hηH hW hW0 hT hn hreal with
      ⟨-, hlt⟩ | ⟨-, hlt⟩
    · exact (not_lt.2 hxL) hlt
    · exact (not_lt.2 hxR) hlt
  exact Complex.ext (by simpa using hre) (by simpa using him)

/-- Reflection preserves the continuous trace and its filled hulls. -/
theorem isLoewnerTrace_reflect_of_isLoewnerTrace (hη : IsLoewnerTrace W η) :
    IsLoewnerTrace (-W) (fun t => LP.reflectC (η t)) := by
  refine ⟨by change LP.reflectC (η 0) = 0; rw [hη.1, LP.reflectC_zero],
    LP.continuous_reflectC.comp_continuousOn hη.2.1, ?_⟩
  intro t ht
  rw [LP.fwdHull_neg, hη.2.2 t ht, ← LP.fillH_image_reflectC, image_image]

/-- A trace in the open half-plane has only the two base prime ends over zero. -/
theorem extendFrom_eq_zero_imp_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 < T)
    {x : ℝ} (hF : extendFrom H (fwdMapInv W T) x = 0) :
    x = chartAL W T ∨ x = chartAR W T := by
  have hNR : ∀ t ∈ Ioc (0 : ℝ) T, η t ≠ 0 :=
    fun t ht => ne_zero_of_mem_H (hηH t ht)
  have hxL : chartAL W T ≤ x := by
    by_contra hn
    have hh := (re_extendFrom_neg_of_lt_chartAL_of_mem_H hη hηH hW hW0 hT.le
      (lt_of_not_ge hn)).2
    rw [hF, zero_re] at hh
    exact (lt_irrefl _ hh)
  have hxR : x ≤ chartAR W T := by
    by_contra hn
    have hh := (re_extendFrom_pos_of_chartAR_lt_of_mem_H hη hηH hW hW0 hT.le
      (lt_of_not_ge hn)).2
    rw [hF, zero_re] at hh
    exact (lt_irrefl _ hh)
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · left
    by_contra hn
    have hx : chartAL W T < x := lt_of_le_of_ne hxL (Ne.symm hn)
    have hRη := isLoewnerTrace_reflect_of_isLoewnerTrace hη
    have hR0 : (-W) 0 = 0 := by simp only [Pi.neg_apply, hW0, neg_zero]
    have hRNR : ∀ t ∈ Ioc (0 : ℝ) T, LP.reflectC (η t) ≠ 0 := by
      intro t ht hn
      exact hNR t ht (LP.reflectC_injective (hn.trans LP.reflectC_zero.symm))
    have hRF := CfNoReturn.extendFrom_fwdMapInv_neg hη hW hW0 hT.le
      (x := (x : ℂ)) (by simp [Hbar])
    rw [LP.reflectC_ofReal, hF, LP.reflectC_zero] at hRF
    have hxR' : -x < rightImg (-W) 0 T - (-W) T := by
      change -x < rightImg (fun t => -W t) 0 T - -W T
      rw [chartAL] at hx
      linarith only [hx]
    exact Prop49Exit.extendFrom_ne_zero_of_noReturn hRη hW.neg hR0 hT hRNR
      (neg_pos.2 hneg) hxR' hRF
  · have hh := extendFrom_zero hη hW hW0 hT.le
    rw [hzero] at hF
    exact False.elim (hNR T ⟨hT, le_rfl⟩ (hh.symm.trans hF))
  · right
    by_contra hn
    exact Prop49Exit.extendFrom_ne_zero_of_noReturn hη hW hW0 hT hNR hpos
      (show x < rightImg W 0 T - W T from lt_of_le_of_ne hxR hn) hF

/-- Real inverse values away from zero identify their original real forward point. -/
theorem eq_re_fwdMap_of_extendFrom_eq_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W T) x = r) :
    x = (QuantumZipper.fwdMap W T r).re := by
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hη hηH hW hW0 hr hT
  have he := eq_of_extendFrom_eq_of_isForwardSol hW hW0 hT hv hη
    (show (x : ℂ) ∈ Hbar by simp [Hbar]) hF
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩, ← he, ofReal_re]

/-- The filled hull of an interior trace avoids every nonzero real point up to closure. -/
theorem ofReal_notMem_closure_fwdHull_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hT : 0 ≤ T) :
    ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull W T) := by
  have hfill : IsFilling (fwdHull W T) (η '' Icc 0 T) := by
    rw [hη.2.2 T hT]
    exact isFilling_fillH (isCompact_Icc.image_of_continuousOn
      (hη.2.1.mono Icc_subset_Ici_self))
  intro x hx
  refine GlueCond.ofReal_notMem_closure_of_isFilling hfill
    (fun _ hz => hz.1) (InteractingSLE.isBounded_fwdHull hW T)
    (hη.isCompact_image T).isClosed ?_ hx
  rintro y hy ⟨r, hr, he⟩
  rcases hr.1.eq_or_lt with h0 | hpos
  · rw [← h0, hη.1] at he
    exact hy (by exact_mod_cast he.symm)
  · have hh := hηH r ⟨hpos, hr.2⟩
    rw [he] at hh
    exact not_lt.2 (show (y : ℂ).im ≤ 0 by simp) hh

/-- The only possible closure point outside the hull is its starting point. -/
theorem closure_fwdHull_subset_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hT : 0 ≤ T) :
    ∀ z ∈ closure (fwdHull W T), z ∈ fwdHull W T ∨ z = 0 := by
  intro z hz
  have hzH : z ∈ Hbar := by
    rw [← closure_H]
    exact closure_mono (fun _ hv => hv.1) hz
  rcases (show 0 ≤ z.im from hzH).eq_or_lt with he | hpos
  · right
    have hreal : (z.re : ℂ) = z := Complex.ext rfl (by simp [he])
    have hre : z.re = 0 := by
      by_contra hn
      exact ofReal_notMem_closure_fwdHull_of_mem_H hη hηH hW hT z.re hn (hreal ▸ hz)
    rw [← hreal, hre, ofReal_zero]
  · exact Or.inl (CrossCond.Word49.closure_inter_H_subset_fwdHull hW hT ⟨hz, hpos⟩)

end InteractingSLE.Sec5.CrossRestart
