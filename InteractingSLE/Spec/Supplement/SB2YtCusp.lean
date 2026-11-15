/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GCusp
import InteractingSLE.Spec.Supplement.SB2YtFib

/-!
# SB2(1)'s `cusp` field without the interior-tip hypothesis

Packet PROVE-T14-SB2DRV (round 13). **`cusp_of_isSB2RelChain_noTip`**: `cusp_of_isSB2RelChain` (`SB2GCusp`) without
its hypothesis `γ(s) ∈ ℍ`. That hypothesis entered twice: the largest nonnegative real point of `γ([0, s])` was not the
tip, and a left landing at the tip was excluded. When the tip is real, both are fibres of the tip, and the real
fibre of the tip is the tip coordinate `0` (`eq_zero_of_extendFrom_eq_tip`), so they add no exceptional point.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open scoped NNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C
open WangWu (chartAL chartAR)
open Supp8.BHMean (jointInv)
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

section CuspNoTip

variable {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ}

/-- **SB2(1)'s cusp field without the interior-tip hypothesis.** -/
theorem cusp_of_isSB2RelChain_noTip {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (htL : β' tL = realMin (p '' Icc 0 1)) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s)) (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀)
    (hwt : fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal))) :
    {x : ℝ | x ∈ Ico (chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        (chartAR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) ∧
      extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∈
        closure (fillH (p '' Icc 0 1)) ∧
      ¬ ∃ r > 0, ∀ᶠ y in 𝓝[H] (x : ℂ), jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s) y ∈
        freeNear (fillH (p '' Icc 0 1)) (fwdHull w ((tL : ℝ) + s))
          (extendFrom H (jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ)) r}.Finite := by
  have hch' := hch
  obtain ⟨hWr, hWr0, hηr, hc0, hcm, hcc, hKK⟩ := hch'
  set γℝ : ℝ → ℂ := fun r : ℝ => γ r.toNNReal with hγℝ
  set u := capClock γℝ s with hudef
  set F := extendFrom H (fwdMapInv Wr u) with hF
  have hsI : s ∈ Icc 0 S₀ := ⟨hs.1.le, hs.2⟩
  obtain ⟨hu0, hηu, hK, hIn, -⟩ := hKK s hsI
  have hupos : 0 < u := by
    have := hcm ⟨le_rfl, hs.1.le.trans hs.2⟩ hsI hs.1
    rwa [hc0] at this
  -- trace times of the points of `γ([0, s])`
  have hclock : ∀ r : ℝ≥0, r ≤ s.toNNReal → 0 ≤ capClock γℝ r ∧ ηr (capClock γℝ r) = γ r ∧
      (r < s.toNNReal → capClock γℝ r < u) := by
    intro r hr
    have hrs : (r : ℝ) ≤ s := (Real.le_toNNReal_iff_coe_le hs.1.le).1 hr
    obtain ⟨h1, h2, -⟩ := hKK r ⟨r.coe_nonneg, hrs.trans hs.2⟩
    refine ⟨h1, by rw [h2, Real.toNNReal_coe], fun hlt => ?_⟩
    have hlt' : (r : ℝ) < s := Real.lt_toNNReal_iff_coe_lt.1 hlt
    exact hcm ⟨r.coe_nonneg, hrs.trans hs.2⟩ hsI hlt'
  have hinj : InjOn ηr (Icc 0 u) := by
    have hivt := intermediate_value_Icc hs.1.le (hcc.mono (Icc_subset_Icc_right hs.2))
    rw [hc0] at hivt
    intro ρ₁ h₁ ρ₂ h₂ he
    obtain ⟨t₁, ht₁, rfl⟩ := hivt h₁
    obtain ⟨t₂, ht₂, rfl⟩ := hivt h₂
    rw [(hKK t₁ ⟨ht₁.1, ht₁.2.trans hs.2⟩).2.1, (hKK t₂ ⟨ht₂.1, ht₂.2.trans hs.2⟩).2.1] at he
    have h := hγ.2.1 he
    rw [Real.toNNReal_eq_toNNReal_iff ht₁.1 ht₂.1] at h
    rw [h]
  -- the extreme nonnegative real point
  obtain ⟨rM, hrMs, hrMim, hrMre, hmax⟩ := exists_realMax hγ hγ0 s.toNNReal
  have hM : γ rM = (((γ rM).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hrMim])
  obtain ⟨hρM0, hηM, hρM⟩ := hclock rM hrMs
  obtain ⟨hρ00, hη0, hρ0⟩ := hclock 0 zero_le
  have hspos : (0 : ℝ≥0) < s.toNNReal := Real.toNNReal_pos.2 hs.1
  have hcs : capClock γℝ ((s.toNNReal : ℝ≥0) : ℝ) = u := by rw [Real.coe_toNNReal _ hs.1.le]
  -- a nonnegative fibre point at the tip would be the tip coordinate (`eq_zero_of_extendFrom_eq_tip`)
  have hfinPos : {x : ℝ | 0 < x ∧ F x = ηr (capClock γℝ rM)}.Finite := by
    rcases lt_or_eq_of_le hrMs with hrMlt | hrMeq
    · exact (subsingleton_fibre_pos hηr hWr hWr0 hρM0 (hρM hrMlt) hinj).finite
    · refine Set.finite_empty.subset fun x hx => ?_
      have hx2 : F x = ηr u := by rw [← hcs, ← hrMeq]; exact hx.2
      exact absurd (eq_zero_of_extendFrom_eq_tip hηr hWr hWr0 hupos hinj hx2) hx.1.ne'
  have hfin : ({0} ∪ {x : ℝ | 0 < x ∧ F x = ηr (capClock γℝ rM)} ∪
      {x : ℝ | x < 0 ∧ F x = ηr (capClock γℝ ((0 : ℝ≥0) : ℝ))}).Finite :=
    ((finite_singleton 0).union hfinPos).union (subsingleton_fibre_neg hηr hWr hWr0 hρ00 (hρ0 hspos) hinj).finite
  refine hfin.subset ?_
  rintro x ⟨hx, hland, hnot⟩
  have hxb : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  -- the relative landing is a point of `γ([0, s])`
  obtain ⟨r, hr, hre⟩ : F x ∈ γ '' Icc 0 s.toNNReal := by
    have hlt : chartAL Wr u < chartAR Wr u := lt_of_le_of_lt hx.1 hx.2
    have hFK : F x ∈ closure (fwdHull Wr u) :=
      Supp8.RelTrans.Icc_subset_hullImage hηr hWr hWr0 hupos hlt (Ico_subset_Icc_self hx)
    have hFl := (hηr.hasBdryLimits hWr hWr0 hupos.le).tendsto hxb
    have hneb : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hxb)
    have hFc : F x ∈ closure (H \ fwdHull Wr u) :=
      mem_closure_of_tendsto hFl (eventually_nhdsWithin_of_forall fun y hy =>
        QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hupos.le hy)
    rw [hK] at hFK hFc
    exact mem_of_mem_closure_fillH_of_mem_closure_compl (isCompact_Icc.image hγ.1).isClosed hFK hFc
  have hlandeq : extendFrom H (jointInv c.2.1 Wr u) (x : ℂ) = g (F x) :=
    extendFrom_jointInv_eq hgc hgi hWr hWr0 hηr hu0 hxb
  rw [hlandeq] at hland hnot
  -- the relative landing is a nonnegative real point
  have hFxim : (F x).im = 0 := by
    by_contra hne
    have hFH : F x ∈ H := lt_of_le_of_ne (by rw [← hre]; exact hγ.2.2.1 r) (Ne.symm hne)
    have hgD := SB.g_mem_of_mem_H hc.1 hgi hFH
    exact hgD.2 (mem_fillH_of_mem_closure hland hgD.1)
  have hFxre : 0 ≤ (F x).re := by
    by_contra hneg
    rw [not_le] at hneg
    have hFr : F x = (((F x).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFxim])
    rw [hFr] at hland
    exact g_notMem_closure_of_neg hp hp0 hc hgc hgi hneg hland
  have hγrim : (γ r).im = 0 := by rw [hre]; exact hFxim
  have hγrre : 0 ≤ (γ r).re := by rw [hre]; exact hFxre
  rcases lt_trichotomy x 0 with hxn | hx0 | hxp
  · refine Or.inr ⟨hxn, ?_⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with hr0 | hr0
    · rw [hη0, hr0]; exact hre.symm
    · exfalso
      rcases eq_or_lt_of_le hr.2 with hrs | hrs
      · have htipx : F x = ηr u := by
          rw [← hre, hrs, ← hcs]
          exact (hclock s.toNNReal le_rfl).2.1.symm
        exact hxn.ne (eq_zero_of_extendFrom_eq_tip hηr hWr hWr0 hupos hinj htipx)
      · apply hnot
        obtain ⟨ρ, hρ, hev⟩ := exists_freeNear_of_neg hp hp0 hpH hc hgc hgi hβ' hβ'0 hA htL hγ hγ0 hlift hWr
          hWr0 hηr hu0 hηu hK hIn hxn hr0 hrs hre.symm
        refine ⟨ρ, hρ, ?_⟩
        rw [hwt, ← hre, hlift]
        exact hev
  · exact Or.inl (Or.inl hx0)
  · refine Or.inl (Or.inr ⟨hxp, ?_⟩)
    rcases lt_trichotomy r rM with hlt | heq | hgt
    · exact (false_of_rightApproach hηr hWr hWr0 hu0 hγ hγ0 hηu hK hrMs hM hrMre hmax hxp hlt hre.symm).elim
    · rw [hηM, ← heq]; exact hre.symm
    · exact absurd hγrre (not_le.2 (re_neg_of_im_eq_zero_of_lt hηr hWr hWr0 hu0 hγ hγ0 hηu hK hrMs hM hrMre
        hmax hgt hr.2 hγrim))

end CuspNoTip

end InteractingSLE.Theorem14.SB.FinRel
