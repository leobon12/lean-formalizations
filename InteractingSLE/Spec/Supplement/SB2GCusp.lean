/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GRight
import InteractingSLE.Spec.Supplement.SB2FinCusp
import InteractingSLE.Spec.Supplement.SB2FinWord
import InteractingSLE.Spec.Supplement.SBLemmaS5SideProof
import InteractingSLE.Spec.Supplement.SB2GLift

/-!
# SB2(1)'s `cusp` field

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2, ruling R84). The field `cusp` of `IsRelConfigJC` for SB2(1)'s geometry:
all but finitely many relative hull-image points `x ∈ [a_L, a_R)` whose joint landing lies on `closure (fill A)` are
one-sided cusp points (`freeNear`).

* **`cusp_of_isSB2RelChain`** (no named input besides the S1/S2 data): the exceptional set lies in
  `{0} ∪ {x > 0 | F(x) = q_M} ∪ {x < 0 | F(x) = 0}`, where `F` is the relative boundary map and `q_M` the largest
  nonnegative real point of `γ([0, s])`; each fibre has at most one point on each side (`SB2GFibre`).
* **`isRelConfigJC_of_s2_cusp`**: `isRelConfigJC_of_s2_force` with `hcusp` discharged.

## Proof

For `x ∈ [a_L, a_R)` the relative landing `F(x)` is a point `γ(r)`, `r ≤ s` (as in `landK`), and the joint landing is
`g(F(x))`. If `F(x) ∈ ℍ`, `g(F(x)) ∈ D_A`, which misses `closure (fill A)`; if `F(x) < 0` is real, `g(F(x))` is a free
real point left of `L` (`IsLeftEntryChart`). So `F(x) = γ(r) ≥ 0` is real. Right of the tip coordinate (`x > 0`),
`r < r_M` is impossible (`false_of_rightApproach`), and `r > r_M` gives a negative real point
(`re_neg_of_im_eq_zero_of_lt`); so `F(x) = γ(r_M)`. Left of it (`x < 0`), `r = s` is excluded by `γ(s) ∈ ℍ`, `r = 0` is
the fibre over `γ(0)`, and for `0 < r < s` the approaches `F(y)`, `y → x`, lie on the left side of the continued curve
`γ̂ = extCurve` (`mem_leftSide_extCurve`), which has no real point after `s`; S5's transport
(`SB.s5_image_leftSide_inter_H` with `bt := γ̂`) carries them to the left side of the glued curve, which agrees with
`β'` on `[0, t_L + s]`; by the side principle (`Supp9B.eventually_mem_leftSide_of_eqOn`) they are on the left side of
`β'` near `β'(t_L + r)`, and `eventually_freeNear_of_leftSide` (round 4) gives the one-sided cusp condition.
Deterministic.
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

/-- Points of `ℍ` adherent to a filling belong to it. -/
theorem mem_fillH_of_mem_closure {Y : Set ℂ} {z : ℂ} (hz : z ∈ closure (fillH Y)) (hzH : z ∈ H) : z ∈ fillH Y := by
  by_contra hn
  have hfr : z ∈ frontier (fillH Y) := ⟨hz, fun hi => hn (interior_subset hi)⟩
  exact hn ⟨hzH, Or.inl (frontier_fillH_inter_H_subset Y ⟨hfr, hzH⟩)⟩

section Cusp

variable {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ}

/-- A negative real point is carried by `g` to a free real point left of `L`, off `closure (fill A)`. -/
theorem g_notMem_closure_of_neg (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {v : ℝ} (hv : v < 0) : g (v : ℂ) ∉ closure (fillH (p '' Icc 0 1)) := by
  set A := p '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨e, -, -, heg, hesurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
  obtain ⟨x', hx'L, hex'⟩ := hesurj v hv
  rw [← hex', (heg x' hx'L).2]
  obtain ⟨ε, hε, hball⟩ := SB.isFreeAt_of_lt hAc (fun y hy => realMin_le_of_mem hAc hy) hx'L
  intro hcl
  obtain ⟨z, hzF, hzb⟩ := Metric.mem_closure_iff.1 hcl ε hε
  have hz := hball ⟨mem_ball.2 (by rw [dist_comm]; exact hzb), hzF.1⟩
  exact hz.2 hzF

/-- **Left of the tip coordinate, a landing at a later witness point is a one-sided cusp point.** -/
theorem exists_freeNear_of_neg {β' γ : ℝ≥0 → ℂ} {tL sN : ℝ≥0} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {u : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (htL : β' tL = realMin (p '' Icc 0 1)) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s)) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hηu : ηr u = γ sN) (hK : fwdHull Wr u = fillH (γ '' Icc 0 sN))
    (hIn : ∀ z ∈ fillH (β' '' Icc 0 (tL + sN)), z ∉ fillH (p '' Icc 0 1) → c.1 z ∈ fwdHull Wr u)
    {x : ℝ} (hx : x < 0) {r : ℝ≥0} (hr0 : 0 < r) (hrs : r < sN)
    (hFx : extendFrom H (fwdMapInv Wr u) (x : ℂ) = γ r) :
    ∃ ρ > 0, ∀ᶠ y in 𝓝[H] (x : ℂ), jointInv c.2.1 Wr u y ∈
      freeNear (fillH (p '' Icc 0 1)) (fillH (β' '' Icc 0 (tL + sN))) (β' (tL + r)) ρ := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  obtain ⟨-, hFc, -, -⟩ := hηr.fiber_hyps hWr hWr0 hu
  have hP := isProperCurve_extCurve hηr hWr hWr0 hu hγ hηu hK
  have hγe0 : extCurve Wr u γ sN 0 = 0 := by rw [extCurve_of_le zero_le]; exact hγ0
  -- the glued curve of S5 with the continued relative curve
  have hβC : IsProperCompletion β' (tL + sN) β' := ⟨hβ'.1, hβ'.2.1, hβ'.2.2.1, hβ'.2.2.2, fun _ _ => rfl⟩
  have hbtβ : ∀ t ≤ tL + sN - tL, g (extCurve Wr u γ sN t) = β' (tL + t) := fun t ht => by
    rw [add_tsub_cancel_left] at ht
    rw [extCurve_of_le ht, hlift]
  have hreal : ∀ t, tL + sN - tL < t → (extCurve Wr u γ sN t).im = 0 → (extCurve Wr u γ sN t).re < 0 :=
    fun t ht him => by
      rw [add_tsub_cancel_left] at ht
      exact absurd him (ne_of_gt (im_extCurve_pos hWr hWr0 hu ht))
  have htr := SB.s5_image_leftSide_inter_H hp hp0 hpH hβ'0 hβC hA hc hgc hgi le_self_add htL hP hγe0 hbtβ hreal
  have hGC := SB.isProperCompletion_gluedCurve hp hp0 hpH hβ'0 hβC hA hc hgc hgi le_self_add htL hP hbtβ hreal
  have hG := Supp9B.isProperCurve_of_isProperCompletion hGC
  have hG0 : (SB.gluedCurve β' g (extCurve Wr u γ sN) tL 0).im = 0 := by
    rw [hGC.2.2.2.2 0 zero_le, hβ'0]; rfl
  have hside := Supp9B.eventually_mem_leftSide_of_eqOn hG hβ' hG0 (fun t ht => (hGC.2.2.2.2 t ht).symm)
    (show tL + r < tL + sN from add_lt_add_of_le_of_lt le_rfl hrs)
  rw [hGC.2.2.2.2 _ (add_le_add le_rfl hrs.le)] at hside
  -- the joint approach
  have hxb : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hFH : ∀ y ∈ H, F y ∈ H := fun y hy => by
    rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hy]
    exact QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy
  have hFt : Tendsto F (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (γ r)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
    · rw [← hFx]; exact ((hFc _ hxb).mono QuantumZipper.H_subset_Hbar).tendsto
    · exact le_of_lt (show 0 < (F y).im from hFH y hy)
  have hjoint : ∀ y ∈ H, jointInv c.2.1 Wr u y = g (F y) := fun y hy => by
    simp only [jointInv]
    rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hy,
      hgi (QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy)]
  have hlim : Tendsto (jointInv c.2.1 Wr u) (𝓝[H] (x : ℂ)) (𝓝 (β' (tL + r))) := by
    have h1 := (hgc (γ r) (hγ.2.2.1 r)).tendsto.comp hFt
    rw [hlift] at h1
    exact h1.congr' (eventually_nhdsWithin_of_forall fun y hy => (hjoint y hy).symm)
  refine eventually_freeNear_of_leftSide hp hp0 hβ' hβ'0 hA htL (lt_add_of_pos_right tL hr0)
    (add_lt_add_of_le_of_lt le_rfl hrs) hlim ?_
  have hre : ∀ᶠ y in 𝓝[H] (x : ℂ), y.re < 0 :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_re continuous_const).mem_nhds (by simpa using hx))
  filter_upwards [hre, self_mem_nhdsWithin, hlim.eventually hside] with y hyre hyH hyside
  have hL := mem_leftSide_extCurve hηr hWr hWr0 hu hγ hγ0 hηu hK hyH hyre
  have hgL := htr ⟨F y, ⟨hL, hFH y hyH⟩, rfl⟩
  rw [hjoint y hyH] at hyside ⊢
  refine ⟨hyside hgL, ?_⟩
  have hD : g (F y) ∈ H \ fillH (p '' Icc 0 1) := SB.g_mem_of_mem_H hc.1 hgi (hFH y hyH)
  refine ⟨hD.1, fun hmem => ?_⟩
  have h1 := hIn _ hmem hD.2
  rw [hgi (hFH y hyH), hc.1.fwd_inv (hFH y hyH)] at h1
  have hm : fwdMapInv Wr u y ∈ H \ fwdHull Wr u := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 hu]; exact ⟨y, hyH, rfl⟩
  rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hyH] at h1
  exact hm.2 h1

/-- **SB2(1)'s `cusp` field** (ruling R84): all but finitely many relative hull-image points of `[a_L, a_R)` whose
joint landing lies on `closure (fill A)` are one-sided cusp points. -/
theorem cusp_of_isSB2RelChain {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (htL : β' tL = realMin (p '' Icc 0 1)) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s)) (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀) (hγH : γ s.toNNReal ∈ H)
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
  have hrMlt : rM < s.toNNReal := lt_of_le_of_ne hrMs fun h => by
    rw [h] at hrMim
    exact (ne_of_gt (show 0 < (γ s.toNNReal).im from hγH)) hrMim
  obtain ⟨hρM0, hηM, hρM⟩ := hclock rM hrMs
  obtain ⟨hρ00, hη0, hρ0⟩ := hclock 0 zero_le
  have hspos : (0 : ℝ≥0) < s.toNNReal := Real.toNNReal_pos.2 hs.1
  have hfin : ({0} ∪ {x : ℝ | 0 < x ∧ F x = ηr (capClock γℝ rM)} ∪
      {x : ℝ | x < 0 ∧ F x = ηr (capClock γℝ ((0 : ℝ≥0) : ℝ))}).Finite :=
    ((finite_singleton 0).union (subsingleton_fibre_pos hηr hWr hWr0 hρM0 (hρM hrMlt) hinj).finite).union
      (subsingleton_fibre_neg hηr hWr hWr0 hρ00 (hρ0 hspos) hinj).finite
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
      · rw [hrs] at hγrim
        exact (ne_of_gt (show 0 < (γ s.toNNReal).im from hγH)) hγrim
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

/-- **SB2(1)'s cusp configuration with the `cusp` field discharged** (`isRelConfigJC_of_s2_force` with `hcusp` from
`cusp_of_isSB2RelChain`; conditional assembly with a distinct name). Remaining named inputs: `hliftR` (the chart lift's
boundary values right of the retained set), `hpinch` (finitely many pinch points of `∂D_A`, for `finK`), and the
physical chain with its fresh tip (`hw hw0 hη hwt hηβ hγH`). -/
theorem isRelConfigJC_of_s2_cusp {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {κ χ : ℝ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H)
    (hliftR : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ closure (fillH (p '' Icc 0 1)) →
      Tendsto c.2.2 (𝓝[H \ fillH (p '' Icc 0 1)] (y : ℂ)) (𝓝 0))
    (hpinch : {v : ℝ | ∃ v' : ℝ, v' ≠ v ∧ g v' = g v}.Finite)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (htL : β' tL = realMin (p '' Icc 0 1)) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀)
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal)))
    (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hγH : γ s.toNNReal ∈ H) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJC (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w ((tL : ℝ) + s))
        (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
        (flowedJumps xL' xR' w ((tL : ℝ) + s)) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        G₀ GE G
        (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
          χ * ((QuantumZipper.logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im +
            (LΨ z).im)) :=
  isRelConfigJC_of_s2_force hxL hxR hxL' hxR' hp hp0 hc hgc hgi hliftR hpinch hβ' hγ hlift hch hS₀S hnR hs hw hw0
    hη hwt hηβ hγH
    (cusp_of_isSB2RelChain hp hp0 hpH hc hgc hgi hβ' hβ'0 hA htL hγ hγ0 hlift hch hs hγH hwt)

/-- **`isRelConfigJC_of_s2_cusp` with `hliftR` from `LiftRealOn c`** (e.g. a recentred run chart,
`liftRealOn_runChart`, `liftRealOn_recenter`). Conditional assembly with a distinct name. -/
theorem isRelConfigJC_of_s2_liftOn {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ Sm : ℝ}
    {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {w : ℝ → ℝ} {η : ℝ → ℂ} {κ χ : ℝ}
    {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H)
    (hL : LiftRealOn c)
    (hpinch : {v : ℝ | ∃ v' : ℝ, v' ≠ v ∧ g v' = g v}.Finite)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (htL : β' tL = realMin (p '' Icc 0 1)) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hch : IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr) (hS₀S : S₀ < Sm)
    (hnR : interior {r ∈ Ioo (0 : ℝ) Sm | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅)
    {s : ℝ} (hs : s ∈ Ioc 0 S₀)
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hwt : fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal)))
    (hηβ : ∀ r ∈ Icc (0 : ℝ) ((tL : ℝ) + s), η r = β' r.toNNReal) (hγH : γ s.toNNReal ∈ H) :
    ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ), EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH (p '' Icc 0 1)) ∧
      IsRelConfigJC (fillH (p '' Icc 0 1)) c.1 c.2.1 LΨ ∅ w Wr η ηr ((tL : ℝ) + s)
        (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ) (forceBoundaryData κ ρL ρR xL xR)
        (flowedData κ ρL' ρR' xL' xR' w ((tL : ℝ) + s))
        (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
        (flowedJumps xL' xR' w ((tL : ℝ) + s)) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        G₀ GE G
        (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)) -
          χ * ((QuantumZipper.logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) (c.1 z)).im +
            (LΨ z).im)) :=
  isRelConfigJC_of_s2_cusp hxL hxR hxL' hxR' hp hp0 hpH hc hgc hgi
    (fun y _ hy => hliftR_of_liftRealOn hc.1 hL y hy) hpinch hβ' hβ'0 hA htL hγ hγ0 hlift hch hS₀S hnR hs hw
    hw0 hη hwt hηβ hγH

end Cusp

end InteractingSLE.Theorem14.SB.FinRel
