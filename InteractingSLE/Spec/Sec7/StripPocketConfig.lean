/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordAssembly
import InteractingSLE.Spec.Sec7.StripSysSel

/-!
# Theorem 1.3's pocket word: the strip pocket's configuration from the walls' reverse visit order

Packet PROVE-STRIPSYS30. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L431–L489,
pp. 410–412):

> "Their full schedules lie in `[−π/2, π/2]`, so Lemma 5.7 places them in the same continuous counterflow range, in
> reverse first-visit order. […] For a point in the completed counterflow range let `T(z)` be its first counterflow
> visit time. Distinct points of an incoming path have strictly decreasing `T` in its incoming order: reverse
> containment gives weak decrease, and equality at a finite time would make a continuous curve occupy two distinct
> points at that time." (p. 410)
>
> "If `y₀ = α(b)`, reverse first-visit order gives `T(α(b)) ≤ T(β(r)) < T(α(1))`, hence `b > 1` (RS13.5). […]
> Parametrize the two completed simple paths on `[0, 1]` to apply Aux. lemma 33. Their common-contact order is
> increasing, by their reverse containment in the same counterflow." (p. 412)

The configuration predicate `PocketCoord.IsChangeConfigInc R L r` of the change pocket (walls `R = α`, `L = β^{(r)}`)
asks for simple proper walls, the increasing contact order of their disc parametrizations, `r > 0` and `L r ∉ R`.
This file derives it, deterministically, from the reverse visit order of the two walls by one continuous counterflow
`η` from `0` read in the chart `m(z) = −1/z` (`PocketJordan.IsWallReverseVisit`, `IsWallVisited`: the conclusions of
Lemma 5.7 that `PocketWordAssembly.IsCfPocketConfig` already records), and proves the source's (RS13.5) in the pocket
coordinates: the selected right arc ends strictly after the first change (`discTime 1 < rightHi`), both from the
counterflow's first visits and from the walls-only event `F_r` (`StripSys.IsContactPoint`).

## Main results

* `discVisit`: the first counterflow visit of a disc point (`⊤` at the flow seed `−1`);
* `antitoneOn_discVisit`, **`strictAntiOn_discVisit`**: weak and strict decrease of `T` along a wall;
* **`isChangeConfigInc_of_reverseVisit`**: the configuration from the reverse visit order;
* **`discTime_one_lt_rightHi_of_discVisit`**: (RS13.5) from `T(β(r)) < T(α(1))`;
* **`discTime_one_lt_rightHi_of_isContactPoint`**: (RS13.5) from the walls-only event `F_r`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.StripPocketConfig

open WangWu Lemma71I PocketCoord PocketJordan PocketMeas

/-! ### First visits of disc points -/

section Visit

variable {η : ℝ → ℂ}

/-- **The first counterflow visit of a point of the closed disc** (Aux. lemma 33's coordinates): the first visit
`T(z)` of the counterflow-chart point `cfPt w = m(cayleyInv w)` by the counterflow `η`, and `⊤` at the flow seed
`w = −1` (whose counterflow-chart point is `∞`; "The original flow seed `x` may have `T(x) = ∞`"). -/
def discVisit (η : ℝ → ℂ) (w : ℂ) : ℝ≥0∞ :=
  if w = -1 then ⊤ else Aux130.firstVisit (nnPath η) (cfPt w)

theorem discVisit_neg_one (η : ℝ → ℂ) : discVisit η (-1) = ⊤ := by simp [discVisit]

theorem discVisit_of_ne {w : ℂ} (hw : w ≠ -1) : discVisit η w = Aux130.firstVisit (nnPath η) (cfPt w) := by
  simp [discVisit, hw]

theorem continuous_nnPath_of (hη : ContinuousOn η (Ici 0)) : Continuous (nnPath η) :=
  hη.comp_continuous NNReal.continuous_coe fun t => t.2

/-- A point visited by time `t` has first visit at most `t`. -/
theorem firstVisit_le_of_mem {p : ℂ} {t : ℝ≥0} (h : p ∈ η '' Icc 0 (t : ℝ)) :
    Aux130.firstVisit (nnPath η) p ≤ t := by
  obtain ⟨u, hu, hup⟩ := h
  have hv : nnPath η u.toNNReal = p := by
    rw [nnPath, Real.coe_toNNReal u hu.1]
    exact hup
  refine (Aux130.firstVisit_le hv).trans (ENNReal.coe_le_coe.2 ?_)
  exact (Real.toNNReal_le_iff_le_coe).2 hu.2

/-- A visited point has a finite first visit. -/
theorem firstVisit_lt_top_of_mem {p : ℂ} {t : ℝ} (h : p ∈ η '' Icc 0 t) :
    Aux130.firstVisit (nnPath η) p < ⊤ := by
  obtain ⟨u, hu, hup⟩ := h
  have hv : nnPath η u.toNNReal = p := by
    rw [nnPath, Real.coe_toNNReal u hu.1]
    exact hup
  exact lt_of_le_of_lt (Aux130.firstVisit_le hv) ENNReal.coe_lt_top

/-- A point with a finite first visit `t` is visited by time `t`. -/
theorem mem_image_firstVisit (hη : ContinuousOn η (Ici 0)) {p : ℂ}
    (hlt : Aux130.firstVisit (nnPath η) p < ⊤) :
    p ∈ η '' Icc 0 ((Aux130.firstVisit (nnPath η) p).toNNReal : ℝ) :=
  ⟨_, ⟨NNReal.coe_nonneg _, le_rfl⟩, Aux130.apply_firstVisit (continuous_nnPath_of hη) hlt⟩

end Visit

/-! ### Strict decrease of the first visits along a wall -/

section Wall

variable {R : ℝ≥0 → ℂ} {η : ℝ → ℂ}

/-- **Reverse containment gives weak decrease** of the first visits along the disc parametrization of a wall. -/
theorem antitoneOn_discVisit (hR : IsSimpleProper R) (hη : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit R η) :
    AntitoneOn (fun s => discVisit η (toDisc (realPath R) s)) (Icc 0 1) := by
  intro s₁ hs₁ s₂ hs₂ h12
  have hc := hR.isProperArc.isDiscCrosscut_toDisc
  rcases eq_or_lt_of_le hs₁.1 with h0 | hpos
  · show discVisit η (toDisc (realPath R) s₂) ≤ discVisit η (toDisc (realPath R) s₁)
    rw [← h0, hc.zero, discVisit_neg_one]
    exact le_top
  · have hs₁' : s₁ ∈ Ioc (0 : ℝ) 1 := ⟨hpos, hs₁.2⟩
    have hs₂' : s₂ ∈ Ioc (0 : ℝ) 1 := ⟨hpos.trans_le h12, hs₂.2⟩
    show discVisit η (toDisc (realPath R) s₂) ≤ discVisit η (toDisc (realPath R) s₁)
    rw [discVisit_of_ne (crosscut_ne_neg_one hc hs₁'), discVisit_of_ne (crosscut_ne_neg_one hc hs₂')]
    rcases eq_top_or_lt_top (Aux130.firstVisit (nnPath η) (cfPt (toDisc (realPath R) s₁))) with htop | hlt
    · rw [htop]
      exact le_top
    · have h2 := wall_rev hR hη0 hrev hs₁' hs₂' h12 (mem_image_firstVisit hη hlt)
      refine (firstVisit_le_of_mem h2).trans_eq ?_
      exact ENNReal.coe_toNNReal hlt.ne

/-- **Strict decrease of the first visits along a wall** (p. 410: "Distinct points of an incoming path have strictly
decreasing `T` in its incoming order: reverse containment gives weak decrease, and equality at a finite time would make
a continuous curve occupy two distinct points at that time"). -/
theorem strictAntiOn_discVisit (hR : IsSimpleProper R) (hη : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit R η) (hvis : IsWallVisited R η) :
    StrictAntiOn (fun s => discVisit η (toDisc (realPath R) s)) (Icc 0 1) := by
  intro s₁ hs₁ s₂ hs₂ h12
  have hc := hR.isProperArc.isDiscCrosscut_toDisc
  have hs₂' : s₂ ∈ Ioc (0 : ℝ) 1 := ⟨hs₁.1.trans_lt h12, hs₂.2⟩
  have hne₂ := crosscut_ne_neg_one hc hs₂'
  obtain ⟨t, ht⟩ := wall_visited hη0 hR hvis hs₂'
  have hfin := firstVisit_lt_top_of_mem ht
  show discVisit η (toDisc (realPath R) s₂) < discVisit η (toDisc (realPath R) s₁)
  rw [discVisit_of_ne hne₂]
  rcases eq_or_lt_of_le hs₁.1 with h0 | hpos
  · rw [← h0, hc.zero, discVisit_neg_one]
    exact hfin
  · have hs₁' : s₁ ∈ Ioc (0 : ℝ) 1 := ⟨hpos, hs₁.2⟩
    have hne₁ := crosscut_ne_neg_one hc hs₁'
    have hle := antitoneOn_discVisit hR hη hη0 hrev hs₁ hs₂ h12.le
    simp only [discVisit_of_ne hne₁, discVisit_of_ne hne₂] at hle
    rw [discVisit_of_ne hne₁]
    refine lt_of_le_of_ne hle fun heq => h12.ne ?_
    have h1 := Aux130.apply_firstVisit (continuous_nnPath_of hη) hfin
    have h2 := Aux130.apply_firstVisit (continuous_nnPath_of hη) (heq ▸ hfin)
    rw [heq] at h1
    exact hc.inj hs₁ hs₂ (injOn_cfPt hne₁ hne₂ (h2.symm.trans h1))

end Wall

/-! ### The configuration -/

section Config

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-- **The strip pocket's configuration from the walls' reverse visit order** (proof of Aux. lemma 130, p. 412: "Their
common-contact order is increasing, by their reverse containment in the same counterflow"): two simple proper walls,
both visited in reverse order by one counterflow `η` from `0` continuous on `[0, ∞)` (the right wall entirely
visited), a positive change time and a change point off the right wall form an `IsChangeConfigInc`. -/
theorem isChangeConfigInc_of_reverseVisit (hR : IsSimpleProper R) (hL : IsSimpleProper L)
    (hη : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0) (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η)
    (hvisR : IsWallVisited R η) (hr : 0 < r) (hoff : L r ∉ range R) : IsChangeConfigInc R L r :=
  ⟨hR, hL, strictMonoOn_contactMap_of_firstVisit hL.isProperArc.isDiscCrosscut_toDisc
    (strictAntiOn_discVisit hR hη hη0 hrevR hvisR) (antitoneOn_discVisit hL hη hη0 hrevL), hr, hoff⟩

/-- **(RS13.5) in the pocket coordinates, from the first visits** (p. 412: "If `y₀ = α(b)`, reverse first-visit order
gives `T(α(b)) ≤ T(β(r)) < T(α(1))`, hence `b > 1`"): on Aux. lemma 130's event `E_r` (`T(L r) < T(R 1)`), the
selected right arc of the change pocket ends strictly after the first change, `discTime 1 < rightHi`. -/
theorem discTime_one_lt_rightHi_of_discVisit (h : IsChangeConfigInc R L r) (hη : ContinuousOn η (Ici 0))
    (hη0 : η 0 = 0) (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η)
    (hT : discVisit η (cayley (L r)) < discVisit η (cayley (R 1))) : discTime 1 < rightHi R L r := by
  obtain ⟨-, hrHi, -, -, hlHi, -, -, e2⟩ := h.changeCorner_props
  obtain ⟨-, -, -, -, hmem, -⟩ := h.changeCorners
  by_contra hle
  push Not at hle
  have h1 : discTime ((1 : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 := discTime_mem_Icc 1
  rw [NNReal.coe_one] at h1
  have a1 := antitoneOn_discVisit h.left hη hη0 hrevL (discTime_mem_Icc r) hlHi hmem.2.le
  have a2 := antitoneOn_discVisit h.right hη hη0 hrevR hrHi h1 hle
  have eR := toDisc_realPath_discTime R 1
  rw [NNReal.coe_one] at eR
  simp only at a1 a2
  rw [toDisc_realPath_discTime] at a1
  rw [eR] at a2
  rw [e2] at a1
  exact lt_irrefl _ (a2.trans_lt (a1.trans_lt hT))

/-- **(RS13.5) in the pocket coordinates, from the walls-only event `F_r`** (p. 412: "Define `F_r` from the two final
labeled paths to be the event that the second change point is off the first path and its first subsequent common
contact is strictly after the first change along that first path"): on `F_r` (`StripSys.IsContactPoint`, in the
half-plane), the selected right arc of the change pocket ends strictly after the first change. -/
theorem discTime_one_lt_rightHi_of_isContactPoint {q : ℚ} (h : IsChangeConfigInc R L (StripSys.rt q))
    (hF : StripSys.IsContactPoint R L q) : discTime 1 < rightHi R L (StripSys.rt q) := by
  obtain ⟨-, hrHi, -, -, hlHi, -, -, e2⟩ := h.changeCorner_props
  obtain ⟨-, -, -, hgap, hmem, -⟩ := h.changeCorners
  have hRcl : closure (range R) = range R := (Lemma71Pin.IsSimpleProper.isClosed_range h.right).closure_eq
  have hHb : ∀ (γ : ℝ≥0 → ℂ), IsSimpleProper γ → ∀ x : ℝ, realPath γ x ∈ Hbar := fun γ hγ x => by
    rcases eq_zero_or_pos (x.toNNReal : ℝ≥0) with hx | hx
    · rw [realPath, hx, hγ.2.2.1]
      exact le_refl (0 : ℂ).im
    · exact le_of_lt (show (0 : ℝ) < (realPath γ x).im from hγ.2.2.2.1 _ hx)
  by_contra hle
  push Not at hle
  have hd1 : discTime 1 < 1 := (discTime_mem_Ico zero_le_one).2
  have hr1 : rightHi R L (StripSys.rt q) < 1 := hle.trans_lt hd1
  -- the closing contact is a finite point of both walls
  have eC : closePt R L (StripSys.rt q) = cayley (realPath R (arcTime (rightHi R L (StripSys.rt q)))) := by
    rw [closePt, toDisc_of_lt hr1]
  have hl1 : leftHi R L (StripSys.rt q) < 1 := by
    refine lt_of_le_of_ne hlHi.2 fun he => ?_
    rw [he, toDisc_one, eC] at e2
    exact cayley_ne_one_of_Hbar (hHb R h.right _) e2.symm
  rw [toDisc_of_lt hl1, eC] at e2
  have eLR := cayley_injOn_Hbar (hHb L h.left _) (hHb R h.right _) e2
  set s : ℝ≥0 := (arcTime (leftHi R L (StripSys.rt q))).toNNReal with hs
  set a : ℝ≥0 := (arcTime (rightHi R L (StripSys.rt q))).toNNReal with ha
  have eLs : L s = R a := eLR
  -- the contact is on the first prefix `R [0, 1]`
  have harc : arcTime (rightHi R L (StripSys.rt q)) ≤ 1 := by
    have := strictMonoOn_arcTime.monotoneOn ⟨hrHi.1, hr1⟩ ⟨(discTime_mem_Ico zero_le_one).1, hd1⟩ hle
    rwa [arcTime_discTime zero_le_one] at this
  have ha1 : a ∈ Icc (0 : ℝ≥0) 1 := ⟨bot_le, by rw [ha]; exact Real.toNNReal_le_one.2 harc⟩
  -- it comes after the change time
  have hlo : discTime (StripSys.rt q) ∈ Ico (0 : ℝ) 1 := discTime_mem_Ico (StripSys.rt q).coe_nonneg
  have hrs : (StripSys.rt q : ℝ) < arcTime (leftHi R L (StripSys.rt q)) := by
    have := strictMonoOn_arcTime hlo ⟨hlo.1.trans hmem.2.le, hl1⟩ hmem.2
    rwa [arcTime_discTime (StripSys.rt q).coe_nonneg] at this
  have hrs' : StripSys.rt q ≤ s := by
    rw [hs]
    exact (Real.le_toNNReal_iff_coe_le (hrs.le.trans' (StripSys.rt q).coe_nonneg)).2 hrs.le
  obtain ⟨u, hru, hus, hu⟩ := hF.2 s hrs' ⟨a, ha1, eLs.symm⟩
  rw [hRcl] at hu
  obtain ⟨v, hv⟩ := hu
  have hru' : StripSys.rt q < u := lt_of_le_of_ne hru fun he => hF.1 (by rw [he, hRcl]; exact ⟨v, hv⟩)
  -- its disc parameter is an interior contact of the gap
  have hdu1 : discTime (StripSys.rt q) < discTime u := discTime_lt_discTime (StripSys.rt q).coe_nonneg hru'
  have hdu2 : discTime u < leftHi R L (StripSys.rt q) := by
    have hus' : (u : ℝ) < arcTime (leftHi R L (StripSys.rt q)) := by
      have := (Real.lt_toNNReal_iff_coe_lt).1 (hs ▸ hus)
      exact this
    have := discTime_lt_discTime u.coe_nonneg hus'
    rwa [discTime_arcTime hl1] at this
  refine hgap.2.2.2 (discTime u) ⟨hmem.1.trans hdu1, hdu2⟩ ⟨discTime_mem_Icc u, discTime v, discTime_mem_Icc v, ?_⟩
  rw [toDisc_realPath_discTime, toDisc_realPath_discTime, hv]

end Config

end InteractingSLE.Sec7.StripPocketConfig
