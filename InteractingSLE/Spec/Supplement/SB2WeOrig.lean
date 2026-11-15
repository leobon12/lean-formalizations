/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WdStep
import InteractingSLE.Spec.Supplement.RelTransHull

/-!
# SB2(1)'s second clause: original-real points keep their heights; the other points are old lower sides

Packet PROVE-T14-SB2WORD (round 2, ruling R120, decision D10 "step 3"). The source (supplement p. 632): "All
original-real groups … have their original weights, because the map reflects positively outside the old real base";
"the active lower-flow sides before the next seed have height `−λ − φχ`". In the launch chart of the lower walk this
is the invariant `OW` of a state `s` with word `β`: there is a set `S` of original-real points (it contains both
untouched rays) on which

* the chart's real profile is strictly increasing, the chart is continuous and every nearby point of `ℍ` lies in the
  chart's range (`ChartFree`: the chart reflects there);
* the word is the original word, read through the profile (off finite sets);

and every chart point off finite sets is either the image of a point of `S`, or a point of an old lower side, of
height exactly `−λ − θχ`, lying right of the image of the whole untouched left ray.

This file proves that `OW` survives a launch (`ow_launch`) and a rightward move (`ow_moveAlong`), and holds at the
root (`ow_root`). Tools: `strictMonoOn_re_fwdMap_alive` (the real flow is strictly increasing on all alive points),
`chartFree_loewner` (a free point alive at the stop stays free), `rRight_rel_launch` (beyond the new right record the
old points are alive).

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H)

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

/-! ### The real flow on all alive points -/

/-- **The real flow is strictly increasing on all alive real points** (both half-lines; `0` is never alive). -/
theorem strictMonoOn_re_fwdMap_alive {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    StrictMonoOn (fun y : ℝ => (fwdMap W T y).re) {y : ℝ | ∃ u, IsForwardSol W (y : ℂ) T u} := by
  have hH := isRealFlow_fwd hW hW0 hT
  have h0 : ¬ ∃ u, IsForwardSol W ((0 : ℝ) : ℂ) T u := hH.1.1
  have hneg : ∀ y : ℝ, y < 0 → (∃ u, IsForwardSol W (y : ℂ) T u) → (fwdMap W T y).re < 0 := fun y hy hA => by
    have hA' : ∃ u, IsForwardSol W (((-(-y)) : ℝ) : ℂ) T u := by rwa [neg_neg]
    have h := hH.2.2.2.2.1 (-y) (by linarith) hA'
    simp only [neg_neg] at h
    linarith
  intro a ha c hc hac
  simp only [mem_ofPred_eq] at ha hc
  rcases lt_trichotomy a 0 with ha0 | ha0 | ha0
  · rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
    · have h1 : ∃ u, IsForwardSol W (((-(-c)) : ℝ) : ℂ) T u := by rwa [neg_neg]
      have h2 : ∃ u, IsForwardSol W (((-(-a)) : ℝ) : ℂ) T u := by rwa [neg_neg]
      have h := hH.2.2.2.2.2.1 (-c) (-a) (by linarith) (by linarith) h1 h2
      simp only [neg_neg] at h
      show (fwdMap W T a).re < (fwdMap W T c).re
      linarith
    · exact absurd (hc0 ▸ hc) h0
    · exact (hneg a ha0 ha).trans (hH.1.2.2.2.1 c hc0 hc)
  · exact absurd (ha0 ▸ ha) h0
  · exact hH.1.2.2.2.2.1 a c ha0 hac ha (by
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · exact absurd (hac.trans hc0) (not_lt.2 ha0.le)
      · exact absurd (hc0 ▸ hc) h0
      · exact hc)

/-! ### Free points of a chart -/

/-- **A free real point of a chart**: every point of `ℍ` near it lies in the chart's range (the chart reflects
there). -/
def ChartFree (c : Chart) (x : ℝ) : Prop :=
  ∃ ρ > 0, ∀ z ∈ H, dist z (x : ℂ) < ρ → z ∈ c.2.1 '' H

/-- **A free point alive at the stop stays free after the stage** (alive points are off the closed hull,
`notMem_closure_fwdHull_of_isForwardSol`; the stage's inverse maps `ℍ` onto `ℍ` minus the hull). -/
theorem chartFree_loewner {c : Chart} (hcc : c.IsConformal) {x : ℝ} (hfree : ChartFree c x)
    (hC : ContinuousAt c.1 (x : ℂ)) {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hal : ∃ u, IsForwardSol V (c.1 x) T u) : ChartFree (c.loewner V T) x := by
  obtain ⟨u, hu⟩ := hal
  have hcl := Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hV hT hu
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hcl
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hC ε hε
  obtain ⟨ρ, hρ, hfr⟩ := hfree
  refine ⟨min ρ δ, lt_min hρ hδ, fun z hz hzx => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hfr z hz (lt_of_lt_of_le hzx (min_le_left _ _))
  have hcw : c.1 (c.2.1 w) = w := hcc.2.2 w hw
  have hd : dist w (c.1 x) < ε := by
    have := hδc (lt_of_lt_of_le hzx (min_le_right _ _))
    rwa [hcw] at this
  have hwK : w ∉ fwdHull V T := fun hK => hball (Metric.mem_ball.2 hd) (subset_closure hK)
  refine ⟨fwdMap V T w, QuantumZipper.FwdHolo.mapsTo_fwdMap hV hT ⟨hw, hwK⟩, ?_⟩
  show c.2.1 (fwdMapInv V T (fwdMap V T w)) = c.2.1 w
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hV hV0 hT ⟨hw, hwK⟩]

/-- Recentring keeps the range of the chart's inverse. -/
theorem chartFree_recenter {c : Chart} {x : ℝ} (hfree : ChartFree c x) (a : ℝ) : ChartFree (c.recenter a) x := by
  obtain ⟨ρ, hρ, hfr⟩ := hfree
  refine ⟨ρ, hρ, fun z hz hzx => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hfr z hz hzx
  refine ⟨w - (a : ℂ), ?_, ?_⟩
  · show 0 < (w - (a : ℂ)).im
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact hw
  · show c.2.1 (w - (a : ℂ) + (a : ℂ)) = c.2.1 w
    rw [sub_add_cancel]

/-! ### The second clause -/

/-- **The original-real points and the old lower sides of a state** (the second clause of SB2(1)'s active word):
a set `S` of original-real points containing both untouched rays, on which the real profile is strictly increasing,
the chart is continuous and free, and the word is the original word (off a finite set `Fx`); off a finite set `Fy`
every chart point is the image of a point of `S` or an old lower side point (height `−λ − θχ`, right of the image of
the whole untouched left ray). -/
def OW (κ θ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  ∃ (S : Set ℝ) (Fx Fy : Finset ℝ),
    (∀ x, x < stRecL s → x ∈ S) ∧ (∀ x, stRecR s < x → x ∈ S) ∧
    StrictMonoOn (rProf (stChart s)) S ∧
    (∀ x ∈ S, ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x) ∧
    (∀ x ∈ S, x ∉ jumps → x ∉ Fx → rProf (stChart s) x ∉ β.jumps → β.fn (rProf (stChart s) x) = b x) ∧
    (∀ y, y ∉ β.jumps → y ∉ Fy →
      (β.fn y = -sleLambda κ - θ * chiC κ ∧ ∀ x, x < stRecL s → rProf (stChart s) x < y) ∨
        ∃ x ∈ S, rProf (stChart s) x = y) ∧
    (∀ x ∈ S, x < stRecL s ∨ 0 ≤ x)

/-- **Alive negative points form a down-set.** -/
theorem alive_of_lt_of_alive_neg {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {z z' : ℝ}
    (hzz' : z < z') (hz' : z' < 0) (hA : ∃ u, IsForwardSol W (z' : ℂ) T u) : ∃ u, IsForwardSol W (z : ℂ) T u := by
  have hHn := (isRealFlow_fwd hW hW0 hT).2
  have h1 : ∃ u, IsForwardSol W (((-(-z')) : ℝ) : ℂ) T u := by rwa [neg_neg]
  have h2 : ∃ u, IsForwardSol W (((-(-z)) : ℝ) : ℂ) T u := hHn.2.1 (-z') (-z) (by linarith) (by linarith) h1
  rwa [neg_neg] at h2

/-- **A point of the untouched left ray alive at the stop stays left of the new left record** (the alive real set is
open, and between the new and the old record every point is dead). -/
theorem lt_stRecL_launch_of_alive {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hc : IsRealChart (stChart s))
    (hs : LLeft s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) {x : ℝ} (hx : x < stRecL s)
    (hal : ∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u) :
    x < stRecL (ExplState.launch s k D θ ⊤) := by
  obtain ⟨-, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWe : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  rw [hWe, rtime_recOf] at hal
  set c := stChart s with hcdef
  have hV : Continuous (stopDrv ⊤ D) := by rw [← hWe]; exact continuous_rdrv _
  have hV0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  have hTs : 0 ≤ stopTime ⊤ D := stopTime_nonneg ⊤ D
  have hH' := (isRealFlow_stop hreg hgood).2
  by_contra hle
  push Not at hle
  set v := rProf c x with hvdef
  have hv : v < 0 := hs.neg hx
  obtain ⟨u, hu⟩ := hal
  have hcl := Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hV hTs hu
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hcl
  -- continuity of the profile at `x`
  have hcx : ContinuousAt (rProf c) x := by
    have hcl' : ContinuousAt (lProf c) (-x) := hs.1.2.1.continuousAt (Ioi_mem_nhds (by linarith))
    have e : rProf c = fun y => -lProf c (-y) := by funext y; rw [lProf_eq, neg_neg, neg_neg]
    rw [e]
    exact (hcl'.comp (by simpa using continuous_neg.continuousAt (x := x))).neg
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcx (min ε (-v)) (lt_min hε (by linarith))
  -- a dead point of the old ray just right of `x`
  set x₁ := min (x + δ / 2) ((x + stRecL s) / 2) with hx₁
  have hxx₁ : x < x₁ := lt_min (by linarith) (by linarith)
  have hx₁r : x₁ < stRecL s := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hR1 : -stRecL (ExplState.launch s k D θ ⊤) = newRec (lProf c) (-stRecL s)
      (fun y : ℝ => ∃ u, IsForwardSol (stopDrv ⊤ D) ((-y : ℝ) : ℂ) (stopTime ⊤ D) u) := by
    rw [hrecL, lRecL_eq_newRec hc, neg_neg]
  have hlt : -x₁ < newRec (lProf c) (-stRecL s)
      (fun y : ℝ => ∃ u, IsForwardSol (stopDrv ⊤ D) ((-y : ℝ) : ℂ) (stopTime ⊤ D) u) := by
    rw [← hR1]; linarith
  obtain ⟨z, hz, hxz⟩ := (lt_csSup_iff (bddAbove_dead hs.1 hH') (insert_nonempty _ _)).1 hlt
  rcases hz with rfl | ⟨hza, hzd⟩
  · linarith
  have hdead : ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) ((rProf c (-z) : ℝ) : ℂ) (stopTime ⊤ D) u := by
    have e : -lProf c z = rProf c (-z) := by rw [lProf_eq, neg_neg]
    rw [← e]
    exact hzd
  have hzr : -z < stRecL s := by linarith
  rcases lt_trichotomy (-z) x with h1 | h1 | h1
  · exact hdead (alive_of_lt_of_alive_neg hV hV0 hTs (hs.strictMonoOn (show -z ∈ Iio (stRecL s) from hzr)
      (show x ∈ Iio (stRecL s) from hx) h1) hv ⟨u, hu⟩)
  · exact hdead (by rw [h1]; exact ⟨u, hu⟩)
  · have hd : dist (-z) x < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left (x + δ / 2) ((x + stRecL s) / 2)]
    have h2 := hδc hd
    rw [Real.dist_eq] at h2
    have h3 : dist ((rProf c (-z) : ℝ) : ℂ) (v : ℂ) < ε := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le h2 (min_le_left _ _)
    have h4 : rProf c (-z) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, abs_neg] at h2
      have := lt_of_lt_of_le h2 (min_le_right _ _)
      rw [abs_of_neg hv] at this
      linarith
    exact hdead (Aux10.exists_isForwardSol_of_notMem_closure hV hV0 hTs h4
      fun hm => hball (Metric.mem_ball.2 h3) hm)

/-- **Beyond the new right record the old points are alive** (the right half of `lLeft_launch`'s relation). -/
theorem rRight_rel_launch {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hc : IsRealChart (stChart s))
    (hm : RightGood (rProf (stChart s)) (stRecR s)) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    ∀ x, stRecR (ExplState.launch s k D θ ⊤) < x → stRecR s < x ∧
      ∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u := by
  obtain ⟨-, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWr : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  rw [hWr, rtime_recOf]
  have hH := (isRealFlow_stop hreg hgood).1
  intro x hx
  rw [hrec, lRecR_eq_newRec hc] at hx
  exact ⟨(le_newRec hm hH).trans_lt hx, (pos_alive_of_newRec_lt hm hH hx).2⟩

/-- The seed is the first left mark of a flow-line word. -/
theorem padFL_fst_fst_zero (c : BoundaryWord) : (padFL 0 0 c.fn c.jumps).1.1 0 = 0 := by
  have h0 : 0 < flowLineNL c.fn c.jumps 0 := by unfold flowLineNL; omega
  have h := padFL_fst_fst_fin c.fn c.jumps ⟨0, h0⟩
  exact h.trans rfl

/-- **The second clause survives a launch** of an angle-`θ` piece with a good record at a finite stop (the stop
word; the new right profile `hR₁` gives the positive chart points). -/
theorem ow_launch {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {β : BoundaryWord} {s : ExplState}
    (hc : IsRealChart (stChart s)) (hcc : (stChart s).IsConformal) (hs : LLeft s)
    (hm : RightGood (rProf (stChart s)) (stRecR s)) (hI : OW κ θ b jumps β s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) (hR₁ : RProf (ExplState.launch s k D θ ⊤)) :
    OW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  obtain ⟨S, Fx, Fy, hSL, hSR, hSm, hSc, hSo, hSy, hSloc⟩ := hI
  obtain ⟨-, -, hrelL⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  have hrelR := rRight_rel_launch hc hm k θ hreg hgood hfin
  obtain ⟨hch, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWe : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  have hTe : rtime (recOf ⊤ D) = stopTime ⊤ D := rtime_recOf ⊤ D
  set r := recOf ⊤ D with hr
  have hW : Continuous (rdrv r) := continuous_rdrv r
  have hW0 : rdrv r 0 = 0 := rdrv_zero r
  have hT : 0 ≤ rtime r := rtime_nonneg r
  set c := stChart s with hcdef
  set γ := stopWord κ (β, θ, r) with hγ
  set f : ℝ → ℝ := fun y => (fwdMap (rdrv r) (rtime r) (y : ℂ)).re with hf
  set A : ℝ → Prop := fun y => ∃ u, IsForwardSol (rdrv r) (y : ℂ) (rtime r) u with hAdef
  have hprof : ∀ x, rProf (stChart (ExplState.launch s k D θ ⊤)) x = f (rProf c x) := by
    intro x
    rw [hch]
    change (fwdMap (stopDrv ⊤ D) (stopTime ⊤ D) (c.1 x)).re = (fwdMap (rdrv r) (rtime r) (rProf c x : ℂ)).re
    rw [hc.eq_ofReal x, hWe, hTe]
  have hA0 : ¬ A 0 := by
    have := (isRealFlow_fwd hW hW0 hT).1.1
    simpa [hAdef] using this
  have hFxfin : ({x | x ∈ S ∧ rProf c x ∈ β.jumps} : Set ℝ).Finite := by
    refine Set.Finite.of_finite_image (f := rProf c) (β.jumps.finite_toSet.subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · exact hSm.injOn.mono fun x hx => hx.1
  have hSL₁ : ∀ x, x < stRecL (ExplState.launch s k D θ ⊤) → x ∈ {x | x ∈ S ∧ A (rProf c x)} := by
    intro x hx
    obtain ⟨hx', hA, -⟩ := hrelL x hx
    exact ⟨hSL x hx', hA⟩
  have hSR₁ : ∀ x, stRecR (ExplState.launch s k D θ ⊤) < x → x ∈ {x | x ∈ S ∧ A (rProf c x)} := by
    intro x hx
    obtain ⟨hx', hA⟩ := hrelR x hx
    exact ⟨hSR x hx', hA⟩
  have hV : Continuous (stopDrv ⊤ D) := by rw [← hWe]; exact hW
  have hV0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  have hTs : 0 ≤ stopTime ⊤ D := stopTime_nonneg ⊤ D
  refine ⟨{x | x ∈ S ∧ A (rProf c x)}, Fx ∪ hFxfin.toFinset, insert 0 ((β.jumps ∪ Fy).image f), hSL₁, hSR₁,
    fun a ha a' ha' h => ?_, fun x hx => ?_, fun x hx hxJ hxF hzJ => ?_, fun y hyJ hyF => ?_,
    fun x hx => ?_⟩
  · rw [hprof, hprof]
    exact strictMonoOn_re_fwdMap_alive hW hW0 hT ha.2 ha'.2 (hSm ha.1 ha'.1 h)
  · obtain ⟨hC, hF⟩ := hSc x hx.1
    obtain ⟨u, hu⟩ := hx.2
    have hu' : IsForwardSol (stopDrv ⊤ D) (c.1 x) (stopTime ⊤ D) u := by
      rw [hc.eq_ofReal x, ← hWe, ← hTe]; exact hu
    rw [hch]
    exact ⟨(ZhanGT4.A1G3L2.continuousAt_fwdMap_of_isForwardSol (show stopTime ⊤ D < stopTime ⊤ D + 1 by linarith)
      hTs hV.continuousOn hu').comp hC, chartFree_loewner hcc hF hC hV hV0 hTs ⟨u, hu'⟩⟩
  · have hxF' : x ∉ Fx := fun h => hxF (Finset.mem_union_left _ h)
    have hvJ : rProf c x ∉ β.jumps := fun h => hxF (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨hx.1, h⟩))
    have hv0 : rProf c x ≠ 0 := fun h => hA0 (h ▸ hx.2)
    rw [hprof] at hzJ ⊢
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · rw [stopWord_fn_fwdMap_neg hκ β θ r hneg hx.2 hvJ hzJ]
      exact hSo x hx.1 hxJ hxF' hvJ
    · rw [stopWord_fn_fwdMap hκ β θ r hpos hx.2 hvJ hzJ]
      exact hSo x hx.1 hxJ hxF' hvJ
  · have hyF0 : y ≠ 0 := fun h => hyF (by rw [h]; exact Finset.mem_insert_self 0 _)
    have hyF1 : ∀ z ∈ β.jumps ∪ Fy, f z ≠ y := fun z hz h =>
      hyF (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨z, hz, h⟩))
    rcases lt_or_gt_of_ne hyF0 with hy0 | hy0
    · by_cases hfirst : ∀ i < flowLineNL β.fn β.jumps 0,
          markPosL (rdrv r) (rtime r) ((padFL 0 0 β.fn β.jumps).1.1 i) < y
      · left
        refine ⟨stopWord_fn_first β θ r hy0 hyJ hfirst, fun x hx => ?_⟩
        obtain ⟨hx', hA, -⟩ := hrelL x hx
        rw [hprof]
        have h0lt : 0 < flowLineNL β.fn β.jumps 0 := by unfold flowLineNL; omega
        have hneg := hs.neg hx'
        have h1 := (le_markPosL_iff hW hW0 hT (le_refl 0) hneg hA).2 hneg.le
        have h2 := hfirst 0 h0lt
        rw [padFL_fst_fst_zero] at h2
        exact lt_of_le_of_lt h1 h2
      push Not at hfirst
      obtain ⟨i, hi, hiy⟩ := hfirst
      have hiy' : y < markPosL (rdrv r) (rtime r) ((padFL 0 0 β.fn β.jumps).1.1 i) :=
        lt_of_le_of_ne hiy fun h => hyJ (h ▸ markPosL_mem_jumps_stopWord (κ := κ) β θ r hi)
      obtain ⟨q, hqx, hqA, hqy⟩ := exists_rat_lt_of_lt_markPosL hW hW0 hT hiy'
      have hq0 : (q : ℝ) < 0 := lt_of_lt_of_le hqx (padFL_fst_fst_nonpos β hi)
      obtain ⟨y₀, hy₀q, hy₀A, hfy₀⟩ := exists_alive_eq_of_lt_re hW hW0 hT hq0 hqA hqy
      have hy₀0 : y₀ < 0 := hy₀q.trans hq0
      have hy₀J : y₀ ∉ β.jumps := fun h => hyF1 y₀ (Finset.mem_union_left _ h) hfy₀
      have hy₀F : y₀ ∉ Fy := fun h => hyF1 y₀ (Finset.mem_union_right _ h) hfy₀
      have hfJ : (fwdMap (rdrv r) (rtime r) y₀).re ∉ γ.jumps := by rw [hfy₀]; exact hyJ
      rcases hSy y₀ hy₀J hy₀F with ⟨hβ, hrt⟩ | ⟨x, hxS, hxy⟩
      · left
        refine ⟨?_, fun x hx => ?_⟩
        · rw [← hfy₀, stopWord_fn_fwdMap_neg hκ β θ r hy₀0 hy₀A hy₀J hfJ]
          exact hβ
        · obtain ⟨hx', hA, -⟩ := hrelL x hx
          rw [hprof, ← hfy₀]
          exact strictMonoOn_re_fwdMap_alive hW hW0 hT hA hy₀A (hrt x hx')
      · right
        refine ⟨x, ⟨hxS, ?_⟩, ?_⟩
        · show A (rProf c x)
          rw [hxy]
          exact hy₀A
        · rw [hprof, hxy]
          exact hfy₀
    · right
      obtain ⟨x, hx, hxy⟩ := RProf.exists_eq hR₁ hy0
      exact ⟨x, hSR₁ x hx, hxy⟩
  · rcases hSloc x hx.1 with h | h
    · exact Or.inl (lt_stRecL_launch_of_alive hc hs k θ hreg hgood hfin h hx.2)
    · exact Or.inr h

/-- **The second clause survives a rightward move** (the chart and the word are recentred by the image `a` of the new
point; the set `S` does not change). -/
theorem ow_moveAlong {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {γ : BoundaryWord} {s₁ : ExplState}
    (hI : OW κ θ b jumps γ s₁) {w : ℝ} (hw : stRecR s₁ < w) :
    OW κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) w) γ) (ExplState.moveAlong s₁ true w true) := by
  obtain ⟨S, Fx, Fy, hSL, hSR, hSm, hSc, hSo, hSy, hSloc⟩ := hI
  set a := rProf (stChart s₁) w with hadef
  have hprof : ∀ x, rProf (stChart (ExplState.moveAlong s₁ true w true)) x = rProf (stChart s₁) x - a := by
    intro x
    rw [stChart_moveAlong, rProf_recenter]
    rfl
  have hR₂ : stRecR (ExplState.moveAlong s₁ true w true) = w := by
    rw [stRecR_moveAlong_true, max_eq_right hw.le]
  have hJ : ∀ z, z - a ∉ (BoundaryWord.shiftW a γ).jumps → z ∉ γ.jumps := fun z hz h =>
    hz (by rw [BoundaryWord.jumps_shiftW]; exact Finset.mem_image_of_mem _ h)
  refine ⟨S, Fx, Fy.image (· - a), fun x hx => hSL x (by rwa [stRecL_moveAlong_true'] at hx),
    fun x hx => hSR x (hw.trans (by rwa [hR₂] at hx)), fun x hx x' hx' h => ?_, fun x hx => ?_,
    fun x hx hxJ hxF hzJ => ?_, fun y hyJ hyF => ?_, fun x hx => by rw [stRecL_moveAlong_true']; exact hSloc x hx⟩
  · rw [hprof, hprof]
    have := hSm hx hx' h
    linarith
  · obtain ⟨hC, hF⟩ := hSc x hx
    rw [stChart_moveAlong]
    exact ⟨hC.sub continuousAt_const, chartFree_recenter hF _⟩
  · rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, sub_add_cancel]
    exact hSo x hx hxJ hxF (hJ _ hzJ)
  · have hyJ' : y + a ∉ γ.jumps := hJ (y + a) (by rwa [add_sub_cancel_right])
    have hyF' : y + a ∉ Fy := fun h => hyF (Finset.mem_image.2 ⟨y + a, h, by ring⟩)
    rw [BoundaryWord.fn_shiftW]
    rcases hSy (y + a) hyJ' hyF' with ⟨hβ, hrt⟩ | ⟨x, hxS, hxy⟩
    · left
      refine ⟨hβ, fun x hx => ?_⟩
      rw [stRecL_moveAlong_true'] at hx
      rw [hprof]
      have := hrt x hx
      linarith
    · right
      exact ⟨x, hxS, by rw [hprof, hxy]; ring⟩

/-- **The second clause at the root** (every nonzero real point is original-real). -/
theorem ow_root {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord} (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    OW κ θ b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) := by
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hc : (stChart (ExplState.init 0)).1 = fun z => z - ((0 : ℝ) : ℂ) := by
    funext z
    simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hci : (stChart (ExplState.init 0)).2.1 = fun z => z + ((0 : ℝ) : ℂ) := by
    funext z
    simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hL0 : stRecL (ExplState.init 0) = 0 := rfl
  have hR0 : stRecR (ExplState.init 0) = 0 := rfl
  refine ⟨{x | x ≠ 0}, ∅, {0}, fun x hx => ?_, fun x hx => ?_, ?_, fun x _ => ?_, fun x _ hxJ _ _ => ?_,
    fun y _ hyF => Or.inr ⟨y, ?_, ?_⟩, fun x hx => ?_⟩
  · rw [hL0] at hx; exact hx.ne
  · rw [hR0] at hx; exact hx.ne'
  · rw [hprof]; exact strictMonoOn_id
  · refine ⟨?_, 1, one_pos, fun z hz _ => ⟨z, hz, ?_⟩⟩
    · rw [hc]; exact (continuous_id.sub continuous_const).continuousAt
    · rw [hci]; simp
  · rw [hprof, BoundaryWord.fn_shiftW, add_zero]; exact hc₀ x hxJ
  · intro h; exact hyF (by simp [h])
  · rw [hprof]
  · rcases lt_or_ge x 0 with h | h
    · exact Or.inl (by rw [hL0]; exact h)
    · exact Or.inr h

/-! ### The boundary correspondence at a free point -/

/-- **At a free point of continuity of a conformal chart, the inverse's boundary map returns the point**: if `g` is a
continuous extension of the chart's inverse to `ℍ̄`, then `g (c x) = x`. -/
theorem bdry_eq_of_chartFree {c : Chart} (hcc : c.IsConformal) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {x : ℝ} (hC : ContinuousAt c.1 (x : ℂ)) (hF : ChartFree c x) (hr : (c.1 x).im = 0) :
    g (c.1 x) = x := by
  have hNB : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (by show (0 : ℝ) ≤ (x : ℂ).im; simp)
  obtain ⟨ρ, hρ, hfr⟩ := hF
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), c.1 z ∈ H ∧ g (c.1 z) = z := by
    filter_upwards [inter_mem_nhdsWithin H (Metric.ball_mem_nhds (x : ℂ) hρ), self_mem_nhdsWithin] with z hz hzH
    obtain ⟨w, hw, rfl⟩ := hfr z hzH (Metric.mem_ball.1 hz.2)
    rw [hcc.2.2 w hw]
    exact ⟨hw, hgi hw⟩
  have h1 : Tendsto (fun z => c.1 z) (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (c.1 x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hC.tendsto.mono_left nhdsWithin_le_nhds,
      hev.mono fun z hz => (show (0 : ℝ) ≤ (c.1 z).im from hz.1.le)⟩
  have h2 : Tendsto (fun z => g (c.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (g (c.1 x))) :=
    (hgc (c.1 x) (show (0 : ℝ) ≤ (c.1 x).im by rw [hr])).tendsto.comp h1
  have h3 : Tendsto (fun z => g (c.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun z hz => hz.2.symm)
  exact tendsto_nhds_unique h2 h3

end InteractingSLE.Theorem14.GW1W
