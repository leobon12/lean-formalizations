/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermK2Chart
import InteractingSLE.Spec.Supplement.GW1ActiveWord
import InteractingSLE.Spec.Supplement.OrdModelCode

/-!
# The chart interval of the completed second path (the stop set)

Packet PROVE-RC-TERM, second run (ruling R124). The real chart points over the completed second path form the
interval between the images of its two ends, which are mark positions of the record:

* `exists_alive_near`, `notMem_closure_fwdHull_of_alive`: aliveness is open; an alive real point is off the closed
  hull;
* `IsEntryData.notMem_path_of_isFreeAt`: a free point is not on the path (a Loewner trace spends no open time
  interval on `ℝ`);
* **`IsEntryData.entryInv_mem_path`**, **`IsEntryData.le_of_entryInv_mem`**, **`IsEntryData.ge_of_entryInv_mem`**
  (builder frame): `entryInv v` is on the path exactly for
  `markPosL V T 0 − markPosL V T (−d) ≤ v ≤ −markPosL V T (−d)`;
* `kEnds U T d`, `mem_aStopSet_kEnds`, **`IsKSample.mem_path_iff`** (original orientation): the stop set
  `aStopSet (kEnds U T d)` is the real segment `[−τ, a_R − τ]`, `τ = markPos U T d`, `a_R = markPos U T 0`, and a real
  chart point `v` lies over the second path exactly when it is in this segment.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open HalfPlaneSep Restart
open Exist.StagedLaw (markPos markPosL)

/-- **Aliveness is open.** -/
theorem exists_alive_near {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {y : ℂ}
    (hy : ∃ u, IsForwardSol W y T u) : ∃ r > 0, ∀ z : ℂ, z ∈ ball y r → ∃ v, IsForwardSol W z T v := by
  obtain ⟨u, hu⟩ := hy
  obtain ⟨δ, hδ, hlow, -⟩ := ZhanGT4.exists_aliveDisc_self hu hT
  exact ⟨ZhanGT4.aliveRad T δ, ZhanGT4.aliveRad_pos hδ, fun z hz =>
    (ZhanGT4.exists_sol_aliveDisc hW hu hδ hlow hz).imp fun v hv => hv.1⟩

/-- **An alive point is off the closed hull.** -/
theorem notMem_closure_fwdHull_of_alive {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {y : ℂ}
    (hy : ∃ u, IsForwardSol W y T u) : y ∉ closure (fwdHull W T) := by
  obtain ⟨r, hr, hall⟩ := exists_alive_near hW hT hy
  intro hmem
  obtain ⟨z, hz, hzy⟩ := Metric.mem_closure_iff.1 hmem r hr
  obtain ⟨v, hv⟩ := hall z (by rwa [mem_ball, dist_comm])
  exact Ito.notMem_fwdHull_of_isForwardSol hW hz.1 hT hv hz

section Builder

variable {V : ℝ → ℝ} {T : ℝ} {ξ : ℝ → ℂ} {p d : ℝ}

/-- **A free point is not on the path.** -/
theorem IsEntryData.notMem_path_of_isFreeAt (h : IsEntryData V T ξ p d) {z : ℂ}
    (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) z) : z ∉ entryPath ξ T d '' Icc 0 1 := by
  rintro ⟨s₀, hs₀, rfl⟩
  obtain ⟨ε, hε, hsub⟩ := hf
  have hT := h.tip.pos
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.1 (h.continuousOn_entryPath s₀ hs₀) ε hε
  have hreal : ∀ s ∈ Icc (0 : ℝ) 1, dist s s₀ < δ → (entryPath ξ T d s).im = 0 := by
    intro s hs hd
    by_contra hne
    have hpos : 0 < (entryPath ξ T d s).im := lt_of_le_of_ne (h.im_entryPath_nonneg hs) (Ne.symm hne)
    have hmem := hsub ⟨hδb hs hd, hpos⟩
    exact hmem.2 ⟨hpos, Or.inl (subset_closure ⟨s, hs, rfl⟩)⟩
  set a := max 0 (s₀ - δ) with ha
  set b := min 1 (s₀ + δ) with hb
  have ha0 : 0 ≤ a := le_max_left _ _
  have hb1 : b ≤ 1 := min_le_left _ _
  have hab : a < b := by
    rw [ha, hb]
    exact max_lt (lt_min one_pos (by linarith [hs₀.1])) (lt_min (by linarith [hs₀.2]) (by linarith))
  have hI : Ioo (a * T) (b * T) ⊆ {r ∈ Ioo (0 : ℝ) T | (ξ r).im = 0} := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt (mul_nonneg ha0 hT.le) hr.1
    have hrT : r < T := lt_of_lt_of_le hr.2 (by nlinarith)
    refine ⟨⟨hr0, hrT⟩, ?_⟩
    have hs : r / T ∈ Icc (0 : ℝ) 1 := ⟨(div_pos hr0 hT).le, (div_le_one hT).2 hrT.le⟩
    have h1 : a < r / T := (lt_div_iff₀ hT).2 hr.1
    have h2 : r / T < b := (div_lt_iff₀ hT).2 hr.2
    have hd : dist (r / T) s₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_right 0 (s₀ - δ)]
      · linarith [min_le_right 1 (s₀ + δ)]
    have h3 := hreal (r / T) hs hd
    simpa only [entryPath, div_mul_cancel₀ r hT.ne', add_im, ofReal_im, add_zero] using h3
  have hne : (interior {r ∈ Ioo (0 : ℝ) T | (ξ r).im = 0}).Nonempty := by
    have hmul := mul_lt_mul_of_pos_right hab hT
    have hmid : (a * T + b * T) / 2 ∈ Ioo (a * T) (b * T) := by
      constructor <;> linarith
    exact ⟨_, interior_maximal hI isOpen_Ioo hmid⟩
  rw [Theorem14.SB.FinRel.interior_real_times_eq_empty h.tip.trace h.tip.cont h.tip.zero] at hne
  exact Set.not_nonempty_empty hne

/-- **Every chart point of the stop segment lies over the path.** -/
theorem IsEntryData.entryInv_mem_path (h : IsEntryData V T ξ p d) {v : ℝ}
    (h1 : markPosL V T 0 - markPosL V T (-d) ≤ v) (h2 : v ≤ -markPosL V T (-d)) :
    entryInv V T d (v : ℂ) ∈ entryPath ξ T d '' Icc 0 1 := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  by_contra hK
  obtain ⟨x, hx, hxd, hf, he⟩ := h.entryInv_untouched hK
  obtain ⟨hal, hF⟩ := h.entryExt_ofReal hxd hf
  have e : v = (fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d) := by
    have := he.symm.trans hF
    exact_mod_cast this
  rcases lt_or_gt_of_ne (sub_ne_zero.2 hxd) with hneg | hpos
  · obtain ⟨r, hr, hall⟩ := exists_alive_near hV hT hal
    have hm0 : 0 < min (r / 2) (-(x - d) / 2) := lt_min (by positivity) (by linarith)
    set y₁ : ℝ := (x - d) + min (r / 2) (-(x - d) / 2) with hy₁
    have hy₁lt : x - d < y₁ := by rw [hy₁]; linarith
    have hy₁neg : y₁ < 0 := by rw [hy₁]; linarith [min_le_right (r / 2) (-(x - d) / 2)]
    have hal₁ : ∃ u, IsForwardSol V (y₁ : ℂ) T u := by
      refine hall _ ?_
      rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hy₁,
        add_sub_cancel_left, abs_of_pos hm0]
      linarith [min_le_left (r / 2) (-(x - d) / 2)]
    have h3 := re_fwdMap_lt_of_alive hV hT hy₁lt hal hal₁
    have h4 := (Theorem14.GW1W.le_markPosL_iff hV hV0 hT le_rfl hy₁neg hal₁).2 hy₁neg.le
    linarith
  · have h3 := (Exist.StagedLaw.isRealFlow_fwd hV hV0 hT).1.2.2.2.1 (x - d) hpos hal
    linarith

/-- **A chart point over the path is not right of the image of the tip.** -/
theorem IsEntryData.le_of_entryInv_mem (h : IsEntryData V T ξ p d) (hp : 0 < p) {v : ℝ}
    (hK : entryInv V T d (v : ℂ) ∈ entryPath ξ T d '' Icc 0 1) : v ≤ -markPosL V T (-d) := by
  by_contra hlt
  have hlt : -markPosL V T (-d) < v := not_le.1 hlt
  have hfree : ∀ x : ℝ, p + d < x → IsFreeAt (entryPath ξ T d '' Icc 0 1) (x : ℂ) := by
    intro x hx
    refine isFreeAt_of_notMem_closure fun hmem => ?_
    obtain ⟨_, ⟨s, hs, rfl⟩, him, hre⟩ :=
      Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH h.isCompact_path h.path_subset_Hbar hmem
    have hm : s * T ∈ Icc (0 : ℝ) T := ⟨mul_nonneg hs.1 h.tip.pos.le, by nlinarith [hs.2, h.tip.pos]⟩
    have him' : (ξ (s * T)).im = 0 := by
      simpa only [entryPath, add_im, ofReal_im, add_zero] using him
    have h1 := h.real_le_tip hp hm him'
    have hre' : x ≤ (ξ (s * T)).re + d := by
      simpa only [entryPath, add_re, ofReal_re] using hre
    linarith
  have hcl : ∀ x : ℝ, p + d ≤ x → (x : ℂ) ∈ closure (entryDom ξ T d) := by
    intro x hx
    have h1 : (x : ℂ) ∈ closure (Complex.ofReal '' Ioi (p + d)) :=
      image_closure_subset_closure_image Complex.continuous_ofReal
        ⟨x, by rw [closure_Ioi]; exact hx, rfl⟩
    refine closure_minimal ?_ isClosed_closure h1
    rintro _ ⟨y, hy, rfl⟩
    exact mem_closure_entryDom_of_isFreeAt (by rw [ofReal_im]) (hfree y hy)
  have hG : ContinuousOn (fun x : ℝ => (entryExt V ξ T d (x : ℂ)).re) (Ici (p + d)) :=
    Complex.continuous_re.comp_continuousOn
      (h.continuousOn_entryExt.comp Complex.continuous_ofReal.continuousOn fun x hx => hcl x hx)
  -- the tip goes to the driver
  have htip : entryExt V ξ T d ((p + d : ℝ) : ℂ) = ((-markPosL V T (-d) : ℝ) : ℂ) := by
    have hne : (𝓝[entryDom ξ T d] ((p + d : ℝ) : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (hcl _ le_rfl)
    have hshift : Tendsto (fun z : ℂ => z - (d : ℂ)) (𝓝[entryDom ξ T d] ((p + d : ℝ) : ℂ))
        (𝓝[H \ fwdHull V T] (p : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
      · have hc : Continuous fun z : ℂ => z - (d : ℂ) := continuous_id.sub continuous_const
        have h0 := (hc.tendsto ((p + d : ℝ) : ℂ)).mono_left (nhdsWithin_le_nhds (s := entryDom ξ T d))
        have e : ((p + d : ℝ) : ℂ) - (d : ℂ) = (p : ℂ) := by push_cast; ring
        rwa [e] at h0
      · have hz' : z ∈ (fun w : ℂ => w + (d : ℂ)) '' (H \ fwdHull V T) := by
          have : z ∈ H \ fillH (entryPath ξ T d '' Icc 0 1) := hz
          rwa [h.fillH_entryPath, ← image_add_real_H_diff] at this
        obtain ⟨w, hw, rfl⟩ := hz'
        simpa only [add_sub_cancel_right] using hw
    have h1 := h.tip.tendsto_fwdMap.comp hshift
    have h2 : Tendsto (entryChart V T d).1 (𝓝[entryDom ξ T d] ((p + d : ℝ) : ℂ))
        (𝓝 (0 - (markPosL V T (-d) : ℂ))) :=
      (h1.sub tendsto_const_nhds).congr fun z => (entryChart_fst V T d z).symm
    rw [tendsto_nhds_unique (h.tendsto_entryExt (hcl _ le_rfl)) h2]
    push_cast
    ring
  obtain ⟨C, hC⟩ := h.exists_norm_entryInv_sub_le
  have hbound : ∀ x : ℝ, p + d ≤ x → x - C ≤ (entryExt V ξ T d (x : ℂ)).re := by
    intro x hx
    have h1 := hC _ (h.entryExt_mem_Hbar (hcl x hx))
    rw [h.entryInv_entryExt (hcl x hx)] at h1
    have h2 := abs_re_le_norm ((x : ℂ) - entryExt V ξ T d (x : ℂ))
    rw [sub_re, ofReal_re] at h2
    linarith [(abs_le.1 (h2.trans h1)).2]
  set X : ℝ := max (p + d + 1) (v + C + 1) with hX
  have hX1 : p + d ≤ X := (by linarith : p + d ≤ p + d + 1).trans (le_max_left _ _)
  have hXv : v < (entryExt V ξ T d (X : ℂ)).re := by
    have := hbound X hX1
    linarith [le_max_right (p + d + 1) (v + C + 1)]
  have hmemI : v ∈ Icc ((entryExt V ξ T d ((p + d : ℝ) : ℂ)).re) ((entryExt V ξ T d (X : ℂ)).re) := by
    rw [htip, ofReal_re]
    exact ⟨hlt.le, hXv.le⟩
  obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc hX1 (hG.mono Icc_subset_Ici_self) hmemI
  have hxv' : (entryExt V ξ T d (x : ℂ)).re = v := hxv
  have hxne : x ≠ p + d := by
    rintro rfl
    rw [htip, ofReal_re] at hxv'
    linarith
  have hxgt : p + d < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
  have hxd : x ≠ d := by linarith
  have hF := (h.entryExt_ofReal hxd (hfree x hxgt)).2
  have hval : entryExt V ξ T d (x : ℂ) = (v : ℂ) := by
    rw [hF, ofReal_re] at hxv'
    rw [hF, hxv']
  have hinv := h.entryInv_entryExt (hcl x hx.1)
  rw [hval] at hinv
  rw [hinv] at hK
  exact h.notMem_path_of_isFreeAt (hfree x hxgt) hK

/-- **A chart point over the path is not left of the image of the far end of the hull.** -/
theorem IsEntryData.ge_of_entryInv_mem (h : IsEntryData V T ξ p d) {v : ℝ}
    (hK : entryInv V T d (v : ℂ) ∈ entryPath ξ T d '' Icc 0 1) :
    markPosL V T 0 - markPosL V T (-d) ≤ v := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  by_contra hlt
  have hlt : v < markPosL V T 0 - markPosL V T (-d) := not_le.1 hlt
  -- an alive point left of the retained seed whose image is right of `v`
  obtain ⟨y₀, hy₀, hal₀, hv₀⟩ : ∃ y₀ : ℝ, y₀ < 0 ∧ (∃ u, IsForwardSol V (y₀ : ℂ) T u) ∧
      v < (fwdMap V T (y₀ : ℂ)).re - markPosL V T (-d) := by
    by_contra hcon
    push Not at hcon
    have hc : -(v + markPosL V T (-d)) ≤ markPos (fun s => -V s) T (-0) := by
      refine Theorem14.GW1W.le_markPos hV.neg (by simp [hV0]) hT fun q hq hal => ?_
      have hq0 : (0 : ℝ) < q := by simpa using hq
      have hal' : ∃ u, IsForwardSol V ((-(q : ℝ) : ℝ) : ℂ) T u :=
        (Exist.StagedLaw.alive_neg_iff V T q).1 hal
      have h1 := hcon (-(q : ℝ)) (by linarith) hal'
      have hr : (fwdMap (-V) T (((q : ℝ)) : ℂ)).re = -(fwdMap V T ((-(q : ℝ) : ℝ) : ℂ)).re := by
        have h2 := QuantumZipper.F1.fwdMap_reflect_ofReal V hT (-(q : ℝ))
        rw [neg_neg] at h2
        rw [h2, Complex.neg_re]
      show -(v + markPosL V T (-d)) ≤ (fwdMap (-V) T ((q : ℝ) : ℂ)).re
      rw [hr]
      linarith
    have hmL0 : markPosL V T 0 = -markPos (fun s => -V s) T (-0) := rfl
    linarith
  set K := entryPath ξ T d '' Icc 0 1 with hKdef
  have hdown : ∀ y : ℝ, y ≤ y₀ → ∃ u, IsForwardSol V (y : ℂ) T u := by
    intro y hy
    rcases hy.eq_or_lt with rfl | hlt'
    · exact hal₀
    · have h1 := (Exist.StagedLaw.isRealFlow_fwd hV hV0 hT).2.2.1 (-y₀) (-y) (by linarith) (by linarith)
        (by simpa only [neg_neg] using hal₀)
      simpa only [neg_neg] using h1
  have hfree : ∀ x : ℝ, x ≤ y₀ + d → IsFreeAt K (x : ℂ) := by
    intro x hx
    refine isFreeAt_of_notMem_closure fun hmem => ?_
    rw [h.fillH_entryPath, ← Homeomorph.coe_addRight, ← Homeomorph.image_closure] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    have hwe' : w = ((x - d : ℝ) : ℂ) := by
      have : w + (d : ℂ) = (x : ℂ) := hwe
      rw [ofReal_sub, ← this]
      ring
    rw [hwe'] at hw
    exact notMem_closure_fwdHull_of_alive hV hT (hdown (x - d) (by linarith)) hw
  have hcl : ∀ x : ℝ, x ≤ y₀ + d → (x : ℂ) ∈ closure (entryDom ξ T d) := fun x hx =>
    mem_closure_entryDom_of_isFreeAt (by rw [ofReal_im]) (hfree x hx)
  have hG : ContinuousOn (fun x : ℝ => (entryExt V ξ T d (x : ℂ)).re) (Iic (y₀ + d)) :=
    Complex.continuous_re.comp_continuousOn
      (h.continuousOn_entryExt.comp Complex.continuous_ofReal.continuousOn fun x hx => hcl x hx)
  obtain ⟨C, hC⟩ := h.exists_norm_entryInv_sub_le
  have hbound : ∀ x : ℝ, x ≤ y₀ + d → (entryExt V ξ T d (x : ℂ)).re ≤ x + C := by
    intro x hx
    have h1 := hC _ (h.entryExt_mem_Hbar (hcl x hx))
    rw [h.entryInv_entryExt (hcl x hx)] at h1
    have h2 := abs_re_le_norm ((x : ℂ) - entryExt V ξ T d (x : ℂ))
    rw [sub_re, ofReal_re] at h2
    linarith [(abs_le.1 (h2.trans h1)).1]
  have hx₀d : y₀ + d ≠ d := by linarith
  have hF₀ := (h.entryExt_ofReal hx₀d (hfree _ le_rfl)).2
  have hx₀v : v < (entryExt V ξ T d ((y₀ + d : ℝ) : ℂ)).re := by
    rw [hF₀, ofReal_re, add_sub_cancel_right]
    exact hv₀
  set X : ℝ := min (y₀ + d - 1) (v - C - 1) with hX
  have hX1 : X ≤ y₀ + d := (min_le_left _ _).trans (by linarith)
  have hXv : (entryExt V ξ T d (X : ℂ)).re < v := by
    have := hbound X hX1
    linarith [min_le_right (y₀ + d - 1) (v - C - 1)]
  obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc hX1 (hG.mono Icc_subset_Iic_self) ⟨hXv.le, hx₀v.le⟩
  have hxv' : (entryExt V ξ T d (x : ℂ)).re = v := hxv
  have hxd : x ≠ d := by linarith [hx.2]
  have hF := (h.entryExt_ofReal hxd (hfree x hx.2)).2
  have hval : entryExt V ξ T d (x : ℂ) = (v : ℂ) := by
    rw [hF, ofReal_re] at hxv'
    rw [hF, hxv']
  have hinv := h.entryInv_entryExt (hcl x hx.2)
  rw [hval] at hinv
  rw [hinv] at hK
  exact h.notMem_path_of_isFreeAt (hfree x hx.2) hK

end Builder

/-! ### The stop set in the original orientation -/

/-- The end points of the stop set: the chart interval of the completed second path, twice. -/
def kEnds (U : ℝ → ℝ) (T d : ℝ) : RLC.OrdModel.Ends :=
  (-markPos U T d, markPos U T 0 - markPos U T d, -markPos U T d, markPos U T 0 - markPos U T d)

theorem mem_seg_iff {a b : ℝ} (hab : a ≤ b) {z : ℂ} :
    z ∈ RLC.OrdModel.seg a b ↔ z.im = 0 ∧ a ≤ z.re ∧ z.re ≤ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [RLC.OrdModel.segPt, ofReal_im, ofReal_re, true_and]
    constructor
    · nlinarith [hx.1, hx.2]
    · nlinarith [hx.1, hx.2]
  · rintro ⟨him, h1, h2⟩
    have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rcases hab.eq_or_lt with rfl | hlt
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      rw [hz, RLC.OrdModel.segPt]
      have : z.re = a := le_antisymm h2 h1
      rw [this]
      simp
    · refine ⟨(z.re - a) / (b - a), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
      rw [hz, RLC.OrdModel.segPt]
      congr 1
      simp only [ofReal_re]
      field_simp
      ring

theorem mem_aStopSet_kEnds {U : ℝ → ℝ} {T d : ℝ} (hle : 0 ≤ markPos U T 0) {z : ℂ} :
    z ∈ RLC.OrdModel.aStopSet (kEnds U T d) ↔
      z.im = 0 ∧ -markPos U T d ≤ z.re ∧ z.re ≤ markPos U T 0 - markPos U T d := by
  have hab : -markPos U T d ≤ markPos U T 0 - markPos U T d := by linarith
  show z ∈ RLC.OrdModel.seg _ _ ∪ RLC.OrdModel.seg _ _ ↔ _
  rw [mem_union, kEnds]
  simp only [mem_seg_iff hab, or_self]

namespace IsKSample

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}
  (h : IsKSample U T ρ₂ q d w ζ ρ₁)
include h

/-- **A real chart point lies over the second path exactly when it is in the stop segment.** -/
theorem mem_path_iff (v : ℝ) :
    reflectC (kInv U (T : ℝ) d (v : ℂ)) ∈ retSet (fun s => reflectC (ρ₂ s)) T d ↔
      -markPos U (T : ℝ) d ≤ v ∧ v ≤ markPos U (T : ℝ) 0 - markPos U (T : ℝ) d := by
  have hE := IsPathSample.entry h
  have hp : 0 < -q := IsPathSample.tipPos h
  have hret := retSet_eq (IsPathSample.tpos h) (fun s => reflectC (ρ₂ s)) d
  have e2 : reflectC (kInv U (T : ℝ) d (v : ℂ)) = entryInv (-U) (T : ℝ) d ((-v : ℝ) : ℂ) := by
    unfold kInv
    rw [LP.reflectC_reflectC, reflectC_ofReal']
  have hfun : (fun s => -(-U) s) = U := funext fun s => by simp
  have hmL : markPosL (-U) (T : ℝ) (-d) = -markPos U (T : ℝ) d := by
    unfold markPosL
    rw [hfun, neg_neg]
  have hm0 : markPosL (-U) (T : ℝ) 0 = -markPos U (T : ℝ) 0 := by
    unfold markPosL
    rw [hfun, neg_zero]
  rw [e2, hret]
  constructor
  · intro hK
    have h1 := hE.ge_of_entryInv_mem hK
    have h2 := hE.le_of_entryInv_mem hp hK
    rw [hmL, hm0] at h1
    rw [hmL] at h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine hE.entryInv_mem_path ?_ ?_
    · rw [hmL, hm0]; linarith
    · rw [hmL]; linarith

end IsKSample

end Term

end InteractingSLE.RealContact
