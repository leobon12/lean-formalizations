/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftChart

/-!
# Lemma S2's lift: the left side of the post-`t_L` arc lies in `D_A`

Packet PROVE-T14-SB5. In the setting of Lemma S2 (supplement p. 577: `A = p([0, 1])`, a proper witness `β` from `0`
with `A` on its closed right side, `L = min (A ∩ ℝ)`, `β(t_L) = L`), let `β''(s) = β(t_L + s)` be the post-`t_L`
arc, a proper curve from `L`. Its whole open left side, intersected with `ℍ`, lies in `D_A = ℍ \ fill(A)`
(`postCurve_leftSide_free`): the source's "the left collar lies in `D_A`" and "At the initial point `L`, the free left
sector is incident to the untouched original-real interval immediately to its left", for every point of the arc at
once, including `L`.

Proof: the left side of `β''` is a connected set off `β` (the pre-`t_L` arc lies on the right of `β''`: it is
connected, misses `β''` and contains `0 > L`) and contains the lower-left quadrant at `L`, so it is inside the left
side of `β`; it misses the closed walk `β([0, t_L])` + the lower semicircle over `[L, 0]` of `SBLemmaS2Loop` and is
unbounded, so that walk winds `0` times about each of its points; and a left point of `β` in `ℍ` about which the walk
winds `0` times is in `D_A` (`free_of_wind_zero`, the argument of `later_leftSide_free` with its winding input
made explicit).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide lowerLeft lowerRight)
open InteractingSLE.HalfPlaneSep (IsFreeAt)

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### Sides of a proper curve from a real seed -/

section Seed

variable {γ : ℝ≥0 → ℂ}

/-- A left point on or below the real axis is strictly left of the seed. -/
theorem re_lt_of_mem_leftSide (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {w : ℂ} (hw : w ∈ leftSide γ)
    (him : w.im ≤ 0) : w.re < (γ 0).re := by
  by_contra hre
  rw [not_lt] at hre
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_leftSide' hγ) w hw
  set w' : ℂ := w - ((δ / 2 : ℝ) : ℂ) * I with hw'
  have hw'b : w' ∈ ball w δ := by
    rw [mem_ball, dist_eq_norm, hw', show w - ((δ / 2 : ℝ) : ℂ) * I - w = ((-(δ / 2) : ℝ) : ℂ) * I by
      push_cast; ring, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hw'L := hball hw'b
  have hw'im : w'.im < 0 := by
    simp only [hw', sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hw're : w'.re = w.re := by simp [hw']
  rcases eq_or_lt_of_le hre with heq | hlt
  · exact connectedComponentIn_subset _ _ hw'L
      (Or.inr ⟨by rw [hw're, heq], by rw [h0]; exact hw'im.le⟩)
  · have hR := Supp9B.lowerRight_subset_rightSide hγ.2.2.1 h0 ⟨by rw [hw're]; exact hlt, hw'im⟩
    exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hγ h0) hw'L hR

/-- A real point right of the seed and off the closed curve is on the right side. -/
theorem ofReal_mem_rightSide_of_gt (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {x : ℝ} (hx : (γ 0).re < x)
    (hxS : (x : ℂ) ∉ seedRayClosure γ) : (x : ℂ) ∈ rightSide γ := by
  have hx' : (x : ℂ) ∈ (seedRayClosure γ)ᶜ := hxS
  rw [Supp9B.compl_seedRayClosure_eq hγ h0] at hx'
  rcases hx' with h | h
  · have := re_lt_of_mem_leftSide hγ h0 h (by simp)
    simp only [ofReal_re] at this
    linarith
  · exact h

end Seed

/-! ### The post-`t_L` arc -/

section Post

/-- The arc of `β` after time `t_L`, reparametrized from `0`. -/
def postCurve (β : ℝ≥0 → ℂ) (tL : ℝ≥0) : ℝ≥0 → ℂ := fun s => β (tL + s)

variable {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {tL : ℝ≥0}

theorem isProperCurve_postCurve (hβ : IsProperCurve β) : IsProperCurve (postCurve β tL) :=
  ⟨hβ.1.comp (continuous_const.add continuous_id), fun _ _ h => add_left_cancel (hβ.2.1 h),
    fun _ => hβ.2.2.1 _, hβ.2.2.2.comp (tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)⟩

theorem postCurve_zero : postCurve β tL 0 = β tL := by simp [postCurve]

/-- **The pre-`t_L` arc lies on the right of the post-`t_L` arc.** -/
theorem pre_subset_rightSide (hβ : IsProperCurve β) (hβ0 : β 0 = 0) {L : ℝ} (htL : β tL = L) (hL0 : L ≤ 0) :
    β '' Iio tL ⊆ rightSide (postCurve β tL) := by
  set β'' := postCurve β tL with hβ''
  have h0'' : (β'' 0).im = 0 := by rw [hβ'', postCurve_zero, htL]; simp
  have hre'' : (β'' 0).re = L := by rw [hβ'', postCurve_zero, htL]; simp
  rcases eq_or_ne tL 0 with htL0 | htL0
  · rintro _ ⟨t, ht, -⟩
    exact absurd ht (by simp [htL0])
  have hoff : ∀ t < tL, β t ∉ seedRayClosure β'' := by
    intro t ht h
    rcases h with ⟨s, hs⟩ | ⟨hre, him⟩
    · have := hβ.2.1 hs
      rw [← this] at ht
      exact absurd ht (not_lt.2 le_self_add)
    · have him' : (β t).im = 0 := le_antisymm (by rw [h0''] at him; exact him) (hβ.2.2.1 t)
      have hβt : β t = β tL := by
        rw [htL]
        exact Complex.ext (by rw [hre, hre'']; simp) (by rw [him']; simp)
      exact absurd (hβ.2.1 hβt) (ne_of_lt ht)
  have hL : L < 0 := by
    refine lt_of_le_of_ne hL0 fun h => htL0 ?_
    rw [h, ofReal_zero, ← hβ0] at htL
    exact hβ.2.1 htL
  have h0R : β 0 ∈ rightSide β'' := by
    rw [hβ0]
    have := ofReal_mem_rightSide_of_gt (isProperCurve_postCurve hβ) h0'' (x := 0) (by rw [hre'']; exact hL)
      (by have := hoff 0 (pos_iff_ne_zero.2 htL0); rwa [hβ0] at this)
    simpa using this
  have hP : IsPreconnected (β '' Iio tL) := isPreconnected_Iio.image _ hβ.1.continuousOn
  show β '' Iio tL ⊆ connectedComponentIn (seedRayClosure β'')ᶜ (β'' 0 + 1 - I)
  rw [connectedComponentIn_eq h0R]
  exact hP.subset_connectedComponentIn (mem_image_of_mem β (pos_iff_ne_zero.2 htL0))
    (by rintro _ ⟨t, ht, rfl⟩; exact hoff t ht)

/-- **The left side of the post-`t_L` arc is inside the left side of `β`.** -/
theorem postCurve_leftSide_subset (hβ : IsProperCurve β) (hβ0 : β 0 = 0) {L : ℝ} (htL : β tL = L)
    (hL0 : L ≤ 0) : leftSide (postCurve β tL) ⊆ leftSide β := by
  set β'' := postCurve β tL with hβ''
  have hβ''p : IsProperCurve β'' := isProperCurve_postCurve hβ
  have h0'' : (β'' 0).im = 0 := by rw [hβ'', postCurve_zero, htL]; simp
  have hre'' : (β'' 0).re = L := by rw [hβ'', postCurve_zero, htL]; simp
  have hpre := pre_subset_rightSide hβ hβ0 htL hL0
  have hoff : leftSide β'' ⊆ (seedRayClosure β)ᶜ := by
    intro z hz h
    rcases h with ⟨t, rfl⟩ | ⟨hre, him⟩
    · rcases lt_or_ge t tL with ht | ht
      · exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hβ''p h0'') hz
          (hpre (mem_image_of_mem β ht))
      · refine connectedComponentIn_subset _ _ hz (Or.inl ⟨t - tL, ?_⟩)
        simp only [hβ'', postCurve, add_tsub_cancel_of_le ht]
    · have him' : z.im ≤ 0 := by rw [hβ0] at him; simpa using him
      have := re_lt_of_mem_leftSide hβ''p h0'' hz him'
      rw [hre'', hre, hβ0] at this
      simp only [zero_re] at this
      linarith
  have href : β'' 0 - 1 - I ∈ leftSide β := by
    refine Supp9B.lowerLeft_subset_leftSide hβ.2.2.1 (by rw [hβ0]; rfl) ⟨?_, ?_⟩
    · simp only [sub_re, one_re, I_re, sub_zero, hβ0, zero_re, hre'']
      linarith
    · simp [h0'']
  show leftSide β'' ⊆ connectedComponentIn (seedRayClosure β)ᶜ (β 0 - 1 - I)
  rw [connectedComponentIn_eq href]
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (Supp9B.leftRef_mem_leftSide hβ''p.2.2.1 h0'') hoff

end Post

/-! ### The free left side -/

section Free

variable {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- A point of the lower semicircle over `[L, 0]` is not left of `L`. -/
theorem le_re_of_mem_s2Lower {L : ℝ} (hL : L < 0) {z : ℂ} (hz : z ∈ s2Lower L) : L ≤ z.re := by
  have hn : ‖s2Nrm L z‖ = 1 := hz.1
  have hre : (s2Nrm L z).re = 2 / L * z.re - 1 := by simp [s2Nrm]
  have h1 := abs_re_le_norm (s2Nrm L z)
  rw [hn, hre] at h1
  have h2 : 2 / L * z.re ≤ 2 := by linarith [(abs_le.1 h1).2]
  by_contra hc
  rw [not_le] at hc
  have h3 : 2 / L * L < 2 / L * z.re := mul_lt_mul_of_neg_left hc (div_neg_of_pos_of_neg two_pos hL)
  have h4 : 2 / L * L = 2 := by field_simp [hL.ne]
  linarith

/-- **A left point of `ℍ` about which the walk `β([0, t_L])` + `S⁻` winds `0` times is in `D_A`** (the argument of
`later_leftSide_free`, with its winding input as a hypothesis). -/
theorem free_of_wind_zero (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hγ : IsProperCurve β)
    (hγ0 : β 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β) (htL : β tL = realMin (p '' Icc 0 1)) {w : ℂ}
    (hwL : w ∈ leftSide β) (hwH : w ∈ H)
    (hw0 : realMin (p '' Icc 0 1) < 0 → s2Wind (realMin (p '' Icc 0 1)) β tL w = 0) :
    w ∈ H \ fillH (p '' Icc 0 1) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨-, -, hLR, -, -⟩ := realBase_facts hp hp0
  have hCA : connectedComponentIn (leftSide β ∩ H) w ⊆ {z | 0 ≤ z.im} \ p '' Icc 0 1 := fun z hz => by
    have hz' := connectedComponentIn_subset _ _ hz
    exact ⟨show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hz'.2),
      fun h => notMem_closedRightSide_of_mem_leftSide hγ hγ0 hz'.1 (hA h)⟩
  have hwC : w ∈ connectedComponentIn (leftSide β ∩ H) w := mem_connectedComponentIn ⟨hwL, hwH⟩
  refine mem_of_isFreeAt ?_ hwH
  rcases unbounded_or_gap hγ hγ0 ⟨hwL, hwH⟩ with hu | ⟨x, hx0, hxγ, hxC⟩
  · exact HalfPlaneSep.isFreeAt_of_not_isBounded hAc.isClosed hAc.isBounded isPreconnected_connectedComponentIn
      hu hCA w hwC
  · rcases lt_trichotomy x (realMin (p '' Icc 0 1)) with hxL | hxL | hxL
    · obtain ⟨δ, hδ, hfree⟩ := isFreeAt_of_lt hAc (fun y hy => (hLR y hy).1) hxL
      obtain ⟨c, hc, hcx⟩ := Metric.mem_closure_iff.1 hxC δ hδ
      have hcH : c ∈ H := (connectedComponentIn_subset _ _ hc).2
      have hcD : c ∈ H \ fillH (p '' Icc 0 1) := hfree ⟨by rw [mem_ball, dist_comm]; exact hcx, hcH⟩
      exact isFreeAt_of_isPreconnected hAc.isClosed isPreconnected_connectedComponentIn hCA hc
        (isFreeAt_of_mem hAc.isClosed hcD) hwC
    · exact absurd ⟨tL, by rw [htL, hxL]⟩ hxγ
    · exfalso
      have hLn : realMin (p '' Icc 0 1) < 0 := hxL.trans hx0
      obtain ⟨ρ, hρ, hg⟩ := gap_ball hγ hγ0 hLn htL ⟨hxL, hx0⟩ (fun ⟨s, _, he⟩ => hxγ ⟨s, he⟩)
      obtain ⟨c, hc, hcx⟩ := Metric.mem_closure_iff.1 hxC ρ hρ
      have h1 := hg c (by rw [mem_ball, dist_comm]; exact hcx)
      rw [s2Wind_eq_of_isPreconnected hγ hγ0 hLn htL isPreconnected_connectedComponentIn
        (fun z hz => leftSide_inter_H_off hLn (connectedComponentIn_subset _ _ hz)) hc hwC, hw0 hLn] at h1
      exact zero_ne_one h1

/-- **The left side of the post-`t_L` arc, in `ℍ`, lies in `D_A`.** -/
theorem postCurve_leftSide_free (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hβ : IsProperCurve β)
    (hβ0 : β 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β) (htL : β tL = realMin (p '' Icc 0 1)) {w : ℂ}
    (hwL : w ∈ leftSide (postCurve β tL)) (hwH : 0 < w.im) : w ∈ H \ fillH (p '' Icc 0 1) := by
  obtain ⟨-, -, -, hL0, -⟩ := realBase_facts hp hp0
  set L := realMin (p '' Icc 0 1) with hLdef
  set β'' := postCurve β tL with hβ''
  have hβ''p : IsProperCurve β'' := isProperCurve_postCurve hβ
  have h0'' : (β'' 0).im = 0 := by rw [hβ'', postCurve_zero, htL]; simp
  have hre'' : (β'' 0).re = L := by rw [hβ'', postCurve_zero, htL]; simp
  refine free_of_wind_zero hp hp0 hβ hβ0 hA htL (postCurve_leftSide_subset hβ hβ0 htL hL0 hwL) hwH
    fun hL => ?_
  have hpre := pre_subset_rightSide hβ hβ0 htL hL0
  have hunb : ¬ IsBounded (leftSide β'') := fun hb => not_isBounded_lowerLeft L
    (hb.subset (by rw [← hre'']; exact Supp9B.lowerLeft_subset_leftSide hβ''p.2.2.1 h0''))
  refine s2Wind_eq_zero_of_isPreconnected hβ hβ0 hL htL isPreconnected_connectedComponentIn hunb
    (fun z hz => ⟨?_, fun hzl => ?_⟩) hwL
  · rintro ⟨t, ht, rfl⟩
    rcases lt_or_eq_of_le ht.2 with htt | htt
    · exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hβ''p h0'') hz
        (hpre (mem_image_of_mem β htt))
    · refine connectedComponentIn_subset _ _ hz (Or.inl ⟨0, ?_⟩)
      rw [hβ'', postCurve_zero, htt]
  · have h1 := re_lt_of_mem_leftSide hβ''p h0'' hz (im_nonpos_of_mem_s2Lower hL hzl)
    rw [hre''] at h1
    exact absurd (le_re_of_mem_s2Lower hL hzl) (not_le.2 h1)

end Free

end SB

end Theorem14

end InteractingSLE
