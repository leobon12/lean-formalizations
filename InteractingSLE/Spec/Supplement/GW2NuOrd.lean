/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuConv
import InteractingSLE.Spec.Supplement.SB2WeOrig
import InteractingSLE.Spec.Supplement.BHMeanReal
import InteractingSLE.Spec.Supplement.GW2BmSide

/-!
# The relative chart keeps the order of real points: earlier bounces left of the tip stay left of it

Packet PROVE-GW2-NOTHR (round 3, D35 (D-a)). BUF's `GW2Bh.rightImg_eq_of_real_tip_off` needs the relative trace to
have no earlier real visit at or beyond the chart image of the tip. The chart `relBdry U s x = −1/Re g_s(−1/x)`
(`GW2Sf.relBdry_of_real`) is increasing on each real half-line off the retained hull, and keeps signs. So the
hypothesis follows from the physical one: every earlier real visit of the physical trace on the tip's side lies
strictly inside the tip.

* **`re_relBdry_lt_of_pos`**, **`re_relBdry_lt_of_neg`**: the chart is strictly increasing on `(0, ∞)` and on
  `(−∞, 0)` off the retained hull;
* **`relTrace_off_of_prior`**, **`relTrace_off_of_prior_neg`**: BUF's `hoff` (right, left) from the physical
  earlier-visit condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Theorem14.GW2Nu

open MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart GW2Bh

variable {U : ℝ → ℝ} {s : ℝ}

/-- The chart value of a real point off the retained hull as `−1/Re g_s(−1/x)`, with `Re g_s(−1/x)` of the sign of
`x`, read from a forward solution. -/
theorem relBdry_re_eq (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) {x : ℝ} (hx0 : x ≠ 0)
    (hxA : (x : ℂ) ∉ closure (invHull U s)) :
    (relBdry U s x).re = -((fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re)⁻¹ := by
  rw [GW2Sf.relBdry_of_real hU hU0 hs hx0 hxA, Complex.ofReal_re]

/-- **The chart is strictly increasing on the positive real points off the retained hull.** -/
theorem re_relBdry_lt_of_pos (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) {x x' : ℝ} (hx : 0 < x)
    (hxx : x < x') (hxA : (x : ℂ) ∉ closure (invHull U s)) (hx'A : (x' : ℂ) ∉ closure (invHull U s)) :
    (relBdry U s x).re < (relBdry U s x').re := by
  have hx' : 0 < x' := hx.trans hxx
  rw [relBdry_re_eq hU hU0 hs hx.ne' hxA, relBdry_re_eq hU hU0 hs hx'.ne' hx'A]
  have hyK := negInv_notMem_closure hx.ne' hxA
  have hy'K := negInv_notMem_closure hx'.ne' hx'A
  have hy0 : -x⁻¹ ≠ 0 := by simp [hx.ne']
  have hy'0 : -x'⁻¹ ≠ 0 := by simp [hx'.ne']
  obtain ⟨u, hu⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hs hyK hy0
  obtain ⟨u', hu'⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hs hy'K hy'0
  have hyy : -x⁻¹ < -x'⁻¹ := neg_lt_neg (inv_strictAnti₀ hx hxx)
  have hlt := GW1W.strictMonoOn_re_fwdMap_alive hU hU0 hs ⟨u, hu⟩ ⟨u', hu'⟩ hyy
  have hneg' : (fwdMap U s ((-x'⁻¹ : ℝ) : ℂ)).re < 0 := by
    have : NeBot (𝓝[H] (((-x'⁻¹ : ℝ)) : ℂ)) := by
      apply mem_closure_iff_nhdsWithin_neBot.1
      rw [closure_H]
      simp [QuantumZipper.Hbar]
    have hF := tendsto_fwdMap_re hU hU0 hs hy'0 hy'K
    obtain ⟨v', -, hv'n, hv'⟩ := exists_tendsto_fwdMap_real hU hU0 hs hy'0 hy'K
    have he : (v' : ℂ) = ((fwdMap U s ((-x'⁻¹ : ℝ) : ℂ)).re : ℂ) := tendsto_nhds_unique hv' hF
    rw [← Complex.ofReal_injective he]
    exact hv'n (by simpa using hx')
  have hm : (fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re < (fwdMap U s ((-x'⁻¹ : ℝ) : ℂ)).re := hlt
  have hmneg : (fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re < 0 := hm.trans hneg'
  have := (inv_lt_inv_of_neg hneg' hmneg).2 hm
  linarith

/-- **The chart is strictly increasing on the negative real points off the retained hull.** -/
theorem re_relBdry_lt_of_neg (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) {x x' : ℝ} (hx' : x' < 0)
    (hxx : x < x') (hxA : (x : ℂ) ∉ closure (invHull U s)) (hx'A : (x' : ℂ) ∉ closure (invHull U s)) :
    (relBdry U s x).re < (relBdry U s x').re := by
  have hx : x < 0 := hxx.trans hx'
  rw [relBdry_re_eq hU hU0 hs hx.ne hxA, relBdry_re_eq hU hU0 hs hx'.ne hx'A]
  have hyK := negInv_notMem_closure hx.ne hxA
  have hy'K := negInv_notMem_closure hx'.ne hx'A
  have hy0 : -x⁻¹ ≠ 0 := by simp [hx.ne]
  have hy'0 : -x'⁻¹ ≠ 0 := by simp [hx'.ne]
  obtain ⟨u, hu⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hs hyK hy0
  obtain ⟨u', hu'⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hs hy'K hy'0
  have hyy : -x⁻¹ < -x'⁻¹ := by
    have := inv_lt_inv_of_neg hx' hx |>.2 hxx
    linarith
  have hlt := GW1W.strictMonoOn_re_fwdMap_alive hU hU0 hs ⟨u, hu⟩ ⟨u', hu'⟩ hyy
  have hpos : 0 < (fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re := by
    have : NeBot (𝓝[H] (((-x⁻¹ : ℝ)) : ℂ)) := by
      apply mem_closure_iff_nhdsWithin_neBot.1
      rw [closure_H]
      simp [QuantumZipper.Hbar]
    have hF := tendsto_fwdMap_re hU hU0 hs hy0 hyK
    obtain ⟨v, hvp, -, hv⟩ := exists_tendsto_fwdMap_real hU hU0 hs hy0 hyK
    have he : (v : ℂ) = ((fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re : ℂ) := tendsto_nhds_unique hv hF
    rw [← Complex.ofReal_injective he]
    exact hvp (by simpa using hx)
  have hm : (fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re < (fwdMap U s ((-x'⁻¹ : ℝ) : ℂ)).re := hlt
  have := (inv_lt_inv₀ (hpos.trans hm) hpos).2 hm
  linarith

variable {γ : ℝ≥0 → ℂ} {a : ℝ≥0 → ℝ} {τ : ℝ≥0}

/-- Before the clock's end, the inverse clock is strictly before `τ`. -/
theorem invClock_lt_of_lt (ha : IsClockOn a τ) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) (a τ)) :
    invClock a τ u.toNNReal < τ := by
  obtain ⟨hle, heq⟩ := invClock_mem ha ⟨hu.1, hu.2.le⟩
  refine lt_of_le_of_ne hle fun h => ?_
  rw [h] at heq
  exact (ne_of_gt hu.2) heq

/-- **BUF's `hoff` from the physical earlier visits (right side).** If the physical tip at `τ` is a positive real
point and every earlier real visit is strictly left of it, then the relative trace has no real visit at or beyond the
chart image of the tip before `a τ`. -/
theorem relTrace_off_of_prior (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hsafe : MapsTo γ (Iic τ) (relSafe U s)) (him : (γ τ).im = 0) (hpos : 0 < (γ τ).re)
    (hprior : ∀ t < τ, (γ t).im = 0 → (γ t).re < (γ τ).re) :
    ∀ u ∈ Ico 0 (a τ), ∀ r : ℝ, (relBdry U s (γ τ)).re ≤ r → relTrace U s γ a τ u ≠ r := by
  intro u hu r hr heq
  set t := invClock a τ u.toNNReal with htdef
  have htτ : t < τ := invClock_lt_of_lt ha hu
  have hτS : γ τ ∈ relSafe U s := hsafe (le_refl τ)
  have htS : γ t ∈ relSafe U s := hsafe htτ.le
  have hτe : γ τ = (((γ τ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hτA : (((γ τ).re : ℝ) : ℂ) ∉ closure (invHull U s) := hτe ▸ hτS.2
  have htip : 0 < (relBdry U s (γ τ)).re := by
    rw [hτe]; exact ((GW2Sf.relBdry_real_sign hU hU0 hs hpos.ne' hτA).1).1 hpos
  have heq' : relBdry U s (γ t) = r := heq
  have hte := eq_re_of_relBdry_eq_real hU hU0 hs htS heq'
  have htA : (((γ t).re : ℝ) : ℂ) ∉ closure (invHull U s) := hte ▸ htS.2
  have hre : (relBdry U s (((γ t).re : ℝ) : ℂ)).re = r := by rw [← hte, heq', Complex.ofReal_re]
  rcases lt_trichotomy (γ t).re 0 with hn | h0 | hp
  · have := ((GW2Sf.relBdry_real_sign hU hU0 hs hn.ne htA).2).1 hn
    linarith
  · rw [h0, Complex.ofReal_zero, relBdry_zero hU hU0 hs, Complex.zero_re] at hre
    linarith
  · have hlt := hprior t htτ (by rw [hte]; simp)
    have := re_relBdry_lt_of_pos hU hU0 hs hp hlt htA hτA
    rw [← hτe] at this
    linarith

/-- **BUF's `hoff` from the physical earlier visits (left side, mirror form).** -/
theorem relTrace_off_of_prior_neg (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hsafe : MapsTo γ (Iic τ) (relSafe U s)) (him : (γ τ).im = 0) (hneg : (γ τ).re < 0)
    (hprior : ∀ t < τ, (γ t).im = 0 → (γ τ).re < (γ t).re) :
    ∀ u ∈ Ico 0 (a τ), ∀ r : ℝ, r ≤ (relBdry U s (γ τ)).re → relTrace U s γ a τ u ≠ r := by
  intro u hu r hr heq
  set t := invClock a τ u.toNNReal with htdef
  have htτ : t < τ := invClock_lt_of_lt ha hu
  have hτS : γ τ ∈ relSafe U s := hsafe (le_refl τ)
  have htS : γ t ∈ relSafe U s := hsafe htτ.le
  have hτe : γ τ = (((γ τ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hτA : (((γ τ).re : ℝ) : ℂ) ∉ closure (invHull U s) := hτe ▸ hτS.2
  have htip : (relBdry U s (γ τ)).re < 0 := by
    rw [hτe]; exact ((GW2Sf.relBdry_real_sign hU hU0 hs hneg.ne hτA).2).1 hneg
  have heq' : relBdry U s (γ t) = r := heq
  have hte := eq_re_of_relBdry_eq_real hU hU0 hs htS heq'
  have htA : (((γ t).re : ℝ) : ℂ) ∉ closure (invHull U s) := hte ▸ htS.2
  have hre : (relBdry U s (((γ t).re : ℝ) : ℂ)).re = r := by rw [← hte, heq', Complex.ofReal_re]
  rcases lt_trichotomy (γ t).re 0 with hn | h0 | hp
  · have hlt := hprior t htτ (by rw [hte]; simp)
    have := re_relBdry_lt_of_neg hU hU0 hs hn hlt hτA htA
    rw [← hτe] at this
    linarith
  · rw [h0, Complex.ofReal_zero, relBdry_zero hU hU0 hs, Complex.zero_re] at hre
    linarith
  · have := ((GW2Sf.relBdry_real_sign hU hU0 hs hp.ne' htA).1).1 hp
    linarith

end InteractingSLE.Theorem14.GW2Nu
