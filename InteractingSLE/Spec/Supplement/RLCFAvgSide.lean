/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCMain

/-!
# Which side of a chart seed an untouched real point lies on

Packet PROVE-RLC-F, piece (iv) (the reduction of a `ChartRealCompletion` instance to one datum interval). W5's real
local frame (p. 535) chooses the reference by the position of the untouched original-real interval: exterior right
(G8), between the current seeds (G2a), exterior left (reflected G8). In the chart, the reference is matched on a chart
interval, so the chart position of the untouched real points must be read off their physical position. This file
proves that correspondence, deterministically.

**Argument.** Let `η` be a prefix from a real seed with tip `η(u)` and let `ψ : ℍ → D` be the inverse chart (continuous
on `ℍ̄`, bounded displacement, `D ⊆ ℍ` off the prefix) with `ψ(w₀) = η(u)`. The prefix followed by the `ψ`-image of the
vertical ray above `w₀` is a proper curve `γ` (`rayCurve`). The chart half-planes `{Re > w₀}`, `{Re < w₀}` of `ℍ` are
connected and are mapped off `γ`, the first onto points far to the right, hence into the right Jordan side of `γ`
(the second into the left side). A real chart point `y > w₀` whose image is a real point off the prefix is a limit of
the first half-plane, so its image lies in the closed right side, off `γ`, hence in the open right side; a real point
right of the seed `η(0)` and off `γ` is also there, and the two sides are disjoint (Jordan separation). Hence:

* **`chart_side_of_real`**: an untouched real image right (left) of the seed `η(0)` has its chart point right (left)
  of `w₀`.

**The real completion property at the contact.** PROVE-RLC-C's `RLC.ChartRealCompletion` quantifies over every
pair of chart prefixes in a ball around a real point `p` with *some* common point after the seeds; its consumer
`RLC.exists_completion_of_realChart` (W5, pp. 535–536) only uses it when the common point lies over `p`, and the
general form asks for configurations no reference of the source covers (e.g. visits of untouched real points on both
sides of a jump at `p`, or a single visit by the flow whose weight the frame does not control). This file states the
form W5 uses, `ChartRealCompletionAt` (common point over `p`; prefixes in `ℍ̄`), re-proves the consumer with it
(`exists_completion_of_realChartAt`, the same proof), and gives the named chart-level input
`RetainedChartRealCompletionAtStatement` with its wiring to the localized real case and to Theorem W5
(`retainedLocalCompletionRealLocStatement_of_chartAt`, `w5Statement_of_chartRealAt_param`). The old input implies the
new one (`retainedChartRealCompletionAtStatement_of_chartReal`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp9B

section Side

variable {η : ℝ≥0 → ℂ} {u : ℝ≥0} {ψ : ℂ → ℂ} {D : Set ℂ} {w₀ M : ℝ}

/-- **A preconnected set off the closed curve which meets the right side lies in it.** -/
theorem subset_rightSide_of_mem' {γ : ℝ≥0 → ℂ} {s : Set ℂ} (hs : IsPreconnected s)
    (hsS : s ⊆ (seedRayClosure γ)ᶜ) {z : ℂ} (hz : z ∈ s) (hzR : z ∈ rightSide γ) : s ⊆ rightSide γ := by
  rw [rightSide, connectedComponentIn_eq hzR]
  exact hs.subset_connectedComponentIn hz hsS

/-- **A preconnected set off the closed curve which meets the left side lies in it.** -/
theorem subset_leftSide_of_mem' {γ : ℝ≥0 → ℂ} {s : Set ℂ} (hs : IsPreconnected s)
    (hsS : s ⊆ (seedRayClosure γ)ᶜ) {z : ℂ} (hz : z ∈ s) (hzL : z ∈ leftSide γ) : s ⊆ leftSide γ := by
  rw [leftSide, connectedComponentIn_eq hzL]
  exact hs.subset_connectedComponentIn hz hsS

/-- **The prefix followed by the chart image of the vertical ray above its chart point.** -/
def rayCurve (η : ℝ≥0 → ℂ) (u : ℝ≥0) (ψ : ℂ → ℂ) (w₀ : ℝ) : ℝ≥0 → ℂ :=
  fun t => if t ≤ u then η t else ψ ((w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I)

theorem rayCurve_of_le {t : ℝ≥0} (ht : t ≤ u) : rayCurve η u ψ w₀ t = η t := by
  simp [rayCurve, ht]

theorem rayCurve_of_lt {t : ℝ≥0} (ht : u < t) :
    rayCurve η u ψ w₀ t = ψ ((w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I) := by
  simp [rayCurve, not_le.2 ht]

theorem ray_mem_H {t : ℝ≥0} (ht : u < t) : (w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I ∈ H := by
  show (0 : ℝ) < ((w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I).im
  have : (u : ℝ) < t := ht
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
  linarith

theorem ray_mem_Hbar {t : ℝ≥0} (ht : u ≤ t) : (w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I ∈ Hbar := by
  show (0 : ℝ) ≤ ((w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I).im
  have : (u : ℝ) ≤ t := ht
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
  linarith

/-- **The ray curve is a proper curve.** -/
theorem isProperCurve_rayCurve (hc : ContinuousOn η (Icc 0 u)) (hi : InjOn η (Icc 0 u))
    (hm : ∀ t ≤ u, 0 ≤ (η t).im) (hDH : D ⊆ H) (hDA : ∀ z ∈ D, z ∉ η '' Icc 0 u) (hmap : MapsTo ψ H D)
    (hinj : InjOn ψ H) (hψc : ContinuousOn ψ Hbar) (hψM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) (hψw : ψ w₀ = η u) :
    IsProperCurve (rayCurve η u ψ w₀) := by
  have hrayc : Continuous fun t : ℝ≥0 => (w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I := by fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
    · exact hc.mono fun t ht => ⟨zero_le, ht⟩
    · exact hψc.comp hrayc.continuousOn fun t ht => ray_mem_Hbar ht
    · intro t ht
      have ht' : t = u := ht
      subst ht'
      simp [hψw]
  · intro s t hst
    rcases le_or_gt s u with hs | hs <;> rcases le_or_gt t u with ht | ht
    · rw [rayCurve_of_le hs, rayCurve_of_le ht] at hst
      exact hi ⟨zero_le, hs⟩ ⟨zero_le, ht⟩ hst
    · rw [rayCurve_of_le hs, rayCurve_of_lt ht] at hst
      exact absurd ⟨s, ⟨zero_le, hs⟩, hst⟩ (hDA _ (hmap (ray_mem_H ht)))
    · rw [rayCurve_of_lt hs, rayCurve_of_le ht] at hst
      exact absurd ⟨t, ⟨zero_le, ht⟩, hst.symm⟩ (hDA _ (hmap (ray_mem_H hs)))
    · rw [rayCurve_of_lt hs, rayCurve_of_lt ht] at hst
      have h := hinj (ray_mem_H hs) (ray_mem_H ht) hst
      have h2 := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h2
      exact NNReal.coe_injective (by linarith)
  · intro t
    rcases le_or_gt t u with ht | ht
    · rw [rayCurve_of_le ht]; exact hm t ht
    · rw [rayCurve_of_lt ht]; exact le_of_lt (hDH (hmap (ray_mem_H ht)))
  · have hlow : ∀ t : ℝ≥0, u < t → ((t : ℝ) - u) - M ≤ ‖rayCurve η u ψ w₀ t‖ := by
      intro t ht
      rw [rayCurve_of_lt ht]
      set v := (w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I
      have h1 : ((t : ℝ) - u) ≤ ‖v‖ := by
        have := Complex.abs_im_le_norm v
        have hv : v.im = (t : ℝ) - u := by simp [v]
        rw [hv] at this
        exact (le_abs_self _).trans this
      have h2 := hψM v (ray_mem_Hbar ht.le)
      have h3 : ‖v‖ - ‖ψ v‖ ≤ ‖ψ v - v‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le _ _
      linarith
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-((u : ℝ) + M))
      (NNReal.tendsto_coe_atTop.2 tendsto_id))
    filter_upwards [eventually_gt_atTop u] with t ht
    have := hlow t ht
    simp only [id]
    linarith

/-- **The chart half-plane right of `w₀` is sent into the right side of the ray curve** (and the one left of `w₀`
into the left side). -/
theorem image_halfPlane_subset_sides (hc : ContinuousOn η (Icc 0 u)) (hi : InjOn η (Icc 0 u))
    (hm : ∀ t ≤ u, 0 ≤ (η t).im) (h0 : (η 0).im = 0) (hDH : D ⊆ H) (hDA : ∀ z ∈ D, z ∉ η '' Icc 0 u)
    (hmap : MapsTo ψ H D) (hinj : InjOn ψ H) (hψc : ContinuousOn ψ Hbar) (hψM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hψw : ψ w₀ = η u) :
    ψ '' {z | 0 < z.im ∧ w₀ < z.re} ⊆ rightSide (rayCurve η u ψ w₀) ∧
      ψ '' {z | 0 < z.im ∧ z.re < w₀} ⊆ leftSide (rayCurve η u ψ w₀) := by
  set γ := rayCurve η u ψ w₀ with hγdef
  have hγ0 : γ 0 = η 0 := rayCurve_of_le zero_le
  have hγi : ∀ t, 0 ≤ (γ t).im := (isProperCurve_rayCurve hc hi hm hDH hDA hmap hinj hψc hψM hψw).2.2.1
  have h0' : (γ 0).im = 0 := by rw [hγ0]; exact h0
  -- a bound on the real parts of the curve
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, ∀ t ≤ u, |(η t).re| ≤ R₁ := by
    obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_norm_le
    exact ⟨R, fun t ht => (Complex.abs_re_le_norm _).trans (hR _ ⟨t, ⟨zero_le, ht⟩, rfl⟩)⟩
  set B : ℝ := max R₁ (|w₀| + M) + 1 with hB
  have hγB : ∀ t, |(γ t).re| < B := by
    intro t
    rcases le_or_gt t u with ht | ht
    · rw [hγdef, rayCurve_of_le ht]
      have := hR₁ t ht
      have : R₁ ≤ max R₁ (|w₀| + M) := le_max_left _ _
      linarith
    · rw [hγdef, rayCurve_of_lt ht]
      set v := (w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I
      have h1 := hψM v (ray_mem_Hbar ht.le)
      have h2 : |(ψ v - v).re| ≤ ‖ψ v - v‖ := Complex.abs_re_le_norm _
      have hv : v.re = w₀ := by simp [v]
      rw [Complex.sub_re, hv] at h2
      have h3 : |(ψ v).re| ≤ |(ψ v).re - w₀| + |w₀| := by
        have := abs_add_le ((ψ v).re - w₀) w₀
        simpa using this
      have : |w₀| + M ≤ max R₁ (|w₀| + M) := le_max_right _ _
      linarith
  have hseedB : |(γ 0).re| < B := hγB 0
  rw [abs_lt] at hseedB
  -- the far half-planes lie in the two sides
  have hfarR : {z : ℂ | B < z.re} ⊆ rightSide γ := by
    refine subset_rightSide_of_mem' (convex_halfSpace_re_gt B).isPreconnected ?_
      (show ((B + 1 : ℝ) : ℂ) - I ∈ {z : ℂ | B < z.re} by simp) ?_
    · rintro z hz (⟨t, rfl⟩ | ⟨hre, -⟩)
      · exact absurd hz (not_lt.2 (le_of_lt (abs_lt.1 (hγB t)).2))
      · rw [Set.mem_ofPred_eq, hre] at hz; linarith
    · refine lowerRight_subset_rightSide hγi h0' ⟨?_, by simp⟩
      simp only [sub_re, ofReal_re, I_re, sub_zero]; linarith
  have hfarL : {z : ℂ | z.re < -B} ⊆ leftSide γ := by
    refine subset_leftSide_of_mem' (convex_halfSpace_re_lt (-B)).isPreconnected ?_
      (show ((-B - 1 : ℝ) : ℂ) - I ∈ {z : ℂ | z.re < -B} by simp) ?_
    · rintro z hz (⟨t, rfl⟩ | ⟨hre, -⟩)
      · exact absurd hz (not_lt.2 (le_of_lt (abs_lt.1 (hγB t)).1))
      · rw [Set.mem_ofPred_eq, hre] at hz; linarith
    · refine lowerLeft_subset_leftSide hγi h0' ⟨?_, by simp⟩
      simp only [sub_re, ofReal_re, I_re, sub_zero]; linarith
  have hoff : ∀ z ∈ H, z.re ≠ w₀ → ψ z ∉ seedRayClosure γ := by
    intro z hz hzw
    rintro (⟨t, ht⟩ | ⟨-, him⟩)
    · rcases le_or_gt t u with htu | htu
      · rw [hγdef, rayCurve_of_le htu] at ht
        exact hDA _ (hmap hz) ⟨t, ⟨zero_le, htu⟩, ht⟩
      · rw [hγdef, rayCurve_of_lt htu] at ht
        have h := hinj (ray_mem_H htu) hz ht
        apply hzw
        rw [← h]; simp
    · have := hDH (hmap hz)
      rw [h0'] at him
      exact absurd this (not_lt.2 him)
  have hre_close : ∀ z ∈ Hbar, |(ψ z).re - z.re| ≤ M := fun z hz => by
    have h := Complex.abs_re_le_norm (ψ z - z)
    rw [Complex.sub_re] at h
    exact h.trans (hψM z hz)
  constructor
  · set Rp : Set ℂ := {z | 0 < z.im ∧ w₀ < z.re} with hRp
    set X : ℝ := max (B + M) w₀ + 1 with hX
    have hz₀ : ((X : ℂ) + I) ∈ Rp := by
      refine ⟨by simp, ?_⟩
      simp only [add_re, ofReal_re, I_re, add_zero]
      linarith [le_max_right (B + M) w₀]
    have hψz₀ : B < (ψ ((X : ℂ) + I)).re := by
      have h := hre_close ((X : ℂ) + I) (le_of_lt hz₀.1)
      rw [abs_le] at h
      simp only [add_re, ofReal_re, I_re, add_zero] at h
      linarith [h.1, le_max_left (B + M) w₀]
    refine subset_rightSide_of_mem' ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_re_gt w₀) |>.isPreconnected
      |>.image ψ (hψc.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz.1)) ?_ ⟨_, hz₀, rfl⟩ (hfarR hψz₀)
    rintro _ ⟨z, hz, rfl⟩
    exact hoff z hz.1 (ne_of_gt hz.2)
  · set Rm : Set ℂ := {z | 0 < z.im ∧ z.re < w₀} with hRm
    set X : ℝ := min (-B - M) w₀ - 1 with hX
    have hz₀ : ((X : ℂ) + I) ∈ Rm := by
      refine ⟨by simp, ?_⟩
      simp only [add_re, ofReal_re, I_re, add_zero]
      linarith [min_le_right (-B - M) w₀]
    have hψz₀ : (ψ ((X : ℂ) + I)).re < -B := by
      have h := hre_close ((X : ℂ) + I) (le_of_lt hz₀.1)
      rw [abs_le] at h
      simp only [add_re, ofReal_re, I_re, add_zero] at h
      linarith [h.2, min_le_left (-B - M) w₀]
    refine subset_leftSide_of_mem' ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_re_lt w₀) |>.isPreconnected
      |>.image ψ (hψc.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz.1)) ?_ ⟨_, hz₀, rfl⟩ (hfarL hψz₀)
    rintro _ ⟨z, hz, rfl⟩
    exact hoff z hz.1 (ne_of_lt hz.2)

/-- **The chart side of an untouched real point.** If the image `ψ(y)` of a real chart point is a real point off the
prefix, then `ψ(y)` right of the seed `η(0)` forces `y > w₀`, and left of it forces `y < w₀`. -/
theorem chart_side_of_real (hc : ContinuousOn η (Icc 0 u)) (hi : InjOn η (Icc 0 u))
    (hm : ∀ t ≤ u, 0 ≤ (η t).im) (h0 : (η 0).im = 0) (hDH : D ⊆ H) (hDA : ∀ z ∈ D, z ∉ η '' Icc 0 u)
    (hmap : MapsTo ψ H D) (hinj : InjOn ψ H) (hψc : ContinuousOn ψ Hbar) (hψM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hψw : ψ w₀ = η u) {y : ℝ} (hyA : ψ y ∉ η '' Icc 0 u) (hyr : (ψ y).im = 0) :
    ((η 0).re < (ψ y).re → w₀ < y) ∧ ((ψ y).re < (η 0).re → y < w₀) := by
  set γ := rayCurve η u ψ w₀ with hγdef
  have hγ := isProperCurve_rayCurve hc hi hm hDH hDA hmap hinj hψc hψM hψw
  have hγ0 : γ 0 = η 0 := rayCurve_of_le zero_le
  have h0' : (γ 0).im = 0 := by rw [hγ0]; exact h0
  obtain ⟨hR, hL⟩ := image_halfPlane_subset_sides hc hi hm h0 hDH hDA hmap hinj hψc hψM hψw
  have hyS : ψ y ∉ seedRayClosure γ := by
    rintro (⟨t, ht⟩ | ⟨hre, him⟩)
    · rcases le_or_gt t u with htu | htu
      · rw [hγdef, rayCurve_of_le htu] at ht
        exact hyA ⟨t, ⟨zero_le, htu⟩, ht⟩
      · rw [hγdef, rayCurve_of_lt htu] at ht
        have h1 : 0 < (ψ ((w₀ : ℂ) + (((t : ℝ) - u : ℝ) : ℂ) * I)).im := hDH (hmap (ray_mem_H htu))
        rw [ht] at h1
        exact absurd hyr (ne_of_gt h1)
    · have he : ψ y = η 0 := Complex.ext (by rw [hre, hγ0]) (by rw [hyr, h0])
      exact hyA ⟨0, ⟨le_rfl, zero_le⟩, he.symm⟩
  have hyw : y ≠ w₀ := fun h => hyA ⟨u, ⟨zero_le, le_rfl⟩, by rw [h, hψw]⟩
  have hyH : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hlim : Tendsto (fun s : ℝ => ψ ((y : ℂ) + (s : ℂ) * I)) (𝓝[>] 0) (𝓝 (ψ y)) := by
    refine (hψc _ hyH).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have : Continuous fun s : ℝ => (y : ℂ) + (s : ℂ) * I := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      show (0 : ℝ) ≤ ((y : ℂ) + (s : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      exact le_of_lt hs
  have hpt : ∀ s : ℝ, ((y : ℂ) + (s : ℂ) * I).im = s ∧ ((y : ℂ) + (s : ℂ) * I).re = y := fun s => by
    simp
  have hdisj := disjoint_leftSide_rightSide hγ h0'
  have hcompl := compl_seedRayClosure_eq hγ h0'
  have hside_R : w₀ < y → ψ y ∈ rightSide γ := by
    intro hwy
    have hcl : ψ y ∈ closure (rightSide γ) := by
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      refine hR ⟨_, ⟨?_, ?_⟩, rfl⟩
      · rw [(hpt s).1]; exact hs
      · rw [(hpt s).2]; exact hwy
    have hmem : ψ y ∈ leftSide γ ∪ rightSide γ := by rw [← hcompl]; exact hyS
    rcases hmem with hl | hr
    · exfalso
      obtain ⟨z, hz⟩ := mem_closure_iff.1 hcl _ (isOpen_leftSide hγ) hl
      exact Set.disjoint_left.1 hdisj hz.1 hz.2
    · exact hr
  have hside_L : y < w₀ → ψ y ∈ leftSide γ := by
    intro hyw'
    have hcl : ψ y ∈ closure (leftSide γ) := by
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      refine hL ⟨_, ⟨?_, ?_⟩, rfl⟩
      · rw [(hpt s).1]; exact hs
      · rw [(hpt s).2]; exact hyw'
    have hmem : ψ y ∈ leftSide γ ∪ rightSide γ := by rw [← hcompl]; exact hyS
    rcases hmem with hl | hr
    · exact hl
    · exfalso
      obtain ⟨z, hz⟩ := mem_closure_iff.1 hcl _ (isOpen_rightSide hγ) hr
      exact Set.disjoint_left.1 hdisj hz.2 hz.1
  have hψy : ψ y = ((ψ y).re : ℂ) := Complex.ext (by simp) (by simp [hyr])
  have hyS' : (((ψ y).re : ℝ) : ℂ) ∉ seedRayClosure γ := by rw [← hψy]; exact hyS
  constructor
  · intro hre
    rcases lt_or_gt_of_ne hyw with hlt | hgt
    · exfalso
      have h1 := hside_L hlt
      have h2 : ψ y ∈ rightSide γ := by
        rw [hψy]; exact ofReal_mem_rightSide hγ.2.2.1 h0' (by show (γ 0).re < _; rw [hγ0]; exact hre) hyS'
      exact Set.disjoint_left.1 hdisj h1 h2
    · exact hgt
  · intro hre
    rcases lt_or_gt_of_ne hyw with hlt | hgt
    · exact hlt
    · exfalso
      have h1 := hside_R hgt
      have h2 : ψ y ∈ leftSide γ := by
        rw [hψy]; exact Supp9B.ofReal_mem_leftSide hγ.2.2.1 h0' (by show _ < (γ 0).re; rw [hγ0]; exact hre) hyS'
      exact Set.disjoint_left.1 hdisj h2 h1

end Side

/-! ### The real completion property at the contact point -/

section At

open Supp7 Supp9 Supp9D Sec2.Assembly

/-- **The chart real completion property at the contact** (W5's real local frame, pp. 535–536, in the form W5 uses
it): `RLC.ChartRealCompletion` with the common point of the two prefixes required to lie over the centre `p` of the
ball (W5's mutual contact: "Its selected real point `p` is a mutual contact, strictly before both original lifetimes",
shortcut note §5.3). PROVE-RLC-C's consumer `exists_completion_of_realChart` applies the property only at such a
common point. -/
def ChartRealCompletionAt (J : Finset ℝ) (x₁ x₂ : ℝ) (A : Set ℂ) (ψ : ℂ → ℂ) (Γ₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞)
    (Γ₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) : Prop :=
  ∀ p ρ : ℝ, 0 < ρ → (∀ y : ℝ, |y - p| < ρ → y ≠ p → y ∉ J) → ρ ≤ |x₁ - p| → ρ ≤ |x₂ - p| →
    ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < U₁ → (s₂ : ℝ≥0∞) < U₂ → (∀ t ≤ s₁, Γ₁ t ∈ Hbar) → (∀ t ≤ s₂, Γ₂ t ∈ Hbar) →
      (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → ψ (Γ₁ t) ∈ ball (p : ℂ) ρ ∧ ψ (Γ₁ t) ∉ A) →
      (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → ψ (Γ₂ t) ∈ ball (p : ℂ) ρ ∧ ψ (Γ₂ t) ∉ A) →
      (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ t₁ = Γ₂ t₂ ∧ ψ (Γ₁ t₁) = p) →
      IsChartCompletable Γ₁ s₁ Γ₂ s₂

/-- `ChartRealCompletion` implies the property at the contact. -/
theorem ChartRealCompletion.chartRealCompletionAt {J : Finset ℝ} {x₁ x₂ : ℝ} {A : Set ℂ} {ψ : ℂ → ℂ}
    {Γ₁ Γ₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞} (h : ChartRealCompletion J x₁ x₂ A ψ Γ₁ U₁ Γ₂ U₂) :
    ChartRealCompletionAt J x₁ x₂ A ψ Γ₁ U₁ Γ₂ U₂ :=
  fun p ρ hρ hJ h1 h2 s₁ s₂ hs₁ hs₂ _ _ hp₁ hp₂ ⟨t₁, t₂, a, b, c, d, e, _⟩ =>
    h p ρ hρ hJ h1 h2 s₁ s₂ hs₁ hs₂ hp₁ hp₂ ⟨t₁, t₂, a, b, c, d, e⟩

/-- **The local completion at a retained pair, pathwise, localized real-contact case, from the property at the
contact** (the proof of PROVE-RLC-C's `exists_completion_of_realChart`, which applies the property only at the chart
point over the contact). -/
theorem exists_completion_of_realChartAt {J : Finset ℝ} {η₁ η₂ Γ₁ Γ₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ U₁ U₂ : ℝ≥0∞}
    {u r a τ : ℝ≥0} {w : ℝ} {ψ : ℂ → ℂ}
    (hc₁ : ContinuousOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hm₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ ζ₁ → 0 ≤ (η₁ x).im) (hm₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ ζ₂ → 0 ≤ (η₂ y).im)
    (h01 : (η₁ 0).im = 0) (h02 : (η₂ 0).im = 0) (hseed : (η₂ 0).re ≤ (η₁ 0).re)
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) (hJ : IsRealJointChart η₁ ζ₁ u η₂ ζ₂ r Γ₁ Γ₂ U₁ U₂ ψ)
    (hw : 0 < w) (hΓ₁0 : Γ₁ 0 = w) (hΓ₂0 : Γ₂ 0 = 0)
    (hCR : ChartRealCompletionAt J (η₁ 0).re (η₂ 0).re (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) ψ Γ₁ U₁ Γ₂ U₂)
    (hua : u < a) (haζ : (a : ℝ≥0∞) < ζ₁) (hrτ : r < τ) (hτζ : (τ : ℝ≥0∞) < ζ₂) (hp : η₁ a = η₂ τ)
    (hf₁ : ∀ x : ℝ≥0, u < x → x ≤ a → η₁ x ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hf₂ : ∀ y : ℝ≥0, r < y → y ≤ τ → η₂ y ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hloc : IsLocalContact J η₁ u a η₂ r τ)
    (hreal : (∃ x : ℝ≥0, u < x ∧ x ≤ a ∧ η₁ x ∉ H) ∨ ∃ y : ℝ≥0, r < y ∧ y ≤ τ ∧ η₂ y ∉ H) :
    ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ∧
      HasOrderedProperCompletions η₁ a₂ η₂ b₂ := by
  obtain ⟨hbij, hoff, hψc, hψM, hψ0, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁⟩,
    ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂⟩, hinj⟩ := hJ
  set A := η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r with hAdef
  have hle₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ (u : ℝ≥0∞) → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => hx.trans (le_of_lt hord.1)
  have hle₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ (r : ℝ≥0∞) → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => hy.trans (le_of_lt hord.2.1)
  have hA : IsClosed A :=
    isClosed_prefixUnion (hc₁.mono fun x hx => hle₁ x (ENNReal.coe_le_coe.2 hx.2))
      (hc₂.mono fun y hy => hle₂ y (ENNReal.coe_le_coe.2 hy.2))
  have hpim : (η₁ a).im = 0 := hloc.im_eq_zero (hm₁ a haζ.le) hreal
  obtain ⟨ρ, hρ, hball₁, hball₂, -, hjump, hρ1, hρ2⟩ := hloc
  set P := (η₁ a).re with hPdef
  have hpP : η₁ a = (P : ℂ) := eq_ofReal_re_of_im_eq_zero hpim
  obtain ⟨s₁, a₂, hs₁σ, hcs₁, haa₂, ha₂ζ, hfr₁, hcimg₁, hc₁0⟩ :=
    exists_chart_cut_open hA isOpen_ball hc₁ hua haζ hf₁ hball₁ hmono₁ himg₁
  obtain ⟨s₂, b₂, hs₂σ, hcs₂, hτb₂, hb₂ζ, hfr₂, hcimg₂, hc₂0⟩ :=
    exists_chart_cut_open hA isOpen_ball hc₂ hrτ hτζ hf₂ hball₂ hmono₂ himg₂
  have h0σ₁ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have h0σ₂ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₂ := by simp
  have hψw : ψ w = η₁ u := by rw [← hΓ₁0, ← (hpth₁ 0 h0σ₁).1, hc₁0]
  -- the chart prefixes are localized and fresh
  have hpre₁ : ∀ t : ℝ≥0, 0 < t → t ≤ s₁ → ψ (Γ₁ t) ∈ ball (η₁ a) ρ ∧ ψ (Γ₁ t) ∉ A := by
    intro t ht hts
    have htσ : (t : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 hts).trans (le_of_lt hs₁σ)
    have hlo : u < c₁ t := by rw [← hc₁0]; exact hmono₁ h0σ₁ htσ ht
    have hhi : c₁ t ≤ a₂ := by rw [← hcs₁]; exact hmono₁.monotoneOn htσ (le_of_lt hs₁σ) hts
    obtain ⟨hA', hN'⟩ := hfr₁ (c₁ t) hlo hhi
    rw [(hpth₁ t htσ).1] at hA' hN'
    exact ⟨hN', hA'⟩
  have hpre₂ : ∀ t : ℝ≥0, 0 < t → t ≤ s₂ → ψ (Γ₂ t) ∈ ball (η₁ a) ρ ∧ ψ (Γ₂ t) ∉ A := by
    intro t ht hts
    have htσ : (t : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 hts).trans (le_of_lt hs₂σ)
    have hlo : r < c₂ t := by rw [← hc₂0]; exact hmono₂ h0σ₂ htσ ht
    have hhi : c₂ t ≤ b₂ := by rw [← hcs₂]; exact hmono₂.monotoneOn htσ (le_of_lt hs₂σ) hts
    obtain ⟨hA', hN'⟩ := hfr₂ (c₂ t) hlo hhi
    rw [(hpth₂ t htσ).1] at hA' hN'
    exact ⟨hN', hA'⟩
  have hs₁0 : 0 < s₁ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hc₁0] at hcs₁
    exact absurd (hcs₁ ▸ haa₂) (not_lt.2 hua.le)
  have hs₂0 : 0 < s₂ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hc₂0] at hcs₂
    exact absurd (hcs₂ ▸ hτb₂) (not_lt.2 hrτ.le)
  -- the chart points over the contact coincide
  have hDH : activeDomain η₁ u η₂ r ⊆ H := fun z hz => hz.1.1
  obtain ⟨t₁, ht₁, hct₁⟩ : a ∈ c₁ '' Icc 0 s₁ := by rw [hcimg₁]; exact ⟨hua.le, haa₂.le⟩
  obtain ⟨t₂, ht₂, hct₂⟩ : τ ∈ c₂ '' Icc 0 s₂ := by rw [hcimg₂]; exact ⟨hrτ.le, hτb₂.le⟩
  have ht₁σ : (t₁ : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 ht₁.2).trans (le_of_lt hs₁σ)
  have ht₂σ : (t₂ : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 ht₂.2).trans (le_of_lt hs₂σ)
  have ht₁0 : 0 < t₁ := pos_iff_ne_zero.2 fun h => by rw [h, hc₁0] at hct₁; exact (ne_of_lt hua) hct₁
  have ht₂0 : 0 < t₂ := pos_iff_ne_zero.2 fun h => by rw [h, hc₂0] at hct₂; exact (ne_of_lt hrτ) hct₂
  have hψt₁ : ψ (Γ₁ t₁) = η₁ a := by rw [← hct₁]; exact ((hpth₁ t₁ ht₁σ).1).symm
  have hψt₂ : ψ (Γ₂ t₂) = η₁ a := by rw [hp, ← hct₂]; exact ((hpth₂ t₂ ht₂σ).1).symm
  have hreal_of : ∀ z : ℂ, z ∈ Hbar → ψ z = η₁ a → z.im = 0 := by
    intro z hz he
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hlt | heq
    · have h1 : (0 : ℝ) < (ψ z).im := hDH (hbij.mapsTo hlt)
      rw [he, hpim] at h1
      exact absurd h1 (lt_irrefl 0)
    · exact heq.symm
  have hΓ₁r := hreal_of _ (hpth₁ t₁ ht₁σ).2 hψt₁
  have hΓ₂r := hreal_of _ (hpth₂ t₂ ht₂σ).2 hψt₂
  have hcommon : Γ₁ t₁ = Γ₂ t₂ := by
    have hpA : η₁ a ∉ A := hf₁ a hua le_rfl
    have h := hinj (Γ₁ t₁).re (Γ₂ t₂).re
      (by rw [← eq_ofReal_re_of_im_eq_zero hΓ₁r, ← eq_ofReal_re_of_im_eq_zero hΓ₂r, hψt₁, hψt₂])
      (by rw [← eq_ofReal_re_of_im_eq_zero hΓ₁r, hψt₁, hpim])
      (by rw [← eq_ofReal_re_of_im_eq_zero hΓ₁r, hψt₁]; exact hpA)
    rw [eq_ofReal_re_of_im_eq_zero hΓ₁r, eq_ofReal_re_of_im_eq_zero hΓ₂r, h]
  -- the chart real completion property, then G10
  have hnorm : ∀ x : ℝ, ‖(x : ℂ) - (P : ℂ)‖ = |x - P| := fun x => by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hρ1' : ρ ≤ |(η₁ 0).re - P| := by
    rw [← hnorm, ← eq_ofReal_re_of_im_eq_zero h01, ← hpP]; exact hρ1
  have hρ2' : ρ ≤ |(η₂ 0).re - P| := by
    rw [← hnorm, ← eq_ofReal_re_of_im_eq_zero h02, ← hpP]; exact hρ2
  have hCC := hCR P ρ hρ hjump hρ1' hρ2' s₁ s₂ (lt_of_lt_of_le hs₁σ hσ₁) (lt_of_lt_of_le hs₂σ hσ₂)
    (fun t ht => (hpth₁ t ((ENNReal.coe_le_coe.2 ht).trans (le_of_lt hs₁σ))).2)
    (fun t ht => (hpth₂ t ((ENNReal.coe_le_coe.2 ht).trans (le_of_lt hs₂σ))).2)
    (fun t ht hts => by rw [← hpP]; exact hpre₁ t ht hts) (fun t ht hts => by rw [← hpP]; exact hpre₂ t ht hts)
    ⟨t₁, t₂, ht₁0, ht₁.2, ht₂0, ht₂.2, hcommon, by rw [hψt₁, hpP]⟩
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hγord, hav₁, hav₂⟩ := hCC
  obtain ⟨γ₁', γ₂', hγ₁', hγ₂', hord', hav₁', hav₂', hreal₁, hreal₂⟩ :=
    Supp7.exists_interiorized_completions_of_seeds hγ₁ hγ₂ (by rw [hΓ₁0]; simp) hγord hav₁ hav₂
  -- the chart real points over genuine original-real points of the ball
  set E : Set ℝ := {y | ψ y ∈ ball (η₁ a) ρ ∧ ψ y ∉ A} with hEdef
  have hψR : Continuous fun y : ℝ => ψ y :=
    hψc.comp_continuous continuous_ofReal fun y => show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hEo : IsOpen E := (isOpen_ball.inter hA.isOpen_compl).preimage hψR
  have hEr : ∀ y ∈ E, (ψ y).im = 0 := fun y hy => im_eq_zero_of_real hA hbij hoff hψc y hy.2
  have hEi : ∀ y ∈ E, ∀ y' ∈ E, ψ y = ψ y' → y = y' := fun y hy y' _ he => hinj y y' he (hEr y hy) hy.2
  have hEside : (∀ y ∈ E, (ψ y).re < (η₁ 0).re) ∨ ∀ y ∈ E, (η₂ 0).re < (ψ y).re := by
    have hre : ∀ y ∈ E, |(ψ y).re - P| < ρ := fun y hy => by
      have h1 := hy.1
      rw [mem_ball, hpP, Complex.dist_eq] at h1
      exact lt_of_le_of_lt (by simpa using abs_re_le_norm (ψ y - P)) h1
    rcases lt_or_gt_of_ne (show P ≠ (η₁ 0).re from fun h => by
      rw [h, sub_self, abs_zero] at hρ1'; exact absurd hρ1' (not_le.2 hρ)) with hlt | hgt
    · refine Or.inl fun y hy => ?_
      have h1 := hre y hy
      rw [abs_of_pos (sub_pos.2 hlt)] at hρ1'
      rw [abs_lt] at h1
      linarith
    · refine Or.inr fun y hy => ?_
      have h1 := hre y hy
      rw [abs_of_neg (sub_neg.2 (lt_of_le_of_lt hseed hgt))] at hρ2'
      rw [abs_lt] at h1
      linarith
  have hglue : ∀ (γ : ℝ≥0 → ℂ), (∀ t, 0 ≤ (γ t).im) →
      (∀ t, (γ t).im = 0 → γ t ∈ Γ₁ '' Iic s₁ ∪ Γ₂ '' Iic s₂) → (∀ t, 0 < t → γ t ≠ Γ₁ 0) →
      (∀ t, 0 < t → γ t ≠ Γ₂ 0) → ∀ t, 0 < t → IsGluePoint E (γ t) := by
    intro γ hγim hγre hγ1 hγ2 t ht
    rcases (hγim t).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq.symm, ?_⟩
      have hz : γ t = ((γ t).re : ℂ) := eq_ofReal_re_of_im_eq_zero heq.symm
      show ψ ((γ t).re : ℂ) ∈ ball (η₁ a) ρ ∧ ψ ((γ t).re : ℂ) ∉ A
      rw [← hz]
      rcases hγre t heq.symm with ⟨t'', ht'', he⟩ | ⟨t'', ht'', he⟩
      · have ht''0 : 0 < t'' := pos_iff_ne_zero.2 fun h0 => hγ1 t ht (by rw [← he, h0])
        rw [← he]; exact hpre₁ t'' ht''0 ht''
      · have ht''0 : 0 < t'' := pos_iff_ne_zero.2 fun h0 => hγ2 t ht (by rw [← he, h0])
        rw [← he]; exact hpre₂ t'' ht''0 ht''
  have hR₁ : ∀ t, 0 < t → IsGluePoint E (γ₁' t) :=
    hglue γ₁' hγ₁'.2.2.1 hreal₁
      (fun t ht he => (ne_of_gt ht) (hγ₁'.2.1 (he.trans (hγ₁'.2.2.2.2 0 zero_le).symm)))
      (fun t _ he => hav₂' ⟨t, he⟩)
  have hR₂ : ∀ t, 0 < t → IsGluePoint E (γ₂' t) :=
    hglue γ₂' hγ₂'.2.2.1 hreal₂ (fun t _ he => hav₁' ⟨t, he⟩)
      (fun t ht he => (ne_of_gt ht) (hγ₂'.2.1 (he.trans (hγ₂'.2.2.2.2 0 zero_le).symm)))
  -- the planar gluing
  have hsub₁ : ∀ x ∈ Icc (0 : ℝ≥0) a₂, (x : ℝ≥0∞) ≤ ζ₁ := fun x hx =>
    (ENNReal.coe_le_coe.2 hx.2).trans (le_of_lt ha₂ζ)
  have hsub₂ : ∀ y ∈ Icc (0 : ℝ≥0) b₂, (y : ℝ≥0∞) ≤ ζ₂ := fun y hy =>
    (ENNReal.coe_le_coe.2 hy.2).trans (le_of_lt hb₂ζ)
  have himg₁' : η₁ '' Icc u a₂ = (fun s => ψ (Γ₁ s)) '' Icc 0 s₁ := by
    rw [← hcimg₁, image_image]
    refine image_congr fun s hs => (hpth₁ s ((ENNReal.coe_le_coe.2 hs.2).trans (le_of_lt hs₁σ))).1
  have himg₂' : η₂ '' Icc r b₂ = (fun s => ψ (Γ₂ s)) '' Icc 0 s₂ := by
    rw [← hcimg₂, image_image]
    refine image_congr fun s hs => (hpth₂ s ((ENNReal.coe_le_coe.2 hs.2).trans (le_of_lt hs₂σ))).1
  have hend₁ : ψ (Γ₁ s₁) = η₁ a₂ := by rw [← hcs₁]; exact ((hpth₁ s₁ (le_of_lt hs₁σ)).1).symm
  have hend₂ : ψ (Γ₂ s₂) = η₂ b₂ := by rw [← hcs₂]; exact ((hpth₂ s₂ (le_of_lt hs₂σ)).1).symm
  refine ⟨a₂, b₂, haa₂, ha₂ζ, hτb₂, hb₂ζ, ?_⟩
  exact hasOrderedProperCompletions_glue_real hord.2.2.2.2.2.2.2.2 h01 h02 hseed (hua.trans haa₂).le
    (hrτ.trans hτb₂).le (hc₁.mono hsub₁) (hi₁.mono hsub₁) (fun x hx => hm₁ x (hsub₁ x ⟨zero_le, hx⟩))
    (hc₂.mono hsub₂) (hi₂.mono hsub₂) (fun y hy => hm₂ y (hsub₂ y ⟨zero_le, hy⟩)) hord.2.2.1 hord.2.2.2.1
    hord.2.2.2.2.1 hord.2.2.2.2.2.1 hDH (Set.disjoint_left.2 fun z hz hzA => hz.1.2 hzA) hbij.mapsTo
    hbij.injOn hψc hψM hψ0 hψw hEo hEi hEr (fun y hy => hy.2) hEside hw hΓ₁0 hΓ₂0 hs₁0 hs₂0 himg₁' hend₁
    himg₂' hend₂ hγ₁' hγ₂' hord' hR₁ hR₂


/-- **Named input: the joint chart and its real completion property at the contact**
(`RLC.RetainedChartRealCompletionStatement` with `ChartRealCompletionAt`; W5's real local frame, pp. 535–536). -/
def RetainedChartRealCompletionAtStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (Γ₁ Γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) (W : Ω → ℝ),
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        0 < W ω ∧ Γ₁ ω 0 = W ω ∧ Γ₂ ω 0 = 0 ∧ ∃ ψ : ℂ → ℂ,
          IsRealJointChart (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r (Γ₁ ω) (Γ₂ ω) (U₁ ω) (U₂ ω) ψ ∧
          ChartRealCompletionAt jumps x₁ x₂ (η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) ψ (Γ₁ ω) (U₁ ω) (Γ₂ ω) (U₂ ω)

/-- PROVE-RLC-C's chart-level named input implies the one at the contact. -/
theorem retainedChartRealCompletionAtStatement_of_chartReal (hC : RetainedChartRealCompletionStatement.{u}) :
    RetainedChartRealCompletionAtStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨Γ₁, Γ₂, U₁, U₂, W, hae⟩ := hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  refine ⟨Γ₁, Γ₂, U₁, U₂, W, ?_⟩
  filter_upwards [hae] with ω hω hord
  obtain ⟨hW, h1, h2, ψ, hJ, hCR⟩ := hω hord
  exact ⟨hW, h1, h2, ψ, hJ, hCR.chartRealCompletionAt⟩

/-- **The localized real-contact case of the local completion** (`RLC.RetainedLocalCompletionRealLocStatement`) from
the chart-level input at the contact. -/
theorem retainedLocalCompletionRealLocStatement_of_chartAt (hC : RetainedChartRealCompletionAtStatement.{u}) :
    RetainedLocalCompletionRealLocStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨Γ₁, Γ₂, U₁, U₂, W, hae⟩ := hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  filter_upwards [hae, Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Supp7.ae_im_nonneg_of_isFlowLine hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₂,
    Supp9.ae_apply_zero_of_isFlowLine hη₁, Supp9.ae_apply_zero_of_isFlowLine hη₂]
    with ω hω c₁ c₂ i₁ i₂ m₁ m₂ z₁ z₂ hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ hloc hreal
  obtain ⟨hW, hΓ₁0, hΓ₂0, ψ, hJ, hCR⟩ := hω hord
  exact exists_completion_of_realChartAt c₁ c₂ i₁ i₂ m₁ m₂ (by rw [z₁]; simp) (by rw [z₂]; simp)
    (by rw [z₁, z₂]; simpa using hx) hord hJ hW hΓ₁0 hΓ₂0 (by rw [z₁, z₂, ofReal_re, ofReal_re]; exact hCR)
    hua haζ hrτ hτζ hp hf₁ hf₂ hloc hreal

/-- **Theorem W5** from the chart-level real-contact input at the contact (as `RLC.w5Statement_of_chartReal_param`). -/
theorem w5Statement_of_chartRealAt_param (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hC : RetainedChartRealCompletionAtStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_realLoc_param h25 hW0a hW0b h77 hJ hCS hG2 hG3 h12p h13 hD
    (retainedLocalCompletionRealLocStatement_of_chartAt hC)

end At

end RLC

end InteractingSLE
