/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux94
import InteractingSLE.Spec.Supplement.RLCMain
import InteractingSLE.Spec.Restart.ChartMeasReduce

/-!
# The gluing at a common first contact (proof of Lemma G2, last paragraph)

Packet PROVE-RLC-I. Source: proof of Lemma G2 (supplement p. 491): "If the complete curves have no finite common point,
their properness and the cyclic order of the two distinct real seeds imply the asserted Jordan order. […] Finally glue
the two disjoint initial arcs to these ordered continuations at their common active prime end. The unbounded component
has the orientation inherited from the real seed order. Closed-side containment of the two new arcs in this component
therefore gives closed-side containment of the complete original arcs. This is the Jordan crosscut theorem with the
bounded initial gap filled. It remains valid if the first contact is real".

Deterministic statements, for two complete curves `α₁` (from `w₁`, proper simple) and `α₂` (from `w₂ < w₁`, continuous)
in `ℍ̄`, each avoiding the other's seed:

* `range_subset_leftSide_of_disjoint`: with no common point, `α₂` lies in the open left side of `α₁`;
* `image_leftSide_inter_H_subset`: at a common first contact, the inverse first-contact chart `ψ` maps the left side of
  the first chart continuation (in `ℍ`) into the left side of `α₁` — `ψ` sends it into the complement of `α₁` (the
  active domain misses the prefixes, `ψ` is injective on `ℍ`), it is preconnected (`isPreconnected_leftSide_inter_H`),
  and it contains points near a far-left chart real point `x`, whose image `ψ(x)` is a far-left physical real point
  (bounded displacement; a point of `ℍ` off the prefixes adherent to the active domain lies in it, and `ψ(x) ∉ D`);
* **`range_subset_closedLeftSide_glue`**: the gluing — the initial arc of `α₂` lies in the left side of `α₁` (it avoids
  `α₁` before the first contact and starts at `w₂`), the contact point is on `α₁`, and every later point is the image of
  a chart point of `γ₂` on `γ₁` or on the left side of `γ₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp9B Restart
open Sec5.Prop55Half (IsSeedProper)

variable {α₁ α₂ γ₁ γ₂ : ℝ≥0 → ℂ} {w₁ w₂ : ℝ}

/-- A real point left of the seed and off a curve in `ℍ̄` is on its open left side. -/
theorem ofReal_mem_leftSide_of_lt_seed (hα : ∀ t, 0 ≤ (α₁ t).im) (h0 : α₁ 0 = w₁) {x : ℝ} (hx : x < w₁)
    (hxα : (x : ℂ) ∉ range α₁) : (x : ℂ) ∈ leftSide α₁ := by
  refine ofReal_mem_leftSide hα (by rw [h0]; simp) (by rw [h0]; simpa using hx) ?_
  rintro (hr | ⟨hre, -⟩)
  · exact hxα hr
  · rw [h0] at hre
    simp only [Complex.ofReal_re] at hre
    exact absurd hre hx.ne

/-- A point of `ℍ̄` with real part `w₁` and on the lower seed ray of a curve from `w₁` is `w₁`. -/
theorem eq_of_mem_seedRay {z : ℂ} (h0 : α₁ 0 = w₁) (hz : 0 ≤ z.im) (hre : z.re = (α₁ 0).re)
    (him : z.im ≤ (α₁ 0).im) : z = w₁ := by
  rw [h0] at hre him
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  exact Complex.ext (by simpa using hre) (by simp; linarith)

/-- **No common point**: a continuous curve in `ℍ̄` from `w₂ < w₁` missing `α₁` and its seed lies in the open left
side of `α₁`. -/
theorem range_subset_leftSide_of_disjoint (hα₁ : ∀ t, 0 ≤ (α₁ t).im) (hc₂ : Continuous α₂)
    (hα₂ : ∀ t, 0 ≤ (α₂ t).im) (hw : w₂ < w₁) (h0₁ : α₁ 0 = w₁) (h0₂ : α₂ 0 = w₂)
    (hw₁ : (w₁ : ℂ) ∉ range α₂) (hdis : ∀ s t, α₁ s ≠ α₂ t) : range α₂ ⊆ leftSide α₁ := by
  have hw₂ : (w₂ : ℂ) ∉ range α₁ := by
    rintro ⟨s, hs⟩
    exact hdis s 0 (by rw [hs, h0₂])
  refine subset_leftSide_of_mem (isPreconnected_range hc₂) ?_ ⟨0, h0₂⟩
    (ofReal_mem_leftSide_of_lt_seed hα₁ h0₁ hw hw₂)
  rintro _ ⟨t, rfl⟩ (⟨s, hs⟩ | ⟨hre, him⟩)
  · exact hdis s t hs
  · exact hw₁ ⟨t, eq_of_mem_seedRay h0₁ (hα₂ t) hre him⟩

/-- A strictly increasing clock onto `[s₀, ∞)` starts at `s₀` and reaches every later time. -/
theorem clock_zero_and_surj {c : ℝ≥0 → ℝ≥0} {s₀ : ℝ≥0} (hm : StrictMonoOn c {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤})
    (hi : c '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ⊤}) :
    c 0 = s₀ ∧ ∀ s, s₀ ≤ s → ∃ u, c u = s := by
  have hsurj : ∀ s, s₀ ≤ s → ∃ u, c u = s := by
    intro s hs
    have hmem : s ∈ c '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤} := by rw [hi]; exact ⟨hs, le_top⟩
    obtain ⟨u, -, hu⟩ := hmem
    exact ⟨u, hu⟩
  refine ⟨?_, hsurj⟩
  obtain ⟨v, hv⟩ := hsurj s₀ le_rfl
  have h1 : s₀ ≤ c 0 := by
    have hmem : c 0 ∈ c '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤} := mem_image_of_mem _ (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top)
    rw [hi] at hmem
    exact hmem.1
  have h2 : c 0 ≤ c v := hm.monotoneOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top)
    (show (v : ℝ≥0∞) ≤ ⊤ from le_top) zero_le
  exact le_antisymm (hv ▸ h2) h1

/-- After the first contact, a point of `α₁` is the inverse-chart image of a point of `γ₁` at a positive time. -/
theorem exists_pos_of_clock {c : ℝ≥0 → ℝ≥0} {s₀ : ℝ≥0} (hm : StrictMonoOn c {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤})
    (hi : c '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ⊤}) {s : ℝ≥0} (hs : s₀ < s) :
    ∃ v, 0 < v ∧ c v = s := by
  obtain ⟨h0, hsurj⟩ := clock_zero_and_surj hm hi
  obtain ⟨v, hv⟩ := hsurj s hs.le
  refine ⟨v, pos_iff_ne_zero.2 fun hv0 => ?_, hv⟩
  rw [hv0, h0] at hv
  exact hs.ne hv

/-- **The inverse first-contact chart maps the chart left side of `γ₁` into the left side of `α₁`.** -/
theorem image_leftSide_inter_H_subset (hα₁ : IsProperCurve α₁) (hc₂ : Continuous α₂) (h0₁ : α₁ 0 = w₁)
    {s₀ t₀ : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} (hC : IsFirstContactChart α₁ s₀ α₂ t₀ φ ψ lift)
    {c₁ : ℝ≥0 → ℝ≥0} (hm₁ : StrictMonoOn c₁ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤})
    (hi₁ : c₁ '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ⊤} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ⊤})
    (he₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ⊤ → α₁ (c₁ u) = ψ (γ₁ u)) (hγ₁ : IsSeedProper γ₁) :
    ψ '' (leftSide γ₁ ∩ H) ⊆ leftSide α₁ := by
  obtain ⟨-, hBij, -, hψoff, -, -, -, hψc, -, ⟨M, hM⟩, -⟩ := hC
  set D := activeDomain α₁ s₀ α₂ t₀ with hDdef
  set A := α₁ '' Icc 0 s₀ ∪ α₂ '' Icc 0 t₀ with hAdef
  have hD : ∀ z ∈ D, z ∈ H ∧ z ∉ A := fun z hz => hz.1
  have hAc : IsCompact A :=
    (isCompact_Icc.image_of_continuousOn hα₁.1.continuousOn).union
      (isCompact_Icc.image_of_continuousOn hc₂.continuousOn)
  -- a point of `α₁` after `s₀` is the inverse-chart image of a point of `γ₁` at a positive time
  have hα₁D : ∀ s, s₀ < s → ∃ v, 0 < v ∧ α₁ s = ψ (γ₁ v) := by
    intro s hs
    obtain ⟨v, hv, hcv⟩ := exists_pos_of_clock hm₁ hi₁ hs
    exact ⟨v, hv, by rw [← hcv, he₁ v le_top]⟩
  -- the image avoids the closed curve
  have hmaps : ψ '' (leftSide γ₁ ∩ H) ⊆ (seedRayClosure α₁)ᶜ := by
    rintro _ ⟨z, ⟨hzL, hzH⟩, rfl⟩ hz
    have hzD : ψ z ∈ D := hBij.mapsTo hzH
    rcases hz with ⟨s, hs⟩ | ⟨-, him⟩
    · by_cases hss : s ≤ s₀
      · exact (hD _ hzD).2 (Or.inl ⟨s, ⟨zero_le, hss⟩, hs⟩)
      · obtain ⟨v, hv, hsv⟩ := hα₁D s (not_le.1 hss)
        have hvH := hγ₁.2.2.2.1 v hv
        have heq : γ₁ v = z := hBij.injOn hvH hzH (hsv.symm.trans hs)
        exact (connectedComponentIn_subset _ _ hzL) (Or.inl ⟨v, heq⟩)
    · have h1 : (0 : ℝ) < (ψ z).im := (hD _ hzD).1
      rw [h0₁] at him
      simp only [Complex.ofReal_im] at him
      linarith
  have hpc : IsPreconnected (ψ '' (leftSide γ₁ ∩ H)) :=
    (isPreconnected_leftSide_inter_H hγ₁.isProperCurve (by rw [hγ₁.2.2.1]; simp) hγ₁.2.2.2.1).image ψ
      (hψc.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz.2)
  -- a far-left chart real point
  obtain ⟨R, hR⟩ := hAc.isBounded.exists_norm_le
  set x : ℝ := -(|R| + |M| + |w₁| + 1) with hxdef
  have hxneg : x < 0 := by
    have := abs_nonneg R; have := abs_nonneg M; have := abs_nonneg w₁
    rw [hxdef]; linarith
  have hxHbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hψxc : ContinuousWithinAt ψ Hbar x := hψc _ hxHbar
  have hxcl : (x : ℂ) ∈ closure H := mem_closure_iff_nhdsWithin_neBot.2 (nhdsWithin_H_ofReal_neBot x)
  have hψx_cl : ψ x ∈ closure D := by
    have := (hψxc.mono fun z (hz : z ∈ H) => show (0 : ℝ) ≤ z.im from le_of_lt hz).mem_closure_image hxcl
    rwa [hBij.image_eq] at this
  have hdisp : ‖ψ x - x‖ ≤ M := hM _ hxHbar
  have hnorm : |R| + |w₁| + 1 ≤ ‖ψ x‖ := by
    have h1 : ‖(x : ℂ)‖ = |R| + |M| + |w₁| + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hxneg, hxdef]; ring
    have h2 := norm_sub_norm_le (x : ℂ) (ψ x)
    rw [norm_sub_rev] at h2
    have := le_abs_self M
    linarith
  have hψxA : ψ x ∉ A := fun hA => by
    have := hR _ hA
    have := le_abs_self R
    have := abs_nonneg w₁
    linarith
  have hHbarC : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have him0 : 0 ≤ (ψ x).im :=
    (closure_minimal (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (hD z hz).1) hHbarC) hψx_cl
  have himeq : (ψ x).im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) him0
    have hmem := mem_activeDomain_of_mem_closure hAc.isClosed hψx_cl hpos hψxA
    exact hψoff x (fun hxH => by have : (0 : ℝ) < (x : ℂ).im := hxH; simp at this) hmem
  set X : ℝ := (ψ x).re with hXdef
  have hψX : ψ x = (X : ℂ) := Complex.ext (by simp [hXdef]) (by simp [himeq])
  have hXlt : X < w₁ := by
    have h1 : |(ψ x - x).re| ≤ ‖ψ x - x‖ := Complex.abs_re_le_norm _
    have h2 : (ψ x - x).re = X - x := by simp [hXdef]
    rw [h2] at h1
    have h3 := le_abs_self (X - x)
    have := le_abs_self M
    have := neg_abs_le w₁
    have := abs_nonneg R
    rw [hxdef] at h3
    linarith
  have hXα : (X : ℂ) ∉ range α₁ := by
    rintro ⟨s, hs⟩
    by_cases hss : s ≤ s₀
    · exact hψxA (hψX ▸ Or.inl ⟨s, ⟨zero_le, hss⟩, hs⟩)
    · obtain ⟨v, hv, hsv⟩ := hα₁D s (not_le.1 hss)
      have hD' := (hD _ (hBij.mapsTo (hγ₁.2.2.2.1 v hv))).1
      rw [← hsv, hs] at hD'
      have : (0 : ℝ) < (X : ℂ).im := hD'
      simp at this
  have hXL : (X : ℂ) ∈ leftSide α₁ := ofReal_mem_leftSide_of_lt_seed hα₁.2.2.1 h0₁ hXlt hXα
  obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.1 (isOpen_leftSide hα₁) _ hXL
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 hψxc ε hε
  have hxL₁ : (x : ℂ) ∈ leftSide γ₁ :=
    ofReal_mem_leftSide (fun t => hγ₁.im_nonneg t) (by rw [hγ₁.2.2.1]; simp) (by rw [hγ₁.2.2.1]; simpa using hxneg)
      (ofReal_notMem_seedRayClosure hγ₁.2.2.2.1 (by rw [hγ₁.2.2.1]; simpa using hxneg.ne))
  obtain ⟨ε', hε', hballε'⟩ := Metric.isOpen_iff.1 (isOpen_leftSide hγ₁.isProperCurve) _ hxL₁
  set r : ℝ := min δ ε' / 2 with hrdef
  have hr : 0 < r := half_pos (lt_min hδ hε')
  have hrδ : r < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hε')) (min_le_left _ _)
  have hrε : r < ε' := lt_of_lt_of_le (half_lt_self (lt_min hδ hε')) (min_le_right _ _)
  set z : ℂ := (x : ℂ) + (r : ℂ) * Complex.I with hzdef
  have hzx : dist z x = r := by
    rw [Complex.dist_eq, hzdef, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hzH : z ∈ H := show (0 : ℝ) < z.im by simp [hzdef, hr]
  have hzL : z ∈ leftSide γ₁ := hballε' (by rw [mem_ball, hzx]; exact hrε)
  have hψz : ψ z ∈ leftSide α₁ := by
    refine hballε ?_
    rw [mem_ball, ← hψX]
    exact hδψ (show (0 : ℝ) ≤ z.im from le_of_lt hzH) (by rw [hzx]; exact hrδ)
  exact subset_leftSide_of_mem hpc hmaps ⟨z, ⟨hzL, hzH⟩, rfl⟩ hψz

/-- **The gluing at a common first contact** (proof of Lemma G2, last paragraph). Let `α₁` (from `w₁`, proper simple)
and `α₂` (from `w₂ < w₁`, continuous) be complete curves in `ℍ̄`, each missing the other's seed, with a common first
contact `(s₀, t₀)`, a first-contact chart `(φ, ψ, lift)` of the active domain and chart continuations `γ₁`, `γ₂` (of
infinite lifetime) carried onto the physical continuations by `ψ` (`IsChartClockData`). If `γ₁` is a simple proper
curve from `0` in `ℍ` after `0`, `γ₂` starts at `0`, is in `ℍ` after `0` and lies in the closed left side of `γ₁`, then
`α₂` lies in the closed left side of `α₁`. -/
theorem range_subset_closedLeftSide_glue (hα₁ : IsProperCurve α₁) (hc₂ : Continuous α₂)
    (hα₂ : ∀ t, 0 ≤ (α₂ t).im) (hw : w₂ < w₁) (h0₁ : α₁ 0 = w₁) (h0₂ : α₂ 0 = w₂) (hw₂ : (w₂ : ℂ) ∉ range α₁)
    (hw₁ : (w₁ : ℂ) ∉ range α₂) {s₀ t₀ : ℝ≥0} (hfc : IsFirstContact α₁ ⊤ α₂ ⊤ s₀ t₀) {φ ψ : ℂ → ℂ}
    {lift : ℂ → ℝ} (hC : IsFirstContactChart α₁ s₀ α₂ t₀ φ ψ lift)
    (hk : IsChartClockData ψ α₁ ⊤ s₀ α₂ ⊤ t₀ γ₁ γ₂ ⊤ ⊤) (hγ₁ : IsSeedProper γ₁) (hγ₂0 : γ₂ 0 = 0)
    (hγ₂H : ∀ t, 0 < t → γ₂ t ∈ H) (hord : range γ₂ ⊆ closedLeftSide γ₁) :
    range α₂ ⊆ closedLeftSide α₁ := by
  obtain ⟨c₁, c₂, hm₁, hi₁, hm₂, hi₂, -, -, he₁, he₂⟩ := hk
  have hψ0 : ψ 0 = α₁ s₀ := by
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := hC
    exact h
  have hw₂L := ofReal_mem_leftSide_of_lt_seed hα₁.2.2.1 h0₁ hw hw₂
  rintro _ ⟨t, rfl⟩
  rw [closedLeftSide_eq]
  by_cases ht : t < t₀
  · left
    have hsub : α₂ '' Icc 0 t ⊆ leftSide α₁ := by
      refine subset_leftSide_of_mem (isPreconnected_Icc.image _ hc₂.continuousOn) ?_
        ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ (h0₂ ▸ hw₂L)
      rintro _ ⟨t', ⟨-, ht'⟩, rfl⟩ (⟨s, hs⟩ | ⟨hre, him⟩)
      · exact absurd (lt_of_le_of_lt ht' ht) (not_lt.2 (hfc.2.2.2 s t' le_top le_top hs).2)
      · exact hw₁ ⟨t', eq_of_mem_seedRay h0₁ (hα₂ t') hre him⟩
    exact hsub ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩
  · obtain ⟨-, hsurj₂⟩ := clock_zero_and_surj hm₂ hi₂
    obtain ⟨u, rfl⟩ := hsurj₂ t (not_lt.1 ht)
    rw [he₂ u le_top]
    rcases eq_zero_or_pos u with rfl | hu
    · right
      rw [hγ₂0, hψ0]
      exact Or.inl ⟨s₀, rfl⟩
    · have huH := hγ₂H u hu
      rcases (show γ₂ u ∈ closedLeftSide γ₁ from hord ⟨u, rfl⟩) with hL | (⟨v, hv⟩ | ⟨-, him⟩)
      · left
        exact image_leftSide_inter_H_subset hα₁ hc₂ h0₁ hC hm₁ hi₁ he₁ hγ₁ ⟨γ₂ u, ⟨hL, huH⟩, rfl⟩
      · right
        rw [← hv, ← he₁ v le_top]
        exact Or.inl ⟨c₁ v, rfl⟩
      · exfalso
        have h1 : (0 : ℝ) < (γ₂ u).im := huH
        rw [hγ₁.2.2.1] at him
        simp only [Complex.zero_im] at him
        linarith

end RLC

end InteractingSLE
