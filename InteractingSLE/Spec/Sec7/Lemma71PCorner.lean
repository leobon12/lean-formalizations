/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PLand

/-!
# Lemma 7.1's (CS), geometric half: corners at arbitrary real chart points and union hulls of two prefixes

Packet PROVE-LEMMA71P. Tools for the junction corners of the middle curve (supplement §2.3, "the removable corner"):

* `outBack`, `continuous_outBack`, `image_outBack`: the union `η₁([0, q₁]) ∪ η₂([0, q₂])` of two prefixes from a
  common real start is the image of one path from that point (out along `η₁` and back, then along `η₂`);
* **`exists_real_tendsto_mapOut_path`**: for the filling `A` of a path image from a real point, wherever a conformal
  chart with domain off `A` lands at a point of `A ∪ ℝ` (not of `ℍ ∖ A`), the transition `g_A ∘ c.2.1` has a real limit
  (cluster-set lemma for the boundary extension of `g_A⁻¹`, `YuanCharacterisation.exists_extension_symm`);
* **`exists_tendsto_of_realLimits_at`**: the removable corner (`Lemma71O.exists_tendsto_zero_of_realLimits`) at an
  arbitrary real point `x₀` (translated chart);
* `tendsto_logDerivFwd_sub_of_le'`: `Lemma71O.tendsto_logDerivFwd_sub_of_le` with the hull condition only at the two
  times used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

/-! ### The union of two prefixes as one path -/

section Path

variable {η₁ η₂ : ℝ≥0 → ℂ}

/-- The path out along `η₁` to time `q₁` and back, then along `η₂`. -/
def outBack (η₁ η₂ : ℝ≥0 → ℂ) (q₁ : ℝ) (r : ℝ) : ℂ :=
  if r ≤ 2 * q₁ then η₁ (q₁ - |q₁ - r|).toNNReal else η₂ (r - 2 * q₁).toNNReal

theorem continuous_outBack (h₁ : Continuous η₁) (h₂ : Continuous η₂) (h0 : η₁ 0 = η₂ 0) (q₁ : ℝ) :
    Continuous (outBack η₁ η₂ q₁) := by
  refine Continuous.if_le (h₁.comp (by fun_prop)) (h₂.comp (by fun_prop)) continuous_id continuous_const
    fun r hr => ?_
  have hr' : r = 2 * q₁ := hr
  rw [hr', sub_self, show q₁ - 2 * q₁ = -q₁ by ring, abs_neg,
    Real.toNNReal_of_nonpos (show q₁ - |q₁| ≤ 0 by linarith [le_abs_self q₁]), Real.toNNReal_zero, h0]

theorem outBack_zero {q₁ : ℝ} (hq : 0 ≤ q₁) : outBack η₁ η₂ q₁ 0 = η₁ 0 := by
  simp [outBack, show (0 : ℝ) ≤ 2 * q₁ by linarith, abs_of_nonneg hq]

theorem image_outBack (h0 : η₁ 0 = η₂ 0) (q₁ q₂ : ℝ≥0) :
    outBack η₁ η₂ q₁ '' Icc 0 (2 * q₁ + q₂) = Restart.prefixSet η₁ q₁ η₂ q₂ := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    unfold outBack
    split_ifs with h
    · refine Or.inl ⟨(q₁ - |q₁ - r|).toNNReal, ⟨zero_le, ?_⟩, rfl⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal']
      exact max_le (by linarith [abs_nonneg (q₁ - r)]) q₁.coe_nonneg
    · refine Or.inr ⟨(r - 2 * q₁).toNNReal, ⟨zero_le, ?_⟩, rfl⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal']
      exact max_le (by linarith [hr.2]) q₂.coe_nonneg
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · have hs' : (s : ℝ) ≤ q₁ := hs.2
      refine ⟨s, ⟨s.coe_nonneg, by linarith [q₂.coe_nonneg, q₁.coe_nonneg]⟩, ?_⟩
      simp only [outBack, show (s : ℝ) ≤ 2 * q₁ by linarith [q₁.coe_nonneg], ↓reduceIte,
        abs_of_nonneg (sub_nonneg.2 hs'), sub_sub_cancel, Real.toNNReal_coe]
    · rcases eq_or_lt_of_le (zero_le (a := s)) with h | h
      · refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
        rw [← h, outBack_zero q₁.coe_nonneg, h0]
      · have hs' : (s : ℝ) ≤ q₂ := hs.2
        have hs0 : (0 : ℝ) < s := h
        refine ⟨2 * q₁ + s, ⟨by positivity, by linarith⟩, ?_⟩
        simp only [outBack, show ¬ (2 * (q₁ : ℝ) + s ≤ 2 * q₁) by linarith, ↓reduceIte, add_sub_cancel_left,
          Real.toNNReal_coe]

end Path

/-! ### Real limits of the map-out of a path hull -/

section MapOut

variable {c : Chart}

/-- **The transition of the map-out of a path hull has a real limit wherever the chart lands off `ℍ ∖ A`**
(cluster-set lemma, as `Lemma71O.exists_tendsto_fwdMap_comp`, for the boundary extension of `g_A⁻¹`). -/
theorem exists_real_tendsto_mapOut_path {ζ : ℝ → ℂ} {S : ℝ} (hS : 0 ≤ S) (hζc : ContinuousOn ζ (Icc 0 S))
    (hζH : MapsTo ζ (Icc 0 S) Hbar) (hζ0 : (ζ 0).im = 0) (hc : c.IsConformal)
    (hCA : (c.dom : Set ℂ) ⊆ H \ fillH (ζ '' Icc 0 S)) {x p : ℂ} (hx : x ∈ Hbar)
    (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 p)) (hp : p ∉ H \ fillH (ζ '' Icc 0 S)) :
    ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => ConformalImage.mapOut (fillH (ζ '' Icc 0 S)) (c.2.1 y)) (𝓝[H] x) (𝓝 v) := by
  set A := fillH (ζ '' Icc 0 S) with hAdef
  set g := ConformalImage.mapOut A with hgdef
  have hA : IsHPHull A := YuanCharacterisation.isHPHull_fillH_image_of_im hζc hS hζ0
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  obtain ⟨F, hF1, hF2, hFd, hFc, hFi, hFR, -, -, -⟩ := YuanCharacterisation.exists_extension_symm hS hζc hζH hζ0
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  have hinv : ∀ y ∈ H, c.2.1 y ∈ H \ A := fun y hy => hCA (hc.inv_mem_dom hy)
  have hGc : ContinuousOn (fun y => g (c.2.1 y)) H := hg.1.1.continuousOn.comp hc.1.continuousOn hinv
  have hGH : MapsTo (fun y => g (c.2.1 y)) H Hbar := fun y hy => H_subset_Hbar (hg.1.2.mapsTo (hinv y hy))
  have hbd : ∀ᶠ y in 𝓝[H] x, ‖g (c.2.1 y)‖ ≤ ‖p‖ + 1 + M := by
    filter_upwards [hland (ball_mem_nhds p one_pos), self_mem_nhdsWithin] with y hyb hy
    have h1 := hM _ (hinv y hy)
    have h2 : ‖c.2.1 y‖ ≤ ‖p‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (c.2.1 y) p
      have hyb' : c.2.1 y ∈ ball p 1 := hyb
      rw [mem_ball, dist_eq_norm] at hyb'
      linarith
    have := norm_le_norm_add_norm_sub' (g (c.2.1 y)) (c.2.1 y)
    linarith
  have hFG : Tendsto (fun y => F (g (c.2.1 y))) (𝓝[H] x) (𝓝 p) :=
    hland.congr' (eventually_nhdsWithin_of_forall fun y hy => (hF2 _ (hinv y hy)).symm)
  obtain ⟨ξ, hξ, hFξ, hT⟩ := exists_tendsto_of_tendsto_comp hFd hFc hFi hFR hx hGc hGH hbd hFG
  refine ⟨ξ, le_antisymm (not_lt.1 fun hpos => hp ?_) hξ, hT⟩
  rw [← hFξ]
  exact (hF1 ξ hpos).1

end MapOut

/-! ### The removable corner at an arbitrary real point -/

section Corner

variable {c : Chart} {C D : Set ℂ} {g : ℂ → ℂ}

theorem tendsto_add_ofReal_nhdsWithin_H (z : ℂ) (a : ℝ) :
    Tendsto (fun y => y + (a : ℂ)) (𝓝[H] z) (𝓝[H] (z + a)) :=
  tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun y hy => show 0 < (y + (a : ℂ)).im by have : 0 < y.im := hy; simpa using this⟩

/-- The chart translated by a real `x₀` (inverse `y ↦ c.2.1 (y + x₀)`). -/
def shiftChart (c : Chart) (x₀ : ℝ) : Chart := (fun z => c.1 z - x₀, fun y => c.2.1 (y + x₀), c.2.2)

theorem isConformal_shiftChart (hc : c.IsConformal) (x₀ : ℝ) : (shiftChart c x₀).IsConformal := by
  have hm : MapsTo (fun y : ℂ => y + (x₀ : ℂ)) H H := fun y hy =>
    show 0 < (y + (x₀ : ℂ)).im by have : 0 < y.im := hy; simpa using this
  refine ⟨hc.1.comp (differentiableOn_id.add_const _) hm, fun y hy => hc.2.1 (hm hy), fun y hy => ?_⟩
  show c.1 (c.2.1 (y + x₀)) - x₀ = y
  rw [hc.2.2 _ (hm hy), add_sub_cancel_right]

theorem dom_shiftChart (hc : c.IsConformal) (x₀ : ℝ) :
    ((shiftChart c x₀).dom : Set ℂ) = c.dom := by
  rw [(isConformal_shiftChart hc x₀).coe_dom, hc.coe_dom]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y + x₀, show 0 < (y + (x₀ : ℂ)).im by have : 0 < y.im := hy; simpa using this, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - x₀, show 0 < (y - (x₀ : ℂ)).im by have : 0 < y.im := hy; simpa using this, ?_⟩
    show c.2.1 (y - x₀ + x₀) = c.2.1 y
    rw [sub_add_cancel]

/-- **The removable corner at a real point `x₀`** (`Lemma71O.exists_tendsto_zero_of_realLimits` for the translated
chart): bounded transition near `x₀` with real limits at the real points `≠ x₀` has a real limit at `x₀`. -/
theorem exists_tendsto_of_realLimits_at (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCD : C ⊆ D)
    (hgd : DifferentiableOn ℂ g D) (hgi : InjOn g D) (hgH : MapsTo g D H) {x₀ r M : ℝ} (hr : 0 < r)
    (hM : ∀ y ∈ ball (x₀ : ℂ) r ∩ H, ‖g (c.2.1 y)‖ ≤ M)
    (hlim : ∀ z ∈ ball (x₀ : ℂ) r, z.im = 0 → z ≠ x₀ → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => g (c.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    ∃ v : ℂ, v.im = 0 ∧ Tendsto (fun y => g (c.2.1 y)) (𝓝[H] (x₀ : ℂ)) (𝓝 v) := by
  have hc' := isConformal_shiftChart hc x₀
  have hdom' : ((shiftChart c x₀).dom : Set ℂ) = C := by rw [dom_shiftChart hc, hdom]
  have hball : ∀ y ∈ ball (0 : ℂ) r, y + (x₀ : ℂ) ∈ ball (x₀ : ℂ) r := fun y hy => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]; rwa [mem_ball, dist_zero_right] at hy
  obtain ⟨v, hv, hT⟩ := Lemma71O.exists_tendsto_zero_of_realLimits hc' hdom' hCD hgd hgi hgH hr
    (M := M) (fun y hy => hM _ ⟨hball y hy.1, show 0 < (y + (x₀ : ℂ)).im by have : 0 < y.im := hy.2; simpa using this⟩)
    (fun z hz hz0 hzne => by
      obtain ⟨v, hv, hT⟩ := hlim (z + x₀) (hball z hz) (by simp [hz0]) (fun h => hzne (by
        have := congrArg (fun w => w - (x₀ : ℂ)) h; simpa using this))
      exact ⟨v, hv, hT.comp (tendsto_add_ofReal_nhdsWithin_H z x₀)⟩)
  refine ⟨v, hv, ?_⟩
  have h2 := tendsto_add_ofReal_nhdsWithin_H (x₀ : ℂ) (-x₀)
  rw [ofReal_neg, add_neg_cancel] at h2
  have h := hT.comp h2
  refine h.congr fun y => ?_
  show g (c.2.1 (y + -(x₀ : ℂ) + x₀)) = g (c.2.1 y)
  rw [neg_add_cancel_right]

end Corner

/-! ### One curve at two times, with the hull condition at those times only -/

section Times

variable {c : Chart} {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- `Lemma71O.tendsto_logDerivFwd_sub_of_le` with the hull condition only at `q` and `q'`. -/
theorem tendsto_logDerivFwd_sub_of_le' (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : Lemma71I.IsSimpleProper η) (hc : c.IsConformal) {q q' : ℝ≥0}
    (hCq : (c.dom : Set ℂ) ⊆ H \ fillH (η '' Icc 0 q)) (hCq' : (c.dom : Set ℂ) ⊆ H \ fillH (η '' Icc 0 q'))
    {x : ℂ} (hx : x ∈ Hbar) {s : ℝ≥0} (hsq : s < q) (hqq' : q ≤ q') (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 (η s))) :
    Tendsto (fun y => (logDerivFwd (fun r : ℝ => W r.toNNReal) q' (c.2.1 y)).im -
      (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im) (𝓝[H] x) (𝓝 0) := by
  rcases eq_or_lt_of_le hqq' with rfl | hlt
  · simp only [sub_self]; exact tendsto_const_nhds
  have hq0 : 0 < q := lt_of_le_of_lt (zero_le (a := s)) hsq
  have hg : IsGeneratingTrace W ⊤ (fun t => η t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  obtain ⟨κ, hKΓ, hgK, hLK⟩ := ReverseArc.exists_physChart hg hW.continuousOn hW0 (WithTop.coe_lt_top q')
  simp only [Complex.ofReal_zero, sub_zero] at hgK hLK
  have hCq₁ : (c.dom : Set ℂ) ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q := by
    rw [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr (WithTop.coe_lt_top q)]; exact hCq
  obtain ⟨v, hv0, hT⟩ := Lemma71O.exists_real_tendsto_wall htr hW hW0 hc hCq₁ hx hsq.le hland
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hη hsq
  have hloc : η '' Icc 0 q' ∩ ball (η s) ρ ⊆ η '' Icc 0 q := by
    rintro _ ⟨⟨t, ht, rfl⟩, htb⟩
    refine ⟨t, ⟨ht.1, ?_⟩, rfl⟩
    by_contra hqt
    exact hball t (le_of_lt (not_le.1 hqt)) htb
  exact Lemma71O.tendsto_lift_sub_of_agree_chart (isCompact_Icc.image hη.1) hKΓ hgK hLK hc hCq' hland hρ htr hW hW0
    hη.2.1 hq0 (image_mono (Icc_subset_Icc_right hqq')) hloc hv0 hT

end Times

end InteractingSLE.Sec7.Lemma71P
