/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76Kernel2Det
import InteractingSLE.Spec.Sec7.ReverseArcSep
import InteractingSLE.Spec.Sec7.Lemma78MeanWordGeom

/-!
# Aux. lemma 60 at a disjoint pair: the first prefix lies on the positive side of the second tip's chart

Packet PROVE-LEMMA76E. Specification §7.2, proof of Lemma 7.6 (p. 269): "Consider now an exposed right-side open
subarc of `α([0, ξ₁)) ∩ ℍ`. It is untouched by the revealed second prefix. Its image under `ψ` is an open interval in
`(0, ∞)` by **Aux.** lemma 60."

For two simple traces `α` from `x₁` and `β` from `x₂ < x₁`, disjoint prefixes `α([0, a])`, `β([0, b])` whose tips are
adherent to the joint unbounded domain `D` (`Lemma76Exit.IsDisjointPair`), and a chart inverse `ψ` of `D` based at the
second tip (`ψ(0) = β(b)`, continuous on `ℍ̄`, a bijection `ℍ → D`, real points off `D`, bounded displacement): every
real chart point `w` with `ψ(w)` on the first prefix is **positive** (`pos_of_inv_mem_fst`).

## Proof

* **No interleaving** (`re_lt_of_mem_snd`): a real point of `β([0, b])` at or right of `x₁` would join `x₂ < x₁` to
  it and trap `x₁`, hence the whole first prefix and its tip, which is adherent to `D`.
* **The crosscut.** Suppose `w ≤ 0`; then `−R < w < 0` for a large `R` (bounded displacement). Let `S` be the closed
  upper semicircle over `[−R, 0]` and `F = ψ(S) ∪ β([0, b])`, a compact connected subset of `ℍ̄` containing the real
  points `y_L = ψ(−R)` (far left) and `x₂`.
* The first prefix misses `F` and contains `x₁`, which is right of every real point of `F`; so `F` is free along the
  whole first prefix, in particular at `ψ(w)`. Points `ψ(w + iδ)` near it lie in the image of the open half-disc `B`
  over `(−R, 0)`, which is connected and misses `F`: so `ψ(B)` lies in the unbounded domain of `F`. Every point of
  `ψ(ℍ)` outside `ψ(S)` is in `ψ(B)` or on a ray image `ψ({c + s(v − c) : s ≥ 1})` going to infinity, so the whole
  of `D \ F` lies in the unbounded domain of `F`.
* A real point `t` with `y_L < t < x₂` is trapped by `F` (it lies under the connected set `F` joining `y_L` and `x₂`)
  but is adherent to `D \ F`. Contradiction.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76E

open HalfPlaneSep Restart

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0}

/-- The active domain of two compact prefixes is the unbounded domain of their union. -/
theorem activeDomain_eq_of_isPathGood (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (ha : (a : ℝ≥0∞) ≤ ζ₁) (hb : (b : ℝ≥0∞) ≤ ζ₂) :
    activeDomain α a β b = H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b) :=
  Lemma76Exit.unboundedPart_eq
    ((Sec7.IsPathGood.isCompact_image hp₁ ha).union (Sec7.IsPathGood.isCompact_image hp₂ hb)).isClosed

/-- A compact preconnected set `F ⊆ ℍ̄` missing the first prefix, with the first tip adherent to the joint domain and
`F` inside the union: if `F` traps one point of the first prefix, contradiction. -/
theorem false_of_isTrappedAt_fst (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ b) {F : Set ℂ} (hFc : IsClosed F)
    (hFK : F ⊆ α '' Icc 0 a ∪ β '' Icc 0 b) (hAF : Disjoint (α '' Icc 0 a) F) {z : ℂ}
    (hz : z ∈ α '' Icc 0 a) (htrap : IsTrappedAt F z) : False := by
  have ha : (a : ℝ≥0∞) ≤ ζ₁ := hpair.1.le
  have hb : (b : ℝ≥0∞) ≤ ζ₂ := hpair.2.1.le
  have hApc : IsPreconnected (α '' Icc 0 a) :=
    isPreconnected_Icc.image _ (Sec7.IsPathGood.continuousOn_Icc hp₁ ha)
  have hAX : α '' Icc 0 a ⊆ {w | 0 ≤ w.im} \ F := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨Sec7.IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs.2).trans ha),
      fun h => Set.disjoint_left.1 hAF ⟨s, hs, rfl⟩ h⟩
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc hApc hAX with hall | hall
  · exact (hall z hz).not_isTrappedAt (hAX hz).1 htrap
  · obtain ⟨ε, hε, hdis⟩ := hall _ ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
    obtain ⟨z', hz'D, hz'⟩ := Metric.mem_closure_iff.1 hpair.2.2.2.2.2 ε hε
    rw [activeDomain_eq_of_isPathGood hp₁ hp₂ ha hb] at hz'D
    exact Set.disjoint_left.1 hdis (mem_ball.2 (by rwa [dist_comm]))
      ⟨hz'D.1, fun h => hz'D.2 (fillH_mono hFK h)⟩

/-- **No interleaving**: every real point of the second prefix is left of the first seed `x₁` (otherwise the second
prefix joins `x₂ < x₁` to a point right of `x₁` and traps the first prefix and its tip). -/
theorem re_lt_of_mem_snd (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ b) {z : ℂ} (hz : z ∈ β '' Icc 0 b) (hz0 : z.im = 0) :
    z.re < x₁ := by
  have hb : (b : ℝ≥0∞) ≤ ζ₂ := hpair.2.1.le
  set F := β '' Icc 0 b with hFdef
  have hFc : IsCompact F := Sec7.IsPathGood.isCompact_image hp₂ hb
  have hFpc : IsPreconnected F := isPreconnected_Icc.image _ (Sec7.IsPathGood.continuousOn_Icc hp₂ hb)
  have hFim : ∀ w ∈ F, 0 ≤ w.im := by
    rintro _ ⟨t, ht, rfl⟩
    exact Sec7.IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hb)
  have hx₁A : ((x₁ : ℝ) : ℂ) ∈ α '' Icc 0 a := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp₁⟩
  have hx₁F : ((x₁ : ℝ) : ℂ) ∉ F := fun h => Set.disjoint_left.1 hpair.2.2.2.1 hx₁A h
  have hx₂F : ((x₂ : ℝ) : ℂ) ∈ F := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp₂⟩
  by_contra hle
  have hle' : x₁ ≤ z.re := not_lt.1 hle
  have hzF : ((z.re : ℝ) : ℂ) ∈ F := by rw [Restart.ofReal_re_eq hz0]; exact hz
  have hne : x₁ ≠ z.re := fun h => hx₁F (by rw [h]; exact hzF)
  have htrap := isTrappedAt_of_isPreconnected hFc hFpc hFim hx₂F hzF hx (lt_of_le_of_ne hle' hne) hx₁F
  exact false_of_isTrappedAt_fst hp₁ hp₂ hpair hFc.isClosed subset_union_right hpair.2.2.2.1 hx₁A htrap

/-! ### The closed upper semicircle -/

/-- The closed upper semicircle of centre `c` and radius `r`. -/
def semicircle (c r : ℝ) : Set ℂ := (fun θ : ℝ => (c : ℂ) + r * exp (θ * I)) '' Icc 0 Real.pi

theorem continuous_semicircleMap (c r : ℝ) : Continuous fun θ : ℝ => (c : ℂ) + r * exp (θ * I) := by
  fun_prop

theorem isCompact_semicircle (c r : ℝ) : IsCompact (semicircle c r) :=
  isCompact_Icc.image (continuous_semicircleMap c r)

theorem isPreconnected_semicircle (c r : ℝ) : IsPreconnected (semicircle c r) :=
  isPreconnected_Icc.image _ (continuous_semicircleMap c r).continuousOn

theorem mem_semicircle_iff {c r : ℝ} (hr : 0 ≤ r) {v : ℂ} :
    v ∈ semicircle c r ↔ 0 ≤ v.im ∧ ‖v - c‖ = r := by
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨?_, ?_⟩
    · have him : ((c : ℂ) + r * exp (θ * I)).im = r * Real.sin θ := by
        rw [add_im, ofReal_im, zero_add, exp_mul_I]
        simp [← ofReal_cos, ← ofReal_sin]
      rw [him]
      exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
    · rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr]
  · rintro ⟨him, hn⟩
    refine ⟨arg (v - c), ⟨arg_nonneg_iff.2 (by simpa using him), arg_le_pi _⟩, ?_⟩
    show (c : ℂ) + (r : ℂ) * exp ((arg (v - c) : ℂ) * I) = v
    rw [← hn, norm_mul_exp_arg_mul_I]
    ring

theorem norm_sub_of_mem_semicircle {c r : ℝ} (hr : 0 ≤ r) {v : ℂ} (hv : v ∈ semicircle c r) : ‖v - c‖ = r :=
  ((mem_semicircle_iff hr).1 hv).2

theorem left_mem_semicircle {c r : ℝ} (hr : 0 ≤ r) : (((c - r : ℝ)) : ℂ) ∈ semicircle c r :=
  (mem_semicircle_iff hr).2 ⟨by simp, by
    rw [show (((c - r : ℝ)) : ℂ) - c = ((-r : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg hr]⟩

theorem right_mem_semicircle {c r : ℝ} (hr : 0 ≤ r) : (((c + r : ℝ)) : ℂ) ∈ semicircle c r :=
  (mem_semicircle_iff hr).2 ⟨by simp, by
    rw [show (((c + r : ℝ)) : ℂ) - c = ((r : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]⟩

/-- **The real points of the semicircle are its two ends.** -/
theorem eq_or_eq_of_mem_semicircle {c r : ℝ} (hr : 0 < r) {v : ℂ} (hv : v ∈ semicircle c r) (hvH : v ∉ H) :
    v = (((c + r : ℝ)) : ℂ) ∨ v = (((c - r : ℝ)) : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := hv
  have him : ((c : ℂ) + r * exp (θ * I)).im = r * Real.sin θ := by
    rw [add_im, ofReal_im, zero_add, exp_mul_I]
    simp [← ofReal_cos, ← ofReal_sin]
  have hs : Real.sin θ ≤ 0 := by
    have : ¬ (0 < r * Real.sin θ) := fun h => hvH (show 0 < ((c : ℂ) + r * exp (θ * I)).im by rw [him]; exact h)
    by_contra hpos
    exact this (mul_pos hr (lt_of_not_ge hpos))
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · left
    rw [← h0]
    push_cast
    simp
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · right
    show (c : ℂ) + r * exp (θ * I) = _
    rw [hpi, exp_pi_mul_I]
    push_cast
    ring
  · exact absurd (Real.sin_pos_of_pos_of_lt_pi h0 hpi) (not_lt.2 hs)

/-! ### Planar helpers -/

/-- A map continuous on `ℍ̄` sending `ℍ` into `ℍ` sends `ℍ̄` into `ℍ̄`. -/
theorem im_nonneg_of_mapsTo {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar) (hψH : MapsTo ψ H H) {v : ℂ}
    (hv : v ∈ Hbar) : 0 ≤ (ψ v).im := by
  set u : ℕ → ℂ := fun n => v + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hu
  have huH : ∀ n, u n ∈ H := fun n => by
    show 0 < (v + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im
    have hv' : 0 ≤ v.im := hv
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    linarith
  have hlim : Tendsto u atTop (𝓝[Hbar] v) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => Lemma76Exit.H_subset_Hbar (huH n)⟩
    have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 0) := by
      have := ((continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const I
      simpa using this
    have h1 := (tendsto_const_nhds (x := v)).add h0
    rw [add_zero] at h1
    exact h1
  have hψ := ((hψc v hv).tendsto.comp hlim)
  exact ge_of_tendsto ((continuous_im.tendsto _).comp hψ) (Eventually.of_forall fun n => (hψH (huH n)).le)

/-- **A compact set whose real points are all left of `x` is free at `x`.** -/
theorem isFreeAt_of_forall_re_lt {F : Set ℂ} (hF : IsCompact F) {x : ℝ} (h : ∀ z ∈ F, z.im = 0 → z.re < x) :
    IsFreeAt F x := by
  have hS : IsCompact (F ∩ {z : ℂ | z.im = 0}) := hF.inter_right (isClosed_eq continuous_im continuous_const)
  obtain ⟨c₀, hc₀, hle⟩ : ∃ c₀ : ℝ, c₀ < x ∧ ∀ z ∈ F, z.im = 0 → z.re ≤ c₀ := by
    rcases (F ∩ {z : ℂ | z.im = 0}).eq_empty_or_nonempty with he | hne
    · exact ⟨x - 1, by linarith, fun z hz hz0 => absurd (show z ∈ F ∩ {z : ℂ | z.im = 0} from ⟨hz, hz0⟩)
        (by rw [he]; exact notMem_empty z)⟩
    · obtain ⟨z₀, hz₀, hmax⟩ := hS.exists_isMaxOn hne continuous_re.continuousOn
      exact ⟨z₀.re, h z₀ hz₀.1 hz₀.2, fun z hz hz0 => hmax ⟨hz, hz0⟩⟩
  obtain ⟨ρ, hρ, -, hdis⟩ := Restart.exists_ball_disjoint_of_gt hF hc₀ hle
  exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun hzF => Set.disjoint_left.1 hdis hz.1 hzF⟩⟩

/-- **A ray to infinity.** For a map `ψ` continuous on `ℍ̄` with bounded displacement, and a closed `F` such that
`ψ` sends every point of `ℍ` outside the closed disc of centre `c ∈ ℝ` and radius `r` into `ℍ \ F`, those points are
sent into the unbounded domain of `F` (the radial ray from `c` through the point goes to infinity outside the disc). -/
theorem mem_H_diff_fillH_of_ray {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar) {M : ℝ}
    (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) {F : Set ℂ} (hF : IsClosed F) {c r : ℝ}
    (hgood : ∀ v ∈ H, r < ‖v - c‖ → ψ v ∈ H \ F) {v : ℂ} (hv : v ∈ H) (hvr : r < ‖v - c‖) :
    ψ v ∈ H \ fillH F := by
  set f : ℝ → ℂ := fun s => (c : ℂ) + (s : ℂ) * (v - c) with hf
  have hfc : Continuous f := by fun_prop
  have hvc0 : 0 < ‖v - (c : ℂ)‖ := by
    have : 0 < (v - (c : ℂ)).im := by simpa using (show 0 < v.im from hv)
    exact lt_of_lt_of_le this ((abs_im_le_norm _).trans' (le_abs_self _))
  have hfH : ∀ s ∈ Ici (1 : ℝ), f s ∈ H := fun s hs => by
    show 0 < ((c : ℂ) + (s : ℂ) * (v - c)).im
    have h1 : (1 : ℝ) ≤ s := hs
    simp only [add_im, ofReal_im, zero_add, mul_im, ofReal_re, sub_im, ofReal_im, sub_zero, ofReal_im,
      zero_mul, add_zero]
    exact mul_pos (by linarith) hv
  have hfn : ∀ s ∈ Ici (1 : ℝ), ‖f s - c‖ = s * ‖v - c‖ := fun s hs => by
    have h1 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
    rw [hf]
    simp only [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
  have hfr : ∀ s ∈ Ici (1 : ℝ), r < ‖f s - c‖ := fun s hs => by
    rw [hfn s hs]
    calc r < ‖v - c‖ := hvr
      _ = 1 * ‖v - c‖ := (one_mul _).symm
      _ ≤ s * ‖v - c‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  set L := f '' Ici 1 with hL
  have hLH : L ⊆ H := by rintro _ ⟨s, hs, rfl⟩; exact hfH s hs
  have hLpc : IsPreconnected (ψ '' L) :=
    (isPreconnected_Ici.image _ hfc.continuousOn).image ψ (hψc.mono fun z hz => Lemma76Exit.H_subset_Hbar (hLH hz))
  have hLsub : ψ '' L ⊆ H \ F := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact hgood _ (hfH s hs) (hfr s hs)
  have hunb : ¬ IsBounded (ψ '' L) := by
    rw [isBounded_iff_forall_norm_le]
    rintro ⟨C, hC⟩
    set s : ℝ := (C + M + ‖(c : ℂ)‖ + 1) / ‖v - c‖ + 1 with hs
    have hs1 : s ∈ Ici (1 : ℝ) := by
      show (1 : ℝ) ≤ s
      have : 0 ≤ (C + M + ‖(c : ℂ)‖ + 1) / ‖v - c‖ ∨ (C + M + ‖(c : ℂ)‖ + 1) / ‖v - c‖ < 0 := le_or_gt _ _
      rcases this with h | h
      · linarith
      · exfalso
        have hC0 := hC (ψ (f 1)) ⟨f 1, ⟨1, (le_refl (1 : ℝ)), rfl⟩, rfl⟩
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (f 1) (Lemma76Exit.H_subset_Hbar (hfH 1 (le_refl (1 : ℝ)))))
        have := div_neg_iff.1 h
        rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 (not_lt.2 hvc0.le)
        · linarith [norm_nonneg (ψ (f 1)), norm_nonneg (c : ℂ)]
    have hfs : C + M + 1 ≤ ‖f s‖ := by
      have h1 : ‖f s - c‖ ≤ ‖f s‖ + ‖(c : ℂ)‖ := norm_sub_le _ _
      rw [hfn s hs1] at h1
      have h2 : C + M + ‖(c : ℂ)‖ + 1 ≤ s * ‖v - c‖ := by
        have h3 : (C + M + ‖(c : ℂ)‖ + 1) / ‖v - c‖ ≤ s - 1 := by rw [hs]; linarith
        have h4 := (div_le_iff₀ hvc0).1 h3
        nlinarith [norm_nonneg (v - c)]
      linarith
    have hψs : ‖f s‖ - M ≤ ‖ψ (f s)‖ := by
      have := hM (f s) (Lemma76Exit.H_subset_Hbar (hfH s hs1))
      have h5 : ‖f s‖ ≤ ‖ψ (f s)‖ + ‖ψ (f s) - f s‖ := by
        calc ‖f s‖ = ‖ψ (f s) - (ψ (f s) - f s)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖ψ (f s)‖ + ‖ψ (f s) - f s‖ := norm_sub_le _ _
      linarith
    have := hC (ψ (f s)) ⟨f s, ⟨s, hs1, rfl⟩, rfl⟩
    linarith
  have hsub := subset_H_diff_fillH_of_not_isBounded hF hLpc hunb hLsub
  exact hsub ⟨v, ⟨1, (le_refl (1 : ℝ)), by simp [hf]⟩, rfl⟩

/-! ### Aux. lemma 60: the first prefix is on the positive side -/

/-- The second half of the contradiction: a free first-prefix point at a chart position `w ∈ (c − r, c + r)` makes
the half-disc image free, which a trapped far-left real point forbids. -/
theorem false_of_neg_aux {ψ : ℂ → ℂ} {K F Sc : Set ℂ} {M R₀ R c r x₂ w ε : ℝ} {yL βb : ℂ}
    (hψc : ContinuousOn ψ Hbar) (hbij : BijOn ψ H (H \ fillH K)) (hKcl : IsClosed K) (hR₀ : 0 < R₀)
    (hKR : K ⊆ ball 0 R₀) (hcr0 : c + r = 0) (hcrR : c - r = -R)
    (hgood : ∀ v ∈ H, ‖v - c‖ ≠ r → ψ v ∈ H \ F)
    (hScmem : ∀ v : ℂ, 0 ≤ v.im → ‖v - c‖ = r → v ∈ Sc) (hScF : ψ '' Sc ⊆ F)
    (hSc : ∀ v ∈ Sc, (v ∈ H ∧ ψ v ∈ H \ fillH K) ∨ ψ v = βb ∨ ψ v = yL) (hβbH : βb ∈ H)
    (hFsub : ∀ z ∈ F, z ∈ ψ '' Sc ∨ ‖z‖ < R₀)
    (hyLψ : ψ ((-R : ℝ) : ℂ) = yL) (hRSc : ((-R : ℝ) : ℂ) ∈ Sc) (hyL0 : yL.im = 0) (hyLre : yL.re ≤ -2 * R₀ - 2)
    (hx₂R : -R₀ < x₂) (hx₂F : ((x₂ : ℝ) : ℂ) ∈ F) (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hFc : IsCompact F) (hFpc : IsPreconnected F) (hFim : ∀ z ∈ F, 0 ≤ z.im)
    (hwR : -R < w) (hw0 : w < 0) (hε : 0 < ε) (hfree : ball (ψ w) ε ∩ H ⊆ H \ fillH F) : False := by
  have hrealHbar : ∀ v : ℝ, ((v : ℝ) : ℂ) ∈ Hbar := fun v => show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp
  -- a point of the half-disc image near `ψ(w)`
  have hwc : ‖((w : ℝ) : ℂ) - c‖ < r := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuousWithinAt_iff.1 (hψc _ (hrealHbar w)) ε hε
  set δ : ℝ := min (δ₀ / 2) ((r - ‖((w : ℝ) : ℂ) - c‖) / 2) with hδdef
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (half_pos (sub_pos.2 hwc))
  have hδ1 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ2 : δ ≤ (r - ‖((w : ℝ) : ℂ) - c‖) / 2 := min_le_right _ _
  set q : ℂ := (w : ℂ) + (δ : ℂ) * I with hqdef
  have hnδ : ‖(δ : ℂ) * I‖ = δ := by rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hqH : q ∈ H := show 0 < q.im by simp [hqdef, hδ]
  have hqdist : dist q w < δ₀ := by
    rw [dist_eq_norm, hqdef, add_sub_cancel_left, hnδ]
    linarith
  have hqc : ‖q - c‖ < r := by
    have : ‖q - c‖ ≤ ‖((w : ℝ) : ℂ) - c‖ + δ := by
      calc ‖q - c‖ = ‖(((w : ℝ) : ℂ) - c) + (δ : ℂ) * I‖ := by rw [hqdef]; ring_nf
        _ ≤ ‖((w : ℝ) : ℂ) - c‖ + ‖(δ : ℂ) * I‖ := norm_add_le _ _
        _ = ‖((w : ℝ) : ℂ) - c‖ + δ := by rw [hnδ]
    linarith
  have hpF : ψ q ∈ H \ fillH F :=
    hfree ⟨mem_ball.2 (hcont (Lemma76Exit.H_subset_Hbar hqH) hqdist), (hbij.mapsTo hqH).1⟩
  -- the half-disc image and the outer rays lie in the unbounded domain of `F`
  set Bh : Set ℂ := ball (c : ℂ) r ∩ H with hBhdef
  have hBhcv : Convex ℝ Bh :=
    (convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
  have hBhpc : IsPreconnected (ψ '' Bh) :=
    hBhcv.isPreconnected.image ψ (hψc.mono fun z hz => Lemma76Exit.H_subset_Hbar hz.2)
  have hBhsub : ψ '' Bh ⊆ H \ F := by
    rintro _ ⟨v, hv, rfl⟩
    exact hgood v hv.2 (ne_of_lt (by simpa [dist_eq_norm] using hv.1))
  have hqBh : q ∈ Bh := ⟨by simpa [dist_eq_norm] using hqc, hqH⟩
  have hin : ∀ v ∈ H, ‖v - c‖ < r → ψ v ∈ H \ fillH F := fun v hv hvr =>
    connectedComponentIn_subset_H_diff_fillH hFc.isClosed hpF
      (hBhpc.subset_connectedComponentIn ⟨q, hqBh, rfl⟩ hBhsub
        ⟨v, ⟨by simpa [dist_eq_norm] using hvr, hv⟩, rfl⟩)
  have hout : ∀ v ∈ H, r < ‖v - c‖ → ψ v ∈ H \ fillH F := fun v hv hvr =>
    mem_H_diff_fillH_of_ray hψc hM hFc.isClosed (fun v' hv' hv'r => hgood v' hv' (ne_of_gt hv'r)) hv hvr
  -- a trapped real point adherent to the domain
  set t : ℝ := yL.re + 1 with htdef
  have htn : R₀ < ‖((t : ℝ) : ℂ)‖ := by
    rw [norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hyLF : (((yL.re : ℝ)) : ℂ) ∈ F := hScF ⟨_, hRSc, by rw [Restart.ofReal_re_eq hyL0, hyLψ]⟩
  have htF : ((t : ℝ) : ℂ) ∉ F := by
    intro htF
    rcases hFsub _ htF with ⟨v, hv, he⟩ | hn
    · rcases hSc v hv with ⟨-, hD⟩ | he' | he'
      · have h1 := hD.1
        rw [he] at h1
        exact absurd h1 (by simp [H])
      · have h1 := hβbH
        rw [← he', he] at h1
        exact absurd h1 (by simp [H])
      · rw [he'] at he
        have h1 := congrArg Complex.re he
        simp only [ofReal_re] at h1
        rw [htdef] at h1
        linarith
    · exact absurd hn (not_lt.2 htn.le)
  have htrap := isTrappedAt_of_isPreconnected hFc hFpc hFim hyLF hx₂F (by linarith) (by linarith) htF
  obtain ⟨ε₂, hε₂, hdis₂⟩ := htrap
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.isOpen_iff.1 hFc.isClosed.isOpen_compl _ htF
  set δ' : ℝ := min ε₂ ε₃ / 2 with hδ'def
  have hδ' : 0 < δ' := half_pos (lt_min hε₂ hε₃)
  have hδ'2 : δ' < ε₂ := by have := min_le_left ε₂ ε₃; rw [hδ'def]; linarith
  have hδ'3 : δ' < ε₃ := by have := min_le_right ε₂ ε₃; rw [hδ'def]; linarith
  set z : ℂ := (t : ℂ) + (δ' : ℂ) * I with hzdef
  have hzH : z ∈ H := show 0 < z.im by simp [hzdef, hδ']
  have hzdist : dist z t = δ' := by
    rw [dist_eq_norm, hzdef, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos hδ']
  have hzn : R₀ ≤ ‖z‖ := by
    have h1 := abs_re_le_norm z
    have hre : z.re = t := by simp [hzdef]
    rw [hre, abs_of_neg (by linarith)] at h1
    linarith
  have hzD : z ∈ H \ fillH K := mem_H_diff_fillH_of_le_norm hKcl hR₀ hKR hzH hzn
  obtain ⟨v, hvH, hvz⟩ := hbij.surjOn hzD
  have hzF : z ∉ F := hball₃ (mem_ball.2 (by rw [hzdist]; exact hδ'3))
  have hvr : ‖v - c‖ ≠ r := fun h =>
    hzF (hScF ⟨v, hScmem v (show (0 : ℝ) < v.im from hvH).le h, hvz⟩)
  have hzFF : z ∈ H \ fillH F := by
    rw [← hvz]
    rcases lt_or_gt_of_ne hvr with h | h
    · exact hin v hvH h
    · exact hout v hvH h
  exact Set.disjoint_left.1 hdis₂ (mem_ball.2 (by rw [hzdist]; exact hδ'2)) hzFF

/-- The contradiction behind Aux. lemma 60: a first-prefix point at a negative chart position `w ∈ (−R, 0)`. -/
theorem false_of_neg (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ b) {ψ : ℂ → ℂ}
    (hbij : BijOn ψ H (H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b)))
    (hreal : ∀ w ∉ H, ψ w ∉ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b))
    (hψc : ContinuousOn ψ Hbar) (hψ0 : ψ 0 = β b) {M : ℝ} (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) (hM0 : 0 ≤ M)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hnormK : ∀ z ∈ α '' Icc 0 a ∪ β '' Icc 0 b, ‖z‖ < R₀)
    (hψHbar : ∀ v ∈ Hbar, 0 ≤ (ψ v).im)
    (hKD : ∀ z ∈ α '' Icc 0 a ∪ β '' Icc 0 b, z ∉ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b))
    (hdisp : ∀ v : ℝ, |v| - M ≤ ‖ψ v‖) (hx₂R : -R₀ < x₂)
    {R : ℝ} (hR : R = 2 * R₀ + M + 2) {w : ℝ} (hwR : -R < w) (hw0 : w < 0) (hw : ψ w ∈ α '' Icc 0 a) :
    False := by
  set A := α '' Icc 0 a with hAdef
  set Bs := β '' Icc 0 b with hBdef
  set K := A ∪ Bs with hKdef
  have ha : (a : ℝ≥0∞) ≤ ζ₁ := hpair.1.le
  have hb : (b : ℝ≥0∞) ≤ ζ₂ := hpair.2.1.le
  have hAc : IsCompact A := Sec7.IsPathGood.isCompact_image hp₁ ha
  have hBc : IsCompact Bs := Sec7.IsPathGood.isCompact_image hp₂ hb
  have hKc : IsCompact K := hAc.union hBc
  have hKR : K ⊆ ball 0 R₀ := fun z hz => mem_ball_zero_iff.2 (hnormK z hz)
  have hBpc : IsPreconnected Bs := isPreconnected_Icc.image _ (Sec7.IsPathGood.continuousOn_Icc hp₂ hb)
  have hrealHbar : ∀ v : ℝ, ((v : ℝ) : ℂ) ∈ Hbar := fun v => show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp
  have hRpos : 0 < R := by rw [hR]; linarith
  set c : ℝ := -R / 2 with hc
  set r : ℝ := R / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcr0 : c + r = 0 := by rw [hc, hr]; ring
  have hcrR : c - r = -R := by rw [hc, hr]; ring
  set Sc := semicircle c r with hScdef
  have hScHbar : Sc ⊆ Hbar := fun v hv => ((mem_semicircle_iff hr0.le).1 hv).1
  have h0Sc : (0 : ℂ) ∈ Sc := by
    have := right_mem_semicircle (c := c) hr0.le
    rw [hcr0, ofReal_zero] at this
    exact this
  have hRSc : ((-R : ℝ) : ℂ) ∈ Sc := by
    have := left_mem_semicircle (c := c) hr0.le
    rw [hcrR] at this
    exact this
  set yL := ψ ((-R : ℝ) : ℂ) with hyLdef
  have hyLn : R₀ < ‖yL‖ := by
    have := hdisp (-R)
    rw [← hyLdef, abs_neg, abs_of_pos hRpos] at this
    linarith
  have hyL0 : yL.im = 0 := by
    have hnH : ((-R : ℝ) : ℂ) ∉ H := fun h => by
      have : (0 : ℝ) < ((-R : ℝ) : ℂ).im := h
      simp at this
    refine le_antisymm (not_lt.1 fun hpos => hreal _ hnH ?_) (hψHbar _ (hrealHbar _))
    exact mem_H_diff_fillH_of_le_norm hKc.isClosed hR₀ hKR hpos hyLn.le
  have hyLre : yL.re ≤ -2 * R₀ - 2 := by
    have h1 := hM _ (hrealHbar (-R))
    rw [← hyLdef] at h1
    have h2 := Complex.abs_re_le_norm (yL - ((-R : ℝ) : ℂ))
    have h3 : (yL - ((-R : ℝ) : ℂ)).re = yL.re + R := by simp
    rw [h3] at h2
    have := le_abs_self (yL.re + R)
    linarith
  -- the crosscut `F = ψ(S) ∪ β([0, b])`
  set F := ψ '' Sc ∪ Bs with hFdef
  have hScIm : IsCompact (ψ '' Sc) := (isCompact_semicircle c r).image_of_continuousOn (hψc.mono hScHbar)
  have hFc : IsCompact F := hScIm.union hBc
  have hFpc : IsPreconnected F :=
    IsPreconnected.union (β b) ⟨0, h0Sc, hψ0⟩ ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩
      ((isPreconnected_semicircle c r).image ψ (hψc.mono hScHbar)) hBpc
  have hFim : ∀ z ∈ F, 0 ≤ z.im := by
    rintro z (⟨v, hv, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact hψHbar v (hScHbar hv)
    · exact Sec7.IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hb)
  have hSc : ∀ v ∈ Sc, (v ∈ H ∧ ψ v ∈ H \ fillH K) ∨ ψ v = β b ∨ ψ v = yL := by
    intro v hv
    by_cases hvH : v ∈ H
    · exact Or.inl ⟨hvH, hbij.mapsTo hvH⟩
    · rcases eq_or_eq_of_mem_semicircle hr0 hv hvH with h | h
      · rw [h, hcr0, ofReal_zero, hψ0]; exact Or.inr (Or.inl rfl)
      · rw [h, hcrR]; exact Or.inr (Or.inr rfl)
  have hβbH : β b ∈ H := hpair.2.2.1
  have hβbB : β b ∈ Bs := ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩
  have hgood : ∀ v ∈ H, ‖v - c‖ ≠ r → ψ v ∈ H \ F := by
    intro v hv hvr
    have hvD := hbij.mapsTo hv
    refine ⟨hvD.1, ?_⟩
    rintro (⟨v', hv', he⟩ | hB)
    · by_cases hv'H : v' ∈ H
      · exact hvr (by rw [← hbij.injOn hv'H hv he]; exact norm_sub_of_mem_semicircle hr0.le hv')
      · exact hreal v' hv'H (by rw [he]; exact hvD)
    · exact hKD _ (Or.inr hB) hvD
  have hAF : Disjoint A F := by
    rw [Set.disjoint_left]
    rintro z hzA (⟨v, hv, rfl⟩ | hzB)
    · rcases hSc v hv with ⟨-, hD⟩ | he | he
      · exact hKD _ (Or.inl hzA) hD
      · rw [he] at hzA; exact Set.disjoint_left.1 hpair.2.2.2.1 hzA hβbB
      · rw [he] at hzA; exact absurd (hnormK _ (Or.inl hzA)) (not_lt.2 hyLn.le)
    · exact Set.disjoint_left.1 hpair.2.2.2.1 hzA hzB
  -- `F` is free at `x₁`, hence along the first prefix
  have hfree₁ : IsFreeAt F x₁ := by
    refine isFreeAt_of_forall_re_lt hFc fun z hz hz0 => ?_
    rcases hz with ⟨v, hv, rfl⟩ | hzB
    · rcases hSc v hv with ⟨-, hD⟩ | he | he
      · exact absurd hz0 (ne_of_gt hD.1)
      · rw [he] at hz0; exact absurd hz0 (ne_of_gt hβbH)
      · rw [he]; linarith
    · exact re_lt_of_mem_snd hp₁ hp₂ hx hpair hzB hz0
  have hApc : IsPreconnected A := isPreconnected_Icc.image _ (Sec7.IsPathGood.continuousOn_Icc hp₁ ha)
  have hAX : A ⊆ {z | 0 ≤ z.im} \ F := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨Sec7.IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs.2).trans ha),
      fun h => Set.disjoint_left.1 hAF ⟨s, hs, rfl⟩ h⟩
  have hx₁A : ((x₁ : ℝ) : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp₁⟩
  have hfreew : IsFreeAt F (ψ w) := by
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc.isClosed hApc hAX with hall | hall
    · exact hall _ hw
    · exact absurd (hall _ hx₁A) (hfree₁.not_isTrappedAt (by simp))
  obtain ⟨ε, hε, hfree⟩ := hfreew
  have hFsub : ∀ z ∈ F, z ∈ ψ '' Sc ∨ ‖z‖ < R₀ := by
    rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (hnormK z (Or.inr hz))
  exact false_of_neg_aux hψc hbij hKc.isClosed hR₀ hKR hcr0 hcrR hgood
    (fun v hv hvr => (mem_semicircle_iff hr0.le).2 ⟨hv, hvr⟩) subset_union_left hSc hβbH hFsub rfl hRSc hyL0
    hyLre hx₂R (Or.inr ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp₂⟩) hM hFc hFpc hFim hwR hw0 hε hfree

/-- **Aux. lemma 60 at a disjoint pair** (proof of Lemma 7.6, p. 269). For simple traces `α` from `x₁` and `β` from
`x₂ < x₁` at a good configuration (`Lemma76Exit.IsDisjointPair`), and a chart inverse `ψ` of the joint unbounded domain
based at the second tip (`ψ(0) = β(b)`; continuous on `ℍ̄`; a bijection of `ℍ` onto the domain; real points off the
domain; bounded displacement), every real chart point `w` with `ψ(w)` on the first prefix `α([0, a])` is positive. -/
theorem pos_of_inv_mem_fst (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ b) {ψ : ℂ → ℂ}
    (hbij : BijOn ψ H (activeDomain α a β b)) (hreal : ∀ w ∉ H, ψ w ∉ activeDomain α a β b)
    (hψc : ContinuousOn ψ Hbar) (hψ0 : ψ 0 = β b) (hMex : ∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    {w : ℝ} (hw : ψ w ∈ α '' Icc 0 a) : 0 < w := by
  obtain ⟨M, hM⟩ := hMex
  have ha : (a : ℝ≥0∞) ≤ ζ₁ := hpair.1.le
  have hb : (b : ℝ≥0∞) ≤ ζ₂ := hpair.2.1.le
  set A := α '' Icc 0 a with hAdef
  set Bs := β '' Icc 0 b with hBdef
  have hAc : IsCompact A := Sec7.IsPathGood.isCompact_image hp₁ ha
  have hBc : IsCompact Bs := Sec7.IsPathGood.isCompact_image hp₂ hb
  have hKc : IsCompact (A ∪ Bs) := hAc.union hBc
  have hD := activeDomain_eq_of_isPathGood hp₁ hp₂ ha hb
  rw [hD] at hbij hreal
  have hrealH : ∀ v : ℝ, ((v : ℝ) : ℂ) ∉ H := fun v h => by
    have : (0 : ℝ) < ((v : ℝ) : ℂ).im := h
    simp at this
  have hrealHbar : ∀ v : ℝ, ((v : ℝ) : ℂ) ∈ Hbar := fun v => show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hrealHbar 0))
  obtain ⟨R₀', hR₀'⟩ := hKc.isBounded.subset_ball 0
  set R₀ := max R₀' 1 with hR₀def
  have hKR : A ∪ Bs ⊆ ball 0 R₀ := hR₀'.trans (ball_subset_ball (le_max_left _ _))
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnormK : ∀ z ∈ A ∪ Bs, ‖z‖ < R₀ := fun z hz => by simpa using hKR hz
  have hψHbar : ∀ v ∈ Hbar, 0 ≤ (ψ v).im := fun v hv =>
    im_nonneg_of_mapsTo hψc (fun v' hv' => (hbij.mapsTo hv').1) hv
  have hKD : ∀ z ∈ A ∪ Bs, z ∉ H \ fillH (A ∪ Bs) := fun z hz hzD =>
    hzD.2 ⟨hzD.1, Or.inl (subset_closure hz)⟩
  -- displacement bounds at real chart points
  have hdisp : ∀ v : ℝ, |v| - M ≤ ‖ψ v‖ := fun v => by
    have h1 := hM v (hrealHbar v)
    have h2 : ‖((v : ℝ) : ℂ)‖ ≤ ‖ψ v‖ + ‖ψ v - v‖ := by
      calc ‖((v : ℝ) : ℂ)‖ = ‖ψ v - (ψ v - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖ψ v‖ + ‖ψ v - v‖ := norm_sub_le _ _
    rw [norm_real, Real.norm_eq_abs] at h2
    linarith
  have hx₂K : ((x₂ : ℝ) : ℂ) ∈ A ∪ Bs := Or.inr ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp₂⟩
  have hx₂R : -R₀ < x₂ := by
    have := hnormK _ hx₂K
    rw [norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le x₂]
  by_contra hw0
  have hw0' : w ≤ 0 := not_lt.1 hw0
  set R : ℝ := 2 * R₀ + M + 2 with hRdef
  -- `w ≠ 0` and `−R < w`
  have hwne : w ≠ 0 := by
    rintro rfl
    rw [ofReal_zero, hψ0] at hw
    exact Set.disjoint_left.1 hpair.2.2.2.1 hw ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩
  have hwR : -R < w := by
    by_contra hle
    have h1 := hdisp w
    have h2 := hnormK _ (Or.inl hw)
    have h3 : R ≤ |w| := by rw [abs_of_nonpos hw0']; linarith
    linarith
  have hwneg : w < 0 := lt_of_le_of_ne hw0' hwne
  exact false_of_neg hp₁ hp₂ hx hpair hbij hreal hψc hψ0 hM hM0 hR₀ hnormK hψHbar hKD hdisp hx₂R
    (by rfl) hwR hwneg hw

end Lemma76E

end Sec7

end InteractingSLE
