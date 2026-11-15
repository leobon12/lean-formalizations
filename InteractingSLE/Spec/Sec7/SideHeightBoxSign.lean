/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcMain
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import QuantumZipper.Proofs.Thm11.ForwardTamed

/-!
# The side of the first trace seen from the first-contact domain, in a single-path chart

Packet PROVE-SIDEHEIGHT2 (specification §7.2, proof of Lemma 7.8, pp. 292–294, and Aux. lemma 69, p. 273: "The side
incident to `D` is the right side of `α₁`"). Two good paths `α` from `0` and `β` from `x₂ < 0` have a first contact
`α(s₀) = β(t₀)` (interior or real). For every stop `q < s₀` with an interior tip `α(q)`, every approach to an interior
point `α(s)`, `s < q`, from the joint unbounded domain `D = ℍ \ fill(α([0, s₀]) ∪ β([0, t₀]))` has a **positive**
limit of the centred chart `f_q` (`pos_of_approach`).

This is the chart at a deterministic stop `q` that the single-path comparison of Lemma 7.8 needs; PROVE-LEMMA76B's
`exists_pos_tendsto` treats the chart at the contact time `s₀` when the contact is interior.

## Proof

Suppose the limit `y` is negative (it is not `0`: `F̄_q(y) = α(s) ≠ α(q)`). As `F̄_q(y) ∈ ℍ`, `y` exceeds the image
`L_q − W_q` of `0⁻` (`neg_rightImg_sub_lt_of_extendFrom_mem_H'`). Let `x_s = β(t_s)` be the last real point of
`β([0, t₀])`; the whole of `β([0, t₀])` is free for `α([0, q])` (the tip property of `α` frees `β(t₀) = α(s₀)`), and
`x_s < 0` (otherwise `β([0, t_s])` traps the seed `0`, hence all of `α([0, q])`, in particular the approached point).
The free real point `x_s` is alive for the reflected flow, so its chart value `c` satisfies `c ≤ L_q − W_q < y`
(`le_neg_rightImg_of_isForwardSol`). In the chart, the compact connected set
`C = f_q(β([t_s, t₀])) ∪ γ_q([0, s₀ − q])` (`γ_q` the shifted trace, `F̄_q ∘ γ_q = α(q + ·)`) contains the real points
`c < y < 0` but not `y`, so it traps `y` (`isTrappedAt_of_isPreconnected`). The chart image of `D` is connected,
unbounded and misses `C`, so it lies in the unbounded domain of `C`; but it accumulates at `y`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE

namespace Sec7

namespace SideHeightBox

open HalfPlaneSep Restart ReverseArc MartChar.RealFlow

/-! ### The image of a free real point left of the driver -/

section Flow

/-- **A real point left of the driver that the flow keeps alive has chart value below the image of `0⁻`**: if the
centred flow from `x < 0` exists on `[0, t]`, then `Re v_t ≤ −R⁻_t − W_t` with `R⁻_t = rightImg (−W) 0 t` (so
`−R⁻_t − W_t` is the image `L_t − W_t` of `0⁻`). -/
theorem le_neg_rightImg_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {x t : ℝ} (ht : 0 ≤ t)
    (hx : x < 0) {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (x : ℂ) t v) :
    (v t).re ≤ -rightImg (fun s => -W s) 0 t - W t := by
  have him : ∀ r ∈ Icc (0 : ℝ) t, (v r).im = 0 := QuantumZipper.im_isForwardSol_real hW ht hv
  have hre : ∀ r ∈ Icc (0 : ℝ) t, (v r).re < 0 :=
    QuantumZipper.re_neg_isForwardSol_real hW ht hv (by rw [hW0]; exact hx)
  set X : ℝ → ℝ := fun r => -(v r).re with hXdef
  have hvc : ContinuousOn v (Icc 0 t) := hv.1
  have hX : IsPosSol (fun s => -W s) (-x) t X := by
    refine ⟨(Complex.continuous_re.comp_continuousOn hvc).neg, fun r hr => ⟨by simp [hXdef, hre r hr], ?_⟩⟩
    have hsub : Icc (0 : ℝ) r ⊆ Icc 0 t := Icc_subset_Icc_right hr.2
    have hint : IntervalIntegrable (fun s => 2 / v s) MeasureTheory.volume 0 r := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hr.1]
      exact continuousOn_const.div (hvc.mono hsub) fun s hs => (hv.2 s (hsub hs)).1
    have heq := congrArg Complex.re (hv.2 r hr).2
    have hre_int : (∫ s in (0 : ℝ)..r, 2 / v s).re = ∫ s in (0 : ℝ)..r, (2 / v s).re :=
      (intervalIntegral.intervalIntegral_re hint).symm
    have hcongr : ∫ s in (0 : ℝ)..r, (2 / v s).re = ∫ s in (0 : ℝ)..r, -(2 / X s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hr.1] at hs
      have hs' := hsub hs
      have hvs : v s = ((v s).re : ℂ) := Complex.ext (by simp) (by simp [him s hs'])
      show (2 / v s).re = -(2 / -(v s).re)
      rw [hvs, show (2 : ℂ) / ((v s).re : ℂ) = (((2 : ℝ) / (v s).re : ℝ) : ℂ) by push_cast; ring, ofReal_re]
      simp only [ofReal_re, div_neg, neg_neg]
    rw [add_re, sub_re, ofReal_re, ofReal_re, hre_int, hcongr, intervalIntegral.integral_neg] at heq
    show X r = -x - (-W r) + ∫ s in (0 : ℝ)..r, 2 / X s
    have hXr : X r = -(v r).re := rfl
    linarith
  have halive : Alive (fun s => -W s) (-x) t := ⟨X, hX⟩
  have hcf : cflow (fun s => -W s) (-x) t = X t := cflow_eq_of_isPosSol hW.neg hX ⟨ht, le_rfl⟩
  have hle : rightImg (fun s => -W s) 0 t ≤ gImg (fun s => -W s) (-x) t :=
    rightImg_le_gImg hW.neg ht (show (0 : ℝ) < -x by linarith) halive
  have hg : gImg (fun s => -W s) (-x) t = -W t + X t := by rw [gImg, hcf]
  have hXt : X t = -(v t).re := rfl
  linarith

end Flow

/-! ### The sign of an approach in the chart at an earlier stop -/

section Sign

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₂ : ℝ} {w : ℝ≥0 → ℝ}

theorem ofReal_re_of_im {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [h])

theorem ofReal_notMem_H (x : ℝ) : (x : ℂ) ∉ H := fun h => by
  have h' : (0 : ℝ) < (x : ℂ).im := h
  simp at h'

theorem neBot_nhdsWithin_H_ofReal (x : ℝ) : (𝓝[H] (x : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 ?_
  rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  show (0 : ℝ) ≤ (x : ℂ).im
  simp

/-- **The joint unbounded domain sees the positive side of the first trace in its chart at every earlier stop**
(Aux. lemma 69 in the chart at a deterministic stop): for good paths `α` from `0` and `β` from `x₂ < 0` with first
contact `α(s₀) = β(t₀)` (before the lifetime of `α`), a stop `q < s₀` with interior tip, and an interior point
`α(s)`, `s < q`, every approach to `α(s)` from `ℍ \ fill(α([0, s₀]) ∪ β([0, t₀]))` along which the chart `f_q` has a
real limit `y` has `y > 0`. -/
theorem pos_of_approach (hp₁ : IsPathGood α ζ₁ 0) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < 0)
    (hg : IsGeneratingTrace w ζ₁ α) (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ₁}) (hw0 : w 0 = 0)
    {s₀ t₀ q s : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) (hc : β t₀ = α s₀)
    (hdisj : ∀ t < t₀, β t ∉ α '' Icc 0 s₀) (hsq : s < q) (hqs : q < s₀) (hsH : α s ∈ H) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)] (α s)) {y : ℝ}
    (hy : Tendsto (fwdMap (fun r : ℝ => w r.toNNReal) q) U (𝓝 (y : ℂ))) : 0 < y := by
  classical
  have hinj : InjOn α {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁} := hp₁.1
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hsq
  have hqζ : (q : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hqs).trans hs₀
  have hch := isChart hg hwc hw0 hinj hqζ hq0
  set f := fwdMap (fun r : ℝ => w r.toNNReal) q with hfdef
  set Φ := extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) with hΦdef
  set A := α '' Icc 0 q with hAdef
  set K := α '' Icc 0 s₀ ∪ β '' Icc 0 t₀ with hKdef
  have hAc : IsCompact A := IsPathGood.isCompact_image hp₁ hqζ.le
  have hKc : IsCompact K :=
    (IsPathGood.isCompact_image hp₁ hs₀.le).union (IsPathGood.isCompact_image hp₂ ht₀)
  have hAK : A ⊆ K := (image_mono (Icc_subset_Icc_right hqs.le)).trans subset_union_left
  have hDA : H \ fillH K ⊆ H \ fillH A := sdiff_subset_sdiff_right (fillH_mono hAK)
  have hDne : (𝓝[H \ fillH K] (α s)).NeBot := Filter.neBot_of_le hU
  -- the limit is the chart preimage of `α(s)`
  have hUA : (U : Filter ℂ) ≤ 𝓝[H \ fillH A] (α s) := hU.trans (nhdsWithin_mono _ hDA)
  obtain ⟨y', -, hfy', hΦy⟩ := hch.cluster U (α s) hUA
  have hyy : y' = (y : ℂ) := tendsto_nhds_unique hfy' hy
  rw [hyy] at hΦy
  have hsζ : (s : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 (hsq.trans hqs).le).trans hs₀.le
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, ofReal_zero, hch.tip] at hΦy
    exact (ne_of_lt hsq) (hinj hqζ.le hsζ hΦy).symm
  refine lt_of_le_of_ne (not_lt.1 fun hyneg => ?_) (Ne.symm hy0)
  -- the frozen driver; `y` lies right of the image of `0⁻`
  obtain ⟨t₂, hs₀t₂, ht₂⟩ := exists_real_btwn_of_lt hs₀
  have hqt₂ : (q : ℝ) < t₂ := (NNReal.coe_lt_coe.2 hqs).trans hs₀t₂
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  set W' := frozenDrive w t₂ with hW'def
  have hW' : Continuous W' := continuous_frozenDrive_of_lt hwc ht₂
  have hW'0 : W' 0 = 0 := by rw [hW'def, frozenDrive_zero ht₂0, hw0]
  have heqW : ∀ r ∈ Icc (0 : ℝ) t₂, (fun r : ℝ => w r.toNNReal) r = W' r := fun r hr => (frozenDrive_eq hr).symm
  have hfW : f = fwdMap W' q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => heqW r ⟨hr.1, hr.2.trans hqt₂.le⟩
  have hΦW : Φ = extendFrom H (fwdMapInv W' q) := by rw [hΦdef, fwdMapInv_eq_of_eqOn q.coe_nonneg hqt₂ heqW]
  have hB := (hg.isLoewnerTraceLT ht₂).hasBdryLimits hW' hW'0 q.coe_nonneg hqt₂
  have hΦyH : extendFrom H (fwdMapInv W' q) y ∈ H := by rw [← hΦW, hΦy]; exact hsH
  have hlow := SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hW' hW'0 q.coe_nonneg hΦyH
  -- the second path up to the contact is free for `α([0, q])`
  have hAcl : IsClosed A := hAc.isClosed
  have hαs₀A : α s₀ ∉ A := by
    rintro ⟨u, hu, hue⟩
    have := hinj (show (u : ℝ≥0∞) ≤ ζ₁ from (ENNReal.coe_le_coe.2 hu.2).trans hqζ.le) hs₀.le hue
    exact absurd (this ▸ hu.2) (not_le.2 hqs)
  have hβA : ∀ t ≤ t₀, β t ∉ A := by
    intro t ht hA
    rcases lt_or_eq_of_le ht with ht' | rfl
    · exact hdisj t ht' ((image_mono (Icc_subset_Icc_right hqs.le)) hA)
    · rw [hc] at hA; exact hαs₀A hA
  have hβX : β '' Icc 0 t₀ ⊆ {z : ℂ | 0 ≤ z.im} \ A := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans ht₀), hβA t ht.2⟩
  have hβc := IsPathGood.continuousOn_Icc hp₂ ht₀
  have hβpc : IsPreconnected (β '' Icc 0 t₀) := isPreconnected_Icc.image _ hβc
  have htipfree : IsFreeAt A (α s₀) := IsPathGood.isFreeAt_of_lt hp₁ hqs hs₀.le
  have hβfree : ∀ t ≤ t₀, IsFreeAt A (β t) := by
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hAcl hβpc hβX with hall | hall
    · exact fun t ht => hall _ ⟨t, ⟨zero_le, ht⟩, rfl⟩
    · exfalso
      have := hall _ ⟨t₀, ⟨zero_le, le_rfl⟩, rfl⟩
      rw [hc] at this
      exact htipfree.not_isTrappedAt (IsPathGood.im_nonneg hp₁ hs₀.le) this
  -- the last real point of `β([0, t₀])`
  set T := Icc 0 t₀ ∩ β ⁻¹' Hᶜ with hTdef
  have hTc : IsClosed T :=
    hβc.preimage_isClosed_of_isClosed isClosed_Icc QuantumZipper.isOpen_H.isClosed_compl
  have hβ0 : β 0 = x₂ := IsPathGood.zero hp₂
  have h0T : (0 : ℝ≥0) ∈ T := ⟨⟨le_rfl, zero_le⟩, fun h => by
    have : (β 0).im = 0 := by rw [hβ0]; simp
    exact absurd h (by rw [show β 0 ∈ H ↔ 0 < (β 0).im from Iff.rfl, this]; exact lt_irrefl 0)⟩
  have hTb : BddAbove T := ⟨t₀, fun t ht => ht.1.2⟩
  set ts := sSup T with htsdef
  have hts : ts ∈ T := hTc.csSup_mem ⟨0, h0T⟩ hTb
  have htst₀ : ts ≤ t₀ := hts.1.2
  have hafter : ∀ t, ts < t → t ≤ t₀ → β t ∈ H := fun t h1 h2 => by
    by_contra hn
    exact absurd (le_csSup hTb ⟨⟨zero_le, h2⟩, hn⟩) (not_le.2 h1)
  have htsζ : (ts : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 htst₀).trans ht₀
  have hxsim : (β ts).im = 0 := IsPathGood.im_eq_zero hp₂ htsζ hts.2
  set xs := (β ts).re with hxsdef
  have hβts : β ts = (xs : ℂ) := Complex.ext (by simp [hxsdef]) (by simp [hxsim])
  have hxsfree : IsFreeAt A (xs : ℂ) := hβts ▸ hβfree ts htst₀
  have hxsA : (xs : ℂ) ∉ A := hβts ▸ hβA ts htst₀
  have h0A : ((0 : ℝ) : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₁⟩
  -- the last real point is left of the seed
  have hxs : xs < 0 := by
    rcases lt_trichotomy xs 0 with h | h | h
    · exact h
    · exact absurd (by rw [h]; exact h0A) hxsA
    exfalso
    set K' := β '' Icc 0 ts with hK'def
    have hK'c : IsCompact K' := IsPathGood.isCompact_image hp₂ htsζ
    have hK'pc : IsPreconnected K' := isPreconnected_Icc.image _ (hβc.mono (Icc_subset_Icc_right htst₀))
    have hK'im : ∀ z ∈ K', 0 ≤ z.im := by
      rintro _ ⟨t, ht, rfl⟩; exact IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans htsζ)
    have hAK' : ∀ z ∈ A, z ∉ K' := by
      rintro z hzA ⟨t, ht, rfl⟩
      exact hβA t (ht.2.trans htst₀) hzA
    have htrap0 := isTrappedAt_of_isPreconnected hK'c hK'pc hK'im (u := x₂) (v := xs)
      ⟨0, ⟨le_rfl, zero_le⟩, hβ0⟩ ⟨ts, ⟨zero_le, le_rfl⟩, hβts⟩ hx h (fun h' => hAK' _ h0A h')
    have hApc : IsPreconnected A := isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp₁ hqζ.le)
    have hAX : A ⊆ {z : ℂ | 0 ≤ z.im} \ K' := by
      rintro z hz
      refine ⟨?_, hAK' z hz⟩
      obtain ⟨u, hu, rfl⟩ := hz
      exact IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hu.2).trans hqζ.le)
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hK'c.isClosed hApc hAX with hall | hall
    · exact (hall _ h0A).not_isTrappedAt (by simp) htrap0
    · obtain ⟨ε, hε, hdis⟩ := hall (α s) ⟨s, ⟨zero_le, hsq.le⟩, rfl⟩
      have hK'K : K' ⊆ K := (image_mono (Icc_subset_Icc_right htst₀)).trans subset_union_right
      have hmem : H \ fillH K ∩ ball (α s) ε ∈ 𝓝[H \ fillH K] (α s) :=
        inter_mem_nhdsWithin _ (ball_mem_nhds _ hε)
      obtain ⟨z, hzD, hzb⟩ := hDne.nonempty_of_mem hmem
      exact Set.disjoint_left.1 hdis hzb ⟨hzD.1, fun h => hzD.2 (fillH_mono hK'K h)⟩
  -- the chart value of the last real point lies left of `y`
  obtain ⟨c, hfc, hΦc, -⟩ := hch.free_real xs hxsfree
  have hcy : c < y := by
    obtain ⟨ε, hε, hεsub⟩ := hxsfree
    have hhull : fwdHull W' q = fillH A := by
      rw [← fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ heqW]
      exact SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hg hqζ
    have hdis : Disjoint (ball (xs : ℂ) ε) (fwdHull W' q) := by
      rw [Set.disjoint_left]
      intro z hzb hzK
      exact (hεsub ⟨hzb, hzK.1⟩).2 (hhull ▸ hzK)
    obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW' hW'0 (ne_of_lt hxs) q.coe_nonneg hε hdis
    have hlim := tendsto_fwdMap_of_isForwardSol hW' q.coe_nonneg hv
    rw [← hfW] at hlim
    have := neBot_nhdsWithin_H_ofReal xs
    have hcv : ((c : ℝ) : ℂ) = v q := tendsto_nhds_unique hfc hlim
    have hle := le_neg_rightImg_of_isForwardSol hW' hW'0 q.coe_nonneg hxs hv
    rw [← hcv, ofReal_re] at hle
    linarith
  -- the shifted trace: the chart image of `α([q, s₀])`
  obtain ⟨Wg, γ, T', hs₀T', hWgc, hWg0, hγ, hWeq, hγeq⟩ := exists_global_model hg hwc hw0 hs₀
  have hqT' : (q : ℝ) < T' := (NNReal.coe_lt_coe.2 hqs).trans hs₀T'
  have hΦg : Φ = extendFrom H (fwdMapInv Wg q) := by
    rw [hΦdef, fwdMapInv_eq_of_eqOn q.coe_nonneg hqT' fun r hr => (hWeq r hr).symm]
  obtain ⟨hγq, hext⟩ := hγ.isLoewnerTrace_shift_and_extendFrom hWgc hWg0 q.coe_nonneg
  set γq := loewnerTip (QuantumZipper.RS.shiftDrive Wg q) with hγqdef
  set r₀ : ℝ := (s₀ : ℝ) - q with hr₀
  have hr₀0 : 0 ≤ r₀ := sub_nonneg.2 (NNReal.coe_le_coe.2 hqs.le)
  have hΦγ : ∀ u ∈ Icc (0 : ℝ) r₀, Φ (γq u) = α (q + u).toNNReal := fun u hu => by
    rw [hΦg, hext u hu.1, hγeq (q + u) ⟨by linarith [hu.1, NNReal.coe_nonneg q], by linarith [hu.2]⟩]
  have hle_s₀ : ∀ u ∈ Icc (0 : ℝ) r₀, (q + u).toNNReal ≤ s₀ := fun u hu => by
    rw [Real.toNNReal_le_iff_le_coe]; linarith [hu.2]
  have hγqc : ContinuousOn γq (Icc 0 r₀) := hγq.2.1.mono Icc_subset_Ici_self
  set e := γq r₀ with hedef
  have hΦe : Φ e = α s₀ := by
    rw [hΦγ r₀ ⟨hr₀0, le_rfl⟩, hr₀, add_sub_cancel, Real.toNNReal_coe]
  have heHbar : e ∈ Hbar := (hγ.extendFrom_shift_tip hWgc hWg0 q.coe_nonneg hr₀0).1
  -- the chart image of `β([t_s, t₀])`
  set b : ℝ≥0 → ℂ := fun t => if t ≤ ts then ((c : ℝ) : ℂ) else f (β t) with hbdef
  have hβD : ∀ t, ts < t → t ≤ t₀ → β t ∈ H \ fillH A := fun t h1 h2 =>
    mem_H_diff_fillH_of_isFreeAt (hβfree t h2) (hafter t h1 h2)
  have hbc : ContinuousOn b (Icc ts t₀) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · subst h1
      rw [← Ioc_insert_left htst₀, continuousWithinAt_insert_self]
      have hbt : b ts = ((c : ℝ) : ℂ) := by simp [hbdef]
      show Tendsto b (𝓝[Ioc ts t₀] ts) (𝓝 (b ts))
      rw [hbt]
      have hβt : Tendsto β (𝓝[Ioc ts t₀] ts) (𝓝[H] (xs : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => hafter t ht.1 ht.2⟩
        rw [← hβts]
        exact (hβc ts ⟨zero_le, htst₀⟩).tendsto.mono_left (nhdsWithin_mono _ fun t ht => ⟨zero_le, ht.2⟩)
      exact (hfc.comp hβt).congr' (eventually_nhdsWithin_of_forall fun t ht => by
        simp [hbdef, not_le.2 ht.1])
    · have hn : Ioi ts ∈ 𝓝 t := isOpen_Ioi.mem_nhds h1
      have hβat : ContinuousWithinAt β (Icc ts t₀) t :=
        (hβc t ⟨zero_le, ht.2⟩).mono (Icc_subset_Icc_left zero_le)
      have hfat : ContinuousAt f (β t) :=
        (hch.cont _ (hβD t h1 ht.2)).continuousAt
          ((isOpen_H_diff_fillH hAc.isBounded).mem_nhds (hβD t h1 ht.2))
      refine (hfat.comp_continuousWithinAt hβat).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds hn] with t' ht'
        simp [hbdef, not_le.2 (show ts < t' from ht')]
      · simp [hbdef, not_le.2 h1]
  have hbt₀ : b t₀ = e := by
    rcases eq_or_lt_of_le htst₀ with h | h
    · have hb : b t₀ = ((c : ℝ) : ℂ) := by simp [hbdef, h.symm.le]
      rw [hb]
      have hxsc : β t₀ = (xs : ℂ) := h ▸ hβts
      have heR : e.im = 0 := by
        rcases mem_H_or_im_eq_zero heHbar with he | he
        · exfalso
          have hm := (hch.inv_mem he).1
          rw [hΦe, ← hc, hxsc] at hm
          exact ofReal_notMem_H _ hm
        · exact he
      have hΦre : Φ (e.re : ℂ) = (xs : ℂ) := by rw [ofReal_re_of_im heR, hΦe, ← hc, hxsc]
      have := hch.eq_of_inv_eq hfc hΦre
      rw [← ofReal_re_of_im heR, this]
    · have hb : b t₀ = f (β t₀) := by simp [hbdef, not_le.2 h]
      rw [hb, hc]
      have heH : e ∈ H := by
        rcases mem_H_or_im_eq_zero heHbar with he | he
        · exact he
        · exfalso
          have hαH : α s₀ ∈ H := hc ▸ hafter t₀ h le_rfl
          have hbd := hch.bdry e.re (by rw [ofReal_re_of_im he, hΦe]; exact hαH)
          rw [ofReal_re_of_im he, hΦe] at hbd
          exact hαs₀A hbd
      rw [← hΦe, hch.f_inv e heH]
  -- the compact connected chart set `C`
  set C := b '' Icc ts t₀ ∪ γq '' Icc 0 r₀ with hCdef
  have heCβ : e ∈ b '' Icc ts t₀ := ⟨t₀, ⟨htst₀, le_rfl⟩, hbt₀⟩
  have heCα : e ∈ γq '' Icc 0 r₀ := ⟨r₀, ⟨hr₀0, le_rfl⟩, rfl⟩
  have hCc : IsCompact C :=
    (isCompact_Icc.image_of_continuousOn hbc).union (isCompact_Icc.image_of_continuousOn hγqc)
  have hCpc : IsPreconnected C :=
    (isPreconnected_Icc.image _ hbc).union e heCβ heCα (isPreconnected_Icc.image _ hγqc)
  have hCim : ∀ z ∈ C, 0 ≤ z.im := by
    rintro z (⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩)
    · by_cases h : t ≤ ts
      · simp [hbdef, h]
      · simp only [hbdef, h, ↓reduceIte]
        exact (hch.maps (hβD t (not_le.1 h) ht.2)).le
    · exact (hγ.extendFrom_shift_tip hWgc hWg0 q.coe_nonneg hu.1).1
  have hcC : ((c : ℝ) : ℂ) ∈ C := Or.inl ⟨ts, ⟨le_rfl, htst₀⟩, by simp [hbdef]⟩
  have h0C : ((0 : ℝ) : ℂ) ∈ C := Or.inr ⟨0, ⟨le_rfl, hr₀0⟩, by rw [hγq.1]; simp⟩
  have hyC : (y : ℂ) ∉ C := by
    rintro (⟨t, ht, hbt⟩ | ⟨u, hu, hγu⟩)
    · by_cases h : t ≤ ts
      · simp only [hbdef, h, ↓reduceIte] at hbt
        have : c = y := by exact_mod_cast hbt
        linarith
      · simp only [hbdef, h, ↓reduceIte] at hbt
        have hm := hch.maps (hβD t (not_le.1 h) ht.2)
        rw [hbt] at hm
        exact ofReal_notMem_H _ hm
    · have h1 := hΦγ u hu
      rw [hγu, hΦy] at h1
      have h2 := hinj hsζ ((ENNReal.coe_le_coe.2 (hle_s₀ u hu)).trans hs₀.le) h1
      have h3 : (s : ℝ) = q + u := by rw [h2, Real.coe_toNNReal _ (by linarith [hu.1, NNReal.coe_nonneg q])]
      have h4 : (s : ℝ) < q := NNReal.coe_lt_coe.2 hsq
      linarith [hu.1]
  obtain ⟨ε, hε, hdisC⟩ := isTrappedAt_of_isPreconnected hCc hCpc hCim hcC h0C hcy hyneg hyC
  -- the chart image of the joint unbounded domain lies in the unbounded domain of `C`
  have hfD : ∀ z ∈ H \ fillH K, f z ∈ H \ fillH C := by
    intro z hz
    have hZD : connectedComponentIn (H \ K) z ⊆ H \ fillH K :=
      connectedComponentIn_subset_H_diff_fillH hKc.isClosed hz
    have hzK : z ∈ H \ K := ((mem_H_diff_fillH_of_isClosed hKc.isClosed).1 hz).1
    have hZunb : ¬ IsBounded (connectedComponentIn (H \ K) z) :=
      ((mem_H_diff_fillH_of_isClosed hKc.isClosed).1 hz).2
    have hZpc : IsPreconnected (connectedComponentIn (H \ K) z) := isPreconnected_connectedComponentIn
    have hfZ : f '' connectedComponentIn (H \ K) z ⊆ H \ C := by
      rintro _ ⟨z', hz', rfl⟩
      have hz'D := hZD hz'
      have hz'A := hDA hz'D
      have hz'K : z' ∉ K := fun h => hz'D.2 ⟨hz'D.1, Or.inl (subset_closure h)⟩
      refine ⟨hch.maps hz'A, ?_⟩
      rintro (⟨t, ht, hbt⟩ | ⟨u, hu, hγu⟩)
      · by_cases h : t ≤ ts
        · simp only [hbdef, h, ↓reduceIte] at hbt
          have hm := hch.maps hz'A
          rw [← hbt] at hm
          exact ofReal_notMem_H _ hm
        · simp only [hbdef, h, ↓reduceIte] at hbt
          have := hch.injOn (hβD t (not_le.1 h) ht.2) hz'A hbt
          exact hz'K (this ▸ Or.inr ⟨t, ⟨zero_le, ht.2⟩, rfl⟩)
      · have h1 := hΦγ u hu
        rw [hγu, hch.inv_f z' hz'A] at h1
        exact hz'K (h1 ▸ Or.inl ⟨_, ⟨zero_le, hle_s₀ u hu⟩, rfl⟩)
    have hfZpc : IsPreconnected (f '' connectedComponentIn (H \ K) z) :=
      hZpc.image f (hch.cont.mono (hZD.trans hDA))
    have hfZunb : ¬ IsBounded (f '' connectedComponentIn (H \ K) z) := by
      obtain ⟨M, hM⟩ := hch.bdd
      intro hb
      apply hZunb
      obtain ⟨R, hR⟩ := hb.subset_closedBall 0
      refine (isBounded_closedBall (x := (0 : ℂ)) (r := R + M)).subset fun z' hz' => ?_
      have h1 := hR ⟨z', hz', rfl⟩
      have h2 := hM z' (hDA (hZD hz'))
      rw [mem_closedBall, dist_zero_right] at h1 ⊢
      calc ‖z'‖ = ‖f z' - (f z' - z')‖ := by ring_nf
        _ ≤ ‖f z'‖ + ‖f z' - z'‖ := norm_sub_le _ _
        _ ≤ R + M := add_le_add h1 h2
    exact subset_H_diff_fillH_of_not_isBounded hCc.isClosed hfZpc hfZunb hfZ
      ⟨z, mem_connectedComponentIn hzK, rfl⟩
  have hev : ∀ᶠ z in (U : Filter ℂ), z ∈ H \ fillH K := hU self_mem_nhdsWithin
  have hev2 : ∀ᶠ z in (U : Filter ℂ), f z ∈ ball (y : ℂ) ε := hy (ball_mem_nhds _ hε)
  obtain ⟨z, hz1, hz2⟩ := (hev.and hev2).exists
  exact Set.disjoint_left.1 hdisC hz2 (hfD z hz1)

/-- **The positive side in the physical chart of the first trace** (`pos_of_approach` for a path from `x₁`, with the
second path from `x₂ < x₁`): the chart `f_q(· − x₁)` has a positive limit along every approach to an interior point
`α(s)`, `s < q < s₀`, from the joint unbounded domain. -/
theorem pos_of_approach_phys {x₁ : ℝ} (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ₁ (fun t => α t - x₁)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₁})
    (hW0 : W 0 = 0) {s₀ t₀ q s : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) (hc : β t₀ = α s₀)
    (hdisj : ∀ t < t₀, β t ∉ α '' Icc 0 s₀) (hsq : s < q) (hqs : q < s₀) (hsH : α s ∈ H) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)] (α s)) {y : ℝ}
    (hy : Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₁)) U (𝓝 (y : ℂ))) : 0 < y := by
  set e := transR (-x₁) with he
  have heap : ∀ z, e z = z - x₁ := fun z => by rw [he, transR_apply]; push_cast; ring
  have hp₁' : IsPathGood (fun t => e (α t)) ζ₁ 0 := by
    refine ⟨fun a ha b hb hab => hp₁.1 ha hb (e.injective hab), W, hWc, hW0, ?_⟩
    simpa [heap] using hg
  have hp₂' : IsPathGood (fun t => e (β t)) ζ₂ (x₂ - x₁) := by
    obtain ⟨hi, w, hw, hw0, hg₂⟩ := hp₂
    refine ⟨fun a ha b hb hab => hi ha hb (e.injective hab), w, hw, hw0, ?_⟩
    have e₁ : (fun t => e (β t) - ((x₂ - x₁ : ℝ) : ℂ)) = fun t => β t - x₂ := by
      funext t; rw [heap]; push_cast; ring
    rw [e₁]; exact hg₂
  have himA : (fun t => e (α t)) '' Icc 0 s₀ = e '' (α '' Icc 0 s₀) := by rw [image_image]
  have himB : (fun t => e (β t)) '' Icc 0 t₀ = e '' (β '' Icc 0 t₀) := by rw [image_image]
  have hU' : ((U.map e : Ultrafilter ℂ) : Filter ℂ) ≤
      𝓝[H \ fillH ((fun t => e (α t)) '' Icc 0 s₀ ∪ (fun t => e (β t)) '' Icc 0 t₀)] (e (α s)) := by
    rw [Ultrafilter.coe_map, himA, himB, ← image_union, fillH_image_homeomorph e (transR_mem_H _) ?_,
      ← image_H_diff_homeomorph e (transR_mem_H _), ← e.isEmbedding.map_nhdsWithin_eq]
    · exact map_mono hU
    · intro S
      constructor
      · intro h
        have := (isometry_add_right (x₁ : ℂ)).lipschitzWith.isBounded_image h
        rwa [← image_comp, show ((fun z => z + (x₁ : ℂ)) ∘ e) = id from funext fun z => by
          simp [heap], image_id] at this
      · exact (isometry_add_right _).lipschitzWith.isBounded_image
  have hH : ∀ z, e z ∈ H ↔ z ∈ H := transR_mem_H _
  refine pos_of_approach hp₁' hp₂' (by linarith) (by simpa [heap] using hg) hWc hW0 hs₀ ht₀
    (by simp only [hc]) (fun t ht hm => hdisj t ht (by
      obtain ⟨u, hu, hue⟩ := hm
      exact ⟨u, hu, e.injective hue⟩)) hsq hqs ((hH _).2 hsH) _ hU' ?_
  rw [Ultrafilter.coe_map]
  refine tendsto_map'_iff.2 (hy.congr fun z => ?_)
  simp only [Function.comp_apply, heap]

/-- **The negative side in the physical chart of the second trace** (the reflection of `pos_of_approach_phys`): for
`β` from `x₂ < x₁` with first contact `β(t₀) = α(s₀)` before its lifetime, a stop `q < t₀` and an interior point
`β(s)`, `s < q`, the chart `f_q(· − x₂)` has a negative limit along every approach from the joint unbounded domain. -/
theorem neg_of_approach_phys {x₁ : ℝ} (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ₂ (fun t => β t - x₂)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₂})
    (hW0 : W 0 = 0) {s₀ t₀ q s : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ₂) (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁) (hc : α s₀ = β t₀)
    (hdisj : ∀ t < s₀, α t ∉ β '' Icc 0 t₀) (hsq : s < q) (hqt : q < t₀) (hsH : β s ∈ H) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)] (β s)) {y : ℝ}
    (hy : Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₂)) U (𝓝 (y : ℂ))) : y < 0 := by
  set R := LP.reflectHomeo with hR
  have hRap : ∀ z, R z = LP.reflectC z := fun z => rfl
  have hRH : ∀ z, R z ∈ H ↔ z ∈ H := fun z => LP.reflectC_mem_H_iff
  have hg' : IsGeneratingTrace (-W) ζ₂ (fun t => LP.reflectC (β t) - ((-x₂ : ℝ) : ℂ)) := by
    have h := LP.isGeneratingTrace_reflect hg
    have e₁ : (fun t => LP.reflectC (β t - x₂)) = fun t => LP.reflectC (β t) - ((-x₂ : ℝ) : ℂ) := by
      funext t; rw [LP.reflectC_sub, LP.reflectC_ofReal]
    rwa [e₁] at h
  have himA : (fun t => LP.reflectC (β t)) '' Icc 0 t₀ = R '' (β '' Icc 0 t₀) := by rw [image_image]; rfl
  have himB : (fun t => LP.reflectC (α t)) '' Icc 0 s₀ = R '' (α '' Icc 0 s₀) := by rw [image_image]; rfl
  have hU' : ((U.map R : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓝[H \ fillH ((fun t => LP.reflectC (β t)) '' Icc 0 t₀ ∪
      (fun t => LP.reflectC (α t)) '' Icc 0 s₀)] (LP.reflectC (β s)) := by
    rw [Ultrafilter.coe_map, himA, himB, ← image_union, fillH_image_homeomorph R hRH ?_,
      ← image_H_diff_homeomorph R hRH, ← hRap, ← R.isEmbedding.map_nhdsWithin_eq, union_comm]
    · exact map_mono hU
    · intro S; exact LP.isBounded_reflectC_image_iff
  have hpos := pos_of_approach_phys hp₂.reflect hp₁.reflect (by linarith) hg' hWc.neg (by simp [hW0]) ht₀ hs₀
    (by simp only [hc]) (fun t ht hm => hdisj t ht (by
      obtain ⟨u, hu, hue⟩ := hm
      exact ⟨u, hu, LP.reflectC_injective hue⟩)) hsq hqt (LP.reflectC_mem_H_iff.2 hsH) _ hU' (y := -y) ?_
  · linarith
  rw [Ultrafilter.coe_map]
  have h1 := (LP.continuous_reflectC.tendsto _).comp hy
  rw [LP.reflectC_ofReal] at h1
  refine tendsto_map'_iff.2 (h1.congr fun z => ?_)
  simp only [Function.comp_apply, hRap]
  have e₂ : LP.reflectC z - ((-x₂ : ℝ) : ℂ) = LP.reflectC (z - x₂) := by
    rw [LP.reflectC_sub, LP.reflectC_ofReal]
  have e₃ : (fun r : ℝ => (-W) r.toNNReal) = -(fun r : ℝ => W r.toNNReal) := rfl
  rw [e₂, e₃, LP.fwdMap_neg _ (NNReal.coe_nonneg q)]

end Sign

/-! ### The physical chart -/

section PhysChart

variable {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}

/-- **The chart facts of a simple trace from the real seed `x`** stopped at `q`, for the chart `f(z) = f_q(z − x)` and
the continuous extension `Φ(w) = F̄_q(w) + x` of its inverse (the physical form of `ReverseArc.IsChart`, with the
holomorphy of `Φ` on `ℍ`). -/
structure IsPhysChart (α : ℝ≥0 → ℂ) (q : ℝ≥0) (f Φ : ℂ → ℂ) : Prop where
  maps : MapsTo f (H \ fillH (α '' Icc 0 q)) H
  injOn : InjOn f (H \ fillH (α '' Icc 0 q))
  cont : ContinuousOn f (H \ fillH (α '' Icc 0 q))
  inv_cont : ContinuousOn Φ Hbar
  inv_mem : MapsTo Φ H (H \ fillH (α '' Icc 0 q))
  f_inv : ∀ w ∈ H, f (Φ w) = w
  inv_f : ∀ z ∈ H \ fillH (α '' Icc 0 q), Φ (f z) = z
  diff : DifferentiableOn ℂ Φ H
  tip : Φ 0 = α q
  tip_fibre : α q ∈ H → ∀ y : ℝ, Φ y = α q → y = 0
  bdry : ∀ y : ℝ, Φ y ∈ H → Φ y ∈ α '' Icc 0 q
  cluster : ∀ (U : Ultrafilter ℂ) (p : ℂ), (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q)] p →
    ∃ y ∈ Hbar, Tendsto f U (𝓝 y) ∧ Φ y = p

theorem extendFrom_eqOn_H {F : ℂ → ℂ} (hF : ContinuousOn F H) : EqOn (extendFrom H F) F H := fun z hz =>
  extendFrom_eq (subset_closure hz) ((hF z hz).tendsto)

/-- **The physical chart facts** of a simple frozen generating trace from `x`, stopped at `0 < q < ζ`. -/
theorem isPhysChart (hg : IsGeneratingTrace W ζ (fun t => α t - x)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ})
    (hW0 : W 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ}) (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) :
    IsPhysChart α q (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x))
      (fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) w + x) := by
  have hinj' : InjOn (fun t => α t - x) {t | (t : ℝ≥0∞) ≤ ζ} := fun a ha b hb hab =>
    hinj ha hb (sub_left_injective hab)
  have hch := isChart hg hWc hW0 hinj' hq hq0
  have hiff := mem_H_diff_fillH_phys_iff (α := α) x q
  -- holomorphy of the inverse, through the global model
  obtain ⟨Wg, γ, T', hqT', hWgc, hWg0, -, hWeq, -⟩ := exists_global_model hg hWc hW0 hq
  have hΦg : fwdMapInv (fun r : ℝ => W r.toNNReal) q = fwdMapInv Wg q :=
    fwdMapInv_eq_of_eqOn q.coe_nonneg hqT' fun r hr => (hWeq r hr).symm
  have hdg : DifferentiableOn ℂ (fwdMapInv Wg q) H :=
    QuantumZipper.RS.differentiableOn_fwdMapInv hWgc hWg0 q.coe_nonneg
  refine ⟨fun z hz => hch.maps ((hiff z).1 hz), fun a ha b hb hab => ?_, ?_, hch.inv_cont.add continuousOn_const,
    fun w hw => ?_, fun w hw => ?_, fun z hz => ?_, ?_, ?_, fun htip y hy => ?_, fun y hy => ?_,
    fun U p hU => ?_⟩
  · have := hch.injOn ((hiff a).1 ha) ((hiff b).1 hb) hab
    exact sub_left_injective this
  · exact hch.cont.comp (continuous_sub_right (x : ℂ)).continuousOn fun z hz => (hiff z).1 hz
  · rw [hiff, add_sub_cancel_right]
    exact hch.inv_mem hw
  · show fwdMap _ q (extendFrom H _ w + x - x) = w
    rw [add_sub_cancel_right]
    exact hch.f_inv w hw
  · show extendFrom H _ (fwdMap _ q (z - x)) + x = z
    rw [hch.inv_f _ ((hiff z).1 hz), sub_add_cancel]
  · have h1 : DifferentiableOn ℂ (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q)) H := by
      rw [hΦg]
      exact hdg.congr (extendFrom_eqOn_H hdg.continuousOn)
    exact h1.add_const (x : ℂ)
  · show extendFrom H _ 0 + x = α q
    rw [hch.tip, sub_add_cancel]
  · have h1 : extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) y = α q - x := by
      have := congrArg (fun z => z - (x : ℂ)) hy
      simpa using this
    refine hch.tip_fibre ?_ y h1
    show 0 < (α q - x).im
    simpa using (show 0 < (α q).im from htip)
  · have hH : extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) y ∈ H := by
      have : 0 < (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) y + x).im := hy
      show 0 < (extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) y).im
      simpa using this
    obtain ⟨t, ht, hte⟩ := hch.bdry y hH
    exact ⟨t, ht, by simp only at hte; rw [← hte, sub_add_cancel]⟩
  · set e : ℂ → ℂ := fun z => z - x with he
    have hU' : ((U.map e : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓝[H \ fillH ((fun t => α t - x) '' Icc 0 q)] (p - x) := by
      rw [Ultrafilter.coe_map]
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (x : ℂ)).tendsto p).comp
        (hU.trans nhdsWithin_le_nhds), ?_⟩
      filter_upwards [hU self_mem_nhdsWithin] with z hz using (hiff z).1 hz
    obtain ⟨y, hyH, hfy, hΦy⟩ := hch.cluster _ (p - x) hU'
    refine ⟨y, hyH, ?_, ?_⟩
    · rw [Ultrafilter.coe_map] at hfy
      exact tendsto_map'_iff.1 hfy
    · show extendFrom H _ y + x = p
      rw [hΦy, sub_add_cancel]

/-- **The chart limit at a point of the stopped trace is real**, and `Φ` maps it back to the point. -/
theorem IsPhysChart.exists_real_tendsto {f Φ : ℂ → ℂ} (hch : IsPhysChart α q f Φ) {p : ℂ}
    (hp : p ∈ α '' Icc 0 q) (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q)] p) :
    ∃ y : ℝ, Tendsto f U (𝓝 (y : ℂ)) ∧ Φ y = p := by
  obtain ⟨y, hyH, hfy, hΦy⟩ := hch.cluster U p hU
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have hm := hch.inv_mem hpos
    rw [hΦy] at hm
    exact hm.2 ⟨hm.1, Or.inl (subset_closure hp)⟩
  refine ⟨y.re, ?_, ?_⟩ <;> rw [ofReal_re_of_im hyim]
  exacts [hfy, hΦy]

end PhysChart

/-! ### Real points of the trace: the local argument -/

section Local

/-- **A connected compact parameter set mapped onto a real segment.** A good path whose trace contains a nondegenerate
real segment is impossible: the parameters of the segment form an interval (the restriction is a homeomorphism), on
which the path would be real, against the density of interior times. -/
theorem not_forall_Icc_mem_image {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x₀ : ℝ} (hp : IsPathGood η ζ x₀) {s₀ : ℝ≥0}
    (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ) {u v : ℝ} (huv : u < v) : ¬ ∀ x ∈ Icc u v, (x : ℂ) ∈ η '' Icc 0 s₀ := by
  intro h
  have hc := IsPathGood.continuousOn_Icc hp hs₀
  have hi := IsPathGood.injOn_Icc hp hs₀
  set J : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc u v with hJ
  have hJc : IsClosed J := (isCompact_Icc.image continuous_ofReal).isClosed
  set E := Icc 0 s₀ ∩ η ⁻¹' J with hE
  have hEc : IsCompact E :=
    isCompact_Icc.of_isClosed_subset (hc.preimage_isClosed_of_isClosed isClosed_Icc hJc) inter_subset_left
  have : CompactSpace E := isCompact_iff_compactSpace.1 hEc
  set g : E → ℂ := fun t => η t with hgdef
  have hgc : Continuous g := hc.comp_continuous continuous_subtype_val fun t => t.2.1
  have hgi : Function.Injective g := fun a b hab => Subtype.ext (hi a.2.1 b.2.1 hab)
  have hemb := hgc.isClosedEmbedding hgi
  have hrange : Set.range g = J := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact t.2.2
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht, hte⟩ := h x hx
      exact ⟨⟨t, ht, by rw [mem_preimage, hte]; exact ⟨x, hx, rfl⟩⟩, hte⟩
  have hJpc : IsPreconnected J := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have hEpc : IsPreconnected (univ : Set E) := by
    rw [← hemb.isInducing.isPreconnected_image, image_univ, hrange]
    exact hJpc
  have hEpc' : IsPreconnected E := by
    have := hEpc.image Subtype.val continuous_subtype_val.continuousOn
    rwa [image_univ, Subtype.range_coe] at this
  obtain ⟨a, ha, hau⟩ := h u ⟨le_rfl, huv.le⟩
  obtain ⟨b, hb, hbv⟩ := h v ⟨huv.le, le_rfl⟩
  have haE : a ∈ E := ⟨ha, by rw [mem_preimage, hau]; exact ⟨u, ⟨le_rfl, huv.le⟩, rfl⟩⟩
  have hbE : b ∈ E := ⟨hb, by rw [mem_preimage, hbv]; exact ⟨v, ⟨huv.le, le_rfl⟩, rfl⟩⟩
  have hab : a ≠ b := by
    intro he
    rw [he, hbv] at hau
    exact (ne_of_lt huv) (by exact_mod_cast hau.symm)
  have hcase : ∀ a' b' : ℝ≥0, a' ∈ E → b' ∈ E → a' < b' → False := by
    intro a' b' ha' hb' hlt
    obtain ⟨t, ht, htH⟩ := IsPathGood.exists_mem_H hp hlt ((ENNReal.coe_le_coe.2 hb'.1.2).trans hs₀)
    have htE : t ∈ E := hEpc'.Icc_subset ha' hb' ⟨ht.1.le, ht.2.le⟩
    obtain ⟨x, -, hx⟩ := htE.2
    rw [← hx] at htH
    exact ofReal_notMem_H x htH
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact hcase a b haE hbE hlt
  · exact hcase b a hbE haE hlt

/-- **The side at every point of the trace, from the side at interior points** (the local argument; Lemma 7.8, p. 294:
"An original real contact in the interior of one arc creates no further exceptional datum"). Let `f` map the
unbounded domain of a closed set `A` into `ℍ` with inverse `Φ`, continuous on `ℍ̄` and holomorphic on `ℍ`, and let
`Γ ⊇ A` agree with `A` near `p`. Suppose every approach from `ℍ \ fill Γ` to a point `Φ(y') ∈ ℍ` (`y' ≠ 0`) along
which `f → y'` has `σ y' > 0`, and that near `p` the real points adherent to `ℍ \ fill Γ` lie in a set `S` containing
no real segment. Then every approach to `p` from `ℍ \ fill Γ` along which `f → y ≠ 0` has `σ y > 0`.

If `σ y < 0`, the half-disc at `y` maps into `ℍ \ fill Γ`, so every nearby real `y'` has `Φ(y')` adherent to it, and
`Φ(y')` cannot be in `ℍ`; the real points `Φ(y')` lie in `S`, so `Re Φ` is constant near `y` (a connected image), and
`Φ` is constant on a real segment, which the Schwarz reflection and the identity theorem forbid. -/
theorem sign_of_approach {σ : ℝ} (hσ : σ ≠ 0) {A S Γ : Set ℂ} {f Φ : ℂ → ℂ} {p : ℂ} (hΓ : IsClosed Γ)
    (hAΓ : A ⊆ Γ) (hmaps : MapsTo f (H \ fillH A) H) (hΦc : ContinuousOn Φ Hbar)
    (hΦH : MapsTo Φ H (H \ fillH A)) (hfΦ : ∀ w ∈ H, f (Φ w) = w) (hΦf : ∀ z ∈ H \ fillH A, Φ (f z) = z)
    (hΦd : DifferentiableOn ℂ Φ H) {r : ℝ} (hr : 0 < r) (hloc : Γ ∩ ball p r ⊆ A)
    (hreal : ∀ z ∈ ball p r, z.im = 0 → z ∈ closure (H \ fillH Γ) → z ∈ S)
    (hS : ∀ u v : ℝ, u < v → ¬ ∀ x ∈ Icc u v, (x : ℂ) ∈ S)
    (hint : ∀ y' : ℝ, y' ≠ 0 → Φ y' ∈ H → ∀ U' : Ultrafilter ℂ, (U' : Filter ℂ) ≤ 𝓝[H \ fillH Γ] (Φ y') →
      Tendsto f U' (𝓝 (y' : ℂ)) → 0 < σ * y')
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH Γ] p) {y : ℝ} (hy0 : y ≠ 0)
    (hy : Tendsto f U (𝓝 (y : ℂ))) : 0 < σ * y := by
  by_contra hneg
  have hσy : σ * y < 0 := lt_of_le_of_ne (not_lt.1 hneg) (mul_ne_zero hσ hy0)
  have hDA : H \ fillH Γ ⊆ H \ fillH A := sdiff_subset_sdiff_right (fillH_mono hAΓ)
  have hrealH : ∀ t : ℝ, ((t : ℝ) : ℂ) ∈ Hbar := fun t => by show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im; simp
  -- `Φ(y) = p`
  have hev : ∀ᶠ z in (U : Filter ℂ), z ∈ H \ fillH Γ := hU self_mem_nhdsWithin
  have hfH : Tendsto f U (𝓝[Hbar] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hy, hev.mono fun z hz => H_subset_Hbar (hmaps (hDA hz))⟩
  have hΦy : Φ y = p := tendsto_nhds_unique ((hΦc _ (hrealH y)).tendsto.comp hfH)
    ((tendsto_nhds_of_tendsto_nhdsWithin hU).congr' (hev.mono fun z hz => (hΦf z (hDA hz)).symm))
  -- the half-disc at `y` maps into the domain
  obtain ⟨ε, hε, hno⟩ := exists_ball_notMem_of_approach hΓ hAΓ hmaps hΦc hΦH hΦf hr hloc U hU hy
  have hΦD : ∀ w ∈ ball (y : ℂ) ε, w ∈ H → Φ w ∈ H \ fillH Γ := fun w hw hwH => by
    refine ⟨(hΦH hwH).1, fun hK => hno _ (hΦH hwH) hK ?_⟩
    rw [hfΦ w hwH]
    exact hw
  obtain ⟨δ₀, hδ₀, hδ₀Φ⟩ := Metric.continuousWithinAt_iff.1 (hΦc _ (hrealH y)) r hr
  set δ := min (min (ε / 2) δ₀) (|y| / 2) with hδdef
  have hδ : 0 < δ := lt_min (lt_min (half_pos hε) hδ₀) (half_pos (abs_pos.2 hy0))
  have hδε : δ ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδδ₀ : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hδy : δ ≤ |y| / 2 := min_le_right _ _
  -- the facts along the real interval `(y − δ, y + δ)`
  have hI : ∀ y' : ℝ, |y' - y| < δ → (Φ y').im = 0 ∧ Φ y' ∈ S := by
    intro y' hy'
    have hσy' : σ * y' < 0 := by
      have h1 : |σ * y' - σ * y| < |σ * y| / 2 := by
        rw [← mul_sub, abs_mul, abs_mul, mul_div_assoc]
        exact mul_lt_mul_of_pos_left (hy'.trans_le hδy) (abs_pos.2 hσ)
      have h2 : |σ * y| = -(σ * y) := abs_of_neg hσy
      have h3 := (abs_sub_lt_iff.1 h1).1
      linarith
    have hy'0 : y' ≠ 0 := fun h => by rw [h, mul_zero] at hσy'; exact lt_irrefl 0 hσy'
    have hdist : dist ((y' : ℝ) : ℂ) (y : ℂ) < δ := by rwa [Complex.dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    have hball : Φ y' ∈ ball p r := by
      rw [← hΦy]
      exact hδ₀Φ (hrealH y') (hdist.trans_le hδδ₀)
    -- approaches to `Φ(y')` through the half-disc
    have hnear : ∀ᶠ z in 𝓝[H] ((y' : ℝ) : ℂ), Φ z ∈ H \ fillH Γ := by
      have hb : ball ((y' : ℝ) : ℂ) (ε / 2) ∈ 𝓝 ((y' : ℝ) : ℂ) := ball_mem_nhds _ (half_pos hε)
      filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with z hzb hzH
      refine hΦD z ?_ hzH
      rw [mem_ball] at hzb ⊢
      calc dist z (y : ℂ) ≤ dist z ((y' : ℝ) : ℂ) + dist ((y' : ℝ) : ℂ) (y : ℂ) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hzb (hdist.trans_le hδε)
        _ = ε := add_halves ε
    have hne := neBot_nhdsWithin_H_ofReal y'
    have hΦt : Tendsto Φ (𝓝[H] ((y' : ℝ) : ℂ)) (𝓝[H \ fillH Γ] (Φ y')) :=
      tendsto_nhdsWithin_iff.2 ⟨((hΦc _ (hrealH y')).mono H_subset_Hbar).tendsto, hnear⟩
    have hcl : Φ y' ∈ closure (H \ fillH Γ) := mem_closure_of_tendsto (tendsto_nhds_of_tendsto_nhdsWithin hΦt) hnear
    have hnH : Φ y' ∉ H := by
      intro hH
      set U' := Ultrafilter.of (Filter.map Φ (𝓝[H] ((y' : ℝ) : ℂ))) with hU'def
      have hU'le : (U' : Filter ℂ) ≤ Filter.map Φ (𝓝[H] ((y' : ℝ) : ℂ)) := Ultrafilter.of_le _
      have hfU' : Tendsto f U' (𝓝 (y' : ℂ)) := by
        refine Tendsto.mono_left ?_ hU'le
        rw [tendsto_map'_iff]
        exact (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall fun z hz => (hfΦ z hz).symm)
      have := hint y' hy'0 hH U' (hU'le.trans hΦt) hfU'
      linarith
    have hHbar : Φ y' ∈ Hbar := by
      have := closure_mono (show H \ fillH Γ ⊆ H from sdiff_subset) hcl
      rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar] at this
    have him : (Φ y').im = 0 := le_antisymm (not_lt.1 hnH) hHbar
    exact ⟨him, hreal _ hball him hcl⟩
  have hIy : |y - y| < δ := by rw [sub_self, abs_zero]; exact hδ
  have hcim : (Φ y).im = 0 := (hI y hIy).1
  by_cases hconst : ∀ y' : ℝ, |y' - y| < δ → Φ y' = Φ y
  · -- `Φ` constant on a real segment: the Schwarz reflection
    have hd : DifferentiableOn ℂ (fun z => Φ z - Φ y) (H ∩ ball (y : ℂ) δ) :=
      (hΦd.mono inter_subset_left).sub_const _
    have hc : ContinuousOn (fun z => Φ z - Φ y) (Hbar ∩ ball (y : ℂ) δ) :=
      (hΦc.mono inter_subset_left).sub continuousOn_const
    have hre : ∀ z ∈ ball (y : ℂ) δ, z.im = 0 → (Φ z - Φ y).im = 0 := by
      intro z hz hzim
      have hz' : z = ((z.re : ℝ) : ℂ) := (ofReal_re_of_im hzim).symm
      have hd' : |z.re - y| < δ := by
        rw [mem_ball, hz', Complex.dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hz
        exact hz
      rw [hz', hconst z.re hd', sub_self, zero_im]
    obtain ⟨G, hGd, hGeq, -⟩ := QuantumZipper.CA.exists_reflection_extension hd hc hre
    have hGa : AnalyticOnNhd ℂ G (ball (y : ℂ) δ) := hGd.analyticOnNhd isOpen_ball
    have hseq : Tendsto (fun n : ℕ => (((y + δ / ((n : ℝ) + 2)) : ℝ) : ℂ)) atTop (𝓝[≠] (y : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          refine tendsto_const_nhds.div_atTop ?_
          exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun n : ℕ => y + δ / ((n : ℝ) + 2)) atTop (𝓝 y) := by
          simpa using (tendsto_const_nhds (x := y)).add h1
        exact (continuous_ofReal.tendsto y).comp h2
      · show (((y + δ / ((n : ℝ) + 2)) : ℝ) : ℂ) ≠ (y : ℂ)
        intro h
        have : δ / ((n : ℝ) + 2) = 0 := by
          have h' := ofReal_injective h
          linarith
        exact (div_pos hδ (by positivity)).ne' this
    have hG0 : ∀ n : ℕ, G (((y + δ / ((n : ℝ) + 2)) : ℝ) : ℂ) = 0 := by
      intro n
      set t : ℝ := y + δ / ((n : ℝ) + 2) with htdef
      have hlt : |t - y| < δ := by
        rw [htdef, add_sub_cancel_left, abs_of_pos (div_pos hδ (by positivity))]
        exact div_lt_self hδ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      have hmem : ((t : ℝ) : ℂ) ∈ Hbar ∩ ball (y : ℂ) δ := by
        refine ⟨hrealH t, ?_⟩
        rw [mem_ball, Complex.dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs]
        exact hlt
      rw [hGeq hmem]
      show Φ t - Φ y = 0
      rw [hconst t hlt, sub_self]
    have hfreq : ∃ᶠ z in 𝓝[≠] (y : ℂ), G z = 0 := hseq.frequently (Frequently.of_forall hG0)
    have hzero := hGa.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball _ _).isPreconnected
      (mem_ball_self hδ) hfreq
    set z₀ : ℂ := (y : ℂ) + ((δ / 2 : ℝ) : ℂ) * I with hz₀
    have hz₀H : z₀ ∈ H := by show 0 < z₀.im; simp [hz₀, hδ]
    have hz₀b : z₀ ∈ ball (y : ℂ) δ := by
      rw [mem_ball, Complex.dist_eq, hz₀, add_sub_cancel_left, norm_mul, norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    have h1 := hGeq ⟨H_subset_Hbar hz₀H, hz₀b⟩
    rw [hzero hz₀b] at h1
    have h2 : Φ z₀ = Φ y := by
      have := h1.symm
      simp only [Pi.zero_apply] at this
      exact sub_eq_zero.1 this
    have h3 : 0 < (Φ z₀).im := (hΦH hz₀H).1
    rw [h2, hcim] at h3
    exact lt_irrefl 0 h3
  · -- `Re Φ` takes two values: a real segment of `S`
    push Not at hconst
    obtain ⟨y₁, hy₁, hne⟩ := hconst
    have h1 := hI y₁ hy₁
    have hre_ne : (Φ y₁).re ≠ (Φ y).re := fun h => hne (Complex.ext h (h1.1.trans hcim.symm))
    set g : ℝ → ℝ := fun t => (Φ t).re with hgdef
    set I₀ := Ioo (y - δ) (y + δ) with hI₀
    have hmemI : ∀ t ∈ I₀, |t - y| < δ := fun t ht => abs_sub_lt_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hgc : ContinuousOn g I₀ :=
      Complex.continuous_re.comp_continuousOn ((hΦc.comp continuous_ofReal.continuousOn fun t _ => hrealH t))
    have hpc : IsPreconnected (g '' I₀) := isPreconnected_Ioo.image g hgc
    have hyI : y ∈ I₀ := ⟨by linarith, by linarith⟩
    have hy₁I : y₁ ∈ I₀ := ⟨by linarith [(abs_sub_lt_iff.1 hy₁).2], by linarith [(abs_sub_lt_iff.1 hy₁).1]⟩
    have hseg : ∀ x ∈ Icc (min (g y₁) (g y)) (max (g y₁) (g y)), (x : ℂ) ∈ S := by
      intro x hx
      have hm1 : min (g y₁) (g y) ∈ g '' I₀ := by
        rcases min_choice (g y₁) (g y) with h | h <;> rw [h]
        exacts [mem_image_of_mem g hy₁I, mem_image_of_mem g hyI]
      have hm2 : max (g y₁) (g y) ∈ g '' I₀ := by
        rcases max_choice (g y₁) (g y) with h | h <;> rw [h]
        exacts [mem_image_of_mem g hy₁I, mem_image_of_mem g hyI]
      obtain ⟨t, ht, rfl⟩ := hpc.Icc_subset hm1 hm2 hx
      have := hI t (hmemI t ht)
      rw [show ((g t : ℝ) : ℂ) = Φ t from ofReal_re_of_im this.1]
      exact this.2
    exact hS _ _ (min_lt_max.2 hre_ne) hseg

end Local

/-! ### The side at every point of the two traces -/

section General

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **Local agreement before the contact**: near `α(s)`, `s < q ≤ s₀`, the union `α([0, s₀]) ∪ β([0, t₀])` of two
paths with first contact `α(s₀) = β(t₀)` is the prefix `α([0, q])`. -/
theorem exists_ball_inter_subset (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) {s₀ t₀ q s : ℝ≥0}
    (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁) (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) (hc : β t₀ = α s₀) (hdisj : ∀ t < t₀, β t ∉ α '' Icc 0 s₀)
    (hsq : s < q) (hqs : q ≤ s₀) :
    ∃ r > 0, (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀) ∩ ball (α s) r ⊆ α '' Icc 0 q := by
  have hinj := IsPathGood.injOn_Icc hp₁ hs₀
  set Z := β '' Icc 0 t₀ ∪ α '' Icc q s₀ with hZdef
  have hZc : IsCompact Z := (IsPathGood.isCompact_image hp₂ ht₀).union (IsPathGood.isCompact_image_Icc hp₁ hs₀)
  have hsI : s ∈ Icc 0 s₀ := ⟨zero_le, (hsq.trans_le hqs).le⟩
  have hsZ : α s ∉ Z := by
    rintro (⟨t, ht, hte⟩ | ⟨u, hu, hue⟩)
    · rcases lt_or_eq_of_le ht.2 with ht' | rfl
      · exact hdisj t ht' ⟨s, hsI, hte.symm⟩
      · rw [hc] at hte
        have := hinj ⟨zero_le, le_rfl⟩ hsI hte
        exact absurd (this ▸ hsq.trans_le hqs) (lt_irrefl _)
    · have := hinj ⟨zero_le, hu.2⟩ hsI hue
      exact absurd (this ▸ hu.1) (not_le.2 hsq)
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.1 hZc.isClosed.isOpen_compl _ hsZ
  refine ⟨r, hr, ?_⟩
  rintro z ⟨⟨u, hu, rfl⟩ | hzβ, hzb⟩
  · by_cases huq : u ≤ q
    · exact ⟨u, ⟨hu.1, huq⟩, rfl⟩
    · exact absurd (Or.inr ⟨u, ⟨(not_le.1 huq).le, hu.2⟩, rfl⟩) (hrZ hzb)
  · exact absurd (Or.inl hzβ) (hrZ hzb)

/-- **The joint unbounded domain sees the positive side of the first trace at every point of it before the contact**
(interior points: `pos_of_approach_phys`; real points of the trace: the local argument `sign_of_approach`). The real
points adherent to the domain near `α(s)` are assumed to lie on `α` (`hreal`; in the first-contact chart this is
`notMem_closure_D_of_mem_Ioo`). -/
theorem pos_of_approach_gen (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ₁ (fun t => α t - x₁)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₁})
    (hW0 : W 0 = 0) {s₀ t₀ q s : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) (hc : β t₀ = α s₀)
    (hdisj : ∀ t < t₀, β t ∉ α '' Icc 0 s₀) (hsq : s < q) (hqs : q < s₀) (htip : α q ∈ H) {r : ℝ} (hr : 0 < r)
    (hreal : ∀ z ∈ ball (α s) r, z.im = 0 → z ∈ closure (H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)) →
      z ∈ α '' Icc 0 s₀)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)] (α s)) {y : ℝ}
    (hy : Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₁)) U (𝓝 (y : ℂ))) : 0 < y := by
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hsq
  have hqζ : (q : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hqs).trans hs₀
  have hch := isPhysChart hg hWc hW0 hp₁.1 hqζ hq0
  have hKc : IsCompact (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀) :=
    (IsPathGood.isCompact_image hp₁ hs₀.le).union (IsPathGood.isCompact_image hp₂ ht₀)
  have hAK : α '' Icc 0 q ⊆ α '' Icc 0 s₀ ∪ β '' Icc 0 t₀ :=
    (image_mono (Icc_subset_Icc_right hqs.le)).trans subset_union_left
  obtain ⟨r₂, hr₂, hloc⟩ := exists_ball_inter_subset hp₁ hp₂ hs₀.le ht₀ hc hdisj hsq hqs.le
  have hUA : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q)] (α s) :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono hAK)))
  obtain ⟨y', hfy', hΦy'⟩ := hch.exists_real_tendsto ⟨s, ⟨zero_le, hsq.le⟩, rfl⟩ U hUA
  have hyy : y' = y := ofReal_injective (tendsto_nhds_unique hfy' hy)
  subst hyy
  have hsζ : (s : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 (hsq.trans hqs).le).trans hs₀.le
  have hy0 : y' ≠ 0 := by
    intro h0
    rw [h0, ofReal_zero, hch.tip] at hΦy'
    exact (ne_of_lt hsq) (hp₁.1 hqζ.le hsζ hΦy').symm
  have hint : ∀ y'' : ℝ, y'' ≠ 0 → (fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) w + x₁) y'' ∈ H →
      ∀ U' : Ultrafilter ℂ, (U' : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)]
        ((fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) w + x₁) y'') →
      Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₁)) U' (𝓝 (y'' : ℂ)) → 0 < 1 * y'' := by
    intro y'' hy''0 hH U' hU' hfU'
    obtain ⟨s', hs', hs'e⟩ := hch.bdry y'' hH
    have hs'q : s' < q := lt_of_le_of_ne hs'.2 fun h => hy''0 (hch.tip_fibre htip y'' (by rw [← hs'e, h]))
    simp only at hH hU'
    rw [← hs'e] at hH hU'
    rw [one_mul]
    exact pos_of_approach_phys hp₁ hp₂ hx hg hWc hW0 hs₀ ht₀ hc hdisj hs'q hqs hH U' hU' hfU'
  have := sign_of_approach one_ne_zero hKc.isClosed hAK hch.maps hch.inv_cont hch.inv_mem hch.f_inv hch.inv_f
    hch.diff (lt_min hr hr₂) (fun z hz => hloc ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩)
    (fun z hz => hreal z (ball_subset_ball (min_le_left _ _) hz))
    (fun u v huv => not_forall_Icc_mem_image hp₁ hs₀.le huv) hint U hU hy0 hy
  linarith

/-- **The joint unbounded domain sees the negative side of the second trace at every point of it before the
contact** (the mirror image of `pos_of_approach_gen`). -/
theorem neg_of_approach_gen (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ₂ (fun t => β t - x₂)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₂})
    (hW0 : W 0 = 0) {s₀ t₀ q s : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ₂) (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁) (hc : α s₀ = β t₀)
    (hdisj : ∀ t < s₀, α t ∉ β '' Icc 0 t₀) (hsq : s < q) (hqt : q < t₀) (htip : β q ∈ H) {r : ℝ} (hr : 0 < r)
    (hreal : ∀ z ∈ ball (β s) r, z.im = 0 → z ∈ closure (H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)) →
      z ∈ β '' Icc 0 t₀)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)] (β s)) {y : ℝ}
    (hy : Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₂)) U (𝓝 (y : ℂ))) : y < 0 := by
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hsq
  have hqζ : (q : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hqt).trans ht₀
  have hch := isPhysChart hg hWc hW0 hp₂.1 hqζ hq0
  have hKc : IsCompact (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀) :=
    (IsPathGood.isCompact_image hp₁ hs₀).union (IsPathGood.isCompact_image hp₂ ht₀.le)
  have hAK : β '' Icc 0 q ⊆ α '' Icc 0 s₀ ∪ β '' Icc 0 t₀ :=
    (image_mono (Icc_subset_Icc_right hqt.le)).trans subset_union_right
  obtain ⟨r₂, hr₂, hloc⟩ := exists_ball_inter_subset hp₂ hp₁ ht₀.le hs₀ hc hdisj hsq hqt.le
  rw [union_comm] at hloc
  have hUA : (U : Filter ℂ) ≤ 𝓝[H \ fillH (β '' Icc 0 q)] (β s) :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono hAK)))
  obtain ⟨y', hfy', hΦy'⟩ := hch.exists_real_tendsto ⟨s, ⟨zero_le, hsq.le⟩, rfl⟩ U hUA
  have hyy : y' = y := ofReal_injective (tendsto_nhds_unique hfy' hy)
  subst hyy
  have hsζ : (s : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 (hsq.trans hqt).le).trans ht₀.le
  have hy0 : y' ≠ 0 := by
    intro h0
    rw [h0, ofReal_zero, hch.tip] at hΦy'
    exact (ne_of_lt hsq) (hp₂.1 hqζ.le hsζ hΦy').symm
  have hint : ∀ y'' : ℝ, y'' ≠ 0 → (fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) w + x₂) y'' ∈ H →
      ∀ U' : Ultrafilter ℂ, (U' : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 s₀ ∪ β '' Icc 0 t₀)]
        ((fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) q) w + x₂) y'') →
      Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₂)) U' (𝓝 (y'' : ℂ)) → 0 < -1 * y'' := by
    intro y'' hy''0 hH U' hU' hfU'
    obtain ⟨s', hs', hs'e⟩ := hch.bdry y'' hH
    have hs'q : s' < q := lt_of_le_of_ne hs'.2 fun h => hy''0 (hch.tip_fibre htip y'' (by rw [← hs'e, h]))
    simp only at hH hU'
    rw [← hs'e] at hH hU'
    have := neg_of_approach_phys hp₁ hp₂ hx hg hWc hW0 ht₀ hs₀ hc hdisj hs'q hqt hH U' hU' hfU'
    linarith
  have := sign_of_approach (neg_ne_zero.2 one_ne_zero) hKc.isClosed hAK hch.maps hch.inv_cont hch.inv_mem
    hch.f_inv hch.inv_f hch.diff (lt_min hr hr₂) (fun z hz => hloc ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩)
    (fun z hz => hreal z (ball_subset_ball (min_le_left _ _) hz))
    (fun u v huv => not_forall_Icc_mem_image hp₂ ht₀.le huv) hint U hU hy0 hy
  linarith

end General

end SideHeightBox

end Sec7

end InteractingSLE
