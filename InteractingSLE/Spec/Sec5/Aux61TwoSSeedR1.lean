/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61TwoSSeed
import InteractingSLE.Spec.Sec5.Aux61RestartFinRetargetLog
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# Aux. 61, the two new sides: R1's inherited own branch is seed-normalized

Packet PROVE-AUX61-TWOSIDES ("check R1's lift normalisation first"). R1's restart chart has the lift
`Im physicalRestartLog (stripTargetHull D)`; by R1's chain rule (`physicalRestartLog_chain`) this is the additional
logarithm (zero phase on the current collar, `exists_restartAdditionalLog_phase_zero`) plus the **own** branch
`physicalRestartLog A`, `A = stripTargetHull (ℍ ∖ K_r)`, `K_r` the physical hull at the restart time. This file proves
that the own branch carries no extra multiple of `2π` at the old tip relative to the physical flow's own logarithm:

  **`tendsto_im_physicalRestartLog_sub_logDerivFwd`** : `Im (physicalRestartLog A − L_r) ∘ F_r → 0` at `0`.

Proof. `N = mapOut A ∘ R ∘ F_r` (`R(z) = z/(1 − z)`) is a conformal self-map of `ℍ` and
`Λ = (physicalRestartLog A − L_r) ∘ F_r` a continuous logarithm of `N′` (chain rule). `N` is real-boundary-conformal at
every real point `ξ` with `F̄_r(ξ) ≠ 1` (properness of `mapOut A`: `R ∘ F_r` tends to a point off `ℍ ∖ A`), so `Im Λ`
has a limit in `2πℤ` there, constant along the real interval `[0, p₁]` (the tip image `0`, the right side of the slit,
the right base point and a real point `p₁` just right of it with `x₁ = F̄_r(p₁) ∈ (0, ½)`). At `p₁` all three terms are
untouched-point limits (Aux. 57 for `A` at `R(x₁)` and for `K_r` at `x₁`; `−2 log(1 − x₁)` is real), so the integer
is `0`. Consequently a restart chart with R1's lift needs the height offset `a = 0` (the seed heights are `∓λ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61TwoS

open WangWu (IsProperArc chartAL chartAR)
open Aux61Restart (stripRightRetarget stripTargetHull physicalRestartLog stripRightRetargetLog)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}

/-- The boundary value of the inverse Loewner map at a real point is never a point of `ℍ ∖ K_t`. -/
theorem extendFrom_notMem_compl_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) {t : ℝ}
    (ht : 0 ≤ t) (x : ℝ) : extendFrom H (fwdMapInv W t) x ∉ H \ fwdHull W t := by
  intro hx
  have hNB := GlueImg.nhdsWithin_H_neBot x
  have hB := hη.hasBdryLimits hW hW0 ht
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hfc : ContinuousAt (fwdMap W t) (extendFrom H (fwdMapInv W t) x) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht).mem_nhds hx)).continuousAt
  have h1 := hfc.tendsto.comp (hB.tendsto hxH)
  have h2 : Tendsto (fun y => fwdMap W t (fwdMapInv W t y)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hy).symm
  have h3 := tendsto_nhds_unique h1 h2
  have h4 : (0 : ℝ) < (fwdMap W t (extendFrom H (fwdMapInv W t) x)).im :=
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hx
  rw [h3] at h4
  simp at h4

/-- The retargeting map is continuous off `1`. -/
theorem continuousAt_stripRightRetarget {q : ℂ} (hq : q ≠ 1) : ContinuousAt stripRightRetarget q := by
  have he : stripRightRetarget = fun z : ℂ => z / (1 - z) := funext Aux61Restart.stripRightRetarget_eq
  rw [he]
  exact continuousAt_id.div (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 (Ne.symm hq))

/-- **R1's own branch is seed-normalized**: `Im (physicalRestartLog A − L_r) ∘ F_r → 0` at the old tip, for
`A = stripTargetHull (ℍ ∖ K_r)` and a simple proper physical trace. -/
theorem tendsto_im_physicalRestartLog_sub_logDerivFwd (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsLoewnerTrace W η) (hηp : IsProperArc η) (hr : 0 < r) :
    Tendsto (fun z => (physicalRestartLog (stripTargetHull (H \ fwdHull W r)) (fwdMapInv W r z) -
      logDerivFwd W r (fwdMapInv W r z)).im) (𝓝[H] 0) (𝓝 0) := by
  set O := H \ fwdHull W r with hOdef
  set A := stripTargetHull O with hAdef
  set F := fwdMapInv W r with hFdef
  set R := stripRightRetarget with hRdef
  have hOo : IsOpen O := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr.le
  have hOs : IsSimplyConnected O := (isHPHull_fwdHull hW hr.le).2.2.2
  have hOH : O ⊆ H := fun z hz => hz.1
  have hcol : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ O := by
    obtain ⟨ρ, hρ, hd⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hη hηp hr.le (r := 1) one_ne_zero
    rw [ofReal_one] at hd
    exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun hK => Set.disjoint_left.1 hd hz.1 hK⟩⟩
  have hA : IsHPHull A := Aux61Restart.isHPHull_stripTargetHull hOo hOs hOH hcol
  have hRO : H \ A = R '' O := Aux61Restart.H_diff_stripTargetHull hOH
  have hmaps : MapsTo R O (H \ A) := fun z hz => by rw [hRO]; exact mem_image_of_mem _ hz
  have hL := Aux61Restart.isDerivLog_physicalRestartLog hOo hA hOH hmaps
  have hg := ConformalImage.isMapOut_mapOut hA
  have hRconf := Aux61Restart.isConformalBijection_stripRightRetarget
  have hFO : ∀ z ∈ H, F z ∈ O := fun z hz => QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hr.le hz
  set N : ℂ → ℂ := fun z => ConformalImage.mapOut A (R (F z)) with hNdef
  set Λ : ℂ → ℂ := fun z => physicalRestartLog A (F z) - logDerivFwd W r (F z) with hΛdef
  -- `N` is a conformal self-map of `ℍ`, `Λ` a continuous logarithm of `N′`
  have hFd : ∀ z ∈ H, HasDerivAt F (deriv (fwdMap W r) (F z))⁻¹ z := fun z hz => by
    have hFz := hFO z hz
    have e3 := (isDerivLog_fwdMap hW hr.le).2 (F z) hFz
    have hf : HasDerivAt (fwdMap W r) (deriv (fwdMap W r) (F z)) (F z) :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr.le _ hFz).differentiableAt (hOo.mem_nhds hFz)).hasDerivAt
    refine HasDerivAt.of_local_left_inverse ?_ hf (by rw [← e3]; exact exp_ne_zero _) ?_
    · exact ((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hr.le).differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hz)).continuousAt
    · filter_upwards [QuantumZipper.isOpen_H.mem_nhds hz] with y hy
      exact QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr.le hy
  have hGd : ∀ z ∈ H, HasDerivAt (ConformalImage.mapOut A ∘ R) (deriv (ConformalImage.mapOut A ∘ R) (F z)) (F z) :=
    fun z hz => by
      have hFz := hFO z hz
      have h1 : DifferentiableAt ℂ R (F z) := hRconf.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds (hOH hFz))
      have h2 : DifferentiableAt ℂ (ConformalImage.mapOut A) (R (F z)) :=
        hg.1.1.differentiableAt (hA.isOpen.mem_nhds (hmaps hFz))
      exact (h2.comp (F z) h1).hasDerivAt
  have hNder : ∀ z ∈ H, HasDerivAt N (deriv (ConformalImage.mapOut A ∘ R) (F z) * (deriv (fwdMap W r) (F z))⁻¹) z :=
    fun z hz => (hGd z hz).comp z (hFd z hz)
  have hNd : DifferentiableOn ℂ N H := fun z hz => (hNder z hz).differentiableAt.differentiableWithinAt
  have hNmaps : MapsTo N H H := fun z hz => hg.1.2.mapsTo (hmaps (hFO z hz))
  have hNinj : InjOn N H := by
    intro z₁ hz₁ z₂ hz₂ he
    have h1 := hg.1.2.injOn (hmaps (hFO z₁ hz₁)) (hmaps (hFO z₂ hz₂)) he
    have h2 := hRconf.2.injOn (hOH (hFO z₁ hz₁)) (hOH (hFO z₂ hz₂)) h1
    rw [← QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr.le hz₁, ← QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr.le hz₂]
    exact congrArg _ h2
  have hΛc : ContinuousOn Λ H := by
    intro z hz
    have hFz := hFO z hz
    have hFc : ContinuousAt F z := (hFd z hz).continuousAt
    have h1 : ContinuousAt (physicalRestartLog A) (F z) := (hL.1.differentiableAt (hOo.mem_nhds hFz)).continuousAt
    have h2 := continuousAt_logDerivFwd hW hr.le hFz
    exact ((h1.comp hFc).sub (h2.comp hFc)).continuousWithinAt
  have hΛe : ∀ z ∈ H, exp (Λ z) = deriv N z := fun z hz => by
    have hFz := hFO z hz
    rw [(hNder z hz).deriv, hΛdef, exp_sub, hL.2 _ hFz, (isDerivLog_fwdMap hW hr.le).2 _ hFz, div_eq_mul_inv]
  have hB := hη.hasBdryLimits hW hW0 hr.le
  -- **regularity** of `N` at every real point whose boundary image is not the target `1`
  have hreg : ∀ ξ : ℝ, extendFrom H F ξ ≠ 1 → ∃ ε > 0, ∃ G, IsPosReflect N G ξ ε := by
    intro ξ hξ
    have hξH : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    obtain ⟨ε, hε, hεsub⟩ := Metric.continuousWithinAt_iff.1 (hB.continuousOn ξ hξH) _ (dist_pos.2 hξ)
    refine ⟨ε, hε, exists_isPosReflect hε (hNd.mono inter_subset_left) (hNmaps.mono_left inter_subset_left)
      (hNinj.mono inter_subset_left) fun x hx => ?_⟩
    have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    set q := extendFrom H F x with hqdef
    have hq1 : q ≠ 1 := by
      intro h
      have := hεsub hxH hx
      rw [← hqdef, h, dist_comm] at this
      exact lt_irrefl _ this
    have hqO : q ∉ O := extendFrom_notMem_compl_fwdHull hW hW0 hη hr.le x
    have hFq : Tendsto F (𝓝[H] (x : ℂ)) (𝓝 q) := hB.tendsto hxH
    have hqcl : q ∈ Hbar := by
      have hNB := GlueImg.nhdsWithin_H_neBot x
      have := mem_closure_of_tendsto hFq (eventually_nhdsWithin_of_forall fun y hy => (hFO y hy).1)
      rwa [closure_H] at this
    have hRq : R q ∉ H \ A := by
      rw [hRO]
      rintro ⟨o, ho, he⟩
      by_cases hqH : q ∈ H
      · exact hqO (hRconf.2.injOn hqH (hOH ho) he.symm ▸ ho)
      · have hq0 : q.im = 0 := le_antisymm (not_lt.1 hqH) hqcl
        have hRq0 : (R q).im = 0 := by
          rw [hRdef, Aux61Restart.stripRightRetarget_eq, div_im, sub_im, one_im, hq0]
          simp
        have : (R o).im > 0 := hRconf.2.mapsTo (hOH ho)
        rw [he, hRq0] at this
        exact lt_irrefl _ this
    have hRF : Tendsto (fun y => R (F y)) (𝓝[H] (x : ℂ)) (𝓝[H \ A] (R q)) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuousAt_stripRightRetarget hq1).tendsto.comp hFq,
        eventually_nhdsWithin_of_forall fun y hy => hmaps (hFO y hy)⟩
    exact (IsMapOut.tendsto_im_nhdsWithin hA hg hRq).comp hRF
  -- the integer at a regular point
  have hint : ∀ ξ : ℝ, extendFrom H F ξ ≠ 1 →
      ∃ k : ℤ, Tendsto (fun z => (Λ z).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * π * k)) := fun ξ hξ => by
    obtain ⟨ε, -, G, hG⟩ := hreg ξ hξ
    exact hG.exists_int_tendsto_im (hΛc.mono inter_subset_left) fun z hz => hΛe z hz.1
  -- the right base point `p₁`
  set a := chartAR W r with hadef
  have ha0 := GlueImg.extendFrom_chartAR_eq_zero hη hηp hW hW0 hr
  obtain ⟨η₀, hη₀, hη₀sub⟩ := Metric.continuousWithinAt_iff.1
    (hB.continuousOn (a : ℂ) (mem_Hbar_of_im_eq_zero (by simp))) (1 / 2) (by norm_num)
  have hsmall : ∀ x : ℝ, |x - a| < η₀ → ‖extendFrom H F x‖ < 1 / 2 := fun x hx => by
    have := @hη₀sub (x : ℂ) (mem_Hbar_of_im_eq_zero (by simp)) (by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx)
    rwa [ha0, dist_zero_right] at this
  set p₁ := a + η₀ / 2 with hp₁def
  have ha_nn : 0 ≤ a := WangWu.chartAR_nonneg hW hr.le
  obtain ⟨hx₁im, hx₁pos⟩ := GlueImg.re_extendFrom_pos_of_chartAR_lt hη hηp hW hW0 hr
    (show chartAR W r < p₁ by rw [hp₁def]; linarith)
  set x₁ := (extendFrom H F p₁).re with hx₁def
  have hx₁e : (x₁ : ℂ) = extendFrom H F p₁ := ofReal_re_eq hx₁im
  have hx₁half : x₁ < 1 / 2 := by
    have h1 := hsmall p₁ (by rw [abs_lt]; constructor <;> linarith)
    have h2 : |x₁| ≤ ‖extendFrom H F p₁‖ := abs_re_le_norm _
    linarith [le_abs_self x₁]
  -- `Im Λ → 0` at `p₁`
  have hNB₁ := GlueImg.nhdsWithin_H_neBot p₁
  have hF₁ : Tendsto F (𝓝[H] (p₁ : ℂ)) (𝓝[H] (x₁ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by rw [hx₁e]; exact hB.tendsto (mem_Hbar_of_im_eq_zero (by simp)),
      eventually_nhdsWithin_of_forall fun y hy => (hFO y hy).1⟩
  have hx₁ne : x₁ ≠ 0 := hx₁pos.ne'
  have hx₁1 : (x₁ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set u : ℝ := x₁ / (1 - x₁) with hudef
  have hRu : R (x₁ : ℂ) = (u : ℂ) := by
    rw [hRdef, Aux61Restart.stripRightRetarget_eq, hudef, ofReal_div, ofReal_sub, ofReal_one]
  have hRF₁ : Tendsto (fun y => R (F y)) (𝓝[H] (p₁ : ℂ)) (𝓝[H] (u : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => hOH (hFO y hy) |>
      fun h => hRconf.2.mapsTo h⟩
    rw [← hRu]
    exact (continuousAt_stripRightRetarget hx₁1).tendsto.comp (hF₁.mono_right nhdsWithin_le_nhds)
  -- the ball about `R(x₁)` misses `A`
  obtain ⟨ρ₀, hρ₀, hd₀⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hη hηp hr.le hx₁ne
  have hUc : ContinuousAt Aux61Restart.stripRightUntarget (u : ℂ) := by
    have hden : (1 : ℂ) * (u : ℂ) + 1 ≠ 0 := by
      rw [one_mul, ← ofReal_one, ← ofReal_add]
      exact ofReal_ne_zero.2 (by
        have : 0 < u := div_pos hx₁pos (by linarith)
        linarith)
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) (by simpa using hden)
  have hUu : Aux61Restart.stripRightUntarget (u : ℂ) = (x₁ : ℂ) := by
    simp only [Aux61Restart.stripRightUntarget, QuantumZipper.CA.realMobius, ofReal_one, one_mul, ofReal_zero,
      add_zero, hudef]
    have h1 : (1 : ℂ) - x₁ ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.2 (by linarith)
    rw [ofReal_div, ofReal_sub, ofReal_one]
    field_simp
    ring
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.continuousAt_iff.1 hUc ρ₀ hρ₀
  have hdA : Disjoint (ball (u : ℂ) ρ) A := by
    rw [Set.disjoint_left]
    intro w hw hwA
    have hwH : w ∈ H := hA.1 hwA
    have hUw : Aux61Restart.stripRightUntarget w ∈ ball (x₁ : ℂ) ρ₀ := by
      have := hρsub hw; rwa [hUu] at this
    have hUwH : Aux61Restart.stripRightUntarget w ∈ H :=
      Aux61Restart.isConformalBijection_stripRightUntarget.2.mapsTo hwH
    have hUwO : Aux61Restart.stripRightUntarget w ∈ O := ⟨hUwH, fun hK => Set.disjoint_left.1 hd₀ hUw hK⟩
    have : w ∈ H \ A := by
      rw [hRO]; exact ⟨_, hUwO, Aux61Restart.stripRightRetarget_untarget hwH⟩
    exact this.2 hwA
  have hL1 : Tendsto (fun y => (Restart.canonDerivLog A (R (F y))).im) (𝓝[H] (p₁ : ℂ)) (𝓝 0) :=
    (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hA (Restart.isCanonicalDerivLog_canonDerivLog hA) hg hρ
      hdA).comp hRF₁
  have hL2 : Tendsto (fun y => (stripRightRetargetLog (F y)).im) (𝓝[H] (p₁ : ℂ)) (𝓝 0) := by
    have hslit : (1 : ℂ) - x₁ ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_mem_slitPlane.2 (by linarith)
    have hc : ContinuousAt stripRightRetargetLog (x₁ : ℂ) :=
      ((continuousAt_clog hslit).comp (continuousAt_const.sub continuousAt_id)).const_mul (-2 : ℂ)
    have h := (continuous_im.tendsto _).comp (hc.tendsto.comp (hF₁.mono_right nhdsWithin_le_nhds))
    have h0 : (stripRightRetargetLog (x₁ : ℂ)).im = 0 := by
      rw [stripRightRetargetLog, ← ofReal_one, ← ofReal_sub, ← ofReal_log (by linarith), ← ofReal_ofNat,
        ← ofReal_neg, ← ofReal_mul, ofReal_im]
    rw [h0] at h
    exact h
  obtain ⟨ρ', hρ', hd'⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hη hηp hr.le hx₁ne
  have hL3 : Tendsto (fun y => (logDerivFwd W r (F y)).im) (𝓝[H] (p₁ : ℂ)) (𝓝 0) :=
    (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW hr.le)
      (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW hW0 hr.le) (isMapOut_fwdMap hW hW0 hr.le) hρ' hd').comp hF₁
  have hΛ₁ : Tendsto (fun z => (Λ z).im) (𝓝[H] (p₁ : ℂ)) (𝓝 0) := by
    have := (hL1.add hL2).sub hL3
    simp only [add_zero, sub_zero] at this
    refine this.congr fun y => ?_
    simp only [hΛdef, Aux61Restart.physicalRestartLog, sub_im, add_im]
    rfl
  -- transport along `[0, p₁]`
  have hgood : ∀ ξ ∈ Icc (0 : ℝ) p₁, extendFrom H F ξ ≠ 1 := by
    intro ξ hξ h1
    rcases lt_trichotomy ξ a with hlt | heq | hgt
    · have hH : extendFrom H F ξ ∈ H := by
        rcases hξ.1.eq_or_lt with h0 | hpos
        · rw [← h0, ofReal_zero, hFdef, WangWu.extendFrom_zero hη hW hW0 hr.le]
          exact hηp.mem_H r hr
        · exact GlueImg.extendFrom_mem_H_of_chartAL_lt hη hηp hW hW0 hr
            ((WangWu.chartAL_nonpos hW hr.le).trans_lt hpos) hlt
      rw [h1] at hH
      exact absurd hH (by simp [QuantumZipper.H])
    · rw [heq, ha0] at h1; exact zero_ne_one h1
    · have h2 := hsmall ξ (by rw [abs_lt]; constructor <;> linarith [hξ.2])
      rw [h1, norm_one] at h2
      norm_num at h2
  have h := GlueImg.tendsto_zero_of_forall_tendsto_two_pi_int (I := Icc (0 : ℝ) p₁) isPreconnected_Icc
    (fun ξ hξ => hint ξ (hgood ξ hξ)) (x₀ := p₁) ⟨by linarith, le_rfl⟩ hΛ₁ (x := 0) ⟨le_rfl, by linarith⟩
  rw [ofReal_zero] at h
  exact h

/-- **R1's retained lift is seed-normalized.** For the retained component `D ⊆ ℍ ∖ K_r` with bounded retargeted
hull `B = stripTargetHull D` and a collar `F_r(ℍ ∩ B(0, δ)) ⊆ D` of the old tip, the inherited physical logarithm of
the restart chart minus the physical flow's own logarithm has imaginary part tending to `0` at the old tip:
`Im (physicalRestartLog B − L_r) ∘ F_r → 0` at `0` (R1's chain rule, the additional logarithm's zero phase on the
current collar, and `tendsto_im_physicalRestartLog_sub_logDerivFwd`). -/
theorem tendsto_im_physicalRestartLog_retained_sub_logDerivFwd (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsLoewnerTrace W η) (hηp : IsProperArc η) (hr : 0 < r) {D : Set ℂ} (hDO : D ⊆ H \ fwdHull W r)
    (hB : IsHPHull (stripTargetHull D)) (hcollar : ∃ δ > 0, MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) D) :
    Tendsto (fun z => (physicalRestartLog (stripTargetHull D) (fwdMapInv W r z) -
      logDerivFwd W r (fwdMapInv W r z)).im) (𝓝[H] 0) (𝓝 0) := by
  set O := H \ fwdHull W r with hOdef
  set A := stripTargetHull O with hAdef
  set B := stripTargetHull D with hBdef
  set F := fwdMapInv W r with hFdef
  set R := stripRightRetarget with hRdef
  have hOo : IsOpen O := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr.le
  have hOs : IsSimplyConnected O := (isHPHull_fwdHull hW hr.le).2.2.2
  have hOH : O ⊆ H := fun z hz => hz.1
  have hcol : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ O := by
    obtain ⟨ρ, hρ, hd⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hη hηp hr.le (r := 1) one_ne_zero
    rw [ofReal_one] at hd
    exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun hK => Set.disjoint_left.1 hd hz.1 hK⟩⟩
  have hA : IsHPHull A := Aux61Restart.isHPHull_stripTargetHull hOo hOs hOH hcol
  have hDH : D ⊆ H := fun z hz => (hDO hz).1
  have hRconf := Aux61Restart.isConformalBijection_stripRightRetarget
  have hAB : A ⊆ B := by
    intro z hz
    refine ⟨hz.1, fun hzD => hz.2 ?_⟩
    obtain ⟨d, hd, rfl⟩ := hzD
    exact ⟨d, hDO hd, rfl⟩
  have hRO : H \ A = R '' O := Aux61Restart.H_diff_stripTargetHull hOH
  have hRD : H \ B = R '' D := Aux61Restart.H_diff_stripTargetHull hDH
  obtain ⟨δ, hδ, hcD⟩ := hcollar
  -- the additional logarithm has zero phase on the current collar
  have hFbij := isConformalBijection_fwdMapInv hW hW0 hr.le
  have hRbij : IsConformalBijection R O (H \ A) := by
    refine ⟨hRconf.1.mono hOH, ?_⟩
    rw [hRO]
    exact (hRconf.2.injOn.mono hOH).bijOn_image
  have hRF : IsConformalBijection (R ∘ F) H (H \ A) := isConformalBijection_comp hRbij hFbij
  have hηr : η r ∈ H := hηp.mem_H r hr
  have hηr1 : η r ≠ 1 := fun h => by rw [h] at hηr; exact absurd hηr (by simp [QuantumZipper.H])
  have hF₀ : Tendsto (R ∘ F) (𝓝[H] 0) (𝓝 (R (η r))) :=
    (continuousAt_stripRightRetarget hηr1).tendsto.comp (hη.tendsto_fwdMapInv_tip hW hW0 hr.le)
  have hcur : ∃ δ > 0, MapsTo (R ∘ F) (ball 0 δ ∩ H) (H \ B) :=
    ⟨δ, hδ, fun z hz => by rw [hRD]; exact mem_image_of_mem _ (hcD hz)⟩
  obtain ⟨-, -, -, -, -, hadd⟩ := Aux61Restart.exists_restartAdditionalLog_phase_zero hA hB hAB hRF hF₀ hcur
  have hown := tendsto_im_physicalRestartLog_sub_logDerivFwd hW hW0 hη hηp hr
  have hsum := hadd.add hown
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (0 : ℂ) hδ)] with z hz
  have hzB : R (F z) ∈ H \ B := by rw [hRD]; exact mem_image_of_mem _ (hcD ⟨hz.2, hz.1⟩)
  simp only [Function.comp_apply]
  rw [Aux61Restart.physicalRestartLog_chain hA hB hAB hzB]
  simp only [sub_im, add_im]
  ring

end InteractingSLE.Sec5.Aux61TwoS
