/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfTip
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase

/-!
# Lemma 4.7's direction, item (B): the inverse transition map at physical real points, for non-simple curves

Packet PROVE-CFRESTART2. GLUECOND8's (R2c) lemmas `GlueImg.imgTheta_tendsto_of_extendFrom_neg`, `…_pos` (at a
physical real point of the image chart, `Θ` tends to a real point of the same sign and the branch of `arg Θ′` tends
to `0`) assume a simple new curve and a simple image trace. Their proofs use simplicity only through the forward
solution of a nonzero real point and a ball around a nonzero real point missing the image hull; for traces staying in
`ℍ` at positive times these are `exists_isForwardSol_of_mem_H` (PROVE-CFRESTART) and
`ofReal_notMem_closure_fwdHull_of_mem_H` (PROVE-CFRESTART-C). The ports below (proofs copied with these two
replacements) apply to the non-simple counterflow and its non-simple image:

* `imgTheta_tendsto_of_extendFrom_neg_of_mem_H`, `imgTheta_tendsto_of_extendFrom_pos_of_mem_H`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg MartChar.RealFlow Restart.RetAux79
open CrossCond.Word49 (junL junR)

variable {Wα Wβ W' : ℝ → ℝ} {t s T : ℝ}

/-- **(R2c) A physical real point left of the left base point** (`F̄′_T(x) = r` with `junL < r < 0`): `Ψ⁻¹` sends `r`
to a negative physical real point `z₀` (`R(r)` lies right of the counterflow's right base image), so `Θ` tends to the
negative real point `f̄_t(z₀)`, and the branch tends to `0` (Aux. 57 for `f_t` at `z₀`, for `f′_T` at `r`, and the
normalized `arg_Ψ` at `z₀`). -/
theorem imgTheta_tendsto_of_extendFrom_neg_of_mem_H {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α)
    (hαH : ∀ r ∈ Ioc (0 : ℝ) t, α r ∈ H)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0) (hjL : 0 < rightImg Wβ 0 s - Wβ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'H : ∀ r ∈ Ioc (0 : ℝ) T, η' r ∈ H) {x r : ℝ} (hx : extendFrom H (fwdMapInv W' T) x = r) (hr0 : r < 0)
    (hrj : junL Wβ s < r) :
    (∃ p : ℝ, p < 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set g₀ := rightImg Wβ 0 s - Wβ s with hg₀
  set ρ : ℝ := -r⁻¹ with hρdef
  have hρ : rightImg Wβ 0 s < ρ + Wβ s := by
    have h1 : -1 < r * g₀ := by
      have := hrj
      rw [junL, ← hg₀, div_lt_iff₀ hjL] at this
      exact this
    have h2 : g₀ < ρ := by
      rw [hρdef, show -r⁻¹ = 1 / (-r) by rw [one_div, inv_neg], lt_div_iff₀ (neg_pos.2 hr0)]
      linarith
    linarith
  obtain ⟨y, hy0, hya, hyg⟩ := exists_alive_gImg_eq hWβ hs hρ
  have hu := isForwardSol_of_alive hWβ hya
  have hcf : cflow Wβ y s = ρ := by rw [gImg] at hyg; linarith
  have hFs : extendFrom H (fwdMapInv Wβ s) (ρ : ℂ) = y := by
    have := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hWβ hWβ0 hs (show (0 : ℝ) ≤ (y : ℂ).im by simp) hu
    simpa only [hcf] using this
  have h1 := tendsto_fwdMapInv_nhdsWithin_of_real hη' hW' hW'0 hT hx
  have h2 := (tendsto_negInv_nhdsWithin_H hr0.ne).comp h1
  have h3 : Tendsto (fun y' => fwdMapInv Wβ s (negInv (fwdMapInv W' T y'))) (𝓝[H] (x : ℂ)) (𝓝[H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y' hy' =>
      QuantumZipper.RS.fwdMapInv_mem_H hWβ hWβ0 hs
        (negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy'))⟩
    have := (hB.tendsto (show (0 : ℝ) ≤ ((ρ : ℝ) : ℂ).im by simp)).comp h2
    rw [hFs] at this
    exact this
  have hΦ : Tendsto (fun y' => revChartInv Wβ s (fwdMapInv W' T y')) (𝓝[H] (x : ℂ))
      (𝓝[H] ((-y⁻¹ : ℝ) : ℂ)) := (tendsto_negInv_nhdsWithin_H hy0.ne').comp h3
  set z₀ : ℝ := -y⁻¹ with hz₀def
  have hz₀ : z₀ < 0 := neg_neg_of_pos (inv_pos.2 hy0)
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hα hαH hWα hWα0 hz₀.ne ht.le
  rcases isForwardSol_real_cases hWα hWα0 ht.le hv with ⟨hpos, -, -⟩ | ⟨-, hal, hvt⟩
  · exact absurd hpos (not_lt.2 hz₀.le)
  refine ⟨⟨-gImg (fun r => -Wα r) (-z₀) t - Wα t, ?_, ?_⟩, ?_⟩
  · have := hal.lt_gImg (show Continuous fun r => -Wα r from hWα.neg) ⟨ht.le, le_rfl⟩
    linarith
  · have := (tendsto_fwdMap_of_isForwardSol hWα ht.le hv).comp hΦ
    rw [hvt] at this
    exact this
  -- the branch
  obtain ⟨ρ₁, hρ₁, hd₁⟩ := exists_ball_disjoint_of_notMem_closure (hKt z₀ hz₀.ne)
  have a1 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hWα ht.le)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hWα hWα0 ht.le) (isMapOut_fwdMap hWα hWα0 ht.le) hρ₁ hd₁).comp hΦ
  obtain ⟨ρ₂, hρ₂, hd₂⟩ := exists_ball_disjoint_of_notMem_closure
    (ofReal_notMem_closure_fwdHull_of_mem_H hη' hη'H hW' hT r hr0.ne)
  have a2 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW' hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW' hW'0 hT) (isMapOut_fwdMap hW' hW'0 hT) hρ₂ hd₂).comp h1
  have hy' : ((-z₀⁻¹ : ℝ) : ℂ) ∉ closure (fwdHull Wβ s) := by
    intro hm
    have := hKs _ hm (by simp)
    rw [hz₀def, inv_neg, neg_neg, inv_inv] at this
    exact hy0.ne' (by exact_mod_cast this)
  obtain ⟨ρ₃, hρ₃, hd₃⟩ := exists_ball_disjoint_of_notMem_closure hy'
  have a3 := (tendsto_im_logDerivPsi hWβ hWβ0 hs hz₀.ne hρ₃ hd₃).comp hΦ
  have h := a1.sub (a2.add a3)
  rw [add_zero, sub_zero] at h
  exact h

/-- **(R2c), right mirror**: a physical real point right of the right base point (`0 < r < junR`): `Θ` tends to a
positive real point and the branch tends to `0`. -/
theorem imgTheta_tendsto_of_extendFrom_pos_of_mem_H {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α)
    (hαH : ∀ r ∈ Ioc (0 : ℝ) t, α r ∈ H)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv Wβ s))
    (hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0)
    (hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η')
    (hη'H : ∀ r ∈ Ioc (0 : ℝ) T, η' r ∈ H) {x r : ℝ} (hx : extendFrom H (fwdMapInv W' T) x = r) (hr0 : 0 < r)
    (hrj : r < junR Wβ s) :
    (∃ p : ℝ, 0 < p ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p : ℂ))) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set h₀ := -rightImg (fun r => -Wβ r) 0 s - Wβ s with hh₀
  set ρ : ℝ := -r⁻¹ with hρdef
  have hρ : rightImg (fun r => -Wβ r) 0 s < -ρ + -Wβ s := by
    have h1 : r * (-h₀) < 1 := by
      have := hrj
      rw [junR, ← hh₀, lt_div_iff_of_neg hjR] at this
      linarith
    have h2 : ρ < h₀ := by
      have hr' : 0 < r⁻¹ := inv_pos.2 hr0
      have e : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
      rw [hρdef]
      nlinarith
    linarith
  obtain ⟨y, hy0, hya, hyg⟩ := exists_alive_gImg_eq (show Continuous fun r => -Wβ r from hWβ.neg) hs hρ
  have hu := isForwardSol_neg_of_alive hWβ hya
  have hcf : cflow (fun r => -Wβ r) y s = -ρ := by rw [gImg] at hyg; linarith
  have hFs : extendFrom H (fwdMapInv Wβ s) (ρ : ℂ) = -(y : ℂ) := by
    have := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hWβ hWβ0 hs (show (0 : ℝ) ≤ (-(y : ℂ)).im by simp) hu
    simp only [hcf, Complex.ofReal_neg, neg_neg] at this
    exact this
  have h1 := tendsto_fwdMapInv_nhdsWithin_of_real hη' hW' hW'0 hT hx
  have h2 := (tendsto_negInv_nhdsWithin_H hr0.ne').comp h1
  have h3 : Tendsto (fun y' => fwdMapInv Wβ s (negInv (fwdMapInv W' T y'))) (𝓝[H] (x : ℂ))
      (𝓝[H] ((-y : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y' hy' =>
      QuantumZipper.RS.fwdMapInv_mem_H hWβ hWβ0 hs
        (negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy'))⟩
    have := (hB.tendsto (show (0 : ℝ) ≤ ((ρ : ℝ) : ℂ).im by simp)).comp h2
    rw [hFs] at this
    rw [Complex.ofReal_neg]
    exact this
  have hΦ : Tendsto (fun y' => revChartInv Wβ s (fwdMapInv W' T y')) (𝓝[H] (x : ℂ))
      (𝓝[H] ((-(-y)⁻¹ : ℝ) : ℂ)) := (tendsto_negInv_nhdsWithin_H (neg_ne_zero.2 hy0.ne')).comp h3
  set z₀ : ℝ := -(-y)⁻¹ with hz₀def
  have hz₀ : 0 < z₀ := by rw [hz₀def, inv_neg, neg_neg]; exact inv_pos.2 hy0
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hα hαH hWα hWα0 hz₀.ne' ht.le
  rcases isForwardSol_real_cases hWα hWα0 ht.le hv with ⟨-, hal, hvt⟩ | ⟨hneg, -, -⟩
  swap
  · exact absurd hneg (not_lt.2 hz₀.le)
  refine ⟨⟨gImg Wα z₀ t - Wα t, ?_, ?_⟩, ?_⟩
  · have := hal.lt_gImg hWα ⟨ht.le, le_rfl⟩
    linarith
  · have := (tendsto_fwdMap_of_isForwardSol hWα ht.le hv).comp hΦ
    rw [hvt] at this
    exact this
  obtain ⟨ρ₁, hρ₁, hd₁⟩ := exists_ball_disjoint_of_notMem_closure (hKt z₀ hz₀.ne')
  have a1 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hWα ht.le)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hWα hWα0 ht.le) (isMapOut_fwdMap hWα hWα0 ht.le) hρ₁ hd₁).comp hΦ
  obtain ⟨ρ₂, hρ₂, hd₂⟩ := exists_ball_disjoint_of_notMem_closure
    (ofReal_notMem_closure_fwdHull_of_mem_H hη' hη'H hW' hT r hr0.ne')
  have a2 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hW' hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW' hW'0 hT) (isMapOut_fwdMap hW' hW'0 hT) hρ₂ hd₂).comp h1
  have hy' : ((-z₀⁻¹ : ℝ) : ℂ) ∉ closure (fwdHull Wβ s) := by
    intro hm
    have := hKs _ hm (by simp)
    rw [hz₀def, inv_neg, neg_neg, inv_inv] at this
    exact hy0.ne' (neg_eq_zero.1 (by exact_mod_cast this))
  obtain ⟨ρ₃, hρ₃, hd₃⟩ := exists_ball_disjoint_of_notMem_closure hy'
  have a3 := (tendsto_im_logDerivPsi hWβ hWβ0 hs hz₀.ne' hρ₃ hd₃).comp hΦ
  have h := a1.sub (a2.add a3)
  rw [add_zero, sub_zero] at h
  exact h

/-! ### Points of the image chart over the new curve's hull -/

/-- **The per-point inputs at a point of the image chart over the new curve's hull** (non-simple; GLUECOND8's (R2b)
with the base point `0` replaced by any limit point `p ∉ ℍ ∖ K_t` of `Φ = Ψ⁻¹ ∘ F′_T`). If `Φ → p` along `𝓝[ℍ] x`
and `Θ` has no cluster value `0` at `x`, then `Θ` has a nonzero real limit at `x` and the branch tends to a multiple
of `2π`. (Every cluster value `p₁` of the bounded `Θ` has `F̄_t(p₁) = p`, so `p₁ ∉ ℍ`.) -/
theorem imgTheta_limits_of_tendsto_Phi {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 ≤ t) (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t))
    (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T)
    (hGc : IsClosed (negInv '' fwdHull Wβ s)) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t)))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x : ℝ} {p : ℂ}
    (hΦ : Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 p))
    (hp : p ∉ H \ fwdHull Wα t)
    (hnz : ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ 𝓝[H] (x : ℂ) →
      ¬ Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 0)) :
    (∃ p₀ : ℝ, p₀ ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)) := by
  have := nhdsWithin_H_neBot x
  set U := Ultrafilter.of (𝓝[H] (x : ℂ)) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[H] (x : ℂ) := Ultrafilter.of_le _
  obtain ⟨C, -, hC⟩ := exists_norm_fwdMap_sub_le hWα hWα0 ht
  have hmem : ∀ᶠ y in 𝓝[H] (x : ℂ), revChartInv Wβ s (fwdMapInv W' T y) ∈
      H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) :=
    eventually_nhdsWithin_of_forall fun y hy => revChartInv_fwdMapInv_mem hWβ hWβ0 hs hW' hW'0 hT hK' hy
  have hsmall : ∀ᶠ y in 𝓝[H] (x : ℂ), revChartInv Wβ s (fwdMapInv W' T y) ∈ ball p 1 :=
    hΦ (ball_mem_nhds _ one_pos)
  have hbd : ∀ᶠ y in 𝓝[H] (x : ℂ), imgTheta Wα t Wβ s W' T y ∈ closedBall (0 : ℂ) (C + (‖p‖ + 1)) := by
    filter_upwards [hmem, hsmall] with y hy1 hy2
    have h1 := hC _ ⟨hy1.1, fun h => hy1.2 (Or.inl h)⟩
    have hy2' : ‖revChartInv Wβ s (fwdMapInv W' T y)‖ ≤ ‖p‖ + 1 := by
      rw [mem_ball, dist_eq_norm] at hy2
      have := norm_le_insert' (revChartInv Wβ s (fwdMapInv W' T y)) p
      linarith
    rw [mem_closedBall_zero_iff]
    calc ‖imgTheta Wα t Wβ s W' T y‖ = ‖(fwdMap Wα t (revChartInv Wβ s (fwdMapInv W' T y)) -
          revChartInv Wβ s (fwdMapInv W' T y)) + revChartInv Wβ s (fwdMapInv W' T y)‖ := by
          rw [sub_add_cancel]; rfl
      _ ≤ C + (‖p‖ + 1) := (norm_add_le _ _).trans (add_le_add h1 hy2')
  obtain ⟨p₁, -, hp₁⟩ := (isCompact_closedBall (0 : ℂ) (C + (‖p‖ + 1))).ultrafilter_le_nhds
    (U.map (imgTheta Wα t Wβ s W' T)) (by rw [Ultrafilter.coe_map]; exact tendsto_principal.2 (hU hbd))
  have hΘU : Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 p₁) := by rwa [Ultrafilter.coe_map] at hp₁
  have hΘH : ∀ᶠ y in (U : Filter ℂ), imgTheta Wα t Wβ s W' T y ∈ H := hU (hmem.mono fun y hy =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht ⟨hy.1, fun h => hy.2 (Or.inl h)⟩)
  have hpH : p₁ ∈ Hbar := closure_H ▸ mem_closure_of_tendsto hΘU hΘH
  have hB := hα.hasBdryLimits hWα hWα0 ht
  have h1 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) U
      (𝓝 (extendFrom H (fwdMapInv Wα t) p₁)) :=
    (hB.tendsto hpH).comp (tendsto_nhdsWithin_iff.2 ⟨hΘU, hΘH⟩)
  have h2 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) U (𝓝 p) := by
    refine (hΦ.mono_left hU).congr' (hU (hmem.mono fun y hy => ?_))
    exact show _ = fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y) from
      (QuantumZipper.RS.fwdMapInv_fwdMap hWα hWα0 ht ⟨hy.1, fun h => hy.2 (Or.inl h)⟩).symm
  have hp0 : extendFrom H (fwdMapInv Wα t) p₁ = p := tendsto_nhds_unique h1 h2
  have hpR : p₁.im = 0 := by
    rcases (show (0 : ℝ) ≤ p₁.im from hpH).lt_or_eq with hpos | h0
    · exfalso
      have e := extendFrom_fwdMapInv_eq hWα hWα0 ht (show p₁ ∈ H from hpos)
      have hm := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWα hWα0 ht (show p₁ ∈ H from hpos)
      rw [← e, hp0] at hm
      exact hp hm
    · exact h0.symm
  have hpne : p₁.re ≠ 0 := by
    intro h
    have hp' : p₁ = 0 := Complex.ext (by simpa using h) (by simpa using hpR)
    rw [hp'] at hΘU
    exact hnz U hU hΘU
  have hpe : p₁ = (p₁.re : ℂ) := Complex.ext (by simp) (by simp [hpR])
  rw [hpe] at hΘU
  exact imgTheta_limits_of_ultrafilter hα hWα hWα0 ht hKt hWβ hWβ0 hs hW' hW'0 hT hGc hdisj hdis hK' hpne hU hΘU

/-- **`Φ` has a limit off `ℍ ∖ K_t` over the image hull.** If the inverse boundary value `F̄′_T(x)` is `0` or lies in
`ℍ`, then `Φ = Ψ⁻¹ ∘ F′_T` tends along `𝓝[ℍ] x` to a point `p ∉ ℍ ∖ K_t`: `p = 0`, resp. the point of `K_t` over
`F̄′_T(x)`, which lies in the image hull `K′_T = Ψ(K_t)` (otherwise `f′_T` would be continuous there and `x` would
lie in `ℍ`). -/
theorem exists_tendsto_Phi_of_extendFrom {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {x : ℝ}
    (hx : extendFrom H (fwdMapInv W' T) x = 0 ∨ extendFrom H (fwdMapInv W' T) x ∈ H) :
    ∃ p : ℂ, Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      p ∉ H \ fwdHull Wα t ∧ (extendFrom H (fwdMapInv W' T) x ∈ H → p ∈ fwdHull Wα t) := by
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hF : Tendsto (fwdMapInv W' T) (𝓝[H] (x : ℂ)) (𝓝 (extendFrom H (fwdMapInv W' T) x)) :=
    (hη'.hasBdryLimits hW' hW'0 hT).tendsto hxbar
  have hFH : ∀ᶠ y in 𝓝[H] (x : ℂ), fwdMapInv W' T y ∈ H :=
    eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy
  rcases hx with h0 | hH
  · refine ⟨0, ?_, fun h => by have h1 : (0 : ℝ) < (0 : ℂ).im := h.1; simp at h1, fun h => ?_⟩
    swap
    · rw [h0] at h
      have h1 : (0 : ℝ) < (0 : ℂ).im := h
      simp at h1
    rw [h0] at hF
    exact (GlueImg.tendsto_revChartInv_nhdsWithin_zero hWβ hWβ0 hs).comp (tendsto_nhdsWithin_iff.2 ⟨hF, hFH⟩)
  · set w₀ := extendFrom H (fwdMapInv W' T) x with hw₀
    have hw₀K : w₀ ∈ fwdHull W' T := by
      by_contra hn
      have hcont : ContinuousAt (fwdMap W' T) w₀ :=
        (QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW' hT ⟨hH, hn⟩).continuousAt
      have h1 : Tendsto (fun y => fwdMap W' T (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 (fwdMap W' T w₀)) :=
        hcont.tendsto.comp hF
      have h2 : Tendsto (fun y => fwdMap W' T (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
        refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy).symm
      have := nhdsWithin_H_neBot x
      have he := tendsto_nhds_unique h1 h2
      have hm := QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT ⟨hH, hn⟩
      rw [he] at hm
      exact lt_irrefl _ (show (0 : ℝ) < ((x : ℝ) : ℂ).im from hm |>.trans_eq (by simp))
    rw [hK'] at hw₀K
    obtain ⟨k, hk, hkw⟩ := hw₀K
    have hkG : k ∈ H \ negInv '' fwdHull Wβ s :=
      ⟨(QuantumZipper.fwdHull_mono (W := Wα)).2 t hk, fun h => Set.disjoint_left.1 hdisj hk h⟩
    refine ⟨k, ?_, fun h => h.2 hk, fun _ => hk⟩
    have hc : ContinuousAt (revChartInv Wβ s) w₀ :=
      (continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hH)
    have := hc.tendsto.comp hF
    rw [← hkw, revChartInv_revChart hWβ hWβ0 hs hkG] at this
    exact this

end InteractingSLE.Sec5.CrossRestart
