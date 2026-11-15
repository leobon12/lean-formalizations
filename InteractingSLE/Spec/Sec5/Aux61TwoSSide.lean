/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61TwoSSeed

/-!
# Aux. 61, the two new sides: the slit-side limits in the restart chart

Packet PROVE-AUX61-TWOSIDES, item (D1), the configuration form (Astra's follow-up 4 §1.1, L113–L123: "At every
further pre-contact stop the two new sides have the canonical flow-line germs … The chain rule, with the branch
fixed at the initial seed, gives the same phase on the connected new slit. No branch may be reset modulo 2π.").

In the configuration `IsTwoSideConfig`, let `x′` be a real point of the restart chart at time `t` whose inverse
Loewner image is a point `Ψ(β′(s′))`, `0 < s′ < σ`, of the new slit before the comparison time `σ`. Then:

* **`exists_cluster`** : the inverse transition `Θ = f_σ ∘ Ψ⁻¹ ∘ F_t` tends (inside `ℍ`) to a real point `p ≠ 0` of the
  flow chart with `F̄_σ(p) = β(s′)`, and `Ξ = Θ⁻¹` tends to `x′` at `p`;
* **`tendsto_theta_of_neg`**, **`tendsto_theta_of_pos`** : **orientation** (`p` is on the same side of the flow tip
  as `x′` is of the chart tip: the sign of the reflected `Ξ` is transported from the seed along an interval of good
  points) and **the branch** (`Im thetaLog → 0` at `x′`: the integer of `Im xiLog` is transported from the collar,
  where it is `0`, along the same kind of interval; `thetaLog = −xiLog ∘ Θ`);
* **`tendsto_slitMean_of_neg`**, **`tendsto_slitMean_of_pos`** : the slit-side limit of the combination
  `u_ph ∘ Θ + a − u_c − k · Im thetaLog`, given the boundary values of `u_ph` on the flow slit side and of `u_c`
  at `x′`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.Aux61TwoS

open WangWu (IsProperArc chartAL chartAR)

namespace IsTwoSideConfig

variable {W : ℝ → ℝ} {β β' : ℝ → ℂ} {σ τ : ℝ} {Ω : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {δ : ℝ} {w : ℝ → ℝ}
  {γ : ℝ → ℂ} {t : ℝ}

variable (hc : IsTwoSideConfig W β β' σ τ Ω Ψ Ψi LΨ δ w γ t)
include hc

/-- **The cluster point.** At a real point `x′` of the restart chart whose inverse Loewner image is the slit point
`Ψ(β′(s′))`, `0 < s′ < σ`, the inverse transition `Θ` tends inside `ℍ` to a real point `p ≠ 0` with `F̄_σ(p) = β(s′)`,
and `Ξ → x′` at `p`. -/
theorem exists_cluster {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) :
    ∃ p : ℝ, p ≠ 0 ∧ extendFrom H (fwdMapInv W σ) p = β s' ∧
      Tendsto (thetaMap W σ Ψi w t) (𝓝[H] (x' : ℂ)) (𝓝[H] (p : ℂ)) ∧
      Tendsto (xiMap w t Ψ W σ) (𝓝[H] (p : ℂ)) (𝓝 (x' : ℂ)) := by
  have hNB := GlueImg.nhdsWithin_H_neBot x'
  set U := Ultrafilter.of (𝓝[H] (x' : ℂ)) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[H] (x' : ℂ) := Ultrafilter.of_le _
  have hs'Ω : β' s' ∈ Ω := hc.cont_mapsTo ⟨hs', hs'σ.le.trans hc.σ_lt_τ.le⟩
  have hββ : β' s' = β s' := hc.cont_eqOn ⟨hs'.le, hs'σ.le⟩
  have hiC : ContinuousAt Ψi (Ψ (β' s')) :=
    hc.inv_contOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds (hc.mapsTo hs'Ω))
  set Φ : ℂ → ℂ := fun y => Ψi (fwdMapInv w t y) with hΦdef
  have hΦ : Tendsto Φ (𝓝[H] (x' : ℂ)) (𝓝[H \ fwdHull W σ] (β s')) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => hc.inv_fwdMapInv_mem hy⟩
    have := hiC.tendsto.comp hx'
    rwa [hc.inv_apply _ hs'Ω, hββ] at this
  obtain ⟨p, hp0, hFp, hlim, -⟩ := WangWu.exists_real_tendsto_fwdMap hc.trace hc.arc hc.hW hc.hW0 hs' hs'σ
    subset_rfl (U.map Φ) (by rw [Ultrafilter.coe_map]; exact (hΦ.mono_left hU))
  have hΘU : Tendsto (thetaMap W σ Ψi w t) U (𝓝[H] (p : ℂ)) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff] at hlim
    exact hlim
  have hgood : IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) p) := Or.inr ⟨s', ⟨hs', hs'σ⟩, hFp⟩
  obtain ⟨ε, hε, hreg, G, hG⟩ := hc.exists_isPosReflect_xi hgood
  have hpB : (p : ℂ) ∈ ball (p : ℂ) ε := mem_ball_self hε
  have hGp : G p = x' := by
    have hGc : ContinuousAt G p := (hG.diff.differentiableAt (isOpen_ball.mem_nhds hpB)).continuousAt
    have h1 : Tendsto (fun y => G (thetaMap W σ Ψi w t y)) U (𝓝 (G p)) :=
      hGc.tendsto.comp (hΘU.mono_right nhdsWithin_le_nhds)
    have hin : ∀ᶠ y in (U : Filter ℂ), thetaMap W σ Ψi w t y ∈ H ∩ ball (p : ℂ) ε :=
      hΘU (inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hpB))
    have h2 : Tendsto (fun y => G (thetaMap W σ Ψi w t y)) U (𝓝 (x' : ℂ)) := by
      have hid : Tendsto (fun y : ℂ => y) U (𝓝 (x' : ℂ)) := hU.trans nhdsWithin_le_nhds
      refine hid.congr' ?_
      filter_upwards [hin, hU self_mem_nhdsWithin] with y hy hyH
      rw [hG.eqOn hy, hc.xiMap_thetaMap hyH]
    exact tendsto_nhds_unique h1 h2
  have hΘ := hG.tendsto_leftInv fun z hz => hc.thetaMap_xiMap hz.1 (hreg z hz).1 (hreg z hz).2
  have hΞ := hG.tendsto hpB
  rw [hGp] at hΘ hΞ
  exact ⟨p, hp0, hFp, hΘ, hΞ⟩

/-- The slit point `β(s′)` lies in `ℍ`. -/
theorem slit_mem_H {s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ) : β s' ∈ H := by
  rw [← hc.cont_eqOn ⟨hs'.le, hs'σ.le⟩]
  exact hc.dom_subset (hc.cont_mapsTo ⟨hs', hs'σ.le.trans hc.σ_lt_τ.le⟩)

/-- `Im thetaLog → 0` at `x′` once `Θ → p` inside `ℍ` and `Im xiLog → 0` at `p`. -/
theorem tendsto_im_thetaLog {x' p : ℝ} (hΘ : Tendsto (thetaMap W σ Ψi w t) (𝓝[H] (x' : ℂ)) (𝓝[H] (p : ℂ)))
    (hlog : Tendsto (fun y => (xiLog w t Ψ LΨ W σ y).im) (𝓝[H] (p : ℂ)) (𝓝 0)) :
    Tendsto (fun y => (thetaLog W σ Ψi LΨ w t y).im) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  have h := (hlog.comp hΘ).neg
  rw [neg_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Function.comp_apply, hc.thetaLog_eq hy, neg_im]

/-- **The left side of the new slit.** If `x′ < 0`, the inverse transition tends to a point `p` of the left side of
the flow slit (`chartAL < p < 0`, `F̄_σ(p) = β(s′)`), and `Im thetaLog → 0` at `x′`. -/
theorem tendsto_theta_of_neg {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : x' < 0) :
    ∃ p : ℝ, chartAL W σ < p ∧ p < 0 ∧ extendFrom H (fwdMapInv W σ) p = β s' ∧
      Tendsto (thetaMap W σ Ψi w t) (𝓝[H] (x' : ℂ)) (𝓝[H] (p : ℂ)) ∧
      Tendsto (fun y => (thetaLog W σ Ψi LΨ w t y).im) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  obtain ⟨p, hp0, hFp, hΘ, hΞ⟩ := hc.exists_cluster hs' hs'σ hx'
  have hFpH : extendFrom H (fwdMapInv W σ) p ∈ H := by rw [hFp]; exact hc.slit_mem_H hs' hs'σ
  obtain ⟨hpL, hpR⟩ := GlueImg.chartAL_lt_of_extendFrom_mem_H hc.trace hc.hW hc.hW0 hc.σ_nonneg hFpH
  have hpneg : p < 0 := by
    rcases lt_or_gt_of_ne hp0 with h | h
    · exact h
    exfalso
    obtain ⟨v₁, hv₁, hgoodR, ξ, hξ, hξpos, hξδ⟩ := hc.exists_right_base
    have hgood : ∀ x ∈ Icc p v₁, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := fun x hx => by
      rcases lt_or_ge x (chartAR W σ) with hxR | hxR
      · exact hc.isGoodPt_of_slit (hpL.trans_le hx.1) hxR (h.trans_le hx.1).ne'
      · exact hgoodR x ⟨hxR, hx.2⟩
    obtain ⟨x₀, -, hx₀, hΞ₀, -⟩ := hc.seed_limits hξ hξδ hξpos.ne'
    have := hc.pos_of_interval hgood ⟨(hpR.trans hv₁).le, le_rfl⟩ (hx₀ hξpos) hΞ₀
      ⟨le_rfl, (hpR.trans hv₁).le⟩ hΞ
    linarith
  obtain ⟨v₁, hv₁, hgoodL, ξ, hξ, hξneg, hξδ⟩ := hc.exists_left_base
  have hgood : ∀ x ∈ Icc v₁ p, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := fun x hx => by
    rcases le_or_gt x (chartAL W σ) with hxL | hxL
    · exact hgoodL x ⟨hx.1, hxL⟩
    · exact hc.isGoodPt_of_slit hxL ((hx.2.trans_lt hpneg).trans_le (WangWu.chartAR_nonneg hc.hW hc.σ_nonneg))
        (hx.2.trans_lt hpneg).ne
  obtain ⟨-, -, -, -, hlog₀⟩ := hc.seed_limits hξ hξδ hξneg.ne
  have hlogp := hc.tendsto_im_xiLog_of_interval hgood ⟨le_rfl, (hv₁.trans hpL).le⟩ hlog₀
    ⟨(hv₁.trans hpL).le, le_rfl⟩
  exact ⟨p, hpL, hpneg, hFp, hΘ, hc.tendsto_im_thetaLog hΘ hlogp⟩

/-- **The right side of the new slit** (mirror of `tendsto_theta_of_neg`). -/
theorem tendsto_theta_of_pos {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : 0 < x') :
    ∃ p : ℝ, 0 < p ∧ p < chartAR W σ ∧ extendFrom H (fwdMapInv W σ) p = β s' ∧
      Tendsto (thetaMap W σ Ψi w t) (𝓝[H] (x' : ℂ)) (𝓝[H] (p : ℂ)) ∧
      Tendsto (fun y => (thetaLog W σ Ψi LΨ w t y).im) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  obtain ⟨p, hp0, hFp, hΘ, hΞ⟩ := hc.exists_cluster hs' hs'σ hx'
  have hFpH : extendFrom H (fwdMapInv W σ) p ∈ H := by rw [hFp]; exact hc.slit_mem_H hs' hs'σ
  obtain ⟨hpL, hpR⟩ := GlueImg.chartAL_lt_of_extendFrom_mem_H hc.trace hc.hW hc.hW0 hc.σ_nonneg hFpH
  have hppos : 0 < p := by
    rcases lt_or_gt_of_ne hp0 with h | h
    swap
    · exact h
    exfalso
    obtain ⟨v₁, hv₁, hgoodL, ξ, hξ, hξneg, hξδ⟩ := hc.exists_left_base
    have hgood : ∀ x ∈ Icc v₁ p, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := fun x hx => by
      rcases le_or_gt x (chartAL W σ) with hxL | hxL
      · exact hgoodL x ⟨hx.1, hxL⟩
      · exact hc.isGoodPt_of_slit hxL (hx.2.trans_lt hpR) (hx.2.trans_lt h).ne
    obtain ⟨x₀, hx₀, -, hΞ₀, -⟩ := hc.seed_limits hξ hξδ hξneg.ne
    have := hc.neg_of_interval hgood ⟨le_rfl, (hv₁.trans hpL).le⟩ (hx₀ hξneg) hΞ₀
      ⟨(hv₁.trans hpL).le, le_rfl⟩ hΞ
    linarith
  obtain ⟨v₁, hv₁, hgoodR, ξ, hξ, hξpos, hξδ⟩ := hc.exists_right_base
  have hgood : ∀ x ∈ Icc p v₁, IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) x) := fun x hx => by
    rcases lt_or_ge x (chartAR W σ) with hxR | hxR
    · exact hc.isGoodPt_of_slit ((WangWu.chartAL_nonpos hc.hW hc.σ_nonneg).trans_lt (hppos.trans_le hx.1)) hxR
        (hppos.trans_le hx.1).ne'
    · exact hgoodR x ⟨hxR, hx.2⟩
  obtain ⟨-, -, -, -, hlog₀⟩ := hc.seed_limits hξ hξδ hξpos.ne'
  have hlogp := hc.tendsto_im_xiLog_of_interval hgood ⟨(hpR.trans hv₁).le, le_rfl⟩ hlog₀
    ⟨le_rfl, (hpR.trans hv₁).le⟩
  exact ⟨p, hppos, hpR, hFp, hΘ, hc.tendsto_im_thetaLog hΘ hlogp⟩

/-- **The slit-side limit of the mean combination (left side).** If `u_ph` has the boundary value `b_ph` on the left
side `(chartAL, 0)` of the flow slit and `u_c` has the boundary value `b_c` at `x′ < 0`, then
`u_ph ∘ Θ + a − u_c − k · Im thetaLog → b_ph + a − b_c` at `x′`. -/
theorem tendsto_slitMean_of_neg {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : x' < 0) {uph uc : ℂ → ℝ}
    {bph bc : ℝ} (huph : ∀ p : ℝ, chartAL W σ < p → p < 0 → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bph))
    (huc : Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bc)) (a k : ℝ) :
    Tendsto (fun y => uph (thetaMap W σ Ψi w t y) + a - uc y - k * (thetaLog W σ Ψi LΨ w t y).im)
      (𝓝[H] (x' : ℂ)) (𝓝 (bph + a - bc)) := by
  obtain ⟨p, hpL, hp0, -, hΘ, hlog⟩ := hc.tendsto_theta_of_neg hs' hs'σ hx' hx'0
  have h := (((huph p hpL hp0).comp hΘ).add_const a).sub huc |>.sub (hlog.const_mul k)
  rw [mul_zero, sub_zero] at h
  exact h

/-- **The slit-side limit of the mean combination (right side).** -/
theorem tendsto_slitMean_of_pos {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : 0 < x') {uph uc : ℂ → ℝ}
    {bph bc : ℝ} (huph : ∀ p : ℝ, 0 < p → p < chartAR W σ → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bph))
    (huc : Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bc)) (a k : ℝ) :
    Tendsto (fun y => uph (thetaMap W σ Ψi w t y) + a - uc y - k * (thetaLog W σ Ψi LΨ w t y).im)
      (𝓝[H] (x' : ℂ)) (𝓝 (bph + a - bc)) := by
  obtain ⟨p, hp0, hpR, -, hΘ, hlog⟩ := hc.tendsto_theta_of_pos hs' hs'σ hx' hx'0
  have h := (((huph p hp0 hpR).comp hΘ).add_const a).sub huc |>.sub (hlog.const_mul k)
  rw [mul_zero, sub_zero] at h
  exact h

end IsTwoSideConfig

end InteractingSLE.Sec5.Aux61TwoS
