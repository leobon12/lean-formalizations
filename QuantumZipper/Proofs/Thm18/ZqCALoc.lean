import QuantumZipper.Proofs.Thm18.ZqCMass
import QuantumZipper.Proofs.Thm18.G1ProfileGap
import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.Zipper.D3PlusLocal
import QuantumZipper.Proofs.GFF.CircleFubini
import QuantumZipper.Proofs.Section5.Prop17PalmCReg
import QuantumZipper.Proofs.Thm18.G1G0Stmt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE-A: the zoom through a local map only reads the field near the zoom point

`agreeNear_zoomFieldVia_recF`: the zoom `zoomFieldVia γ L · x ψ` of the rebuilt field
`recF (vOf y)` agrees with that of `y` on every dyadic folded circle of `ball 0 r`, whenever `ψ`
sends the upper half of `ball 0 r` into `{w ∈ ℍ | ‖w + x‖ ≤ 1/2}`.

Chain: `recF (vOf y)` and `y` agree on the dyadic folded circles inside the upper unit disc
(`recF_vOf_apply`), hence their regularized circle averages agree on `ballH (3/4)` at small
radii (`avgReg_recF_H`), hence the regularized pairings with measures carried by `ballH (3/4)`
agree (`evalReg_recF_ballH`); translating by `x` and pushing a folded circle by `ψ` keeps the
relevant measures in that region (a folded circle gives no mass to the real axis:
`foldedCircle_im_zero_null`).

Motivation: locality of circle averages, Duplantier–Sheffield, arXiv:0808.1560, §3. The
bookkeeping is an own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open Factorization G2PalmLoc

/-- Regularized circle averages of `recF (vOf y)` and `y` agree at points of the upper half of
the closed disc of radius `3/4`, at radii `≤ 1/8`. -/
theorem avgReg_recF_H (y : FieldSample) {k : ℕ} (hk : radius k ≤ 1 / 8) {u : ℂ}
    (hu : u ∈ Hbar) (hu' : ‖u‖ ≤ 3 / 4) : avgReg (recF (vOf y)) k u = avgReg y k u := by
  have hev : ∀ᶠ n in atTop, recF (vOf y) (foldedCircle (dyadicRoundC n u) (radius k)) =
      y (foldedCircle (dyadicRoundC n u) (radius k)) := by
    filter_upwards [eventually_ge_atTop 5] with n hn
    obtain ⟨j, hj⟩ := dyadicIndex_surj n k u
    have hdz := CircleCont.norm_dyadicRoundC_sub_le n u
    have hpow : (2 : ℝ) ^ 5 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : 2 * (1 / 2 ^ n : ℝ) ≤ 1 / 16 := by
      have : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ 5 := one_div_le_one_div_of_le (by positivity) hpow
      norm_num at this ⊢; linarith
    have hnorm : ‖dyadicRoundC n u‖ ≤ 3 / 4 + 1 / 16 := by
      have := norm_sub_norm_le (dyadicRoundC n u) u
      linarith
    have hfit : fitJ j := by
      unfold fitJ
      rw [hj]
      exact ⟨Positivity.dyadicRoundC_mem_Hbar n hu, by simp only; linarith⟩
    have := recF_vOf_apply y hfit
    rw [hj] at this
    exact this
  unfold avgReg limUnder
  rw [Filter.map_congr hev]

/-- Locality of `evalReg`: it only reads the regularized averages on a carrier of `ν`, at small
radii. -/
theorem evalReg_congr_of_ae {y y' : FieldSample} {ν : Measure ℂ} {S : Set ℂ}
    (hν : ∀ᵐ w ∂ν, w ∈ S) (h : ∀ᶠ k in atTop, ∀ u ∈ S, avgReg y k u = avgReg y' k u) :
    evalReg y ν = evalReg y' ν := by
  unfold evalReg
  apply D3Plus.limUnder_congr_eventually
  filter_upwards [h] with k hk
  refine integral_congr_ae ?_
  filter_upwards [hν] with w hw
  exact hk w hw

theorem eventually_radius_le_eighth : ∀ᶠ k in atTop, radius k ≤ 1 / 8 := by
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (c := 1 / 8) (by norm_num)
  filter_upwards [eventually_ge_atTop K] with k hk
  exact (hK k hk).le

theorem evalReg_recF_ballH (y : FieldSample) {ν : Measure ℂ}
    (hν : ∀ᵐ w ∂ν, w ∈ CircleFubini.ballH (3 / 4)) :
    evalReg (recF (vOf y)) ν = evalReg y ν := by
  refine evalReg_congr_of_ae hν ?_
  filter_upwards [eventually_radius_le_eighth] with k hk u hu
  have hu1 := hu.1
  rw [mem_closedBall, dist_zero_right] at hu1
  exact avgReg_recF_H y hk hu.2 hu1

/-- The translated fields have the same regularized averages at points `w ∈ ℍ̄` with
`‖w + x‖ ≤ 1/2`, at radii `≤ 1/8`. -/
theorem avgReg_translate_recF (y : FieldSample) (x : ℝ) {k : ℕ} (hk : radius k ≤ 1 / 8)
    {w : ℂ} (hwx : ‖w + (x : ℂ)‖ ≤ 1 / 2) :
    avgReg (translate (recF (vOf y)) (x : ℂ)) k w = avgReg (translate y (x : ℂ)) k w := by
  unfold avgReg
  apply D3Plus.limUnder_congr_eventually
  filter_upwards [eventually_ge_atTop 4] with n hn
  simp only [translate]
  rw [S5.FieldLaw.Raw.palmC_fc_map_add_real]
  apply evalReg_recF_ballH
  have hdz := CircleCont.norm_dyadicRoundC_sub_le n w
  have hpow : (2 : ℝ) ^ 4 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h2 : 2 * (1 / 2 ^ n : ℝ) ≤ 1 / 8 := by
    have : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ 4 := one_div_le_one_div_of_le (by positivity) hpow
    norm_num at this ⊢; linarith
  have hnorm : ‖dyadicRoundC n w + (x : ℂ)‖ + radius k ≤ 3 / 4 := by
    have e : dyadicRoundC n w + (x : ℂ) = (dyadicRoundC n w - w) + (w + (x : ℂ)) := by ring
    rw [e]
    linarith [norm_add_le (dyadicRoundC n w - w) (w + (x : ℂ))]
  exact ae_iff.2 (CircleFubini.foldedCircle_support (radius_pos k).le hnorm)

/-- A folded circle of positive radius gives no mass to the real axis. -/
theorem foldedCircle_im_zero_null (d : ℂ) {r : ℝ} (hr : 0 < r) :
    foldedCircle d r {w : ℂ | w.im = 0} = 0 := by
  have hm : MeasurableSet {w : ℂ | w.im = 0} :=
    measurableSet_eq_fun Complex.measurable_im measurable_const
  rw [TwoPoint.foldedCircle_apply' d r hm]
  have hZ : volume {θ : ℝ | (circleMap d r θ).im = 0} = 0 := by
    have hAi : AnalyticOnNhd ℝ (fun θ => (circleMap d r θ).im) univ := fun θ _ => by
      have := (Complex.imCLM.analyticAt (circleMap d r θ)).comp
        (analyticOnNhd_circleMap d r θ (mem_univ θ))
      simpa [Function.comp_def] using this
    rcases G1RC.volume_level_eq_zero_or_eqOn hAi isPreconnected_univ 0 with h | ⟨-, h⟩
    · simpa using h
    · have h0 := h (mem_univ 0)
      have h1 := h (mem_univ (π / 2))
      simp only [G1RC.circleMap_im', Real.sin_zero, Real.sin_pi_div_two] at h0 h1
      linarith
  refine mul_eq_zero_of_right _ (measure_mono_null ?_ hZ)
  intro θ hθ
  obtain ⟨-, h⟩ := hθ
  simp only [Set.mem_ofPred_eq, foldH] at h ⊢
  split_ifs at h
  · exact h
  · simpa using h

/-- Pushing a small folded circle by `ψ` lands a.e. in `{w ∈ ℍ̄ | ‖w + x‖ ≤ 1/2}`. -/
theorem ae_map_foldedCircle_good {ψ : ℂ → ℂ} (hψm : Measurable ψ) {r x : ℝ}
    (hψ : ∀ w ∈ Metric.ball (0 : ℂ) r, 0 < w.im → 0 < (ψ w).im ∧ ‖ψ w + (x : ℂ)‖ ≤ 1 / 2)
    {d : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hdr : ‖d‖ + ρ < r) :
    ∀ᵐ w ∂((foldedCircle d ρ).map ψ), ‖w + (x : ℂ)‖ ≤ 1 / 2 := by
  have hmeas : MeasurableSet {w : ℂ | ‖w + (x : ℂ)‖ ≤ 1 / 2} :=
    measurableSet_le (measurable_norm.comp (measurable_id.add_const _)) measurable_const
  refine (ae_map_iff hψm.aemeasurable hmeas).2 ?_
  have h1 : ∀ᵐ w ∂(foldedCircle d ρ), w ∈ CircleFubini.ballH (‖d‖ + ρ) :=
    ae_iff.2 (CircleFubini.foldedCircle_support hρ.le le_rfl)
  have h2 : ∀ᵐ w ∂(foldedCircle d ρ), w.im ≠ 0 :=
    ae_iff.2 (by simpa using foldedCircle_im_zero_null d hρ)
  filter_upwards [h1, h2] with w hw1 hw2
  have h0 : (0 : ℝ) ≤ w.im := hw1.2
  have hwim : 0 < w.im := lt_of_le_of_ne h0 (Ne.symm hw2)
  have hwb : w ∈ Metric.ball (0 : ℂ) r := by
    have := hw1.1
    rw [mem_closedBall] at this
    rw [mem_ball]
    linarith
  exact (hψ w hwb hwim).2

/-- **ZQ-CORE-A.** The zoom through `ψ` of the rebuilt field agrees with that of `y` on the
dyadic folded circles of `ball 0 r`. -/
theorem agreeNear_zoomFieldVia_recF (γ L : ℝ) (y : FieldSample) (x : ℝ) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) {r : ℝ}
    (hψ : ∀ w ∈ Metric.ball (0 : ℂ) r, 0 < w.im → 0 < (ψ w).im ∧ ‖ψ w + (x : ℂ)‖ ≤ 1 / 2) :
    D3Plus.AgreeNear (zoomFieldVia γ L (recF (vOf y)) x ψ) (zoomFieldVia γ L y x ψ) r := by
  intro n k z hz
  have key : evalReg (translate (recF (vOf y)) (x : ℂ))
      ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) =
      evalReg (translate y (x : ℂ)) ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) := by
    refine evalReg_congr_of_ae (ae_map_foldedCircle_good hψm hψ (radius_pos k) hz) ?_
    filter_upwards [eventually_radius_le_eighth] with k' hk' w hw
    exact avgReg_translate_recF y x hk' hw
  simp only [zoomFieldVia, addConst, coordChange]
  rw [key]

end ZqC
end Thm18Asm
end QuantumZipper
