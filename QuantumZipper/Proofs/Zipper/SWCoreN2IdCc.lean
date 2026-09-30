import QuantumZipper.Proofs.Zipper.SWCoreN2IdPush
import QuantumZipper.Proofs.Zipper.SWCoreB5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2-ID (4): continuity of the `log |ψ'|` term in the centre and the dyadic-centre limit

Task SWC-N2-ID, item (i). For a class map `ψ` and small `r`, `‖ψ'‖ ∈ [m/2, 4M/ρ]` on the
`2r`-neighbourhood of `[a,b]` (Cauchy's estimate for `ψ''`, `norm_deriv2_le_of_class`, and the
mean value theorem), so `s ↦ cc ψ s r` is continuous on `[a − r, b + r]` (dominated convergence,
`swcN2_cc_continuousOn`). Then `avgReg (coordChange x ψ Q) k t`, the limit along the dyadic
roundings `dyadicRound n t → t` (which lie in `[a − r, b + r]` eventually), equals
`evalReg x (fc(t,r).map ψ) + Q cc ψ t r` as soon as the first term is continuous in the centre on
`[a − r, b + r]` (`swcN2_avgReg_eq`; boundary analogue of `swcNA_avgReg_coordChange_eq`).
Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

variable {a b ρ M m : ℝ} {ψ : ℂ → ℂ}

/-- Lower bound for `‖ψ'‖` near `[a,b]` (Cauchy estimate for `ψ''` + mean value theorem). -/
theorem swcN2_norm_deriv_ge (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {s0 : ℝ}
    (hs0 : s0 ∈ Icc a b) {R : ℝ} (hRρ : R ≤ ρ / 8) (hRm : 32 * (|M| + 1) / ρ ^ 2 * R ≤ m / 2)
    {w : ℂ} (hw : w ∈ closedBall (s0 : ℂ) R) : m / 2 ≤ ‖deriv ψ w‖ := by
  have hB : ball (s0 : ℂ) (ρ / 4) ⊆ thickening (ρ / 4) (segC a b) := fun z hz =>
    mem_thickening_iff.2 ⟨(s0 : ℂ), ⟨s0, hs0, rfl⟩, hz⟩
  have hd : ∀ z ∈ ball (s0 : ℂ) (ρ / 4), DifferentiableAt ℂ (deriv ψ) z := fun z hz =>
    (hψ.1.deriv isOpen_thickening).differentiableAt (isOpen_thickening.mem_nhds
      (thickening_mono (by linarith) _ (hB hz)))
  have hbd : ∀ z ∈ ball (s0 : ℂ) (ρ / 4), ‖deriv (deriv ψ) z‖ ≤ 32 * M / ρ ^ 2 := fun z hz =>
    norm_deriv2_le_of_class hψ hρ (hB hz)
  have hwR : ‖w - s0‖ ≤ R := by rw [← dist_eq_norm]; exact hw
  have hwb : w ∈ ball (s0 : ℂ) (ρ / 4) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hd hbd (convex_ball _ _)
    (mem_ball_self (by positivity)) hwb
  have hm0 : m ≤ ‖deriv ψ s0‖ := hψ.2.2.2.2 s0 hs0
  have h1 : 32 * M / ρ ^ 2 * ‖w - s0‖ ≤ 32 * (|M| + 1) / ρ ^ 2 * R := by
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hwR
    have : 32 * M / ρ ^ 2 ≤ 32 * (|M| + 1) / ρ ^ 2 :=
      div_le_div_of_nonneg_right (by linarith [le_abs_self M]) (by positivity)
    calc 32 * M / ρ ^ 2 * ‖w - s0‖ ≤ 32 * (|M| + 1) / ρ ^ 2 * ‖w - s0‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hwR (by positivity)
  have h2 : ‖deriv ψ s0‖ - ‖deriv ψ w‖ ≤ ‖deriv ψ w - deriv ψ s0‖ := by
    have := norm_sub_norm_le (deriv ψ s0) (deriv ψ w)
    rwa [norm_sub_rev] at this
  linarith

/-- **Continuity of `cc ψ · r` on `[a − r, b + r]`** for small `r`. -/
theorem swcN2_cc_continuousOn (hψ : ψ ∈ BdryClass a b ρ M m) (hab : a ≤ b) (hρ : 0 < ρ)
    (hm : 0 < m) {r : ℝ} (hr : 0 < r) (hrρ : 2 * r ≤ ρ / 8)
    (hrm : 32 * (|M| + 1) / ρ ^ 2 * (2 * r) ≤ m / 2) :
    ContinuousOn (fun s : ℝ => CoordChange.cc ψ s r) (Icc (a - r) (b + r)) := by
  set F : ℝ → ℝ → ℝ := fun s θ => Real.log ‖deriv ψ (foldH (circleMap (s : ℂ) r θ))‖ with hF
  have hmeas : Measurable fun z => Real.log ‖deriv ψ z‖ :=
    Real.measurable_log.comp (measurable_deriv ψ).norm
  have hcc : ∀ s, CoordChange.cc ψ s r = ∫ θ, F s θ ∂circM := fun s => by
    unfold CoordChange.cc
    rw [swcN2_fc_eq_map, integral_map (swcN2_measurable_fold_circle _ _).aemeasurable
      hmeas.aestronglyMeasurable]
  simp_rw [hcc]
  -- the points and the derivative bounds
  have hpt : ∀ s ∈ Icc (a - r) (b + r), ∀ θ,
      foldH (circleMap (s : ℂ) r θ) ∈ closedBall ((swcN2Clamp a b s : ℝ) : ℂ) (2 * r) :=
    fun s hs θ => swcN2_fold_mem_ball2 hab hr.le hs θ
  have hs0 : ∀ s, swcN2Clamp a b s ∈ Icc a b := fun s => swcN2Clamp_mem hab s
  have hlo : ∀ s ∈ Icc (a - r) (b + r), ∀ θ,
      m / 2 ≤ ‖deriv ψ (foldH (circleMap (s : ℂ) r θ))‖ := fun s hs θ =>
    swcN2_norm_deriv_ge hψ hρ (hs0 s) hrρ hrm (hpt s hs θ)
  have hthick : ∀ s ∈ Icc (a - r) (b + r), ∀ θ,
      foldH (circleMap (s : ℂ) r θ) ∈ thickening (ρ / 2) (segC a b) := fun s hs θ =>
    mem_thickening_iff.2 ⟨_, ⟨_, hs0 s, rfl⟩,
      lt_of_le_of_lt (mem_closedBall.1 (hpt s hs θ)) (by linarith)⟩
  have hhi : ∀ s ∈ Icc (a - r) (b + r), ∀ θ,
      ‖deriv ψ (foldH (circleMap (s : ℂ) r θ))‖ ≤ 4 * M / ρ := fun s hs θ =>
    norm_deriv_le_of_class hψ hρ (hthick s hs θ)
  refine continuousOn_of_dominated (bound := fun _ => |Real.log (m / 2)| + |Real.log (4 * M / ρ)|)
    (fun s _ => (hmeas.comp (swcN2_measurable_fold_circle _ _)).aestronglyMeasurable)
    (fun s hs => Eventually.of_forall fun θ => ?_) (integrable_const _)
    (Eventually.of_forall fun θ => ?_)
  · have h1 := hlo s hs θ
    have h2 := hhi s hs θ
    have hpos : 0 < ‖deriv ψ (foldH (circleMap (s : ℂ) r θ))‖ := by linarith
    have l1 := Real.log_le_log (by linarith) h1
    have l2 := Real.log_le_log hpos h2
    simp only [hF, Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (m / 2)), abs_nonneg (Real.log (4 * M / ρ))]
    · linarith [le_abs_self (Real.log (4 * M / ρ)), abs_nonneg (Real.log (m / 2))]
  · have hdc : ContinuousOn (deriv ψ) (thickening ρ (segC a b)) :=
      (hψ.1.deriv isOpen_thickening).continuousOn
    have hg : Continuous fun s : ℝ => foldH (circleMap (s : ℂ) r θ) := by
      refine CircleFubini.continuous_foldH'.comp ?_
      simp only [circleMap]
      exact Complex.continuous_ofReal.add continuous_const
    refine ((hdc.comp hg.continuousOn fun s hs =>
      thickening_mono (by linarith) _ (hthick s hs θ)).norm).log fun s hs => ?_
    have := hlo s hs θ
    simp only [comp_apply]
    exact (show 0 < ‖deriv ψ (foldH (circleMap (s : ℂ) r θ))‖ by linarith).ne'

/-- **(i), deterministic form**: the dyadic-centre limit defining `avgReg` of the coordinate
change at a real point `t ∈ [a,b]`, when both terms are continuous in the centre on
`[a − r, b + r]`. -/
theorem swcN2_avgReg_eq (x : FieldSample) (ψ : ℂ → ℂ) (Q : ℝ) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc a b)
    (h1 : ContinuousWithinAt (fun s : ℝ => evalReg x ((foldedCircle (s : ℂ) (radius k)).map ψ))
      (Icc (a - radius k) (b + radius k)) t)
    (h2 : ContinuousWithinAt (fun s : ℝ => CoordChange.cc ψ s (radius k))
      (Icc (a - radius k) (b + radius k)) t) :
    avgReg (coordChange x ψ Q) k (t : ℂ) =
      evalReg x ((foldedCircle (t : ℂ) (radius k)).map ψ) + Q * CoordChange.cc ψ t (radius k) := by
  unfold avgReg
  refine Tendsto.limUnder_eq ?_
  simp_rw [CoordChange.dyadicRoundC_ofReal]
  have hlim : Tendsto (fun n => dyadicRound n t) atTop (𝓝 t) := by
    have := (Complex.continuous_re.tendsto _).comp (RegClosure.tendsto_dyadicRoundC (t : ℂ))
    simpa [comp_def, CoordChange.dyadicRoundC_ofReal] using this
  have hr := radius_pos k
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (1 / 2 : ℝ) ^ n₀ < radius k :=
    exists_pow_lt_of_lt_one hr (by norm_num)
  have hmem : ∀ᶠ n in atTop, dyadicRound n t ∈ Icc (a - radius k) (b + radius k) := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have h1 := CircleCont.abs_dyadicRound_sub_le n t
    have h2 : (1 : ℝ) / 2 ^ n ≤ (1 / 2) ^ n₀ := by
      rw [one_div, ← inv_pow, ← one_div]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    rw [abs_le] at h1
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hw : Tendsto (fun n => dyadicRound n t) atTop
      (𝓝[Icc (a - radius k) (b + radius k)] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, hmem⟩
  exact (h1.tendsto.comp hw).add ((h2.tendsto.comp hw).const_mul Q)

end SWCore
end QuantumZipper
