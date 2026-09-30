import QuantumZipper.Proofs.Thm18.A1RSFrost

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (7): the smeared measures are Frostman, uniformly in the smoothing radius

For a probability measure `μ` on `ℍ̄` (the pushed side circle `μ_t`) which is `γ`-Frostman, has
bounded support and small mass near `ℝ` (`μ{Im ≤ δ} ≤ C δ^{1/2}`), the smeared measures
`ν_ρ = (μ ⊗ angMeas).map (f_t⁻¹ ∘ U_ρ)`, `U_ρ(z, θ) = fold(z + ρ e^{iθ})`, `ρ ∈ [0, 1]`, are
`min(1/4, γ)/2`-Frostman with one constant (`isFrostman_smeared`). Inputs:

* `norm_sub_mul_le_fwdMapInv`: `τ ‖u − v‖ ≤ √(R² + 4t) ‖f_t⁻¹ u − f_t⁻¹ v‖` for
  `τ ≤ Im u, Im v ≤ R` (the two-point lower bound `TwoPoint.twoPoint_lower_sq` for the reverse
  flow, `f_t⁻¹ = revMap` of the time-reversed driver, `UnzipInvariance.fwdMapInv_eq_revMap_timeRev`;
  the height bound `TwoPoint.im_revMap_sq_le`);
* `prod_foldU_ball_le`: the law of `U_ρ` gives mass `≤ 2 C_μ r^γ` to every closed `r`-ball (a
  ball and its mirror image, Fubini over the angle);
* the strip bound `prod_strip_le` (A1RSStrip.lean) and the abstract step
  `isFrostman_map_of_chart` (A1RSFrost.lean).

Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper
namespace R18
namespace A1RS

open TwoPoint

/-- **Lower two-point bound for `f_t⁻¹` at bounded height.** -/
theorem norm_sub_mul_le_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {u v : ℂ} {τ R : ℝ} (hτ : 0 < τ) (hu : τ ≤ u.im) (hv : τ ≤ v.im)
    (huR : u.im ≤ R) (hvR : v.im ≤ R) :
    τ * ‖u - v‖ ≤ Real.sqrt (R ^ 2 + 4 * t) * ‖fwdMapInv W t u - fwdMapInv W t v‖ := by
  have hu0 : u ∈ H := show 0 < u.im by linarith
  have hv0 : v ∈ H := show 0 < v.im by linarith
  set V : ℝ → ℝ := fun s => W (t - s) - W t with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu0,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hv0]
  set M := Real.sqrt (R ^ 2 + 4 * t)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hfu := im_revMap_pos hV hu0 ht
  have hfv := im_revMap_pos hV hv0 ht
  have hfuM : (revMap V t u).im ≤ M := (le_abs_self _).trans
    (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hV hu0 ht]))
  have hfvM : (revMap V t v).im ≤ M := (le_abs_self _).trans
    (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hV hv0 ht]))
  have hImp : (revMap V t u).im * (revMap V t v).im ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul hfuM hfvM hfv.le hM
  have hsq : (τ * ‖u - v‖) ^ 2 ≤ (M * ‖revMap V t u - revMap V t v‖) ^ 2 := by
    calc (τ * ‖u - v‖) ^ 2 = ‖u - v‖ ^ 2 * (τ * τ) := by ring
      _ ≤ ‖u - v‖ ^ 2 * (u.im * v.im) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hu hv hτ.le (by linarith)) (sq_nonneg _)
      _ ≤ ‖revMap V t u - revMap V t v‖ ^ 2 * ((revMap V t u).im * (revMap V t v).im) :=
        twoPoint_lower_sq hV hu0 hv0 ht
      _ ≤ ‖revMap V t u - revMap V t v‖ ^ 2 * M ^ 2 :=
        mul_le_mul_of_nonneg_left hImp (sq_nonneg _)
      _ = (M * ‖revMap V t u - revMap V t v‖) ^ 2 := by ring
  have h1 : 0 ≤ τ * ‖u - v‖ := mul_nonneg hτ.le (norm_nonneg _)
  have h2 : 0 ≤ M * ‖revMap V t u - revMap V t v‖ := mul_nonneg hM (norm_nonneg _)
  nlinarith [hsq, h1, h2]

theorem mem_or_conj_of_foldH_mem {v c : ℂ} {r : ℝ} (h : foldH v ∈ closedBall c r) :
    v ∈ closedBall c r ∨ v ∈ closedBall (conj c) r := by
  unfold foldH at h
  split_ifs at h with hv
  · exact Or.inl h
  · right
    rw [mem_closedBall, dist_eq_norm] at h ⊢
    have e : v - conj c = conj (conj v - c) := by simp
    rw [e, Complex.norm_conj]
    exact h

/-- The law of the circle point `z + ρ e^{iθ}` gives mass `≤ C_μ r^γ` to each closed ball. -/
theorem prod_circle_ball_le {μ : Measure ℂ} [IsProbabilityMeasure μ] {γ Cμ : ℝ}
    (hF : IsFrostman μ γ Cμ) (hCμ : 0 ≤ Cμ) (ρ : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (μ.prod E6.XAreaPC.angMeas) {p : ℂ × ℝ | circleMap p.1 ρ p.2 ∈ closedBall c r} ≤
      ENNReal.ofReal (Cμ * r ^ γ) := by
  have hc : Continuous fun p : ℂ × ℝ => circleMap p.1 ρ p.2 := by unfold circleMap; fun_prop
  have hS : MeasurableSet {p : ℂ × ℝ | circleMap p.1 ρ p.2 ∈ closedBall c r} :=
    isClosed_closedBall.measurableSet.preimage hc.measurable
  rw [Measure.prod_apply_symm hS]
  have hslice : ∀ θ : ℝ, μ ((fun z => (z, θ)) ⁻¹' {p : ℂ × ℝ | circleMap p.1 ρ p.2 ∈
      closedBall c r}) ≤ ENNReal.ofReal (Cμ * r ^ γ) := fun θ => by
    have e : (fun z => (z, θ)) ⁻¹' {p : ℂ × ℝ | circleMap p.1 ρ p.2 ∈ closedBall c r} =
        closedBall (c - (ρ : ℂ) * Complex.exp (θ * Complex.I)) r := by
      ext z
      simp only [mem_preimage, mem_setOf_eq, mem_closedBall, dist_eq_norm, circleMap]
      ring_nf
    rw [e, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by
      have := Real.rpow_nonneg hr.le γ; positivity)]
    exact hF _ r hr
  refine (lintegral_mono hslice).trans (le_of_eq ?_)
  rw [lintegral_const, measure_univ, mul_one]

/-- **The law of `U_ρ = fold(z + ρ e^{iθ})` has small balls.** -/
theorem prod_foldU_ball_le {μ : Measure ℂ} [IsProbabilityMeasure μ] {γ Cμ : ℝ}
    (hF : IsFrostman μ γ Cμ) (hCμ : 0 ≤ Cμ) (ρ : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (μ.prod E6.XAreaPC.angMeas).real {p : ℂ × ℝ | foldH (circleMap p.1 ρ p.2) ∈ closedBall c r}
      ≤ 2 * (Cμ * r ^ γ) := by
  have hq : 0 ≤ Cμ * r ^ γ := by have := Real.rpow_nonneg hr.le γ; positivity
  have hsub : {p : ℂ × ℝ | foldH (circleMap p.1 ρ p.2) ∈ closedBall c r} ⊆
      {p : ℂ × ℝ | circleMap p.1 ρ p.2 ∈ closedBall c r} ∪
        {p : ℂ × ℝ | circleMap p.1 ρ p.2 ∈ closedBall (conj c) r} :=
    fun p hp => mem_or_conj_of_foldH_mem hp
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have h1 := ENNReal.toReal_le_of_le_ofReal hq (prod_circle_ball_le hF hCμ ρ c hr)
  have h2 := ENNReal.toReal_le_of_le_ofReal hq (prod_circle_ball_le hF hCμ ρ (conj c) hr)
  rw [measureReal_def, measureReal_def]
  linarith

/-- **The smeared measures are Frostman, uniformly in the smoothing radius `ρ ∈ [0, 1]`.** -/
theorem isFrostman_smeared {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {μ : Measure ℂ} [IsProbabilityMeasure μ] {γ Cμ C R₁ : ℝ} (hγ : 0 < γ) (hCμ : 0 ≤ Cμ)
    (hC : 0 ≤ C) (hR₁ : 0 ≤ R₁) (hF : IsFrostman μ γ Cμ) (hH : ∀ᵐ z ∂μ, 0 ≤ z.im)
    (hB : ∀ᵐ z ∂μ, ‖z‖ ≤ R₁)
    (hmass : ∀ δ : ℝ, 0 < δ → μ.real {z : ℂ | z.im ≤ δ} ≤ C * δ ^ (1 / 2 : ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IsFrostman ((μ.prod E6.XAreaPC.angMeas).map
        (fun p : ℂ × ℝ => fwdMapInv W t (foldH (circleMap p.1 ρ p.2))))
      (min (1 / 4) γ / 2)
      ((2 * C + 2) + 2 * Cμ * (2 * Real.sqrt ((R₁ + 1) ^ 2 + 4 * t)) ^ γ + 1) := by
  set m := μ.prod E6.XAreaPC.angMeas with hm
  set U : ℂ × ℝ → ℂ := fun p => foldH (circleMap p.1 ρ p.2) with hU
  set M := Real.sqrt ((R₁ + 1) ^ 2 + 4 * t) with hMdef
  have hM : 0 < M := Real.sqrt_pos.2 (by positivity)
  have hgm : Measurable (fwdMapInv W t) := RTBeur.measurable_fwdMapInv_rt hW hW0 ht
  set far : Set (ℂ × ℝ) := {p | R₁ < ‖p.1‖} with hfar
  have hfar0 : m far = 0 := by
    have e : far = {z : ℂ | R₁ < ‖z‖} ×ˢ (univ : Set ℝ) := by ext p; simp [hfar]
    rw [e, hm, Measure.prod_prod]
    have : μ {z : ℂ | R₁ < ‖z‖} = 0 := by
      rw [ae_iff] at hB
      simpa [not_le] using hB
    rw [this, zero_mul]
  refine isFrostman_map_of_chart (m := m) (X := U) (bad := fun τ => stripPar ρ τ ∪ far)
    (A1RF.measurable_smear hgm ρ) (by positivity : (0 : ℝ) ≤ 2 * C + 2) (by norm_num : (0 : ℝ) < 1 / 4)
    (by positivity : (0 : ℝ) ≤ 2 * Cμ) hγ hM ?_ ?_ ?_
  · intro τ hτ hτ1
    refine (measureReal_union_le _ _).trans ?_
    have h1 := prod_strip_le hH hC hmass hρ hτ hτ1
    have h2 : m.real far = 0 := by rw [measureReal_def, hfar0, ENNReal.toReal_zero]
    rw [h2, add_zero]
    exact h1
  · intro c r hr
    have := prod_foldU_ball_le hF hCμ ρ c hr
    calc m.real {θ | U θ ∈ closedBall c r} ≤ 2 * (Cμ * r ^ γ) := this
      _ = 2 * Cμ * r ^ γ := by ring
  · intro τ hτ _ p p' hp hp'
    simp only [mem_union, not_or] at hp hp'
    have hlow : ∀ q : ℂ × ℝ, q ∉ stripPar ρ τ → τ ≤ (U q).im := fun q hq => by
      simp only [stripPar, mem_setOf_eq, not_le] at hq
      exact hq.le
    have hhigh : ∀ q : ℂ × ℝ, q ∉ far → (U q).im ≤ R₁ + 1 := fun q hq => by
      simp only [hfar, mem_setOf_eq, not_lt] at hq
      have h1 : (U q).im ≤ ‖U q‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
      have h2 : ‖U q‖ ≤ ‖q.1‖ + ρ := by
        simp only [hU]
        rw [norm_foldH]
        exact norm_circleMap_le_add q.1 hρ q.2
      linarith
    exact norm_sub_mul_le_fwdMapInv hW hW0 ht hτ (hlow p hp.1) (hlow p' hp'.1) (hhigh p hp.2)
      (hhigh p' hp'.2)

end A1RS
end R18
end QuantumZipper
