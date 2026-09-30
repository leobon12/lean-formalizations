import QuantumZipper.Proofs.Thm18.G1PushVar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FROST-B toolkit, part 1: potential estimates for a general Frostman exponent `α`

Copy of the Frostman-exponent-`1/3` potential toolkit with `1/3 ↦ α` (`0 < α ≤ 1`):

* `potMaxα`, `holderKα` (+ nonnegativity): copies of `TwoPoint.potMax`, `TwoPoint.holderK`
  (TwoPointEnergy.lean), which are hard-wired to `α = 1/3`;
* `isFrostman_bindFcα`: copy of `RegCont.isFrostman_bindFc` (RegContEnergy.lean); the cube-root
  arithmetic is replaced by `(2x)^α ≤ 2 x^α` and `t ρ^α ≤ t^α ρ` for `t < ρ`;
* `abs_fcPot_le_Lα`, `abs_fcPot_sub_le_Lα`, `kernelCov_bindFc_eq_Lα`: copies of
  `abs_fcPot_le_L`, `abs_fcPot_sub_le_L`, `kernelCov_bindFc_eq_L` (G1PushVarRad.lean).

Source: the repository's Neumann-potential estimates `TwoPoint.abs_neuPot_le`,
`TwoPoint.abs_neuPot_sub_le` (general `α`), the Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1-type argument. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open CircleFubini TwoPoint RegCont

/-- Bound on `sup |neuPot|` (exponent `α`, mass `1`); `potMax` with `1/3 ↦ α`. -/
def potMaxα (α CF Bf : ℝ) : ℝ := 2 * (CF / α) + 2 * (Real.log (Bf + Bf + 1) * 1)

/-- Hölder constant of `neuPot` (exponent `α`); `holderK` with `1/3 ↦ α`. -/
def holderKα (α CF Bf : ℝ) : ℝ := 2 * (1 + 4 * CF / α) + 2 * potMaxα α CF Bf

theorem potMaxα_nonneg {α CF Bf : ℝ} (hα : 0 < α) (hCF : 0 ≤ CF) (hBf : 0 ≤ Bf) :
    0 ≤ potMaxα α CF Bf := by
  unfold potMaxα
  have : 0 ≤ Real.log (Bf + Bf + 1) := Real.log_nonneg (by linarith)
  have : 0 ≤ CF / α := div_nonneg hCF hα.le
  positivity

theorem holderKα_nonneg {α CF Bf : ℝ} (hα : 0 < α) (hCF : 0 ≤ CF) (hBf : 0 ≤ Bf) :
    0 ≤ holderKα α CF Bf := by
  unfold holderKα
  have := potMaxα_nonneg hα hCF hBf
  have : 0 ≤ 4 * CF / α := div_nonneg (by positivity) hα.le
  positivity

/-- `(2x)^α ≤ 2 x^α` for `x ≥ 0`, `0 < α ≤ 1`. -/
theorem two_mul_rpow_le_α {α x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hx : 0 ≤ x) :
    (2 * x) ^ α ≤ 2 * x ^ α := by
  rw [Real.mul_rpow (by norm_num) hx]
  have h2 : (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
  rw [Real.rpow_one] at h2
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx _)

/-- **Frostman bound for circle averages** (exponent `α`): copy of `RegCont.isFrostman_bindFc`
with `1/3 ↦ α`. -/
theorem isFrostman_bindFcα {ν : Measure ℂ} [IsFiniteMeasure ν] {α C : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : TwoPoint.IsFrostman ν α C) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    TwoPoint.IsFrostman (bindFc ν ρ) α (24 * C) := by
  intro p t ht
  have hC : 0 ≤ C := by
    have := hF 0 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    exact ENNReal.toReal_nonneg.trans this
  set U := Metric.closedBall p (ρ + t) ∪ Metric.closedBall (starRingEnd ℂ p) (ρ + t) with hUdef
  have hUm : MeasurableSet U :=
    Metric.isClosed_closedBall.measurableSet.union Metric.isClosed_closedBall.measurableSet
  have hU : (ν U).toReal ≤ 2 * C * (ρ + t) ^ α := by
    have h1 := hF p (ρ + t) (by linarith)
    have h2 := hF (starRingEnd ℂ p) (ρ + t) (by linarith)
    have hle : (ν U).toReal ≤ (ν (Metric.closedBall p (ρ + t))).toReal +
        (ν (Metric.closedBall (starRingEnd ℂ p) (ρ + t))).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      exact ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)
    linarith
  have hbind : bindFc ν ρ (Metric.closedBall p t) =
      ∫⁻ y, foldedCircle y ρ (Metric.closedBall p t) ∂ν :=
    CircleFubini.bind_circle_apply ν Metric.isClosed_closedBall.measurableSet
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) ν
  set a := t ^ α with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg ht.le _
  rcases le_or_gt ρ t with hρt | hρt
  · have h1 : bindFc ν ρ (Metric.closedBall p t) ≤ ν U := by
      rw [hbind]
      calc ∫⁻ y, foldedCircle y ρ (Metric.closedBall p t) ∂ν ≤ ∫⁻ y, U.indicator 1 y ∂ν :=
            lintegral_mono fun y => foldedCircle_closedBall_le_indicator y p hρ
        _ = ν U := lintegral_indicator_one hUm
    have h2 : (ρ + t) ^ α ≤ 2 * a :=
      (Real.rpow_le_rpow (by linarith) (by linarith : ρ + t ≤ 2 * t) hα.le).trans
        (two_mul_rpow_le_α hα hα1 ht.le)
    calc (bindFc ν ρ (Metric.closedBall p t)).toReal ≤ (ν U).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) h1
      _ ≤ 2 * C * (ρ + t) ^ α := hU
      _ ≤ 24 * C * a := by nlinarith
  · have hρ0 : 0 < ρ := ht.trans hρt
    set b := ρ ^ α with hb
    have hb0 : 0 ≤ b := Real.rpow_nonneg hρ _
    have h1 : bindFc ν ρ (Metric.closedBall p t) ≤ ENNReal.ofReal (6 * t / ρ) * ν U := by
      rw [hbind, ← lintegral_indicator_const hUm]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ U
      · rw [Set.indicator_of_mem hy]; exact foldedCircle_closedBall_le_arc y p hρ0 ht.le
      · rw [Set.indicator_of_notMem hy]
        have := foldedCircle_closedBall_le_indicator y p (t := t) hρ
        rwa [Set.indicator_of_notMem hy] at this
    have h2 : (ρ + t) ^ α ≤ 2 * b :=
      (Real.rpow_le_rpow (by linarith) (by linarith : ρ + t ≤ 2 * ρ) hα.le).trans
        (two_mul_rpow_le_α hα hα1 hρ)
    have h3 : t * b ≤ a * ρ := by
      have e1 : t ≤ ρ ^ (1 - α) * a := by
        have := rpow_le_bound_mul_rpow ht.le hρt.le hα hα1
        rwa [Real.rpow_one] at this
      have e2 : ρ ^ (1 - α) * b = ρ := by
        rw [hb, ← Real.rpow_add hρ0]; norm_num
      calc t * b ≤ ρ ^ (1 - α) * a * b := mul_le_mul_of_nonneg_right e1 hb0
        _ = a * (ρ ^ (1 - α) * b) := by ring
        _ = a * ρ := by rw [e2]
    have h4 : (bindFc ν ρ (Metric.closedBall p t)).toReal ≤ 6 * t / ρ * (ν U).toReal := by
      have := ENNReal.toReal_mono (by finiteness) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have h5 : 6 * t / ρ * (ν U).toReal ≤ 6 * t / ρ * (2 * C * (2 * b)) :=
      mul_le_mul_of_nonneg_left (hU.trans (by nlinarith)) (by positivity)
    refine h4.trans (h5.trans ?_)
    rw [show 6 * t / ρ * (2 * C * (2 * b)) = 24 * C * (t * b) / ρ by ring, div_le_iff₀ hρ0]
    nlinarith

section FcPotLα

variable {κ : Measure ℂ} [IsFiniteMeasure κ] {α CF B L : ℝ}

theorem abs_fcPot_le_Lα (hα : 0 < α) (hCF : 0 ≤ CF) (hB0 : 0 ≤ B) (hL : 0 ≤ L)
    (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) {y : ℂ} {ρ : ℝ} (hy : ‖y‖ ≤ B)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ L) : |fcPot κ ρ y| ≤ potMaxα α CF (B + L) := by
  have hB1 : 0 ≤ B + L := by linarith
  unfold fcPot
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∫ _x, potMaxα α CF (B + L) ∂foldedCircle y ρ = potMaxα α CF (B + L) := by simp
  rw [← this]
  refine integral_mono_ae ?_ (integrable_const _) ?_
  · refine Integrable.of_bound
      (continuous_abs.measurable.comp (measurable_neuPot κ)).aestronglyMeasurable
      (potMaxα α CF (B + L)) ?_
    filter_upwards [foldedCircle_ae_norm_le y hρ] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    have := abs_neuPot_le hFκ hα hCF hB1 hBκ (x := x) (X := B + L) (by linarith)
    rwa [hmκ] at this
  · filter_upwards [foldedCircle_ae_norm_le y hρ] with x hx
    have := abs_neuPot_le hFκ hα hCF hB1 hBκ (x := x) (X := B + L) (by linarith)
    rwa [hmκ] at this

theorem abs_fcPot_sub_le_Lα (hα : 0 < α) (hα1 : α ≤ 1) (hCF : 0 ≤ CF) (hB0 : 0 ≤ B)
    (hL : 0 ≤ L) (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) {y y' : ℂ} {ρ ρ' : ℝ}
    (hy : ‖y‖ ≤ B) (hy' : ‖y'‖ ≤ B) (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ') (hρ1 : ρ ≤ L) (hρ1' : ρ' ≤ L) :
    |fcPot κ ρ y - fcPot κ ρ' y'| ≤
      holderKα α CF (B + L) * (‖y - y'‖ + |ρ - ρ'|) ^ (α / 2) := by
  have hπ := Real.pi_pos
  have hB1 : 0 ≤ B + L := by linarith
  set Pm := potMaxα α CF (B + L)
  set KH := holderKα α CF (B + L)
  have hKH0 : 0 ≤ KH := holderKα_nonneg hα hCF hB1
  have hPb : ∀ x : ℂ, ‖x‖ ≤ B + L → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ hα hCF hB1 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ B + L → ‖x'‖ ≤ B + L →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ (α / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ hα hα1 hCF hB1 hBκ hx hx'
    rwa [hmκ] at this
  have hg : Measurable (neuPot κ) := measurable_neuPot κ
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hvolI : (volume.restrict (Ico (0 : ℝ) (2 * π))).real univ = 2 * π := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  set d := KH * (‖y - y'‖ + |ρ - ρ'|) ^ (α / 2) with hd
  have hnb : ∀ z : ℂ, ‖z‖ ≤ B → ∀ σ, 0 ≤ σ → σ ≤ L → ∀ θ,
      ‖foldH (circleMap z σ θ)‖ ≤ B + L := fun z hz σ hσ hσ1 θ =>
    (norm_foldH _).le.trans ((norm_circleMap_le_add z hσ θ).trans (by linarith))
  have hiθ : ∀ z : ℂ, ‖z‖ ≤ B → ∀ σ, 0 ≤ σ → σ ≤ L →
      Integrable (fun θ => neuPot κ (foldH (circleMap z σ θ)))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := fun z hz σ hσ hσ1 =>
    Integrable.of_bound
      (hg.comp (measurable_foldH.comp (measurable_circleMap z σ))).aestronglyMeasurable
      Pm (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hnb z hz σ hσ hσ1 θ))
  unfold fcPot
  rw [integral_foldedCircle_eq hg, integral_foldedCircle_eq hg, ← mul_sub,
    ← integral_sub (hiθ y hy ρ hρ hρ1) (hiθ y' hy' ρ' hρ' hρ1'), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hθ : ∀ θ, |neuPot κ (foldH (circleMap y ρ θ)) - neuPot κ (foldH (circleMap y' ρ' θ))|
      ≤ d := by
    intro θ
    refine (hH _ _ (hnb y hy ρ hρ hρ1 θ) (hnb y' hy' ρ' hρ' hρ1' θ)).trans ?_
    refine mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity)) hKH0
    exact (norm_foldH_sub_le _ _).trans (norm_circleMap_sub_le y y' ρ ρ' θ)
  calc (2 * π)⁻¹ * |∫ θ in Ico 0 (2 * π), (neuPot κ (foldH (circleMap y ρ θ)) -
        neuPot κ (foldH (circleMap y' ρ' θ)))|
      ≤ (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), d := by
        refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans
          (integral_mono ((hiθ y hy ρ hρ hρ1).sub (hiθ y' hy' ρ' hρ' hρ1')).abs
            (integrable_const d) hθ)) (by positivity)
    _ = d := by
        rw [integral_const, hvolI, smul_eq_mul]
        field_simp

end FcPotLα

/-- `kernelCov neumannH (μ^ρ) κ = ∫ fcPot κ ρ dμ`, for radii `ρ ≤ L` (exponent `α`). -/
theorem kernelCov_bindFc_eq_Lα {μ : Measure ℂ} [IsFiniteMeasure μ] {α B CF L : ℝ}
    (hα : 0 < α) (hB0 : 0 ≤ B)
    (hCF : 0 ≤ CF) (hL : 0 ≤ L) (hBμ : ∀ᵐ y ∂μ, ‖y‖ ≤ B) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ L)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ α CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + L) (hmκ : κ.real univ = 1) :
    kernelCov neumannH (bindFc μ ρ) κ = ∫ y, fcPot κ ρ y ∂μ := by
  have hB1 : 0 ≤ B + L := by linarith
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) μ
  have hint : Integrable (neuPot κ) (bindFc μ ρ) := by
    refine Integrable.of_bound (measurable_neuPot κ).aestronglyMeasurable
      (potMaxα α CF (B + L)) ?_
    filter_upwards [ae_norm_bindFc_le hρ hBμ] with x hx
    rw [Real.norm_eq_abs]
    have := abs_neuPot_le hFκ hα hCF hB1 hBκ (x := x) (X := B + L) (by linarith)
    rwa [hmκ] at this
  exact (CircleFubini.integral_bind_circle μ hint).2

end G1RC
end Thm18Asm
end QuantumZipper
