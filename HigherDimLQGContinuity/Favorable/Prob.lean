import HigherDimLQGContinuity.Favorable.Cantelli
import HigherDimLQGContinuity.Favorable.Numerics
import HigherDimLQGContinuity.Events.RefsProb
import HigherDimLQGContinuity.Amplify.Geodesic

/-!
# The two unit-distance events of Lemma 3.4 (packet P8a)

Packet P8a, blueprint Part A, Lemma `a:lem34` (proof, "Constants"; NA1 item 26, R10; NA0 §2.3). Consumed interface:
I1, `UniformEstimates d ξ̄ 1` (Lemma 2.1 at the unit pin), taken as a hypothesis.

* `p8a_ratio_prob` (Cantelli): with `Y = log ρ^E_g(0, e₁) - log ρ^D_g(0, e₁)` under `𝐏₁` (`E Y = 0` by the mean-log
  centering `a:lem-rho`(c), `E Y² ≤ 4 K₂` by (E4) with `q = 2`), `𝐏₁(Y < log(1 + v)) ≥ c₁ v²` with
  `c₁ = 1/(4(4K₂ + 1))`, uniformly in `ξ, η ∈ (0, ξ̄]`, `D, E` strong, `0 < v ≤ 1`.
* `p8a_small_prob` (inverse crossing): every path from `0` to `e₁` crosses `{1/4 ≤ |x| ≤ 1/2}`, so
  `ρ^D_g(0, e₁) ≥ ρ^D_g(∂B_{1/4}, ∂B_{1/2})` for the (a.s.) length metric `ρ^D_g`; with (E2) (`q = 1`) and Markov,
  `𝐏₁(ρ^D_g(0, e₁) < w) ≤ K_inv w`.
* `p8a_setDistIn_le_apply`: the deterministic crossing bound for a length metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## A crossing bound for length metrics -/

/-- For a length metric, the distance between a point of `B̄_{r₁}(z)` and a point outside `B_{r₂}(z)`
(`r₁ ≤ r₂`) is at least the global set distance between the two spheres. -/
theorem p8a_setDistIn_le_apply {G : ContMetric d} (hG : G.IsLength) {z x y : Rd d} {r₁ r₂ : ℝ}
    (hr : r₁ ≤ r₂) (hx : ‖x - z‖ ≤ r₁) (hy : r₂ ≤ ‖y - z‖) :
    setDistIn G univ (sphere z r₁) (sphere z r₂) ≤ ENNReal.ofReal (G.1 (x, y)) := by
  rw [← G.internal_univ_of_isLength hG x y, G.internal_eq_iInf_len]
  refine le_iInf fun P => le_iInf fun hc => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun _ => ?_
  exact p7_setDistIn_le_len G zero_le_one hc z hr (h0 ▸ hx) (h1 ▸ hy)

/-! ## The ratio event (Cantelli) -/

/-- The log-ratio `Y = log ρ^E_g(0, e₁) - log ρ^D_g(0, e₁)` of the unit distances. -/
def p8aLogRatio (D E : DistRd d → ContMetric d) (g : DistRd d) : ℝ :=
  Real.log ((rho E g).1 (0, e₁ d)) - Real.log ((rho D g).1 (0, e₁ d))

/-- `Y² ≤ 2 A² + 2 B²` in `ℝ≥0∞`, with `A, B` the two logarithms. -/
theorem p8a_ofReal_sq_sub_le (a b : ℝ) :
    ENNReal.ofReal ((a - b) ^ 2) ≤ 2 * ENNReal.ofReal (|a| ^ (2 : ℝ)) + 2 * ENNReal.ofReal (|b| ^ (2 : ℝ)) := by
  rw [Real.rpow_two, Real.rpow_two, sq_abs, sq_abs]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (a + b)]

/-- **The ratio event of Lemma 3.4** (Cantelli; blueprint `a:lem34`, "Constants"): there is `c₁ ∈ (0, 1]` with
`𝐏₁(log ρ^E_g(0, e₁) - log ρ^D_g(0, e₁) < log(1 + v)) ≥ c₁ v²` for all `ξ, η ∈ (0, ξ̄]`, `D, E` strong and
`0 < v ≤ 1`. -/
theorem p8a_ratio_prob (hd : 2 ≤ d) {ξbar : ℝ} (hU : UniformEstimates d ξbar 1) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ v : ℝ, 0 < v → v ≤ 1 →
          ENNReal.ofReal (c₁ * v ^ 2) ≤ pinLaw d 1 {g | p8aLogRatio D E g < Real.log (1 + v)} := by
  obtain ⟨K, hK⟩ := hU.logMoments 0 (e₁ d) (p2_zero_ne_e₁ (by omega)) 2 one_le_two
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set σ2 : ℝ := 4 * K' with hσ2
  have hσ20 : 0 ≤ σ2 := by positivity
  refine ⟨1 / (4 * (σ2 + 1)), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith
  intro ξ hξ η hη D E hD hE v hv hv1
  have hP1 : pinLaw d 1 = normLGFLaw d := pinLaw_one hd
  have : IsProbabilityMeasure (pinLaw d 1) := isProbabilityMeasure_pinLaw hd 1
  have hmA := measurable_log_rho_apply hE.measurable (0, e₁ d)
  have hmB := measurable_log_rho_apply hD.measurable (0, e₁ d)
  have hYm : AEStronglyMeasurable (p8aLogRatio D E) (pinLaw d 1) := (hmA.sub hmB).aestronglyMeasurable
  -- the second moment
  have hKA := hK η hη E hE
  have hKB := hK ξ hξ D hD
  have hsq : ∫⁻ g, ENNReal.ofReal (p8aLogRatio D E g ^ 2) ∂(pinLaw d 1) ≤ ENNReal.ofReal σ2 := by
    have hmEA : Measurable fun g => ENNReal.ofReal (|Real.log ((rho E g).1 (0, e₁ d))| ^ (2 : ℝ)) :=
      ENNReal.measurable_ofReal.comp (hmA.abs.pow_const _)
    have hmEB : Measurable fun g => ENNReal.ofReal (|Real.log ((rho D g).1 (0, e₁ d))| ^ (2 : ℝ)) :=
      ENNReal.measurable_ofReal.comp (hmB.abs.pow_const _)
    have hmA2 : Measurable fun g => 2 * ENNReal.ofReal (|Real.log ((rho E g).1 (0, e₁ d))| ^ (2 : ℝ)) :=
      measurable_const.mul hmEA
    calc ∫⁻ g, ENNReal.ofReal (p8aLogRatio D E g ^ 2) ∂(pinLaw d 1)
        ≤ ∫⁻ g, (2 * ENNReal.ofReal (|Real.log ((rho E g).1 (0, e₁ d))| ^ (2 : ℝ)) +
            2 * ENNReal.ofReal (|Real.log ((rho D g).1 (0, e₁ d))| ^ (2 : ℝ))) ∂(pinLaw d 1) :=
          lintegral_mono fun g => p8a_ofReal_sq_sub_le _ _
      _ = 2 * ∫⁻ g, ENNReal.ofReal (|Real.log ((rho E g).1 (0, e₁ d))| ^ (2 : ℝ)) ∂(pinLaw d 1) +
            2 * ∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (0, e₁ d))| ^ (2 : ℝ)) ∂(pinLaw d 1) := by
          rw [lintegral_add_left hmA2, lintegral_const_mul _ hmEA, lintegral_const_mul _ hmEB]
      _ ≤ 2 * ENNReal.ofReal K' + 2 * ENNReal.ofReal K' := by
          gcongr
          · exact hKA.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          · exact hKB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal σ2 := by
          rw [hσ2, ← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = ENNReal.ofReal 4 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
  -- the mean
  have hmean : ∫ g, p8aLogRatio D E g ∂(pinLaw d 1) = 0 := by
    have hintE := hU.logIntegrable η hη E hE
    have hintD := hU.logIntegrable ξ hξ D hD
    rw [hP1]
    unfold p8aLogRatio
    rw [integral_sub (integrable_log_rho hd hintE) (integrable_log_rho hd hintD), integral_log_rho hd hintE,
      integral_log_rho hd hintD, sub_zero]
  have ht : 0 < Real.log (1 + v) := Real.log_pos (by linarith)
  have hcan := cantelli_lower hYm hσ20 hsq hmean ht
  exact (ENNReal.ofReal_le_ofReal (p8a_cantelli_rate hσ20 hv hv1)).trans hcan

/-- On the ratio event, `ρ^E_g(0, e₁) < (1 + v) ρ^D_g(0, e₁)` (`v > -1`). -/
theorem p8a_lt_of_logRatio_lt {D E : DistRd d → ContMetric d} {g : DistRd d} (hd : 1 ≤ d) {v : ℝ}
    (hv : -1 < v) (h : p8aLogRatio D E g < Real.log (1 + v)) :
    (rho E g).1 (0, e₁ d) < (1 + v) * (rho D g).1 (0, e₁ d) := by
  have hne := p2_zero_ne_e₁ (d := d) hd
  have hE0 : 0 < (rho E g).1 (0, e₁ d) := (rho E g).apply_pos hne
  have hD0 : 0 < (rho D g).1 (0, e₁ d) := (rho D g).apply_pos hne
  unfold p8aLogRatio at h
  rw [← Real.log_div hE0.ne' hD0.ne'] at h
  have h' := (Real.log_lt_log_iff (div_pos hE0 hD0) (by linarith)).1 h
  rwa [div_lt_iff₀ hD0] at h'

/-! ## The small-distance event (inverse crossing) -/

/-- **The small-distance event of Lemma 3.4** (blueprint `a:lem34`, "Constants"): there is `K_inv > 0` with
`𝐏₁(ρ^D_g(0, e₁) < w) ≤ K_inv w` for all `ξ ∈ (0, ξ̄]`, `D` strong and `w > 0` ((E2) with `q = 1`, `z = 0`,
`(r₁, r₂) = (1/4, 1/2)`). -/
theorem p8a_small_prob (hd : 2 ≤ d) {ξbar : ℝ} (hU : UniformEstimates d ξbar 1) :
    ∃ Kinv : ℝ, 0 < Kinv ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → ∀ w : ℝ, 0 < w →
          pinLaw d 1 {g | (rho D g).1 (0, e₁ d) < w} ≤ ENNReal.ofReal (Kinv * w) := by
  obtain ⟨K, hK⟩ := hU.cross 0 (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  refine ⟨max K 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ξ hξ D hD w hw
  have hl := p5b_ae_isLength_rho hd hD one_pos
  have hX := p5b_aemeasurable_setDistIn_univ hD.measurable (pinLaw d 1) hl (sphere (0 : Rd d) (1 / 4))
    (sphere (0 : Rd d) (1 / 2))
  have hmk := p5b_markov (μ := pinLaw d 1)
    (f := fun g => (setDistIn (rho D g) univ (sphere (0 : Rd d) (1 / 4)) (sphere (0 : Rd d) (1 / 2)))⁻¹ ^
      (1 : ℝ)) (hX.inv.pow_const 1) (inv_pos.2 hw) (hK ξ hξ D hD)
  have he₁ : ‖e₁ d - 0‖ = 1 := by rw [sub_zero]; exact HigherDimLFPP.norm_e₁ (by omega)
  have hsub : {g | (rho D g).1 (0, e₁ d) < w} ≤ᵐ[pinLaw d 1]
      {g | ENNReal.ofReal w⁻¹ ≤ (setDistIn (rho D g) univ (sphere (0 : Rd d) (1 / 4))
        (sphere (0 : Rd d) (1 / 2)))⁻¹ ^ (1 : ℝ)} := by
    filter_upwards [hl] with g hg hlt
    change (rho D g).1 (0, e₁ d) < w at hlt
    have hcr := p8a_setDistIn_le_apply hg (z := 0) (x := 0) (y := e₁ d) (r₁ := 1 / 4) (r₂ := 1 / 2)
      (by norm_num) (by rw [sub_zero, norm_zero]; norm_num) (by rw [he₁]; norm_num)
    have hlt' : ENNReal.ofReal ((rho D g).1 (0, e₁ d)) < ENNReal.ofReal w :=
      (ENNReal.ofReal_lt_ofReal_iff hw).2 hlt
    rw [ENNReal.rpow_one, ENNReal.ofReal_inv_of_pos hw]
    exact ENNReal.inv_le_inv.2 (hcr.trans hlt'.le)
  calc pinLaw d 1 {g | (rho D g).1 (0, e₁ d) < w} ≤ _ := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (K / w⁻¹) := hmk
    _ ≤ ENNReal.ofReal (max K 1 * w) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_inv_eq_mul]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le

end HigherDimLQGContinuity
