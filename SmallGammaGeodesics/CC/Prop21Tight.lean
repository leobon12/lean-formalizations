import LQGMetric.Papers.DFGPS.L2_1RadialMeas
import LQGMetric.Papers.LM.L3_4N5
import LQGMetric.Papers.GM.S2.TightGauss
import LQGMetric.Papers.GM.S2.TightA
import LQGMetric.Papers.GM.S1.Eq115

/-!
# [3] Prop 2.1: scalar tail bounds for the whole-plane GFF (packet CC6b; CC0 Details D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10**, last item ("the
normalization `e^{ξ(h_1(0) − h(ρ))}` is a fixed-law, hence tight, factor") and CC6a's recipe item 3
(`planning/handoffs/CC6a.md`, Details §2). The normalization of CC6a's Lemma 2.3* is
`e^{ξ ⟨h, ρ⟩}`; with `ρ = σ_{0,s} * ψ_0` the mollified uniform measure on the circle `∂B_s`
(`CircleAvg.circBump 0 0 s`) the difference `⟨h, ρ⟩ − h_s(0)` has a bounded first moment
(`DFGPS.lintegral_enorm_circBump_sub_circleAvg_le`), uniformly over all whole-plane GFFs:

* `exists_circBump_tail`: for every `η > 0` there is `L` with `P[⟨h, ρ⟩ − h_s(0) ≥ L] ≤ η` for
  every whole-plane GFF on every probability space (Markov);
* `tsupport_circBump_zero_subset`, `integral_circBump_zero`: `ρ` is admissible for CC6a's lemma;
* `abs_log_le_four_mul`: `|log t| ≤ 4x` for `t ∈ [1 − 2x, 1 + 2x + 2x²]`, `0 ≤ x ≤ 1/4` (used for
  the Jacobian term `Q log|χ'|` of the zoomed coupling).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- `ρ = σ_{0,s} * ψ_0` is supported in `B̄_{s+1}`. -/
theorem tsupport_circBump_zero_subset {s R : ℝ} (hs : 0 ≤ s) (hsR : s + 1 < R) :
    tsupport (CircleAvg.circBump 0 0 s : ℂ → ℝ) ⊆ closedBall 0 R :=
  (LM.tsupport_circBump_subset_ball hs (by simpa using hsR)).trans ball_subset_closedBall

/-- **Markov bound for the circle-bump normalization**: for `s > 0` and `η > 0` there is `L > 0`
such that for every whole-plane GFF `h` on every probability space,
`P[⟨h, σ_{0,s} * ψ_0⟩ − h_s(0) ≥ L] ≤ η`. -/
theorem exists_circBump_tail {s : ℝ} (hs : 0 < s) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P →
      P {ω | L ≤ h ω (CircleAvg.circBump 0 0 s) - circleAvg (h ω) s 0} ≤ ENNReal.ofReal η := by
  set q : ℝ≥0∞ := ENNReal.ofReal √(2⁻¹ : ℝ) with hq
  have hq1 : q < 1 := by
    rw [hq, ← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    rw [Real.sqrt_lt' one_pos]
    norm_num
  set B : ℝ≥0∞ := ENNReal.ofReal (2 / √s) * q ^ 0 * (1 - q)⁻¹ with hB
  have hBtop : B ≠ ⊤ := by
    rw [hB, pow_zero, mul_one]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt hq1).ne'
  set L : ℝ := (B.toReal + 1) / η with hL
  have hL0 : 0 < L := by positivity
  refine ⟨L, hL0, ?_⟩
  intro Ω _ P _ h hh
  set X : Ω → ℝ := fun ω => h ω (CircleAvg.circBump 0 0 s) - circleAvg (h ω) s 0 with hX
  have hXm : Measurable X :=
    ((measurable_distOn_apply _).comp hh.measurable).sub
      ((measurable_circleAvg_left s 0).comp hh.measurable)
  have hsub : {ω | L ≤ X ω} ⊆ {ω | ENNReal.ofReal L ≤ ‖X ω‖ₑ} := fun ω hω => by
    show ENNReal.ofReal L ≤ ‖X ω‖ₑ
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hω.trans (le_abs_self _))
  have hmark := meas_ge_le_lintegral_div (μ := P) (f := fun ω => ‖X ω‖ₑ)
    hXm.enorm.aemeasurable (ENNReal.ofReal_pos.2 hL0).ne' ENNReal.ofReal_ne_top
  have hint := DFGPS.lintegral_enorm_circBump_sub_circleAvg_le hh 0 hs 0
  calc P {ω | L ≤ h ω (CircleAvg.circBump 0 0 s) - circleAvg (h ω) s 0}
      ≤ P {ω | ENNReal.ofReal L ≤ ‖X ω‖ₑ} := measure_mono hsub
    _ ≤ (∫⁻ ω, ‖X ω‖ₑ ∂P) / ENNReal.ofReal L := hmark
    _ ≤ B / ENNReal.ofReal L := ENNReal.div_le_div_right hint _
    _ = ENNReal.ofReal (B.toReal / L) := by
        rw [ENNReal.ofReal_div_of_pos hL0, ENNReal.ofReal_toReal hBtop]
    _ ≤ ENNReal.ofReal η := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hL, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
        have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
        nlinarith

/-- `|log t| ≤ 4 x` for `t ∈ [1 − 2x, 1 + 2x + 2x²]` and `0 ≤ x ≤ 1/4`. -/
theorem abs_log_le_four_mul {x t : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (ht1 : 1 - 2 * x ≤ t)
    (ht2 : t ≤ 1 + 2 * x + 2 * x ^ 2) : |Real.log t| ≤ 4 * x := by
  have ht0 : 0 < t := by linarith
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos ht0
    have h2 : 1 - t⁻¹ ≥ -(4 * x) := by
      have htinv : t⁻¹ ≤ 1 + 4 * x := by
        rw [inv_le_iff_one_le_mul₀ ht0]
        nlinarith
      linarith
    linarith
  · have h1 := Real.log_le_sub_one_of_pos ht0
    nlinarith

end SmallGammaGeodesics.CC
