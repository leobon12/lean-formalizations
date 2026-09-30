import QuantumZipper.Proofs.Thm18.G3PalmR
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Section5.Prop17PalmCReg
import QuantumZipper.Proofs.GFF.CoordRegLog
import QuantumZipper.Proofs.GFF.SmoothingConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-PALMRTIGHT, part 1: the boundary measure of the Palm-shifted free field

For `G3PalmRTightStmt γ` (`G3PalmR.lean`) we identify, for a fixed root `x ∈ ℝ`, the boundary
measure `ν^x` of the Palm-shifted unit-normalized free field
`h^x = palmFreeField γ refS X x = N_S(X + (γ/2)(neumannH x · − k_S))` (Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, arXiv:0808.1560, §3.3: under the rooted measure the field is
the GFF plus a `γ`-log singularity at the root).

* `kPot_refS_eq`: `k_S(u) = −2 log⁺‖u‖` for the unit semicircle (same computation as
  `kPot_foldedCircle_three_eq`), so `shiftFun = γ(−log‖· − x‖) + γ log⁺‖·‖`;
* `palmFreeField_fc_eq`: on every folded circle, `h^x = Z_R + logPot γ x + ψ` with
  `Z_R = zField X R` and `ψ = γ log⁺‖·‖ + const(ω)` continuous;
* `ae_qBoundaryMeasure_palm`: a.s. (for fixed `x`, `|x| + 1 ≤ R`)
  `ν^x = e^{γψ/2} · |t − x|^{−γ²/2} · ν_{Z_R}` off `x` (the log-singularity theorem
  `LogSing.ae_logSingularity` plus the continuous shift `LocalRule.qBoundaryMeasure_add_ofFun'`);
* `ae_qBoundaryMeasure_palm_apply`: on subsets of `[−1, 1]` (where `log⁺‖t‖ = 0`) this is a
  finite positive constant times `m^x = |t − x|^{−γ²/2} ν_{Z_R}|_{\{x\}ᶜ}`.

Own bookkeeping around the cited theorems (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw (palmFreeField)
open PalmNorm

/-- The potential of the unit folded semicircle: `k_S(u) = −2 log⁺‖u‖`. -/
theorem kPot_refS_eq (u : ℂ) : kPot (foldedCircle 0 1) u = -2 * Real.posLog ‖u‖ := by
  unfold kPot foldedCircle
  rw [integral_map measurable_foldH.aemeasurable
    (S5.FieldLaw.Raw.palmC_measurable_neumannH u).aestronglyMeasurable]
  simp_rw [S5.FieldLaw.Raw.palmC_neumannH_foldH]
  rw [CoordReg.integral_circleUnif_eq_circleAverage
    (S5.FieldLaw.Raw.palmC_measurable_neumannH u)]
  have e : neumannH u = fun w => (-1 : ℝ) • (Real.log ‖w - u‖ + Real.log ‖w - conj u‖) := by
    funext w
    simp only [neumannH]
    rw [norm_sub_rev u w, show u - conj w = conj (conj u - w) by simp, Complex.norm_conj,
      norm_sub_rev (conj u) w, smul_eq_mul]
    ring
  have hav : ∀ a : ℂ, Real.circleAverage (fun w => Real.log ‖w - a‖) 0 1 =
      Real.posLog ‖a‖ := by
    intro a
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (by norm_num), zero_sub,
      norm_neg]
    simp
  rw [e, Real.circleAverage_fun_smul, Real.circleAverage_fun_add
    (circleIntegrable_log_norm_sub_const _) (circleIntegrable_log_norm_sub_const _), hav, hav,
    Complex.norm_conj, smul_eq_mul]
  ring

/-- The Palm shift at the root `x` for `ϖ = refS`: `γ(−log‖u − x‖) + γ log⁺‖u‖`. -/
theorem shiftFun_refS_eq (γ x : ℝ) (u : ℂ) :
    shiftFun γ (0 : ℂ → ℝ) refS x u = LogSing.logPot γ x u + γ * Real.posLog ‖u‖ := by
  have h1 : ‖(x : ℂ) - conj u‖ = ‖u - (x : ℂ)‖ := by
    rw [show (x : ℂ) - conj u = conj ((x : ℂ) - u) by rw [map_sub, Complex.conj_ofReal],
      Complex.norm_conj, norm_sub_rev]
  simp only [shiftFun, Pi.zero_apply, neumannH, refS, kPot_refS_eq, LogSing.logPot, h1,
    norm_sub_rev (x : ℂ) u]
  ring

theorem integrable_log_sub_real_fc (x : ℝ) (c : ℂ) (ρ : ℝ) :
    Integrable (fun v => Real.log ‖v - (x : ℂ)‖) (foldedCircle c ρ) := by
  rw [foldedCircle, integrable_map_measure
    (show Measurable fun v : ℂ => Real.log ‖v - (x : ℂ)‖ by fun_prop).aestronglyMeasurable
    measurable_foldH.aemeasurable]
  refine (SmoothConv.integrable_log_norm_sub_circleUnif_sc c x ρ).congr
    (ae_of_all _ fun v => ?_)
  simp only [Function.comp_def]
  unfold foldH
  split_ifs
  · rfl
  · rw [show conj v - (x : ℂ) = conj (v - (x : ℂ)) by rw [map_sub, Complex.conj_ofReal],
      Complex.norm_conj]

theorem integrable_posLog_fc (c : ℂ) (ρ : ℝ) :
    Integrable (fun v => Real.posLog ‖v‖) (foldedCircle c ρ) := by
  refine (CoordReg.integrable_log_norm_foldedCircle c ρ).norm.mono'
    (show Measurable fun v : ℂ => Real.posLog ‖v‖ by fun_prop).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg Real.posLog_nonneg]
  unfold Real.posLog
  exact max_le (abs_nonneg _) (le_abs_self _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The (random) additive constant of the Palm field relative to `Z_R + logPot`. -/
def palmK (γ x R : ℝ) (X : Ω → FieldSample) (ω : Ω) : ℝ :=
  X ω (foldedCircle 0 R) - X ω refS - ∫ u, shiftFun γ (0 : ℂ → ℝ) refS x u ∂refS

/-- The continuous part `ψ = γ log⁺‖·‖ + palmK`. -/
def palmPsi (γ x R : ℝ) (X : Ω → FieldSample) (ω : Ω) (u : ℂ) : ℝ :=
  γ * Real.posLog ‖u‖ + palmK γ x R X ω

theorem continuous_palmPsi (γ x R : ℝ) (X : Ω → FieldSample) (ω : Ω) :
    Continuous (palmPsi γ x R X ω) := by
  unfold palmPsi; fun_prop

/-- **The Palm field on folded circles.** -/
theorem palmFreeField_fc_eq (γ x R : ℝ) (ω : Ω) (c : ℂ) (ρ : ℝ) :
    palmFreeField γ refS X x ω (foldedCircle c ρ) =
      (BdryExist.zField X R ω + ofFun (LogSing.logPot γ x) + ofFun (palmPsi γ x R X ω))
        (foldedCircle c ρ) := by
  have hL : Integrable (LogSing.logPot γ x) (foldedCircle c ρ) :=
    (integrable_log_sub_real_fc x c ρ).neg.const_mul γ
  have hP : Integrable (fun u => γ * Real.posLog ‖u‖) (foldedCircle c ρ) :=
    (integrable_posLog_fc c ρ).const_mul γ
  have hA : ∫ u, shiftFun γ (0 : ℂ → ℝ) refS x u ∂foldedCircle c ρ =
      ∫ u, LogSing.logPot γ x u ∂foldedCircle c ρ +
        ∫ u, γ * Real.posLog ‖u‖ ∂foldedCircle c ρ := by
    simp_rw [shiftFun_refS_eq]
    exact integral_add hL hP
  have hΨ : ∫ u, palmPsi γ x R X ω u ∂foldedCircle c ρ =
      ∫ u, γ * Real.posLog ‖u‖ ∂foldedCircle c ρ + palmK γ x R X ω := by
    unfold palmPsi
    rw [integral_add hP (integrable_const _), integral_const, probReal_univ, one_smul]
  simp only [palmFreeField, normAt, addConst, BdryExist.zField, Pi.add_apply, ofFun,
    measure_univ, ENNReal.toReal_one, mul_one]
  rw [hA, hΨ]
  unfold palmK
  ring

theorem bdryApprox_palmFreeField_eq (γ x R : ℝ) (ω : Ω) :
    bdryApprox γ (palmFreeField γ refS X x ω) =
      bdryApprox γ (BdryExist.zField X R ω + ofFun (LogSing.logPot γ x) +
        ofFun (palmPsi γ x R X ω)) := by
  have havg : ∀ (k : ℕ) (z : ℂ), avgReg (palmFreeField γ refS X x ω) k z =
      avgReg (BdryExist.zField X R ω + ofFun (LogSing.logPot γ x) +
        ofFun (palmPsi γ x R X ω)) k z := by
    intro k z
    simp only [avgReg]
    congr 1
    funext n
    exact palmFreeField_fc_eq γ x R ω _ _
  funext k
  simp only [bdryApprox, havg]

theorem qBoundaryMeasure_palmFreeField_eq (γ x R : ℝ) (ω : Ω) :
    qBoundaryMeasure γ (palmFreeField γ refS X x ω) =
      qBoundaryMeasure γ (BdryExist.zField X R ω + ofFun (LogSing.logPot γ x) +
        ofFun (palmPsi γ x R X ω)) := by
  have key : ∀ y z : FieldSample, bdryApprox γ y = bdryApprox γ z →
      qBoundaryMeasure γ y = qBoundaryMeasure γ z := by
    intro y z h
    unfold qBoundaryMeasure
    rw [h]
  exact key _ _ (bdryApprox_palmFreeField_eq γ x R ω)

/-- The log-singular measure `m^x = |t − x|^{−γ²/2} ν_{Z_R}` off `x`. -/
def palmM (γ x R : ℝ) (X : Ω → FieldSample) (ω : Ω) : Measure ℝ :=
  ((qBoundaryMeasure γ (BdryExist.zField X R ω)).restrict {x}ᶜ).withDensity
    (fun t => ENNReal.ofReal (|t - x| ^ (-(γ * γ / 2))))

theorem gamma_lt_Qc_g3prt {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < Qc γ := by
  unfold Qc
  have : γ / 2 < 2 / γ := by rw [lt_div_iff₀ hγ]; nlinarith
  linarith

/-- **The boundary measure of the Palm field** (fixed root `x`, `|x| + 1 ≤ R`). -/
theorem ae_qBoundaryMeasure_palm [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : |x| + 1 ≤ R) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (palmFreeField γ refS X x ω) =
      (palmM γ x R X ω).withDensity
        (fun t => ENNReal.ofReal (Real.exp (γ / 2 * palmPsi γ x R X ω t))) := by
  filter_upwards [LogSing.ae_logSingularity hX hγ hγ2 R (gamma_lt_Qc_g3prt hγ hγ2) x
    (LogSing.p3bBound hX hγ hγ2 hR hx), RegSample.ae_isRegularSample hX] with ω h1 hreg
  have hZ : IsRegularSample (BdryExist.zField X R ω) := hreg.addConst' _
  have hY : IsRegularSample (BdryExist.zField X R ω + ofFun (LogSing.logPot γ x)) :=
    hZ.add_ofFun_log' γ x
  rw [qBoundaryMeasure_palmFreeField_eq γ x R ω,
    LocalRule.qBoundaryMeasure_add_ofFun' hY ⟨_, h1.1⟩ isOpen_univ
      (fun _ => mem_univ _) (continuous_palmPsi γ x R X ω).continuousOn, h1.2.1]
  rfl

/-- On subsets of `[−1, 1]`, `ν^x = e^{γ palmK/2} m^x`. -/
theorem ae_qBoundaryMeasure_palm_apply [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : |x| + 1 ≤ R) :
    ∀ᵐ ω ∂P, ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-1) 1 →
      qBoundaryMeasure γ (palmFreeField γ refS X x ω) A =
        ENNReal.ofReal (Real.exp (γ / 2 * palmK γ x R X ω)) * palmM γ x R X ω A := by
  filter_upwards [ae_qBoundaryMeasure_palm hX hγ hγ2 hR hx] with ω hω A hA hA1
  rw [hω, withDensity_apply _ hA, ← setLIntegral_const]
  refine setLIntegral_congr_fun hA fun t ht => ?_
  have h0 : Real.posLog ‖(t : ℂ)‖ = 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold Real.posLog
    refine max_eq_left (Real.log_nonpos (abs_nonneg _) ?_)
    exact abs_le.2 (hA1 ht)
  simp only [palmPsi, h0, mul_zero, zero_add]

end Thm18Asm
end QuantumZipper
