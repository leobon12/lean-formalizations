import QuantumZipper.Proofs.LQG.AtomlessUncond
import QuantumZipper.Proofs.Thm18.G3ConcreteField
import QuantumZipper.Proofs.LQG.FirstMoment

/-!
# G3 fidelity F3: the boundary measure of the Theorem 1.2 field `h`

Sheffield, arXiv:1012.4797, Theorem 1.8: the Palm point of the concrete G3 scheme is weighted by
`ν_h[−δ, 0]`, `h = 𝔥₀ + X − X(refS)` the Theorem 1.2 field (`normField`, `G3ConcreteField.lean`),
read through the drawn fields (`g3Mass`, `G3FidMass.lean`). This file identifies the *honest*
boundary measure of `h`, which is the input F3 (`handoff/G3.md`) needs:

**`æ_normField_logSingularity`**: a.s., the boundary approximations of `h` converge vaguely and

  `ν_h = (ν_{X − X(fc 0 1)}).restrict {0}ᶜ .withDensity (fun t => ofReal |t|)`,

i.e. `h`'s boundary measure is the length density `|t| dν` of the free field normalized at the
unit semicircle (which is exactly the normalization that `normField` uses), with no atom at `0`.

This is the `|t−s|^{−αγ/2}` boundary version of the log-singularity theorem of Duplantier–
Sheffield (arXiv:0808.1560 §6) / `LogSing.ae_logSingularity`, transported from
`zField X 1 + ofFun (logPot α 0)` to `normField γ X ω`: the two fields agree on every folded circle
(hence `avgReg`–wise, hence their boundary approximations are equal), because subtracting
`X ω (foldedCircle 0 1)` is precisely the `zField X 1` normalization and `h0rev (γ²) = logPot`
with `α = −2/γ`.

Consequences in this file:

* `qBoundaryMeasure_normField_restrict`: the measure-level statement above;
* `normField_Icc_ge`: for `ω` in the a.s. event and `δ > 0`,
  `ν_h(Icc (−δ) 0) ≥ ofReal (δ/2) · ν_1(Icc (−δ) (−δ/2))` with `ν_1 = ν_{zField X 1 ω}` — the
  length density `|t| ≥ δ/2` on the lower half of the interval;
* `lintegral_qBoundaryMeasure_normField_Icc_pos`: `0 < E ν_h[−δ, 0]` (F3's positivity), from the
  available free-field positivity `FirstMoment.lintegral_qBoundaryMeasure_Ioo_pos_X` and the
  scaling relation `ν_X = e^{(γ/2)X(fc 0 1)} • ν_{zField X 1}`
  (`Positivity.ae_qBoundaryMeasure_eq_smul_zField`).

Own bookkeeping (AGENT_GUIDE cost rule); the mathematics is `LogSing.ae_logSingularity`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open K3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- `addConst` adds the constant on a folded circle (a probability measure). -/
theorem addConst_fc (x : FieldSample) (c : ℝ) (d : ℂ) (ρ : ℝ) :
    addConst x c (foldedCircle d ρ) = x (foldedCircle d ρ) + c := by
  simp [addConst]

/-- `h0rev (γ²) = logPot (−2/γ) 0` (for `γ > 0`). -/
theorem h0rev_eq_logPot {γ : ℝ} (hγ : 0 < γ) (z : ℂ) :
    h0rev (γ ^ 2) z = LogSing.logPot (-2 / γ) 0 z := by
  simp only [h0rev, LogSing.logPot, Complex.ofReal_zero, sub_zero]
  rw [Real.sqrt_sq hγ.le]
  ring

/-- **`normField` is `zField X 1 + logPot` on folded circles.** -/
theorem normField_fc_eq {γ : ℝ} (hγ : 0 < γ) (ω : Ω) (d : ℂ) (ρ : ℝ) :
    normField γ X ω (foldedCircle d ρ) =
      (BdryExist.zField X 1 ω + ofFun (LogSing.logPot (-2 / γ) 0)) (foldedCircle d ρ) := by
  have h1 : ofFun (h0rev (γ ^ 2)) (foldedCircle d ρ) =
      ofFun (LogSing.logPot (-2 / γ) 0) (foldedCircle d ρ) := by
    simp only [ofFun]
    exact integral_congr_ae (Eventually.of_forall (h0rev_eq_logPot hγ))
  simp only [normField, BdryExist.zField, Pi.add_apply, addConst_fc, refS]
  rw [h1]
  ring

/-- **F3, honest boundary measure of `h`.** A.s. the boundary approximations of
`h = normField γ X` converge vaguely, the limit is `|t| dν` of the free field normalized at the
unit semicircle, and `ν_h` has no atom at `0`. -/
theorem ae_normField_logSingularity [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P,
      IsVagueLimitR (bdryApprox γ (normField γ X ω)) (qBoundaryMeasure γ (normField γ X ω)) ∧
        qBoundaryMeasure γ (normField γ X ω) =
          ((qBoundaryMeasure γ (BdryExist.zField X 1 ω)).restrict {0}ᶜ).withDensity
            (fun t => ENNReal.ofReal |t|) ∧
        qBoundaryMeasure γ (normField γ X ω) {0} = 0 := by
  have hα : (-2 / γ) < Qc γ := by
    have h1 : -2 / γ < 0 := div_neg_of_neg_of_pos (by norm_num) hγ
    have h2 : 0 < Qc γ := by unfold Qc; positivity
    linarith
  filter_upwards [LogSing.ae_logSingularity hX hγ hγ2 1 hα 0
    (LogSing.p3bBound hX hγ hγ2 one_pos (by simp))] with ω hω
  obtain ⟨hglob, heq, hs0, -⟩ := hω
  set W := BdryExist.zField X 1 ω + ofFun (LogSing.logPot (-2 / γ) 0) with hW
  have hfc : ∀ (d : ℂ) (ρ : ℝ), normField γ X ω (foldedCircle d ρ) = W (foldedCircle d ρ) :=
    fun d ρ => normField_fc_eq hγ ω d ρ
  have hbd : ∀ k, bdryApprox γ (normField γ X ω) k = bdryApprox γ W k := by
    intro k
    have havg : ∀ t : ℝ, avgReg (normField γ X ω) k (t : ℂ) = avgReg W k (t : ℂ) := by
      intro t
      simp only [avgReg]
      congr 1
      funext n
      exact hfc _ _
    simp only [bdryApprox]
    congr 1
    funext t
    rw [havg t]
  have hlim : IsVagueLimitR (bdryApprox γ (normField γ X ω)) (qBoundaryMeasure γ W) := by
    rw [funext hbd]
    exact hglob
  have hq : qBoundaryMeasure γ (normField γ X ω) = qBoundaryMeasure γ W :=
    qBoundaryMeasure_eq hlim
  have hexp : -(-2 / γ * γ / 2) = 1 := by
    field_simp
  have hlim' : IsVagueLimitR (bdryApprox γ (normField γ X ω))
      (qBoundaryMeasure γ (normField γ X ω)) := by
    rw [hq]
    exact hlim
  refine ⟨hlim', ?_, ?_⟩
  · rw [hq, heq]
    congr 1
    funext t
    rw [sub_zero, hexp, Real.rpow_one]
  · rw [hq]
    exact hs0

/-- The measure-level form of `ae_normField_logSingularity`. -/
theorem qBoundaryMeasure_normField_restrict [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P,
      qBoundaryMeasure γ (normField γ X ω) =
        ((qBoundaryMeasure γ (BdryExist.zField X 1 ω)).restrict {0}ᶜ).withDensity
          (fun t => ENNReal.ofReal |t|) :=
  (ae_normField_logSingularity hX hγ hγ2).mono fun _ h => h.2.1

/-- **Length density lower bound.** On `[−δ, 0]`, `ν_h` dominates `(δ/2)` times `ν_{zField X 1}`
on the lower half `(−δ, −δ/2)`, where the density `|t|` is at least `δ/2`. -/
theorem normField_Icc_ge [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal (δ / 2) *
          qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Ioo (-δ) (-(δ / 2))) ≤
        qBoundaryMeasure γ (normField γ X ω) (Icc (-δ) 0) := by
  filter_upwards [qBoundaryMeasure_normField_restrict hX hγ hγ2] with ω hω
  set ν' := (qBoundaryMeasure γ (BdryExist.zField X 1 ω)).restrict {0}ᶜ with hν'
  have hsub : Ioo (-δ) (-(δ / 2)) ⊆ Icc (-δ) 0 := fun t ht =>
    ⟨ht.1.le, (ht.2.trans (by linarith)).le⟩
  have hmem : ∀ t ∈ Ioo (-δ) (-(δ / 2)), t ∈ ({0} : Set ℝ)ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.2, hδ]
  rw [hω, withDensity_apply _ measurableSet_Icc]
  calc ENNReal.ofReal (δ / 2) *
        qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Ioo (-δ) (-(δ / 2)))
      = ENNReal.ofReal (δ / 2) * ν' (Ioo (-δ) (-(δ / 2))) := by
        rw [hν']
        congr 1
        rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 hmem]
    _ = ∫⁻ t, ENNReal.ofReal (δ / 2) ∂(ν'.restrict (Ioo (-δ) (-(δ / 2)))) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, mul_comm]
    _ ≤ ∫⁻ t, ENNReal.ofReal |t| ∂(ν'.restrict (Ioo (-δ) (-(δ / 2)))) := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' measurableSet_Ioo]
        exact Eventually.of_forall fun t ht => ENNReal.ofReal_le_ofReal (by
          rw [abs_of_nonpos (by linarith [ht.2, hδ])]
          linarith [ht.2])
    _ ≤ ∫⁻ t, ENNReal.ofReal |t| ∂(ν'.restrict (Icc (-δ) 0)) :=
        lintegral_mono_set hsub

/-- **F3, positivity for the honest field.** `0 < E ν_h[−δ, 0]`: the length density `|t|` of
`ν_h` is at least `δ/2` on `(−δ, −δ/2)`, and the free field's boundary measure has positive first
moment there (`FirstMoment.lintegral_qBoundaryMeasure_Ioo_pos_X`), the normalization factor
`e^{(γ/2)X(fc 0 1)}` of `Positivity.ae_qBoundaryMeasure_eq_smul_zField` being strictly positive. -/
theorem lintegral_qBoundaryMeasure_normField_Icc_pos [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) :
    0 < ∫⁻ ω, qBoundaryMeasure γ (normField γ X ω) (Icc (-δ) 0) ∂P := by
  have huv : -δ < -(δ / 2) := by linarith
  have hXpos : 0 < ∫⁻ ω, qBoundaryMeasure γ (X ω) (Ioo (-δ) (-(δ / 2))) ∂P :=
    FirstMoment.lintegral_qBoundaryMeasure_Ioo_pos_X hX hγ hγ2 huv
  have hsm := Positivity.ae_qBoundaryMeasure_eq_smul_zField (X := X) hX hγ hγ2 1
  set b : Ω → ℝ≥0∞ :=
    fun ω => qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Ioo (-δ) (-(δ / 2))) with hbdef
  set a : Ω → ℝ≥0∞ :=
    fun ω => ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 1))) with hadef
  have ha : Measurable a :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hX.measurable_coord (foldedCircle 0 1)).const_mul (γ / 2)))
  have hb : AEMeasurable b P :=
    (Measure.measurable_coe measurableSet_Ioo).comp_aemeasurable
      (LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (X := BdryExist.zField X 1)
        (fun μ => (measurable_pi_apply μ).comp (BdryExist.measurable_zField hX 1))
        (BdryExist.ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 1))
  have hkey : ∫⁻ ω, qBoundaryMeasure γ (X ω) (Ioo (-δ) (-(δ / 2))) ∂P =
      ∫⁻ ω, a ω * b ω ∂P :=
    lintegral_congr_ae (by
      filter_upwards [hsm] with ω hω
      simp only [hω, Measure.smul_apply, smul_eq_mul, hbdef, hadef])
  have hpos : 0 < ∫⁻ ω, a ω * b ω ∂P := hkey ▸ hXpos
  have hbpos : 0 < ∫⁻ ω, b ω ∂P := by
    refine pos_iff_ne_zero.2 fun h0 => absurd hpos (not_lt.2 ?_)
    have hbae : b =ᵐ[P] 0 := (lintegral_eq_zero_iff' hb).1 h0
    have hmul : AEMeasurable (fun ω => a ω * b ω) P := ha.aemeasurable.mul hb
    rw [show (∫⁻ ω, a ω * b ω ∂P) = 0 from by
      rw [lintegral_eq_zero_iff' hmul]
      filter_upwards [hbae] with ω hω
      simp [hω]]
  have hge := normField_Icc_ge hX hγ hγ2 hδ
  have hmono : ∫⁻ ω, ENNReal.ofReal (δ / 2) * b ω ∂P ≤
      ∫⁻ ω, qBoundaryMeasure γ (normField γ X ω) (Icc (-δ) 0) ∂P :=
    lintegral_mono_ae hge
  have hfac : ∫⁻ ω, ENNReal.ofReal (δ / 2) * b ω ∂P =
      ENNReal.ofReal (δ / 2) * ∫⁻ ω, b ω ∂P :=
    lintegral_const_mul' _ b ENNReal.ofReal_ne_top
  exact lt_of_lt_of_le (hfac ▸ ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by linarith)).ne' hbpos.ne')
    hmono

end Thm18Asm
end QuantumZipper
