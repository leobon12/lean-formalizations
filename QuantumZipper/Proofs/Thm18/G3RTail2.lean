import QuantumZipper.Proofs.Thm18.G3RTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the region-1 tail node, proof

See `G3RTail` for the argument and sources. Here:
* `ae_g3pShift_good`: a.s., for every continuous `f`, the boundary measure of the shifted
  field `h + g3wProf γ + f` exists with the usual regularity and equals `e^{γ f/2}` times that of
  `h + g3wProf γ` (Duplantier–Sheffield (5.1), `LocalRule.isVagueLimitR_add_ofFun`);
* `null_shift_of_null`: Cameron–Martin transfer of the null event `A ∩ O⁺` to the shifted field;
* the conclusion `g3TRegion1TailStmt_holds` is in `G3RTail3`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- **The boundary measure of the continuously shifted field** (a.s., all `f` at once). -/
theorem ae_g3pShift_good {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ f : ℂ → ℝ, Continuous f →
      IsVagueLimitR (bdryApprox γ (g3pField γ (g3wProf γ) ω + ofFun f))
        (qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω + ofFun f)) ∧
      (∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ (g3wProf γ) ω + ofFun f) k)) ∧
      (∀ s, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω + ofFun f) {s} = 0) ∧
      qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω + ofFun f) =
        (qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω)).withDensity
          fun t => ENNReal.ofReal (Real.exp (γ / 2 * f t)) := by
  filter_upwards [LogSing.ae_logSingularity gffBase.gff hγ hγ2 1 (αC_lt_Qc hγ hγ2) 0
      (LogSing.p3bBound gffBase.gff hγ hγ2 one_pos (by simp)),
    RegSample.ae_isRegularSample gffBase.gff,
    AtomlessUncond.ae_noAtoms_zField' gffBase.gff hγ hγ2 1] with ω hω hreg hat f hf
  obtain ⟨hglob, hform, -⟩ := hω
  set Y := BdryExist.zField X₀ 1 ω + ofFun (LogSing.logPot (αC γ) 0) with hYdef
  have hY : IsRegularSample Y := (hreg.addConst' _).add_ofFun_log' _ 0
  have hb : bdryApprox γ (g3pField γ (g3wProf γ) ω + ofFun f) = bdryApprox γ (Y + ofFun f) := by
    funext k
    have e : ∀ z, avgReg (g3pField γ (g3wProf γ) ω + ofFun f) k z = avgReg (Y + ofFun f) k z :=
      fun z => by
        unfold avgReg
        simp only [Pi.add_apply]
        simp_rw [g3pField_fc_eq_Lf hγ ω, hYdef, logPot_zero_eq_Lf]
    simp only [bdryApprox, e]
  have hvB := LocalRule.isVagueLimitR_add_ofFun hY hglob isOpen_univ (fun t => mem_univ _)
    (φ := f) hf.continuousOn
  rw [← hb] at hvB
  have hqB := qBoundaryMeasure_eq hvB
  have hqh : qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) = qBoundaryMeasure γ Y := by
    have hvh : IsVagueLimitR (bdryApprox γ (g3pField γ (g3wProf γ) ω)) (qBoundaryMeasure γ Y) := by
      rw [bdryApprox_g3pField hγ ω]; exact hglob
    exact qBoundaryMeasure_eq hvh
  refine ⟨hqB ▸ hvB, fun k => ?_, fun s => ?_, ?_⟩
  · rw [hb]; exact LogSing.isFiniteMeasureOnCompacts_bdryApprox (hY.add_ofFun' hf.continuousOn) γ k
  · rw [hqB]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [hform]
    exact withDensity_absolutelyContinuous _ _
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self (hat.measure_singleton s))
  · rw [hqB, hqh]

/-- A.s. the boundary measure of `h + g3wProf γ` charges every interval avoiding `0`. -/
theorem ae_g3pField_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ a b : ℝ, a < b → b < 0 →
      0 < qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Ioo a b) := by
  filter_upwards [ae_g3pField_good hγ hγ2,
    Positivity.ae_forall_pos_qBoundaryMeasure_Ioo gffBase.gff hγ hγ2,
    Positivity.ae_qBoundaryMeasure_eq_smul_zField gffBase.gff hγ hγ2 1] with ω hC hpos hsm a b hab hb0
  obtain ⟨-, -, -, hform⟩ := hC
  have hZ : 0 < qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Ioo a b) := by
    have h := hpos a b hab
    rw [hsm, Measure.smul_apply, smul_eq_mul] at h
    exact pos_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [hform]
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (|t - 0| ^ (-(αC γ * γ / 2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have h0' := (withDensity_apply_eq_zero hmeas).1 h0
  have hsub : Ioo a b ⊆ {t | ENNReal.ofReal (|t - 0| ^ (-(αC γ * γ / 2))) ≠ 0} ∩ Ioo a b :=
    fun t ht => ⟨by
      have : 0 < |t - 0| := by rw [sub_zero, abs_pos]; exact (ht.2.trans hb0).ne
      exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos this _)).ne', ht⟩
  have h1 := measure_mono_null hsub h0'
  rw [Measure.restrict_apply measurableSet_Ioo] at h1
  have h2 : Ioo a b ∩ {0}ᶜ = Ioo a b := inter_eq_left.2 fun t ht h => by
    rw [mem_singleton_iff] at h; exact absurd (h ▸ ht.2) (not_lt.2 hb0.le)
  rw [h2] at h1
  exact hZ.ne' h1

end R18
end QuantumZipper
