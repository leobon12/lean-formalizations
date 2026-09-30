import QuantumZipper.Proofs.Thm18.R18G3TFid
import QuantumZipper.Proofs.Thm18.R18G3TCM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T: honest boundary lengths of scheme `B` (cut-off profile)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71, p. 72 (Remark 5.7: adding a smooth
function changes the boundary measure by a bounded density). For scheme `B` (profile
`g3wCut γ η`, smooth with compact support, `R18G3TCM.contDiff_g3wCut`):

* `ae_g3pBField_good`: a.s., for every `η > 0`, the shifted field has a boundary measure (the
  honest one `ν_h` of `normField` times `e^{(γ/2) g3wCut}`, `LocalRule.isVagueLimitR_add_ofFun`),
  finite approximations and no atoms;
* `ae_g3pBFid_sets` (F2-B), `g3pBZ_pos_lt_top` (F3-B): `g3pZ = E ν_B[−δ, 0] ∈ (0, ∞)`, from the
  free-scheme facts (`lintegral_qBoundaryMeasure_normField_Icc_pos`, `g3HonestFinStmt_main`)
  and the bounded density.

Own bookkeeping on top of the cited lemmas (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The density of scheme `B` against the honest measure. -/
abbrev cutDens (γ η : ℝ) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ / 2 * g3wCut γ η t))

theorem measurable_cutDens (γ η : ℝ) (hη : 0 < η) : Measurable (cutDens γ η) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    ((contDiff_g3wCut γ η hη).continuous.measurable.comp Complex.measurable_ofReal)))

/-- **A.s. input for scheme `B`**, simultaneously for all cut-offs. -/
theorem ae_g3pBField_good {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ η : ℝ, 0 < η →
      IsVagueLimitR (bdryApprox γ (g3pField γ (g3wCut γ η) ω))
        (qBoundaryMeasure γ (g3pField γ (g3wCut γ η) ω)) ∧
      (∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ (g3wCut γ η) ω) k)) ∧
      (∀ s, qBoundaryMeasure γ (g3pField γ (g3wCut γ η) ω) {s} = 0) ∧
      qBoundaryMeasure γ (g3pField γ (g3wCut γ η) ω) =
        (qBoundaryMeasure γ (normField γ X₀ ω)).withDensity (cutDens γ η) := by
  have hαQ : -(2 / γ) < Qc γ := by
    unfold Qc; have : 0 < 2 / γ := by positivity
    linarith [div_pos hγ (show (0 : ℝ) < 2 by norm_num)]
  filter_upwards [LogSing.ae_logSingularity gffBase.gff hγ hγ2 1 hαQ 0
      (LogSing.p3bBound gffBase.gff hγ hγ2 one_pos (by simp)),
    RegSample.ae_isRegularSample gffBase.gff,
    AtomlessUncond.ae_noAtoms_zField' gffBase.gff hγ hγ2 1] with ω hω hreg hat η hη
  obtain ⟨hglob, hform, -⟩ := hω
  set Y := BdryExist.zField X₀ 1 ω + ofFun (LogSing.logPot (-(2 / γ)) 0) with hYdef
  have hY : IsRegularSample Y := (hreg.addConst' _).add_ofFun_log' _ 0
  have hf : Continuous (g3wCut γ η) := (contDiff_g3wCut γ η hη).continuous
  have hbB : bdryApprox γ (g3pField γ (g3wCut γ η) ω) = bdryApprox γ (Y + ofFun (g3wCut γ η)) := by
    funext k
    have e : ∀ z, avgReg (g3pField γ (g3wCut γ η) ω) k z =
        avgReg (Y + ofFun (g3wCut γ η)) k z := fun z => by
      unfold avgReg
      simp only [g3pField, Pi.add_apply, G3Fid.normField_fc hγ, hYdef]
    simp only [bdryApprox, e]
  have hvB := LocalRule.isVagueLimitR_add_ofFun hY hglob isOpen_univ (fun t => mem_univ _)
    (φ := g3wCut γ η) hf.continuousOn
  rw [← hbB] at hvB
  have hqB := qBoundaryMeasure_eq hvB
  have hqh : qBoundaryMeasure γ (normField γ X₀ ω) = qBoundaryMeasure γ Y := by
    have hvh : IsVagueLimitR (bdryApprox γ (normField γ X₀ ω)) (qBoundaryMeasure γ Y) := by
      rw [G3Fid.bdryApprox_normField hγ ω]; exact hglob
    exact qBoundaryMeasure_eq hvh
  refine ⟨hqB ▸ hvB, fun k => ?_, fun s => ?_, ?_⟩
  · rw [hbB]; exact LogSing.isFiniteMeasureOnCompacts_bdryApprox (hY.add_ofFun' hf.continuousOn) γ k
  · rw [hqB]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [hform]
    exact withDensity_absolutelyContinuous _ _
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self (hat.measure_singleton s))
  · rw [hqB, hqh]

/-- **F2-B (sets).** -/
theorem ae_g3pBFid_sets {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      (∀ s ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4),
        (g3pν₁ γ (g3wCut γ i.η) i ω + g3pν₀ γ (g3wCut γ i.η) i ω) s =
          qBoundaryMeasure γ (g3pField γ (g3wCut γ i.η) ω) s) ∧
      (∀ s ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4),
        (g3pν₀ γ (g3wCut γ i.η) i ω + g3pν₂ γ (g3wCut γ i.η) i ω) s =
          qBoundaryMeasure γ (g3pField γ (g3wCut γ i.η) ω) s) := by
  filter_upwards [ae_g3pBField_good hγ hγ2] with ω hω i
  obtain ⟨hv, hfin, hat, -⟩ := hω i.η i.hη
  have h := g3pFid2_of hγ (g3wCut γ i.η) i ω hv hfin hat
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [← Measure.restrict_eq_self _ hs, h.1, Measure.restrict_eq_self _ hs]
  · rw [← Measure.restrict_eq_self _ hs, h.2, Measure.restrict_eq_self _ hs]

/-- `g3pZ = E ν_B[−δ, 0]` for scheme `B`. -/
theorem g3pBZ_eq_honest {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    g3pZ γ (g3wCut γ i.η) i =
      ∫⁻ ω, qBoundaryMeasure γ (g3pField γ (g3wCut γ i.η) ω) (Icc (-i.δ) 0) ∂gffBase.P := by
  rw [g3pZ_eq_lintegral_g3pMass]
  exact lintegral_congr_ae ((ae_g3pBFid_sets hγ hγ2).mono fun ω hω =>
    (hω i).1 _ (Icc_neg_subset_win i (by linarith [i.hη])))

/-- **F3-B.** The Palm mass of scheme `B` is positive and finite. -/
theorem g3pBZ_pos_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    0 < g3pZ γ (g3wCut γ i.η) i ∧ g3pZ γ (g3wCut γ i.η) i < ⊤ := by
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  obtain ⟨M, hM⟩ := (contDiff_g3wCut γ i.η i.hη).continuous.bounded_above_of_compact_support
    (hasCompactSupport_g3wCut γ i.η)
  have hup : ∀ t, cutDens γ i.η t ≤ ENNReal.ofReal (Real.exp (γ / 2 * M)) := fun t => by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 ((Real.norm_eq_abs _).symm ▸ hM (t : ℂ))).2
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hlo : ∀ t, ENNReal.ofReal (Real.exp (γ / 2 * -M)) ≤ cutDens γ i.η t := fun t => by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 ((Real.norm_eq_abs _).symm ▸ hM (t : ℂ))).1
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hmd := measurable_cutDens γ i.η i.hη
  have hae_up : ∀ᵐ ω ∂gffBase.P,
      qBoundaryMeasure γ (g3pField γ (g3wCut γ i.η) ω) (Icc (-i.δ) 0) ≤
        ENNReal.ofReal (Real.exp (γ / 2 * M)) *
          qBoundaryMeasure γ (normField γ X₀ ω) (Icc (-i.δ) 0) := by
    filter_upwards [ae_g3pBField_good hγ hγ2] with ω hω
    rw [(hω i.η i.hη).2.2.2, withDensity_apply _ measurableSet_Icc, ← setLIntegral_const]
    exact setLIntegral_mono measurable_const fun t _ => hup t
  have hae_lo : ∀ᵐ ω ∂gffBase.P,
      ENNReal.ofReal (Real.exp (γ / 2 * -M)) *
          qBoundaryMeasure γ (normField γ X₀ ω) (Icc (-i.δ) 0) ≤
        qBoundaryMeasure γ (g3pField γ (g3wCut γ i.η) ω) (Icc (-i.δ) 0) := by
    filter_upwards [ae_g3pBField_good hγ hγ2] with ω hω
    rw [(hω i.η i.hη).2.2.2, withDensity_apply _ measurableSet_Icc, ← setLIntegral_const]
    exact setLIntegral_mono hmd fun t _ => hlo t
  rw [g3pBZ_eq_honest hγ hγ2 i]
  constructor
  · refine lt_of_lt_of_le ?_ (lintegral_mono_ae hae_lo)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (lintegral_qBoundaryMeasure_normField_Icc_pos gffBase.gff hγ hγ2 hδ).ne'
  · refine lt_of_le_of_lt (lintegral_mono_ae hae_up) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (g3HonestFinStmt_main i hγ hγ2)

end R18
end QuantumZipper
