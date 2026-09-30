import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.LQG.Positivity
import QuantumZipper.Proofs.LQG.WedgeBdryInfStmt

/-!
# WEDGE-BDRY 4 (b), 1/3: the weighted boundary integral of `X + α(−log)`

`InfWeight γ β x` is the weighted mass `∫_{[1,∞)} t^{−β} dν_x` of the boundary measure of `x`
(an `ℝ≥0∞`-valued integral, so the value `⊤` means infinite mass). This file proves the basic
API (`measurableSet_infWeight`, `infWeight_reconstruct`, `infWeight_addConst`: the weight is
invariant under adding a constant because the boundary measure is multiplied by a positive
scalar, rule (5.1)) and the step

* `ae_infWeight_logSing`: for a free field `X` and `α < α'' < Q`, almost surely
  `∫_{[1,∞)} t^{−((α''−α)γ/2)} dν_{X + α(−log‖·‖)} = ⊤`,

obtained from `WedgeBdryFreeInfStmt` (item 4 (a), the free-field statement with weight
`t^{−α''γ/2}`) through the log-singularity identity
`ν_{X + α(−log)} = |t|^{−αγ/2} ν_{X}` restricted to `ℝ∖{0}` (`LogSing.ae_logSingularity`,
`Positivity.ae_qBoundaryMeasure_eq_smul_zField`); on `[1,∞)` away from `0` the two weights
multiply to `t^{−α''γ/2}`. Source: Sheffield, arXiv:1012.4797, §1.6 (the boundary measure
transforms by the (5.1) rule `e^{γφ/2}` for continuous `φ`); the paper's infinite-mass statement
is on p. 21.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace WedgeBdry

open GaussTK (norm_ofReal')

/-- The weight `t ↦ t^{−β}`, as an `ℝ≥0∞`-valued function on `ℝ`. -/
def infWeightFn (β : ℝ) : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (-β))

theorem measurable_infWeightFn (β : ℝ) : Measurable (infWeightFn β) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)

/-- `t^{−β}`-weighted mass of the boundary measure on `[1,∞)`; `⊤` means infinite mass. -/
def InfWeight (γ β : ℝ) (x : FieldSample) : Prop :=
  ∫⁻ t in Ici (1 : ℝ), infWeightFn β t ∂qBoundaryMeasure γ x = ⊤

/-- The weighted infinite mass together with goodness: the measurable event of the
coupling argument (goodness is a conjunct so that the event is a measurable set of samples,
as for `BReg`). -/
def InfGood (γ β : ℝ) (x : FieldSample) : Prop := InfWeight γ β x ∧ IsLQGGood γ x

/-- `InfGood` is a measurable event of the field sample. -/
theorem measurableSet_infGood (γ β : ℝ) : MeasurableSet {x : FieldSample | InfGood γ β x} := by
  classical
  set g : FieldSample → Measure ℝ :=
    fun x => if IsLQGGood γ x then qBoundaryMeasure γ x else 0 with hg_def
  have hg : Measurable g := GoodMeas.measurable_qBoundaryMeasure_global γ
  have hM : Measurable fun ν : Measure ℝ => ∫⁻ t in Ici (1 : ℝ), infWeightFn β t ∂ν := by
    have h : (fun ν : Measure ℝ => ∫⁻ t in Ici (1 : ℝ), infWeightFn β t ∂ν) =
        fun ν : Measure ℝ => ∫⁻ t, (Ici (1 : ℝ)).indicator (infWeightFn β) t ∂ν := by
      funext ν
      exact (lintegral_indicator measurableSet_Ici _).symm
    rw [h]
    exact Measure.measurable_lintegral ((measurable_infWeightFn β).indicator measurableSet_Ici)
  have hcomp : Measurable fun x : FieldSample => ∫⁻ t in Ici (1 : ℝ), infWeightFn β t ∂(g x) :=
    hM.comp hg
  have he : {x : FieldSample | InfGood γ β x} = {x | IsLQGGood γ x} ∩
      {x | ∫⁻ t in Ici (1 : ℝ), infWeightFn β t ∂(g x) = ⊤} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, InfGood]
    constructor
    · rintro ⟨hI, hG⟩
      refine ⟨hG, ?_⟩
      simp only [hg_def, if_pos hG]
      exact hI
    · rintro ⟨hG, hI⟩
      refine ⟨?_, hG⟩
      simp only [hg_def, if_pos hG] at hI
      exact hI
  rw [he]
  exact (GoodMeas.measurableSet_isLQGGood γ).inter (hcomp (measurableSet_singleton ⊤))

theorem infWeight_reconstruct (γ β : ℝ) (x : FieldSample) :
    InfWeight γ β (Factorization.reconstruct (Factorization.coords x)) ↔ InfWeight γ β x := by
  simp only [InfWeight, qBoundaryMeasure_reconstruct]

/-- Adding a constant multiplies the boundary measure by the positive scalar
`e^{γc/2}` (rule (5.1)), which preserves `InfWeight`. -/
theorem infWeight_addConst {γ β : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) (c : ℝ) :
    InfWeight γ β (addConst x c) ↔ InfWeight γ β x := by
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * c / 2)) with hr
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul : ∀ X : ℝ≥0∞, r * X = ⊤ ↔ X = ⊤ := by
    intro X
    rw [ENNReal.mul_eq_top]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h hrt
    · exact fun h => Or.inl ⟨hr0, h⟩
  have h : qBoundaryMeasure γ (addConst x c) = r • qBoundaryMeasure γ x := by
    rw [hr]; exact GoodSample.qBoundaryMeasure_addConst hx c
  simp only [InfWeight]
  rw [h, setLIntegral_smul_measure]
  exact hmul _

/-- Integrating against a `withDensity` measure, restricted to `[1,∞)`. -/
theorem lintegral_Ici_withDensity {ν : Measure ℝ} {g f : ℝ → ℝ≥0∞} (hg : Measurable g)
    (hf : Measurable f) :
    ∫⁻ t in Ici (1 : ℝ), f t ∂(ν.withDensity g) = ∫⁻ t in Ici (1 : ℝ), g t * f t ∂ν := by
  rw [MeasureTheory.restrict_withDensity measurableSet_Ici]
  exact lintegral_withDensity_eq_lintegral_mul (ν.restrict (Ici (1 : ℝ))) hg hf

/-- The measurable density `|t|^{−αγ/2}` of the log singularity at `0`. -/
theorem measurable_absRpow (a : ℝ) : Measurable fun t : ℝ => ENNReal.ofReal (|t| ^ a) :=
  ENNReal.measurable_ofReal.comp (continuous_abs.measurable.pow_const _)

/-- **WEDGE-BDRY 4 (b), step 1.** For a free field `X` and `α < α'' < Q`, almost surely
`∫_{[1,∞)} t^{−((α''−α)γ/2)} dν_{X + α(−log‖·‖)} = ⊤`. -/
theorem ae_infWeight_logSing (hInf : WedgeBdryFreeInfStmt) {γ α α'' : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα : α < α'') (hα'' : α'' < Qc γ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → FieldSample)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, InfWeight γ ((α'' - α) * γ / 2) (X ω + ofFun fun z => α * -Real.log ‖z‖) := by
  have hbase : ∀ᵐ ω ∂P, ∫⁻ t in Ici (1 : ℝ), infWeightFn (α'' * γ / 2) t
      ∂qBoundaryMeasure γ (X ω) = ⊤ := hInf P X hX γ hγ hγ2 α'' hα''
  have hls := LogSing.ae_logSingularity hX hγ hγ2 1 (hα.trans hα'') 0
    (LogSing.p3bBound hX hγ hγ2 one_pos (by simp))
  have hsm := Positivity.ae_qBoundaryMeasure_eq_smul_zField hX hγ hγ2 1
  have hgood := LogSingGood.logSingGoodAS_holds hγ hγ2 (hα.trans hα'') Ω _ P X inferInstance hX
  filter_upwards [hbase, hls, hsm, hgood] with ω hbaseω hlsω hsmω hgoodω
  obtain ⟨-, hνW0, -, -⟩ := hlsω
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 1))) with hr
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmω' : qBoundaryMeasure γ (X ω) = r • qBoundaryMeasure γ (BdryExist.zField X 1 ω) := hsmω
  have hνZ : qBoundaryMeasure γ (BdryExist.zField X 1 ω) = r⁻¹ • qBoundaryMeasure γ (X ω) := by
    rw [hsmω', smul_smul, ENNReal.inv_mul_cancel hr0 hrt, one_smul]
  have hlog : LogSing.logPot α 0 = fun z : ℂ => α * -Real.log ‖z‖ := by
    funext z; simp [LogSing.logPot]
  -- the weighted integral of `ν_{zField + logPot}`
  have hWinf : InfWeight γ ((α'' - α) * γ / 2)
      (BdryExist.zField X 1 ω + ofFun (LogSing.logPot α 0)) := by
    have hνW : qBoundaryMeasure γ (BdryExist.zField X 1 ω + ofFun (LogSing.logPot α 0)) =
        ((qBoundaryMeasure γ (BdryExist.zField X 1 ω)).restrict {0}ᶜ).withDensity
          (fun t => ENNReal.ofReal (|t - 0| ^ (-(α * γ / 2)))) := hνW0
    have hdens : (fun t : ℝ => ENNReal.ofReal (|t - 0| ^ (-(α * γ / 2))))
        = fun t : ℝ => ENNReal.ofReal (|t| ^ (-(α * γ / 2))) := by
      funext t; simp
    have hprod : ∀ t ∈ Ici (1 : ℝ), ENNReal.ofReal (|t| ^ (-(α * γ / 2))) *
        infWeightFn ((α'' - α) * γ / 2) t = infWeightFn (α'' * γ / 2) t := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      show ENNReal.ofReal (|t| ^ (-(α * γ / 2))) * ENNReal.ofReal (t ^ (-((α'' - α) * γ / 2)))
        = ENNReal.ofReal (t ^ (-(α'' * γ / 2)))
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg t) _), abs_of_nonneg ht0.le,
        ← Real.rpow_add ht0,
        show -(α * γ / 2) + -((α'' - α) * γ / 2) = -(α'' * γ / 2) by ring]
    simp only [InfWeight]
    rw [hνW, hdens, hνZ]
    rw [lintegral_Ici_withDensity (measurable_absRpow (-(α * γ / 2))) (measurable_infWeightFn _)]
    rw [Measure.restrict_restrict_of_subset (show Ici (1 : ℝ) ⊆ {0}ᶜ from fun t ht => by
      simp only [mem_compl_iff, mem_singleton_iff]
      have ht1 : (1 : ℝ) ≤ t := ht
      linarith)]
    rw [setLIntegral_smul_measure, setLIntegral_congr_fun measurableSet_Ici hprod, hbaseω]
    exact ENNReal.mul_top (ENNReal.inv_ne_zero.2 hrt)
  -- `X ω + α(−log)` is the log-singular field plus a constant
  have e2 : BdryExist.zField X 1 ω + ofFun (LogSing.logPot α 0) =
      addConst (X ω + ofFun fun z => α * -Real.log ‖z‖) (-(X ω (foldedCircle 0 1))) := by
    funext μ
    simp only [BdryExist.zField, addConst, Pi.add_apply, hlog]
    ring
  have e1 : (X ω + ofFun fun z => α * -Real.log ‖z‖) =
      addConst (BdryExist.zField X 1 ω + ofFun (LogSing.logPot α 0))
        (X ω (foldedCircle 0 1)) := by
    rw [e2]; funext μ; simp only [addConst, Pi.add_apply]; ring
  have hWg : IsLQGGood γ (BdryExist.zField X 1 ω + ofFun (LogSing.logPot α 0)) :=
    e2 ▸ hgoodω.addConst _
  rw [e1, infWeight_addConst hWg (X ω (foldedCircle 0 1))]
  exact hWinf

end WedgeBdry

end QuantumZipper
