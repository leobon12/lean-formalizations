import MatedCRTHarmonic.Canon.Data
import MatedCRTHarmonic.CellScaling.JointScalingOArea
import MatedCRTHarmonic.LQGCone.AreaBridge
import MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import MatedCRTHarmonic.CellScaling.JointScalingOClock
import MatedCRTHarmonic.IGLaw.OBase

/-!
# Whole-plane field's area-time evaluation for [18] Lemma 4.9

The frozen curve `η₀` uses the zero-cone clock. Here the normalized
whole-plane field and the independent Lebesgue-time curve are passed through
The existing Borel inverse-clock functional. This supplies the exact random
function needed for the whole-plane version of the point observable. A proof
that this function has a continuous curve version is still required before
the `C(ℝ, ℂ)`-valued local geometry API can be applied.
-/

set_option autoImplicit false
-- The canonical field and coupling carry large reducible interfaces.
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTPort

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The normalized whole-plane field remains independent of the full
imaginary-geometry data, including the random additive phase. -/
theorem indepFun_normalizedWholePlane_IGdata
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (fun ω => Canon.normalizeWholePlane (X₀ ω))
      (fun ω => (hIG₀ ω, U ω)) P := by
  let pick : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) ×
      MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → MatedCRT.Field :=
    fun q => q.2.2.2.1
  have hp : Measurable pick :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))
  have hn : Measurable Canon.normalizeWholePlane := by
    apply LQGMetric.DFGPS.L219.measurable_addConst_of
    · exact measurable_id
    · exact (LQGMetric.measurable_circleAvg_left 1 0).neg
  simpa only [Function.comp_def, id_eq, pick, Canon.normalizeWholePlane] using
    (D.indep_curve.symm.comp (hn.comp hp) measurable_id)

/-- In particular, the whole-plane field used in Lemma 4.9 is independent of
The actual Lebesgue-time SLE curve. -/
theorem indepFun_normalizedWholePlane_ηL
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (fun ω => Canon.normalizeWholePlane (X₀ ω)) ηL P := by
  let pick : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) ×
      MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → MatedCRT.Field :=
    fun q => q.2.2.2.1
  have hp : Measurable pick :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))
  have hn : Measurable Canon.normalizeWholePlane := by
    apply LQGMetric.DFGPS.L219.measurable_addConst_of
    · exact measurable_id
    · exact (LQGMetric.measurable_circleAvg_left 1 0).neg
  simpa only [Function.comp_def, id_eq, pick, Canon.normalizeWholePlane] using
    ((IGLaw.IsMatingOfTreesCoupling.indepFun_ηL_coneData D).comp
      measurable_id (hn.comp hp)).symm

/-- Area-time evaluation of the *normalized whole-plane* GFF along `ηL`.
Its codomain is the product-measurable function space, pending continuity. -/
def wholePlaneQuantumPath
    (γ : ℝ) (X₀ : Ω → MatedCRT.Field) (ηL : Ω → C(ℝ, ℂ))
    (ω : Ω) (t : ℝ) : ℂ :=
  CellScaling.JointScalingO.parEval γ (Canon.normalizeWholePlane (X₀ ω)) (ηL ω) t

theorem measurable_wholePlaneQuantumPath
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable (wholePlaneQuantumPath γ X₀ ηL) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (CellScaling.JointScalingO.measurable_parEval γ t).comp
    ((Canon.measurable_normalizedWholePlane D).prodMk D.measurable_curves.1)

/-- The whole-plane point observation keeps the imaginary-geometry phase in
The second circle average. The path coordinate is the measurable area-time
function until a continuous version is constructed. -/
def wholePlaneConditioningData
    (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ)
    (ηL : Ω → C(ℝ, ℂ)) (δ : ℝ) (z : ℂ) (ω : Ω) :
    (ℝ → ℂ) × (ℝ × ℝ) :=
  (wholePlaneQuantumPath γ X₀ ηL ω,
    (LQGMetric.circleAvg (Canon.normalizeWholePlane (X₀ ω)) δ z,
      LQGMetric.circleAvg (hIG₀ ω) δ z + U ω))

theorem aemeasurable_wholePlaneConditioningData
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (δ : ℝ) (z : ℂ) :
    AEMeasurable (wholePlaneConditioningData γ X₀ hIG₀ U ηL δ z) P := by
  have hmain : Measurable fun ω =>
      LQGMetric.circleAvg (Canon.normalizeWholePlane (X₀ ω)) δ z :=
    (LQGMetric.measurable_circleAvg_left δ z).comp
      (Canon.measurable_normalizedWholePlane D)
  have hphase : AEMeasurable U P := Canon.aemeasurable_phase D hγ
  have hIG : AEMeasurable (fun ω =>
      LQGMetric.circleAvg (hIG₀ ω) δ z + U ω) P :=
    ((LQGMetric.measurable_circleAvg_left δ z).comp
      D.igField.1.1.measurable).aemeasurable.add hphase
  exact (measurable_wholePlaneQuantumPath D).aemeasurable.prodMk
    (hmain.aemeasurable.prodMk hIG)

/-- The second conditioning coordinate is the actual IG field `hIG₀ + U`,
not the normalized GFF average alone. -/
theorem ae_IGAverage_eq_fieldWithPhase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ∀ᵐ ω ∂P,
      (wholePlaneConditioningData γ X₀ hIG₀ U ηL δ z ω).2.2 =
        LQGMetric.circleAvg (LQGMetric.addConst (hIG₀ ω) (U ω)) δ z := by
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst D.igField.1.1 z hδ]
    with ω hω
  exact (hω (U ω)).symm

/-- On the whole-plane GFF's GMC event, the Borel signed clock reads its
actual selected area on a curve segment. The statement holds at all real
times on one probability-one event. -/
theorem ae_wholePlane_signedClock_eq_selectedArea
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      CellScaling.JointScalingO.clock γ (Canon.normalizeWholePlane (X₀ ω)) (ηL ω) t =
        if 0 ≤ t then
          (CellScaling.lqgArea γ (Canon.normalizeWholePlane (X₀ ω))
            ((ηL ω) '' Icc 0 t)).toReal
        else -((CellScaling.lqgArea γ (Canon.normalizeWholePlane (X₀ ω))
            ((ηL ω) '' Icc t 0)).toReal) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hh := Canon.normalizedWPGFF_of_coupling D
  filter_upwards [ConeArea4.ae_areaGood_univ hh.1 hγ.1 hγ.2] with ω hgood
  intro t
  have hv : CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (Canon.normalizeWholePlane (X₀ ω)))
      (CellScaling.lqgArea γ (Canon.normalizeWholePlane (X₀ ω))) := by
    rw [LQGCone.lqgArea_eq_qAreaC]
    exact LQGCone.vagueLimitC_iff_vagueLimitOn_univ.mpr
      (ConeArea.isVagueLimitOn_qAreaC hgood.1)
  unfold CellScaling.JointScalingO.clock
  rw [CellScaling.JointScalingO.areaSeg_eq γ hv]
  split_ifs with ht
  · rw [uIcc_of_le ht]
  · rw [uIcc_of_ge (le_of_not_ge ht)]

end MatedCRTHarmonic.GMS4cS

