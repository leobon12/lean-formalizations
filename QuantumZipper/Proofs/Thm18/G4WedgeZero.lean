import QuantumZipper.Proofs.Thm18.G4Zero
import QuantumZipper.Proofs.Zipper.E6Read
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.LQG.CanonicalGood

/-!
# G4-WEDGE (3): `WedgeZeroRegStmt` for the `(γ − 2/γ)`-wedge

Theorem 1.8, clause (3) at `t = 0` (Sheffield, arXiv:1012.4797, §1.6) needs that the wedge sample
`Y` is in canonical description with raw = regularized data. `WedgeZeroRegStmt` (G4Zero) has three
parts; here:

* **scale** (`ae_scaleParam_eq_one_of_isQuantumWedge`, unconditional): a.s. `scaleParam γ Y = 1`.
  For the reference canonical field `canonical γ W` the unit half-disc has area `1` and, by the
  strict monotonicity of the area profile of `W` (`WedgeCan4.ae_hasAreaProfile_wedgeField_of_inputs`:
  the area charges every open subset of `ℍ`), every smaller half-disc has area `< 1`. This event
  (read at rational radii) is a measurable event of the coordinates, so it transfers to `Y`
  through the law identity (`WedgeBdry.ae_of_fieldLawFull_eq`); on it `scaleParam = 1` exactly
  (the defining `sInf` is attained at `1`).
* **pairings** (`ae_pairTest_eq_pairRaw_of_isQuantumWedge`, unconditional): the regularized
  pairing of the reference canonical wedge equals the raw one
  (`S5.FieldLaw.Raw.ae_pairRaw_eq_pairTest_wedge`), and the pairing event is an event of
  `fieldLawFull` (as in `E6.readableBy_of_fieldLawFull_eq`).
* **circles**: from the circle regularity of the reference canonical wedge
  `E6.WedgeRefCircleRegStmt γ (γ − 2/γ)` (open node, task WEDGE-CREG), via
  `E6.readableBy_regG_of_isQuantumWedge`.

`wedgeZeroRegStmt_of_circ : (∀ γ ∈ (0,2), E6.WedgeRefCircleRegStmt γ (γ − 2/γ)) → WedgeZeroRegStmt`.

Own elementary arguments (measurable-event bookkeeping; the paper uses the canonical description
(1.8) without comment).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

open AreaProfile

/-! ## 1. The scale event -/

/-- Good, unit area in `B(0,1) ∩ ℍ`, and area `< 1` in `B(0,q) ∩ ℍ` for every rational `q < 1`. -/
def ZeroScaleEv (γ : ℝ) (x : FieldSample) : Prop :=
  IsLQGGood γ x ∧ qAreaMeasure γ x (Metric.ball 0 1 ∩ H) = 1 ∧
    ∀ q : ℚ, (q : ℝ) < 1 → qAreaMeasure γ x (Metric.ball 0 (q : ℝ) ∩ H) < 1

theorem measurableSet_zeroScaleEv (γ : ℝ) : MeasurableSet {x : FieldSample | ZeroScaleEv γ x} := by
  classical
  set g : FieldSample → Measure ℂ :=
    fun x => if IsLQGGood γ x then qAreaMeasure γ x else 0 with hg_def
  have hg : Measurable g := GoodMeas.measurable_qAreaMeasure_global γ
  have hc : ∀ r : ℝ, Measurable fun x : FieldSample => g x (Metric.ball 0 r ∩ H) := fun r =>
    (Measure.measurable_coe (measurableSet_ball_inter_H r)).comp hg
  have he : {x : FieldSample | ZeroScaleEv γ x} = {x | IsLQGGood γ x} ∩
      ({x | g x (Metric.ball 0 1 ∩ H) = 1} ∩
        ⋂ q : ℚ, {x | (q : ℝ) < 1 → g x (Metric.ball 0 (q : ℝ) ∩ H) < 1}) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, ZeroScaleEv]
    constructor
    · rintro ⟨hG, h1, h2⟩
      exact ⟨hG, by simpa only [hg_def, if_pos hG] using h1,
        fun q hq => by simpa only [hg_def, if_pos hG] using h2 q hq⟩
    · rintro ⟨hG, h1, h2⟩
      exact ⟨hG, by simpa only [hg_def, if_pos hG] using h1,
        fun q hq => by simpa only [hg_def, if_pos hG] using h2 q hq⟩
  rw [he]
  refine (GoodMeas.measurableSet_isLQGGood γ).inter
    (((hc 1) (measurableSet_singleton 1)).inter (MeasurableSet.iInter fun q => ?_))
  by_cases hq : (q : ℝ) < 1
  · simp only [hq, true_imp_iff]
    exact measurableSet_lt (hc _) measurable_const
  · simp only [hq, false_imp_iff, ofPred_true, MeasurableSet.univ]

theorem zeroScaleEv_reconstruct (γ : ℝ) (x : FieldSample) :
    ZeroScaleEv γ (Factorization.reconstruct (Factorization.coords x)) ↔ ZeroScaleEv γ x := by
  simp only [ZeroScaleEv, Factorization.qAreaMeasure_congr
    (Factorization.avgReg_reconstruct_coords x) γ, GoodSample.isLQGGood_iff_reconstruct]

/-- On the scale event, `scaleParam = 1`. -/
theorem scaleParam_eq_one_of_ev {γ : ℝ} {x : FieldSample} (h : ZeroScaleEv γ x) :
    scaleParam γ x = 1 := by
  obtain ⟨-, h1, hq⟩ := h
  have hmem : (1 : ℝ) ∈ {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball 0 a ∩ H)} :=
    ⟨one_pos, h1.ge⟩
  have hlb : ∀ a ∈ {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball 0 a ∩ H)}, 1 ≤ a := by
    rintro a ⟨ha0, ha1⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨q, haq, hq1⟩ := exists_rat_btwn hlt
    have hmono : qAreaMeasure γ x (Metric.ball 0 a ∩ H) ≤
        qAreaMeasure γ x (Metric.ball 0 (q : ℝ) ∩ H) :=
      measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball haq.le))
    exact absurd (ha1.trans_lt (hmono.trans_lt (hq q hq1))) (lt_irrefl 1)
  exact IsLeast.csInf_eq ⟨hmem, hlb⟩

/-- The canonical description of a good sample with an area profile lies in the scale event. -/
theorem zeroScaleEv_canonical {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hg : IsLQGGood γ x)
    (hp : HasAreaProfile γ x) : ZeroScaleEv γ (canonical γ x) := by
  obtain ⟨hG, h1⟩ := CanonicalGood.canonical_spec hγ hg hp
  obtain ⟨hs, hs1⟩ := CanonicalGood.scaleParam_spec hp
  refine ⟨hG, h1, fun q hq => ?_⟩
  rw [canonical, GoodTransforms.qAreaMeasure_rescale hg hγ hs,
    Measure.map_apply (show Measurable fun z : ℂ => z / (scaleParam γ x : ℂ) from
      measurable_id.div_const _) (Metric.isOpen_ball.inter isOpen_H).measurableSet,
    GoodTransforms.preimage_div_ball_inter_H hs]
  rw [← hs1]
  by_cases hq0 : (q : ℝ) ≤ 0
  · have : (q : ℝ) * scaleParam γ x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq0 hs.le
    have h0 := profile_nonpos (qAreaMeasure γ x) this
    simp only [profile] at h0
    rw [h0, hs1]
    exact one_pos
  · rw [not_le] at hq0
    exact hp.2.2.1 (mem_Ici.2 (mul_pos hq0 hs).le) (mem_Ici.2 hs.le)
      (by nlinarith)

/-- **`scaleParam γ Y = 1` a.s. for a quantum wedge** (every `α < Q`). -/
theorem ae_scaleParam_eq_one_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → FieldSample}
    (hW : IsQuantumWedge γ α Y P) : ∀ᵐ ω ∂P, scaleParam γ (Y ω) = 1 := by
  have hY := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hZW : IsQuantumWedge γ α (S5.FieldLaw.Raw.refField γ X A) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have hZ := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hZW
  have hprof := WedgeCan4.ae_hasAreaProfile_wedgeField_of_inputs
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα)
    hγ hγ2 hX hA hI
  have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP' hX hA hI
  have href : ∀ᵐ ω ∂P', ZeroScaleEv γ (S5.FieldLaw.Raw.refField γ X A ω) := by
    filter_upwards [hprof, hgood] with ω hp hg
    exact zeroScaleEv_canonical hγ hg hp
  filter_upwards [WedgeBdry.ae_of_fieldLawFull_eq hlaw hY hZ (ZeroScaleEv γ)
    (measurableSet_zeroScaleEv γ) (zeroScaleEv_reconstruct γ) href] with ω hω
  exact scaleParam_eq_one_of_ev hω

/-! ## 2. The pairings -/

/-- **Regularized pairings equal raw pairings a.s. for a quantum wedge** (every `α < Q`). -/
theorem ae_pairTest_eq_pairRaw_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → FieldSample}
    (hW : IsQuantumWedge γ α Y P) (ρ : TestFun H) :
    ∀ᵐ ω ∂P, pairTest (Y ω) ρ.1 = pairRaw (Y ω) ρ.1 := by
  have hY := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hZW : IsQuantumWedge γ α (S5.FieldLaw.Raw.refField γ X A) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have hZ := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hZW
  have hl : P.map (fun ω => WedgeMeas.dataFull H (Y ω)) =
      P'.map (fun ω => WedgeMeas.dataFull H (S5.FieldLaw.Raw.refField γ X A ω)) := hlaw
  have href : ∀ᵐ ω ∂P', pairRaw (S5.FieldLaw.Raw.refField γ X A ω) ρ.1 =
      pairTest (S5.FieldLaw.Raw.refField γ X A ω) ρ.1 := by
    filter_upwards [S5.FieldLaw.Raw.ae_pairRaw_eq_pairTest_wedge hX
      (WedgeCan4.ae_continuous_wedgeProcess hA) (Qc γ) ρ,
      Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI] with ω h hs
    exact (h _ hs.1).1
  have hZ' : ∀ᵐ d ∂P'.map (fun ω => WedgeMeas.dataFull H (S5.FieldLaw.Raw.refField γ X A ω)),
      d.2 ρ = (E6.regG (E6.coordsOfFull d.1)).2 ρ := by
    rw [ae_map_iff hZ (E6.measurableSet_pairEvent E6.measurable_regG ρ)]
    filter_upwards [href] with ω hω
    simpa [WedgeMeas.dataFull, E6.coordsOfFull_coordsFull, E6.regG_coords] using hω
  rw [← hl, ae_map_iff hY (E6.measurableSet_pairEvent E6.measurable_regG ρ)] at hZ'
  filter_upwards [hZ'] with ω hω
  have := hω
  simp only [WedgeMeas.dataFull, E6.coordsOfFull_coordsFull, E6.regG_coords] at this
  exact this.symm

/-! ## 3. `WedgeZeroRegStmt` -/

/-- **`WedgeZeroRegStmt`**, given circle regularity of the reference canonical
`(γ − 2/γ)`-wedge (open node `E6.WedgeRefCircleRegStmt`, task WEDGE-CREG). -/
theorem wedgeZeroRegStmt_of_circ
    (hcirc : ∀ γ : ℝ, 0 < γ → γ < 2 → E6.WedgeRefCircleRegStmt γ (γ - 2 / γ)) :
    WedgeZeroRegStmt := by
  intro γ Ω _ P _ Y hγ hγ2 hW
  refine ⟨?_, fun ρ => ae_pairTest_eq_pairRaw_of_isQuantumWedge hγ hγ2 hW ρ⟩
  have hr := E6.readableBy_regG_of_isQuantumWedge hγ hγ2 (hcirc γ hγ hγ2) hW
  filter_upwards [hr.1, ae_scaleParam_eq_one_of_isQuantumWedge hγ hγ2 hW] with ω hω hs
  refine ⟨fun i => ?_, hs⟩
  rw [E6.regG_coords] at hω
  exact (congrFun hω i).symm

end Thm18Asm
end QuantumZipper
