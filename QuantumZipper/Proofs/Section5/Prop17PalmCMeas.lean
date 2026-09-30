import QuantumZipper.Proofs.Section5.Prop17PalmCReg
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.LQG.WedgeMeasurable

/-!
# Proposition 1.7, Palm-zoom node C: the measurability node is proved (PALM-C)

`prop17PalmCMeasStmt_holds : Prop17PalmCMeasStmt γ` for `0 < γ < 2`. On the full-measure event
where the Palm field is regular at the translated dyadic folded circles
(`prop17PalmCRegStmt_holds`) and the split field `W = palmCSplit γ C x X ω` is good
(`LogSingGood.logSingGoodAS_holds` + a continuous function), the zoomed Palm field, the D3⁺ model
field and `W` have the same values at all dyadic folded circles, hence the same `avgReg`
(`D3Plus.avgReg_congr`). Therefore

* the Palm zoom coordinates are `rescG γ (coords W)`, with
  `rescG γ c = coordsFull (resc Q (c, scaleG γ c))` measurable (`canonical_eq_resc`,
  `scaleG_coords`);
* the local scale of the model field is `scaleOnG γ (coords W)`, the infimum of an up-closed set
  defined through the measurable global area measure `GoodMeas.measurable_qAreaMeasure_global`
  (`qAreaMeasureOn = qAreaMeasure|_U` for good fields, `D3Plus.qAreaMeasureOn_eq_restrict_of_agree`);

and `ω ↦ coords W_ω` is measurable (values of `X` at fixed measures). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

open Classical in
/-- The global area measure read from raw coordinates (junk `0` off good fields). -/
def palmCqAG (γ : ℝ) (c : ℕ → ℝ) : Measure ℂ :=
  if IsLQGGood γ (reconstruct c) then qAreaMeasure γ (reconstruct c) else 0

theorem measurable_palmCqAG (γ : ℝ) : Measurable (palmCqAG γ) := by
  unfold palmCqAG
  convert (GoodMeas.measurable_qAreaMeasure_global γ).comp measurable_reconstruct using 1
  funext c
  by_cases h : IsLQGGood γ (reconstruct c) <;> simp [h]

/-- The local scale on `halfDisc 1`, read from raw coordinates. -/
def palmCScaleOnG (γ : ℝ) (c : ℕ → ℝ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ 1 ≤ palmCqAG γ c (Metric.ball 0 a ∩ H ∩ D3Plus.halfDisc 1)}

theorem measurable_palmCScaleOnG (γ : ℝ) : Measurable (palmCScaleOnG γ) := by
  have hm : ∀ a : ℝ, Measurable fun c => palmCqAG γ c (Metric.ball 0 a ∩ H ∩ D3Plus.halfDisc 1) :=
    fun a => (Measure.measurable_coe ((Metric.isOpen_ball.measurableSet.inter
      isOpen_H.measurableSet).inter (D3Plus.isOpen_halfDisc 1).measurableSet)).comp
      (measurable_palmCqAG γ)
  refine LQGMeas.measurable_sInf_upClosed _ (fun q => (MeasurableSet.const _).inter
    (measurableSet_le measurable_const (hm q))) (fun c a b ha hab => ⟨ha.1.trans_le hab,
      ha.2.trans (measure_mono (inter_subset_inter_left _ (inter_subset_inter_left _
        (Metric.ball_subset_ball hab))))⟩) fun c a ha => ha.1

/-- The canonical coordinates read from raw coordinates. -/
def palmCRescG (γ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ := coordsFull (resc (Qc γ) (c, scaleG γ c))

theorem measurable_palmCRescG (γ : ℝ) : Measurable (palmCRescG γ) :=
  measurable_pi_iff.2 fun _ => (measurable_resc_apply (Qc γ) _).comp
    (measurable_id.prodMk (measurable_scaleG γ))

theorem palmC_avgReg_eq_of_agree {y y' : FieldSample}
    (h : ∀ (n k : ℕ) (z : ℂ), y (foldedCircle (dyadicRoundC n z) (radius k)) =
      y' (foldedCircle (dyadicRoundC n z) (radius k))) :
    avgReg y = avgReg y' := by
  have hag : ∀ r : ℝ, D3Plus.AgreeNear y y' r := fun r n k z _ => h n k z
  funext k z
  exact D3Plus.avgReg_congr (hag (‖z‖ + radius k + 1)) (lt_add_one _)

theorem palmC_canonical_coords {γ : ℝ} {y W : FieldSample} (hW : IsLQGGood γ W)
    (h : avgReg y = avgReg W) : coordsFull (canonical γ y) = palmCRescG γ (coords W) := by
  have e : canonical γ y = canonical γ W := by
    simp only [canonical, rescale, scaleParam_congr h γ]
    exact coordChange_congr h _ _
  rw [e, canonical_eq_resc, palmCRescG, scaleG_coords hW]

theorem palmC_scaleParamOn_coords {γ : ℝ} {y' W : FieldSample} (hW : IsLQGGood γ W)
    (h : avgReg y' = avgReg W) :
    scaleParamOn γ y' (D3Plus.halfDisc 1) = palmCScaleOnG γ (coords W) := by
  have hA : areaApprox γ y' = areaApprox γ W := areaApprox_congr h γ
  have hOn : qAreaMeasureOn γ y' (D3Plus.halfDisc 1) = (qAreaMeasure γ W).restrict
      (D3Plus.halfDisc 1) := by
    rw [show qAreaMeasureOn γ y' (D3Plus.halfDisc 1) = qAreaMeasureOn γ W (D3Plus.halfDisc 1) by
      unfold qAreaMeasureOn; rw [hA]]
    exact D3Plus.qAreaMeasureOn_eq_restrict_of_agree (fun _ _ _ _ => rfl)
      (Prop16Area.G.isVagueLimitOn_H_of_good hW)
  have hq : palmCqAG γ (coords W) = qAreaMeasure γ W := by
    have hg := (GoodSample.isLQGGood_iff_reconstruct γ W).2 hW
    simp only [palmCqAG, hg, ite_true]
    exact qAreaMeasure_congr (avgReg_reconstruct_coords W) γ
  simp only [scaleParamOn, palmCScaleOnG, hOn, hq]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [Measure.restrict_apply ((Metric.isOpen_ball.measurableSet.inter
    isOpen_H.measurableSet))]

theorem measurable_coords_palmCSplit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (γ C x : ℝ) :
    Measurable fun ω => coords (palmCSplit γ C x X ω) := by
  refine measurable_pi_iff.2 fun i => ?_
  set μ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) with hμ
  obtain ⟨-, h2⟩ := integrable_palmC_parts γ x (dyadicIndex i).1 (radius_pos (dyadicIndex i).2)
  have e : (fun ω => coords (palmCSplit γ C x X ω) i) = fun ω =>
      X ω (μ.map (· + (x : ℂ))) + (∫ z, γ * -Real.log ‖z‖ ∂μ) +
        ((∫ z, palmCCorr γ (foldedCircle 0 3) x z ∂μ) + (C / γ - X ω (foldedCircle 0 3))) := by
    funext ω
    show (palmCField X x ω μ + ∫ z, γ * -Real.log ‖z‖ ∂μ) +
      ∫ z, (palmCCorr γ (foldedCircle 0 3) x z + (C / γ - X ω (foldedCircle 0 3))) ∂μ = _
    rw [integral_add h2 (integrable_const _), integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
    rfl
  rw [e]
  exact ((hX.measurable_coord _).add_const _).add
    (((hX.measurable_coord _).const_sub _).const_add _)

/-- **The measurability node holds.** -/
theorem prop17PalmCMeasStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Prop17PalmCMeasStmt γ := by
  intro Ω' _ P' X hP hX x hx
  have := hP
  have hreg := prop17PalmCRegStmt_holds γ Ω' _ P' X hP hX x hx
  have hgood := LogSingGood.logSingGoodAS_holds hγ hγ2 (gamma_lt_Qc' hγ hγ2) Ω' _ P'
    (palmCField X x) hP (isFreeGFFModConstH_translate hX x)
  have hgoodC : ∀ C : ℝ, ∀ᵐ ω ∂P', IsLQGGood γ (palmCSplit γ C x X ω) := fun C =>
    (IndepParams.ae_isLQGGood_add_ofFun (γ := γ) hgood
      (g := fun ω z => palmCCorr γ (foldedCircle 0 3) x z + (C / γ - X ω (foldedCircle 0 3)))
      fun ω => ((continuous_palmCCorr γ x).add continuous_const).continuousOn).mono
        fun ω h => h.1
  refine ⟨fun C => ?_, fun C => ?_⟩
  · refine ((measurable_palmCRescG γ).comp
      (measurable_coords_palmCSplit hX γ C x)).aemeasurable.congr ?_
    filter_upwards [hreg, hgoodC C] with ω hr hg
    exact (palmC_canonical_coords hg (palmC_avgReg_eq_of_agree fun n k z =>
      zoomField_palm_eq_split (radius_pos k) (hr n k z))).symm
  · refine ((measurable_palmCScaleOnG γ).comp
      (measurable_coords_palmCSplit hX γ C x)).aemeasurable.congr ?_
    filter_upwards [hreg, hgoodC C] with ω hr hg
    refine (palmC_scaleParamOn_coords hg (palmC_avgReg_eq_of_agree fun n k z => ?_)).symm
    rw [← zoomField_palm_eq_zoomModel (radius_pos k) (hr n k z)]
    exact zoomField_palm_eq_split (radius_pos k) (hr n k z)

/-- **Node C (Prop. 1.7) from D3⁺(i) (rich form) alone.** -/
theorem prop17FreeFixedZoom_of_D3PlusIRich (hI : D3Plus.D3PlusIStmtRich) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1 :=
  prop17FreeFixedZoom_of_D3PlusI hI (fun γ _ _ => prop17PalmCRegStmt_holds γ)
    fun _ hγ hγ2 => prop17PalmCMeasStmt_holds hγ hγ2

/-- **Node C (Prop. 1.7) from the N2 form of D3⁺(i).** -/
theorem prop17FreeFixedZoom_of_D3PlusIN2 (hN2 : D3Plus.D3PlusIN2RichStmt) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1 :=
  prop17FreeFixedZoom_of_D3PlusIRich (D3Plus.d3PlusIRich_of_N2 hN2)

end Raw
end FieldLaw
end S5
end QuantumZipper
