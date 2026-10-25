import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath.Measurable
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RepairedInterfaces.RepairedAssembly
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete




 
set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath

 

theorem outer_measure_le_of_ae_exclusion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Good Bad : Set Ω) (η : ℝ≥0∞)
    (hGoodMeas : MeasurableSet Good)
    (hGood : 1 ≤ P Good + η)
    (hExclude : ∀ᵐ ω ∂P, ω ∈ Bad → ω ∉ Good) : P Bad ≤ η := by
  have hGoodFinite : P Good ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      (measure_mono (Set.subset_univ Good) |>.trans_eq
        (IsProbabilityMeasure.measure_univ (μ := P)))
  calc
    P Bad ≤ P Goodᶜ := measure_mono_ae hExclude
    _ = 1 - P Good := by rw [measure_compl hGoodMeas hGoodFinite,
      IsProbabilityMeasure.measure_univ]
    _ ≤ η := tsub_le_iff_right.mpr (by simpa only [add_comm] using hGood)

 

theorem r53_of_closed_end_union
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : EndSaving.Interfaces.ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
    (θ : Set.Ioi (0 : ℝ))
    (hEndUnion : ∀ (ν κG κEnd : Set.Ioi (0 : ℝ))
      (η : Set.Ioo (0 : ℝ) 1),
      ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
        ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ → ∀ j : ℕ,
          let b := EndSaving.Interfaces.dyadicRadius j
          ENNReal.ofReal (κG : ℝ) ≤
            P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κG
              ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
          ENNReal.ofReal (1 - (η : ℝ)) ≤
            P (EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd)) :
    ∀ (a : Set.Ioo (3 / 4 : ℝ) 1)
      (κ : Set.Ioi (0 : ℝ)) (p : Set.Ioo (0 : ℝ) 1),
      ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
        ∀ j : ℕ,
          ENNReal.ofReal (κ : ℝ) ≤
            P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
              (EndSaving.Interfaces.dyadicRadius j) κ
              ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
          P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (EndSaving.Interfaces.dyadicRadius j) a
            ⟨Ctop, Ctop.property.1⟩ θ (h ω)} <
              ENNReal.ofReal ((p : ℝ) / 2) := by
  intro a κ p
  have hcReal : 0 < cPlus.toReal := by
    have hm : 0 ≤ cMinus.toReal := ENNReal.toReal_nonneg
    have hlow := objs.cMid'_lower
    have hupp := objs.cMid'_upper
    dsimp [EndSaving.Interfaces.midpoint] at hupp
    linarith
  have hcFinite : cPlus ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hcReal).2.ne
  let c : NNReal := ⟨cPlus.toReal, hcReal.le⟩
  have hc : 0 < c := hcReal
  have hcEq : (c : ℝ≥0∞) = cPlus := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal cPlus.toReal = cPlus
    exact ENNReal.ofReal_toReal hcFinite
  let ν : Set.Ioi (0 : ℝ) := ⟨2 / (θ : ℝ) + 1, by
    have ht : 0 < (θ : ℝ) := θ.property
    exact Set.mem_Ioi.mpr (add_pos_of_nonneg_of_pos
      (div_nonneg (by norm_num) ht.le) zero_lt_one)⟩
  have hν : 2 / (θ : ℝ) < (ν : ℝ) := by dsimp [ν]; linarith
  let κEnd : Set.Ioi (0 : ℝ) :=
    ⟨(1 - (a : ℝ)) / 2,
      div_pos (sub_pos.mpr a.property.2) (by norm_num)⟩
  let η : Set.Ioo (0 : ℝ) 1 :=
    ⟨(p : ℝ) / 4, by constructor <;> nlinarith [p.property.1, p.property.2]⟩
  obtain ⟨δDet, hδDet0, hδDet1, hdet⟩ :=
    deterministic_five_path_gap h D D' ξ Q c hc a θ ν hν
  obtain ⟨δEnd, hδEndApply⟩ := hEndUnion ν κ κEnd η
  obtain ⟨δSmall, hδSmall0, hδSmall1, hsmall⟩ :=
    exists_uniform_R53_scale a θ c hc ν hν
  let δ : ℝ := min δDet (min (δEnd : ℝ) δSmall) / 2
  have hm : 0 < min δDet (min (δEnd : ℝ) δSmall) :=
    lt_min hδDet0 (lt_min δEnd.property.1 hδSmall0)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδDet : δ ≤ δDet := by
    dsimp [δ]
    nlinarith only [hm, min_le_left δDet (min (δEnd : ℝ) δSmall)]
  have hδEnd : δ ≤ (δEnd : ℝ) := by
    dsimp [δ]
    nlinarith only [hm, min_le_right δDet (min (δEnd : ℝ) δSmall),
      min_le_left (δEnd : ℝ) δSmall]
  have hδSmall : δ ≤ δSmall := by
    dsimp [δ]
    nlinarith only [hm, min_le_right δDet (min (δEnd : ℝ) δSmall),
      min_le_right (δEnd : ℝ) δSmall]
  let x : ℝ := ((1 - (a : ℝ)) / 4) * δ
  have hx0 : 0 < x := by
    dsimp [x]
    exact mul_pos (div_pos (sub_pos.mpr a.property.2) (by norm_num)) hδ
  have hxC : x < (c : ℝ) := by
    simpa only [x] using (hsmall δ hδ hδSmall).2.2.2
  let Ctop : Set.Ioo (0 : ℝ) cPlus.toReal :=
    ⟨(c : ℝ) - x, by
      constructor
      · exact sub_pos.mpr hxC
      · change cPlus.toReal - x < cPlus.toReal
        linarith only [hx0]⟩
  refine ⟨Ctop, ?_⟩
  intro j hG
  let b := EndSaving.Interfaces.dyadicRadius j
  let Good := closedSavingVersion h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd
  let Bad := {ω | OptimalConstants.Ratios.HEvent D D' ξ Q b a
    ⟨Ctop, Ctop.property.1⟩ θ (h ω)}
  have hGoodMeas : MeasurableSet Good :=
    measurable_closedSavingVersion h hGFF.1.measurable D D' hD.1 hD'.1
      ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd
  have hGoodProb : ENNReal.ofReal (1 - (η : ℝ)) ≤ P Good := by
    calc
      _ ≤ P (EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd) :=
        hδEndApply δ hδ hδEnd j hG
      _ = P Good := closedSaving_ae_eq P h D D' ξ Q cPlus b ν
        ⟨δ, hδ⟩ κEnd (ae_isCircleAverage_old hGFF.1 b 0)
  have hGoodAdd : 1 ≤ P Good + ENNReal.ofReal (η : ℝ) := by
    have hη0 : 0 ≤ (η : ℝ) := η.property.1.le
    have hη1 : 0 ≤ 1 - (η : ℝ) := sub_nonneg.mpr η.property.2.le
    calc
      1 = ENNReal.ofReal ((1 - (η : ℝ)) + (η : ℝ)) := by norm_num
      _ = ENNReal.ofReal (1 - (η : ℝ)) + ENNReal.ofReal (η : ℝ) :=
        ENNReal.ofReal_add hη1 hη0
      _ ≤ P Good + ENNReal.ofReal (η : ℝ) := add_le_add hGoodProb le_rfl
  have hPlusField : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hGFF.1
  have hDlenAe := hD.2.1 P h hPlusField
  have hD'lenAe := hD'.2.1 P h hPlusField
  have hQA : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hDregAe := BiLipschitz.Barrier.ae_curves_continuous hD hQA P h hGFF
  have hD'regAe := BiLipschitz.Barrier.ae_curves_continuous hD' hQA P h hGFF
  have hCompAe := EndSaving.RepairedInterfaces.optimal_global_upper P h ξ Q D D' hD hD'
    hGFF cMinus cPlus hPlusPos hMinus hPlus
  have hCircleAe := ae_isCircleAverage_old hGFF.1 b 0
  have hExclude : ∀ᵐ ω ∂P, ω ∈ Bad → ω ∉ Good := by
    filter_upwards [hDlenAe, hD'lenAe, hDregAe, hD'regAe,
      hCompAe, hCircleAe] with ω hDlen hD'len hDreg hD'reg hComp hωCircle
    intro hBad hGood
    change OptimalConstants.Ratios.HEvent D D' ξ Q b a ⟨Ctop, Ctop.property.1⟩ θ (h ω) at hBad
    rcases hBad with ⟨hbrH, hCircleH, u, v, hu, hv, _, _, hLower,
      γ, s, t, hGeo, _, _, hDU, hLoopU, hLoopV⟩
    have hEnd : ω ∈ EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν
        ⟨δ, hδ⟩ κEnd := by
      refine ⟨LQGMetric.circleAvg (h ω) b 0, hωCircle, ?_⟩
      simpa only [Good, closedSavingVersion, Set.mem_ofPred_eq] using hGood
    have hStrict := hdet δ hδ hδDet b ω hDlen hD'len hDreg.2.1
      hD'reg.2.1 (by simpa only [hcEq] using hComp)
      (by simpa only [hcEq, κEnd] using hEnd)
      u v hu hv hGeo.2.2.2.2 hLoopU hLoopV hbrH hCircleH hDU
    have hStrict' : (D' (h ω)) (u, v) <
        ENNReal.ofReal (Ctop : ℝ) * (D (h ω)) (u, v) := by
      simpa only [Ctop, x] using hStrict
    exact (not_lt_of_ge hLower) hStrict' 
  have hBound := outer_measure_le_of_ae_exclusion P Good Bad
    (ENNReal.ofReal (η : ℝ)) hGoodMeas hGoodAdd hExclude
  change P Bad < ENNReal.ofReal ((p : ℝ) / 2)
  exact hBound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
    have hp : 0 < (p : ℝ) := p.property.1
    positivity)).mpr (by dsimp [η]; nlinarith [p.property.1]))


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath
