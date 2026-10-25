import SupercriticalLQGUniqueness.B2.DG20Lim.MeasurableLimitSelection
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalCoordConvergence

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_measurable_coupled_limit_metric
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (hRange : ∀ᵐ ω ∂P', ∀ n,
      finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1)
    (hLSC : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      LSCTendsto
        (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
        R.toLSCFun.1)
    (hAgree : ∀ᵐ ω ∂P', ∃ S : RData,
      S.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      S.around = (Ylim ω).2.2 ∧
      ∀ Z W : RatCircle, Z.radius = 0 → W.radius = 0 →
        S.across Z W = S.DfromR Z.center W.center)
    (hGeom : ∀ᵐ ω ∂P', ∃ (R : RData)
      (htri : ∀ x y z : ℂ,
        R.DfromR x z ≤ R.DfromR x y + R.DfromR y z),
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      (R.toLSCMetric htri).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (R.toLSCMetric htri).1 (u, v) < ENNReal.ofReal η →
          dist u v < δ) ∧
      (∀ u v : ℂ, (R.toLSCMetric htri).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (R.toLSCMetric htri).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            (R.toLSCMetric htri).len γ a b = (R.toLSCMetric htri).1 (u, v))) :
    ∃ L : Ω' → LSCMetric, Measurable L ∧
      (∀ᵐ ω ∂P', LSCTendsto
        (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
        (L ω).toLSCFun.1) ∧
      (∀ᵐ ω ∂P', ∀ u v : ℂ,
        B2.Iface.IsRationalPoint u → B2.Iface.IsRationalPoint v →
        Tendsto (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1) (u, v))
          atTop (𝓝 ((L ω).toLSCFun.1 (u, v)))) ∧
      (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
        (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
          ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
        (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
          ∃ (γ : ℝ → ℂ) (a b : ℝ),
            (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
              (L ω).len γ a b = (L ω).1 (u, v))) := by
  let G : ℕ → Ω' → LSCMetric := fun n ω =>
    finiteLSCMetric (circleCoordsInv (Y n ω).2.1)
  have hG : ∀ n, Measurable (G n) := by
    intro n
    exact measurable_finiteLSCMetric.comp
      (measurable_circleCoordsInv.comp
        (measurable_fst.comp (measurable_snd.comp (hYm n))))
  let Good : Ω' → LSCMetric → Prop := fun ω L =>
    LSCTendsto (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
      L.toLSCFun.1 ∧
    (∀ u v : ℂ, B2.Iface.IsRationalPoint u →
      B2.Iface.IsRationalPoint v →
      Tendsto (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1) (u, v))
        atTop (𝓝 (L.toLSCFun.1 (u, v)))) ∧
    L.IsLengthSpace ∧
    (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, L.1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
    (∀ u v : ℂ, L.1 (u, v) < ∞ →
      ∃ (γ : ℝ → ℂ) (a b : ℝ),
        L.IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
          L.len γ a b = L.1 (u, v))
  have hExists : ∀ᵐ ω ∂P', ∃ L : LSCMetric,
      Tendsto (fun n => G n ω) atTop (𝓝 L) ∧ Good ω L := by
    filter_upwards [hConv, hRange, hLSC, hAgree, hGeom] with
      ω hconv hrange hLSCω hAgreeω hGeomω
    obtain ⟨T, hTa, _, hT⟩ := hLSCω
    obtain ⟨S, hSa, _, hSagree⟩ := hAgreeω
    obtain ⟨R, htri, hRa, _, hLen, hEuclid, hGeo⟩ := hGeomω
    have hRT : R.across = T.across := hRa.trans hTa.symm
    have hRS : R.across = S.across := hRa.trans hSa.symm
    have hlsc : LSCTendsto
        (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
        (R.toLSCMetric htri).toLSCFun.1 := by
      rw [RData.toLSCFun_eq_of_across hRT]
      exact hT
    have hagreeR : ∀ Z W : RatCircle, Z.radius = 0 → W.radius = 0 →
        R.across Z W = R.DfromR Z.center W.center := by
      intro Z W hZ hW
      calc
        R.across Z W = S.across Z W := congrFun (congrFun hRS Z) W
        _ = S.DfromR Z.center W.center := hSagree Z W hZ hW
        _ = R.DfromR Z.center W.center :=
          (congrFun (congrFun (RData.DfromR_eq_of_across hRS) Z.center) W.center).symm
    have hrat : ∀ u v : ℂ, B2.Iface.IsRationalPoint u →
        B2.Iface.IsRationalPoint v →
        Tendsto (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1) (u, v))
          atTop (𝓝 ((R.toLSCMetric htri).toLSCFun.1 (u, v))) := by
      intro u v hu hv
      exact rational_point_tendsto_of_zero_circle_agreement
        (fun n => Y n ω) (Ylim ω) hconv hrange R hRa hagreeR htri u v hu hv
    have htendsto : Tendsto (fun n => G n ω) atTop
        (𝓝 (R.toLSCMetric htri)) := by
      rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff]
      have hf : (fun n => (G n ω).toLSCFun.1) =
          (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1)) := by
        funext n
        exact finiteLSCMetric_toLSCFun _
      have hh : LSCTendsto (fun n => (G n ω).toLSCFun.1)
          (R.toLSCMetric htri).toLSCFun.1 := by
        rw [hf]
        exact hlsc
      exact LSCFun.tendsto_of_lscTendsto hh
    exact ⟨R.toLSCMetric htri, htendsto,
      hlsc, hrat, hLen, hEuclid, hGeo⟩
  obtain ⟨L, hLm, hGood⟩ :=
    exists_measurable_lscMetric_limit_with_property P' G hG Good hExists
  refine ⟨L, hLm, ?_, ?_, ?_⟩
  · exact hGood.mono fun _ hω => hω.2.1
  · exact hGood.mono fun _ hω => hω.2.2.1
  · exact hGood.mono fun _ hω => ⟨hω.2.2.2.1, hω.2.2.2.2.1, hω.2.2.2.2.2⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
