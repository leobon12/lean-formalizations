import SupercriticalLQGUniqueness.B2.Final.DG20CoupledGoodCircles
import SupercriticalLQGUniqueness.B2.DG20Lim.AllPointCircleVanishing
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLengthTransfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircLemProb
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer

 



















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify CoordJ pairJ pairJInv)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.DG20Lim (RatCoords RData RatCircle RatAnnulus finiteRatCoords
  finiteCircleCoords finiteAroundCoords circleCoordsInv finiteMetricE finiteLSCMetric
  normalizedContLFPP measurableRatCoordsVersion)

theorem normalizedLFPPMetric_eq_finiteLSCMetric (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (p : ℂ × ℂ) :
    PfeWeyl.normalizedLFPPMetric ξ a φ p = finiteLSCMetric (normalizedContLFPP ξ a φ) p := by
  rw [DG20Lim.finiteLSCMetric_apply]
  apply EReal.coe_ennreal_injective
  rw [DG20Lim.normalizedContLFPP_to_rescaledLFPP, ← PfeWeyl.normalizedLFPPMetric_toLSCFun,
    LSCMetric.toLSCFun_apply]

theorem setDistance_normalizedLFPPMetric_eq_setDist (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (A B : Set ℂ) :
    setDistance (PfeWeyl.normalizedLFPPMetric ξ a φ).1 A B =
      LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ) A B := by
  rw [← setDistance_finiteLSCMetric]
  congr 1
  funext p
  exact normalizedLFPPMetric_eq_finiteLSCMetric ξ a φ p

variable {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
  {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
  {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h' : Ω' → DistC}
  {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}

 
theorem coupled_circle_tendsto_of_coords [IsProbabilityMeasure P']
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hPos : DG20ExponentPositive)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hZ : Final.CoupledRatCoords ξ m e V P' hN L) :
    ∀ᵐ ω ∂P', ∀ O O' : RatCircle, Tendsto (fun n =>
      setDistance (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))).1
        O.toSet O'.toSet) atTop (𝓝 (setDistance (L ω).1 O.toSet O'.toSet)) := by
  obtain ⟨Z, Zlim, hZm, -, hZid, hZconv, hLink⟩ := hZ
  obtain ⟨C, hC, hGood⟩ := Final.coupled_good_circles hS4 hPerc hB Z Zlim hZm hZid hZconv hLink
  obtain ⟨hprob, hcan⟩ := normalized_canonical_model
  have := hprob
  have hX : ∀ δ, IsHeatSmoothing normGFFLaw id δ (V δ) :=
    PfeLocal.l1_isHeatSmoothing_canonical V hB.heat_ae
  let Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords := fun n ω => (pairJ ⊤ (hN n ω), Z n ω)
  let Ylim : Ω' → (CoordJ → ℝ) × RatCoords := fun ω => (pairJ ⊤ (h' ω), Zlim ω)
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    ((LQGMetric.measurable_pairJ ⊤).comp (hB.field_measurable n)).prodMk (hZm n)
  
  have hLaw : ∀ n, P'.map (Y n) = normGFFLaw.map (fun ω =>
      (pairJ ⊤ (id ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) ω))
        (DG20Lim.aemeasurable_normalizedContLFPP_heat_version normGFFLaw id hcan
          (e n) (m (e n)) (ξ : ℝ) (V (e n)) (hX (e n))) ω)) := by
    intro n
    let hDa := DG20Lim.aemeasurable_normalizedContLFPP_heat_version normGFFLaw id hcan
      (e n) (m (e n)) (ξ : ℝ) (V (e n)) (hX (e n))
    let f : DistC → RatCoords := measurableRatCoordsVersion
      (fun ω => normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) ω)) hDa
    have hf : Measurable f := DG20Lim.measurable_measurableRatCoordsVersion _ hDa
    have hfae : ∀ᵐ g ∂normGFFLaw,
        finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) g)) = f g :=
      (DG20Lim.aemeasurable_finiteRatCoords _ hDa).ae_eq_mk
    have hfae' : ∀ᵐ ω ∂P',
        finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))) =
          f (hN n ω) := by
      have : ∀ᵐ g ∂(P'.map (hN n)),
          finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) g)) = f g := by
        rw [hB.field_law n]
        exact hfae
      exact ae_of_ae_map (hB.field_measurable n).aemeasurable this
    have hG : Measurable (fun g : DistC => (pairJ ⊤ g, f g)) :=
      (LQGMetric.measurable_pairJ ⊤).prodMk hf
    calc P'.map (Y n) = P'.map ((fun g : DistC => (pairJ ⊤ g, f g)) ∘ hN n) := by
          refine Measure.map_congr ?_
          filter_upwards [hZid, hfae'] with ω hω hω'
          simp only [Y, Function.comp_apply, hω n, hω']
      _ = (P'.map (hN n)).map (fun g : DistC => (pairJ ⊤ g, f g)) :=
          (Measure.map_map hG (hB.field_measurable n)).symm
      _ = _ := by rw [hB.field_law n]; rfl
  have hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) := by
    filter_upwards [hB.field_tendsto] with ω hω
    exact ((Final.continuous_pairJ_top.tendsto (h' ω)).comp hω).prodMk_nhds (hZconv ω)
  have hRData : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧ R.around = (Ylim ω).2.2 :=
    hLink.mono fun _ hω => by
      obtain ⟨R, ha, hb, _⟩ := hω
      exact ⟨R, ha, hb⟩
  
  have hVanish := DG20Lim.ae_all_coupled_point_circle_vanishing_of_inputs
    hS4 hPos ξ Q hB.exponent m hB.normalizer normGFFLaw P' id hcan V hX e hB.scale_tendsto
    Y Ylim hYm hLaw hConv hRData
  filter_upwards [hGood, hVanish, hConv, hZid, hB.metric_tendsto] with ω hG hV hYω hZω hMω
  obtain ⟨R, ha, hb, hLR, hz⟩ := hG
  have hRange : ∀ n, finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1 :=
    fun n => by
      simp only [Y, hZω n, finiteRatCoords, DG20Lim.circleCoordsInv_finiteCircleCoords]
  have hfin : ∀ n, finiteMetricE (circleCoordsInv (Y n ω).2.1) =
      rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)) := fun n => by
    funext p
    simp only [Y, hZω n, finiteRatCoords, DG20Lim.circleCoordsInv_finiteCircleCoords,
      finiteMetricE]
    exact DG20Lim.normalizedContLFPP_to_rescaledLFPP _ _ _ p
  have hLsc : LSCTendsto (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
      (L ω).toLSCFun.1 := by
    simp only [hfin]
    exact (PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (fun n => m (e n))
      (fun n => V (e n) (hN n ω)) (L ω)).1 hMω
  have hRL : LSCTendsto (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
      R.toLSCFun.1 := by
    rw [← hLR]
    exact hLsc
  have hcrossFin : ∀ n (A : RatAnnulus) (O₁ O₁' Q' : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q' A →
      (Y n ω).2.1 (O₁, Q') ≤ (Y n ω).2.1 (O₁, O₁') + (Y n ω).2.2 A := by
    intro n A O₁ O₁' Q' h₁ hQ'
    simp only [Y, hZω n, finiteRatCoords, finiteCircleCoords, finiteAroundCoords]
    exact finiteCircleDist_le_across_around_crossing _
      (DG20Lim.isLength_normalizedContLFPP _ _ _) A O₁ O₁' Q' h₁ hQ'
  have hinterFin : ∀ n (O Q' : RatCircle), (O.toSet ∩ Q'.toSet).Nonempty →
      (Y n ω).2.1 (O, Q') = 0 := by
    intro n O Q' h
    simp only [Y, hZω n, finiteRatCoords, finiteCircleCoords]
    exact finiteCircleDist_eq_zero_of_inter _ O Q' h
  have hGoodR : ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
      (∀ n, (B n).inner.Surrounds z ∧ R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
      (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) := fun z => by
    obtain ⟨B, h1, h2, h3, -⟩ := hz z
    exact ⟨B, h1, h2, h3⟩
  intro O O'
  have hid := limit_circleCoord_eq_setDistance hYω hRange (L ω) hLsc R ha hb hRL C hC
    hcrossFin hinterFin hGoodR hV O O'
  have hcoord : ∀ n, setDistance (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (V (e n) (hN n ω))).1 O.toSet O'.toSet = (Y n ω).2.1 (O, O') := fun n => by
    rw [setDistance_normalizedLFPPMetric_eq_setDist]
    simp only [Y, hZω n, finiteRatCoords, finiteCircleCoords]
  simp only [hcoord]
  rw [← hid]
  exact tendsto_circleCoord hYω O O'

 


theorem normalizedPointCircles_of_coupledRatCoords [IsProbabilityMeasure P']
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hPos : DG20ExponentPositive)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hZ : Final.CoupledRatCoords ξ m e V P' hN L)
    (Φ : DistC → LSCMetric) (hΦm : Measurable Φ) (hΦ : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ PfeWeyl.NormalizedPointCircles ξ m (fun n => e (ψ n)) Φ := by
  have hCirc := coupled_circle_tendsto_of_coords hS4 hPerc hPos hB hZ
  have _ : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have _ : IsProbabilityMeasure (normGFFLaw.map (pairJ ⊤)) :=
    (Measure.isProbabilityMeasure_map_iff (LQGMetric.measurable_pairJ ⊤).aemeasurable).2
      inferInstance
  have hcomp : ∀ q : RatCircle × RatCircle,
      Measurable fun D : LSCMetric => setDistance D.1 q.1.toSet q.2.toSet := fun q =>
    PfeLocal.l4_measurable_setDistance (isCompact_sphere _ _) (isCompact_sphere _ _)
  have hR : ∀ n, Measurable fun a : CoordJ → ℝ => fun q : RatCircle × RatCircle =>
      setDistance (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
        (V (e n) (pairJInv ⊤ a))).1 q.1.toSet q.2.toSet := by
    intro n
    refine Measurable.of_eval fun q => (hcomp q).comp ?_
    exact measurable_normalizedLFPPMetric_comp (ξ : ℝ) _
      (fun z => (continuous_eval_const z).measurable.comp
        ((hB.heat_measurable (e n)).comp (LQGMetric.measurable_pairJInv ⊤)))
  have hΦc : Measurable fun a : CoordJ → ℝ => fun q : RatCircle × RatCircle =>
      setDistance (Φ (pairJInv ⊤ a)).1 q.1.toSet q.2.toSet :=
    Measurable.of_eval fun q => (hcomp q).comp (hΦm.comp (LQGMetric.measurable_pairJInv ⊤))
  have hh' := hB.limit_field
  have hh'm : Measurable h' := hh'.1.measurable
  have hXlaw : ∀ n, P'.map (fun ω => pairJ ⊤ (hN n ω)) = normGFFLaw.map (pairJ ⊤) := fun n => by
    change P'.map (pairJ ⊤ ∘ hN n) = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) (hB.field_measurable n),
      hB.field_law n]
  have hXllaw : P'.map (fun ω => pairJ ⊤ (h' ω)) = normGFFLaw.map (pairJ ⊤) := by
    change P'.map (pairJ ⊤ ∘ h') = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh'm,
      ← normGFFLaw_eq_of_normalized P' h' hh']
  have hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => pairJ ⊤ (hN n ω)) atTop (𝓝 (pairJ ⊤ (h' ω))) := by
    filter_upwards [hB.field_tendsto] with ω hω
    exact (Final.continuous_pairJ_top.tendsto _).comp hω
  have hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => fun q : RatCircle × RatCircle =>
      setDistance (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
        (V (e n) (pairJInv ⊤ (pairJ ⊤ (hN n ω))))).1 q.1.toSet q.2.toSet) atTop
      (𝓝 (fun q : RatCircle × RatCircle =>
        setDistance (Φ (pairJInv ⊤ (pairJ ⊤ (h' ω)))).1 q.1.toSet q.2.toSet)) := by
    filter_upwards [hCirc, hΦ] with ω hω hL
    refine tendsto_pi_nhds.2 fun q => ?_
    simp only [LQGMetric.pairJInv_pairJ]
    rw [← hL]
    exact hω q.1 q.2
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_coords_gen
    (T := RatCircle × RatCircle → ℝ≥0∞) (normGFFLaw.map (pairJ ⊤))
    (fun (n : ℕ) (a : CoordJ → ℝ) (q : RatCircle × RatCircle) =>
      setDistance (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
        (V (e n) (pairJInv ⊤ a))).1 q.1.toSet q.2.toSet)
    (fun (a : CoordJ → ℝ) (q : RatCircle × RatCircle) =>
      setDistance (Φ (pairJInv ⊤ a)).1 q.1.toSet q.2.toSet) hR hΦc P'
    (fun n ω => pairJ ⊤ (hN n ω)) (fun ω => pairJ ⊤ (h' ω))
    (fun n => (LQGMetric.measurable_pairJ ⊤).comp (hB.field_measurable n))
    ((LQGMetric.measurable_pairJ ⊤).comp hh'm)
    hXlaw hXllaw hXconv hYconv
  refine ⟨ns, hns, ?_⟩
  intro Ω _ P _ h hh X hX x y r x' y' r' hr hr' _
  have hlaw : P.map (fun ω => pairJ ⊤ (h ω)) = normGFFLaw.map (pairJ ⊤) := by
    change P.map (pairJ ⊤ ∘ h) = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh.1.measurable,
      ← normGFFLaw_eq_of_normalized P h hh]
  have h1 := hae P (fun ω => pairJ ⊤ (h ω))
    ((LQGMetric.measurable_pairJ ⊤).comp hh.1.measurable).aemeasurable hlaw
  have hXe := ae_heat_smoothing_sequence_eq P h hh (fun n => e (ns n)) X hX
  have hVe : ∀ᵐ ω ∂P, ∀ n z, V (e (ns n)) (h ω) z = heatMollify (e (ns n) : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    have h2 := hB.heat_ae (e (ns n))
    rw [normGFFLaw_eq_of_normalized P h hh] at h2
    exact ae_of_ae_map hh.1.measurable.aemeasurable h2
  filter_upwards [h1, hXe, hVe] with ω hω hXω hVω
  have heq : ∀ k, X (e (ns k)) ω = V (e (ns k)) (h ω) := fun k =>
    ContinuousMap.ext fun z => (hXω k z).trans (hVω k z).symm
  let O : RatCircle := ⟨x, y, r, hr⟩
  let O' : RatCircle := ⟨x', y', r', hr'⟩
  have hq := (tendsto_pi_nhds.1 hω) (O, O')
  simp only [LQGMetric.pairJInv_pairJ] at hq
  have hfun : (fun k => ENNReal.ofReal ((m (e (ns k)) : ℝ)⁻¹) *
      setDistance (lfppDistance (ξ : ℝ) (X (e (ns k)) ω))
        (Metric.sphere (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ))
        (Metric.sphere (Complex.mk (x' : ℝ) (y' : ℝ)) (r' : ℝ))) =
      fun k => setDistance (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (ns k)))
        (V (e (ns k)) (h ω))).1 O.toSet O'.toSet := by
    funext k
    rw [setDistance_normalizedLFPPMetric, heq k]
    rfl
  rw [hfun]
  exact hq

 

def PfePointCirclesR : Prop :=
  Final.DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    Final.DG20CouplingData ξ Q m e c V P' h' hN L →
    Final.CoupledRatCoords ξ m e V P' hN L →
    ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ PfeWeyl.NormalizedPointCircles ξ m (fun n => e (ψ n)) Φ

theorem pfePointCirclesR_proved : PfePointCirclesR := by
  intro hI ξ Q m e c V Ω' _ _ P' _ h' hN L hB hZ Φ hΦm hΦ
  obtain ⟨hS4, hPerc, -, -, hPos, -⟩ := hI
  exact normalizedPointCircles_of_coupledRatCoords hS4 hPerc hPos hB hZ Φ hΦm hΦ

end SupercriticalLQGUniqueness.B2.PfeAxioms
