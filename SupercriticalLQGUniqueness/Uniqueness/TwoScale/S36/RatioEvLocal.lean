import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.BumpMarginal
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalB




 











set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC DistOn addConst restrictTo)

 
def ratioCarrier (s : ℝ) (x : ℂ) : Set ℂ := {y : ℂ | 4 * s / 5 < ‖y - x‖ ∧ ‖y - x‖ < 16 * s / 5}

 

theorem ratioEv_transfer {d₁ d₂ : LSCMetric} (hB₁ : BiLipschitz.Barrier.Barrier d₁) (hB₂ : BiLipschitz.Barrier.Barrier d₂)
    (hL₁ : d₁.IsLengthSpace) (hL₂ : d₂.IsLengthSpace) {U : Set ℂ}
    (hI : ∀ u v, intExt d₁ U u v = intExt d₂ U u v) {s : ℝ} (hs : 0 < s) (x : ℂ)
    (hU : ratioCarrier s x ⊆ U) : RatioEv d₁ hs x ↔ RatioEv d₂ hs x := by
  have hout : (annOut hs x).toSet ⊆ U := by
    intro y hy
    have hy' : y ∈ Metric.ball x (3 * s) ∧ y ∉ closure (Metric.ball x (2 * s)) := hy
    rw [closure_ball x (by positivity), Metric.mem_ball, Metric.mem_closedBall, not_le,
      dist_eq_norm] at hy'
    exact hU ⟨by linarith [hy'.2], by linarith [hy'.1]⟩
  have hin : {y : ℂ | (annIn hs x).innerRadius < ‖y - (annIn hs x).center‖ ∧
      ‖y - (annIn hs x).center‖ < 3 * s} ⊆ U := by
    intro y hy
    have hy' : s < ‖y - x‖ ∧ ‖y - x‖ < 3 * s := hy
    exact hU ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  have ha := around_transfer hI hout
  have hc := across_transfer hB₁ hB₂ hL₁ hL₂ hI
    (show (annIn hs x).outerRadius < 3 * s by change 2 * s < 3 * s; linarith) hin
  unfold RatioEv
  rw [ha, hc]

theorem ae_ratioEv_addConst_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    {s : ℝ} (hs : 0 < s) (x : ℂ) (t : Ω → ℝ) :
    ∀ᵐ ω ∂P, (RatioEv (D (addConst (h ω) (t ω))) hs x ↔ RatioEv (D (h ω)) hs x) := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul P h hh ξ Q D hD t] with ω hw
  exact ratioEv_scale_iff (D (h ω)) (D (addConst (h ω) (t ω))) _
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    (fun u v => hw (u, v)) hs x

 
theorem canonical_ratio_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {s : ℝ} (hs : 0 < s) (x : ℂ) (U : TopologicalSpace.Opens ℂ)
    (hU : ratioCarrier s x ⊆ U) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      {g : DistC | RatioEv (D g) hs x} =ᵐ[muH P h] restrictTo U ⁻¹' S := by
  have hprob := muH_isProb P h hh.1
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (muH P h) :=
    BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  set E := {g : DistC | RatioEv (D g) hs x} with hEdef
  obtain ⟨FD, -, hlocD⟩ := hD.locality (muH P h) id hμ U
  have hGood : ∀ᵐ g ∂(muH P h), BiLipschitz.Barrier.Barrier (D g) ∧ (D g).IsLengthSpace ∧
      (D g).internal U = FD (restrictTo U g) := by
    filter_upwards [BiLipschitz.OneScale.canonical_gaussianShift_barrier P h hh ξ Q hQ D hD,
      hD.length (muH P h) id hμ, hlocD] with g h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨W, hWae, hWm, hWsub⟩ := hGood.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he hE₁
    have hres : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    obtain ⟨hB₁, hL₁, hi₁⟩ := hWsub g₁ hg₁
    obtain ⟨hB₂, hL₂, hi₂⟩ := hWsub g₂ hg₂
    have hId : ∀ u v, intExt (D g₁) U u v = intExt (D g₂) U u v :=
      intExt_eq_of_internal_eq (by rw [hi₁, hi₂, hres])
    exact (ratioEv_transfer hB₁ hB₂ hL₁ hL₂ hId hs x hU).mp hE₁
  have hB : NullMeasurableSet E ((muH P h).map id) :=
    (measurable_ratioEv D hD.measurable hs x).nullMeasurableSet
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := E) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl) hWm hB hWae hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  exact hFe

 

theorem ratio_centered_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {s : ℝ} (hs : 0 < s) (x : ℂ) (U : TopologicalSpace.Opens ℂ)
    (hU : ratioCarrier s x ⊆ U) (R : ℝ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) R x)) U)
      {ω | RatioEv (D (h ω)) hs x} := by
  set E := {g : DistC | RatioEv (D g) hs x} with hEdef
  let q' : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-LQGMetric.circleAvg (h ω) R x))
  obtain ⟨S, hS, hLocal⟩ := canonical_ratio_local P h hh ξ Q hQ D hD hs x U hU
  have hmeasH := (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  have hLocalProd : {y : Ω × ℝ | BiLipschitz.OneScale.gaussianShift h y ∈ E}
      =ᵐ[P.prod BiLipschitz.OneScale.standardGaussian]
      {y : Ω × ℝ | restrictTo U (BiLipschitz.OneScale.gaussianShift h y) ∈ S} :=
    ae_of_ae_map hmeasH.aemeasurable hLocal
  have hprod : LQGMetric.IsGFFPlusCont (fun y : Ω × ℝ => h y.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh.1)
  have hInv := ae_ratioEv_addConst_iff (P.prod BiLipschitz.OneScale.standardGaussian) (fun y => h y.1)
    hprod ξ Q D hD hs x (fun y => y.2)
  have hAE : ∀ᵐ y ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (h y.1 ∈ E ↔
        BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) R x + y.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with y hi hl
    have hShift : BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) R x + y.2) =
        restrictTo U (BiLipschitz.OneScale.gaussianShift h y) := by
      calc
        BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) R x + y.2) =
            restrictTo U (addConst (addConst (h y.1) (-LQGMetric.circleAvg (h y.1) R x))
              (LQGMetric.circleAvg (h y.1) R x + y.2)) :=
          BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h y.1) y.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 2
          ring
        _ = restrictTo U (BiLipschitz.OneScale.gaussianShift h y) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := BiLipschitz.OneScale.gaussian_smoothing_event P U q'
    (fun ω => LQGMetric.circleAvg (h ω) R x) {ω | h ω ∈ E} S hS hAE
  refine ⟨{ω | BiLipschitz.OneScale.gaussianSmooth U S (q' ω) > 1 / 2}, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U | BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
