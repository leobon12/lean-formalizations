/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovTest

/-!
# The late incoming heights with a sample-dependent side datum (for R100's relifted chart)

Packet PROVE-COLLAR-COVER (third round). Ruling R100 relifts the counterflow chart by `2π(n − 1)` with a branch `n`
that may vary with the sample; read in the unrelifted chart, the offset is then sample-dependent. The incoming part
of the cover is pathwise in the side datum, so it is restated here for side data `eS : Ω → Late.SideData Ω`:

* **`ae_initialHeights_of_meanFormula_testS`**: the initial heights of one test from its mean formula with the offset
  `(eS ω).offset` (the copy of `ae_initialHeights_of_meanFormula_test` with the datum read at each sample);
* **`ae_reference_incoming_own_heights_of_initialS`**: SIDE-COLLAR2's `ae_reference_incoming_own_heights_of_initial`
  with the datum read at each sample (proof copied verbatim, `e ↦ eS ω`; the transport is linear in the target value).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField
open Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopWallsFin Sec7.Lemma71C
  Sec7.Aux119Heights

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The initial heights of one test from its mean formula** (SIDE-COLLAR2's
`initialReferenceHeightsExc_of_meanFormula` for a single test): one local mean `G` of the capacity-`0` reference
with the canonical interior formula (offset of `eS ω`) gives, almost surely on the test, the native word at capacity `0`
as the limit of the base-chart reading. -/
theorem ae_initialHeights_of_meanFormula_testS {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d) (eS : Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    {G : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G)
    (hGform : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
        chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z =
        j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) - (eS ω).offset) :
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ, x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω) (j.target i d).harmonic
        (harmRep (G ω) (H \ j.capacityReference i d 0 ω))) (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d (eS ω) 0 ω x)) := by
  have hSet := j.activeCompl_zero_eq_capacityReference (i := i) hj hRc hLc
  have hgCur := hG
  rw [← hSet] at hgCur
  have hEq := j.ae_initial_reference_eq hj hRc hLc hRm hLm hKilled hCoupling hG hgCur
  filter_upwards [hEq, hG.2.1, hGform] with ω hEq hH hFormulaω hA ξ hξ
  obtain ⟨hv₀, hrep₀⟩ := harmRep_spec hH
  have hEqv := hEq _ hv₀ hrep₀
  have hDriven := SideTest.isDrivenCurve_target hj ω hA
  have hBase := j.isDomainChart_baseChart hj hRc hLc hA
  have hCurrent := j.isDomainChart_relChart_of_ready hj hRc hLc hA (PocketPhaseMeans.capLife_pos hDriven)
  have hPhase := j.initial_phase_window_eq_zero hj hA ((eS ω).phase 0 ω) ξ
  show Tendsto _ _ (𝓝 (forceBoundaryData (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR
      (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a 0 ω -
        segDriver ((j.target i d).curve ω) 0)
      (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a 0 ω -
        segDriver ((j.target i d).curve ω) 0) ξ +
      (eS ω).phase 0 ω * (Ioo
        (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL (Late.leftZero i d j) 0 ω -
          segDriver ((j.target i d).curve ω) 0)
        (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR (Late.rightZero i d j) 0 ω -
          segDriver ((j.target i d).curve ω) 0)).indicator 1 ξ - (eS ω).offset))
  rw [hPhase, add_zero]
  have hlim := ((j.isBoundedHarmonicExtension_initialWordExtension i d ω).2.2 ξ hξ).sub_const (eS ω).offset
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hInv := relChart_zero_inv_of_driven (c := (j.target i d).baseChart) hDriven hz
  have hDom : ((j.target i d).baseChart ω).2.1 z ∈ (j.target i d).domain ω := by
    rw [← hBase.2.1]
    exact mem_image_of_mem _ hz
  have hComp : ((j.target i d).baseChart ω).2.1 z ∈ H \ j.capacityReference i d 0 ω := by
    rw [← hSet, ← hCurrent.2.1, ← hInv]
    exact mem_image_of_mem _ hz
  dsimp only [sideMean]
  rw [hEqv hComp, hFormulaω hA _ hDom, hBase.fwd_inv hz]

theorem ae_reference_incoming_own_heights_of_initialS
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (eS : Ω → Late.SideData Ω) (hHarm : EqOn d.harmonic d.coupledMean H)
    (s : ℕ → ℝ≥0) {g₀ : Ω → DistOn upperHalfPlaneOpens}
    {gB : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hg₀ : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure g₀)
    (hgB : ∀ r, IsLocalSetMean (j.capacityReference i d (s r))
      (j.target i d).zeroField d.measure (gB r))
    (hInitial : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ,
      x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω)
        (j.target i d).harmonic (harmRep (g₀ ω) (H \ j.capacityReference i d 0 ω)))
        (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d (eS ω) 0 ω x))) :
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ r : ℕ,
      d.curve ω (s r) ∈ (j.target i d).domain ω → ∀ q : ℝ≥0,
      (j.visitCapacity d ω (s r)).toNNReal ≤ q →
      ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ q' : ℝ, (q : ℝ) < q' →
      EqOn (fun t : ℝ => segDriver ((j.target i d).curve ω) t.toNNReal) W (Icc 0 q') →
      ∀ (x : ℝ) (a : ℝ → ℂ), QuantumZipper.IsForwardSol W x q a →
      x ∉ forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω) →
      x ∉ (j.target i d).jumps 0 ω →
      (a (j.visitCapacity d ω (s r)).toNNReal).re ∉
        (j.target i d).jumps (j.visitCapacity d ω (s r)).toNNReal ω →
      Tendsto (sideMean (j.target i d).kappa (j.referenceVisitChart i d ω (s r))
        (j.target i d).harmonic (harmRep (gB r ω) (H \ j.capacityReference i d (s r) ω)))
        (𝓝[H] ((a (j.visitCapacity d ω (s r)).toNNReal).re : ℂ))
        (𝓝 (j.nativeSideWord i d (eS ω) (j.visitCapacity d ω (s r)).toNNReal ω
          (a (j.visitCapacity d ω (s r)).toNNReal).re)) := by
  have hSet₀ : j.capacityReference i d 0 =
      eventFilled j.event (j.target i d).domain (fun _ => ∅) := by
    rw [capacityReference, original_filling_zero]
  have hg₀' := hg₀
  rw [hSet₀, target_zeroField] at hg₀'
  have hall := ae_all_iff.2 fun r => ae_exact_height_transport_at_surviving_visit hj
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont hStart hMeas
    hDetermined hLocal (s r) hg₀' (by
      simpa only [capacityReference, target_zeroField] using hgB r)
  have hHB := ae_all_iff.2 fun r => (hgB r).2.1
  filter_upwards [hall, hHB, hg₀.2.1, hInitial, ae_regHull_eq hCoupling hLife]
    with ω hTransportω hHB hH₀ hInitialω hHull hω r hVisit q hOrder W hW hW0 q' hqq' hEq
      x a ha hx hx₀ hxB
  let p := (j.visitCapacity d ω (s r)).toNNReal
  let v₀ := harmRep (g₀ ω) (H \ j.capacityReference i d 0 ω)
  let vB := harmRep (gB r ω) (H \ j.capacityReference i d (s r) ω)
  have hBase := isDomainChart_baseChart hj (hCont 0) (hCont 1) hω
  have hOld := isDomainChart_capacityReference_at_visit hj (hCont 0) (hCont 1)
    hω (s r) hVisit (hHull (s r))
  have hpq : (p : ℝ) ≤ q := by exact_mod_cast hOrder
  have hChart : j.referenceVisitChart i d ω (s r) =
      ((j.target i d).baseChart ω).loewner W p :=
    loewner_congr _ p.coe_nonneg (hpq.trans_lt hqq') hEq
  have haP := QuantumZipper.isForwardSol_restrict ha p.coe_nonneg hpq
  have ha₀ := QuantumZipper.isForwardSol_restrict ha (show (0 : ℝ) ≤ 0 from le_rfl) q.coe_nonneg
  have haZero : (a 0).re = x := by
    simpa only [hW0, Complex.ofReal_zero, sub_zero, Complex.ofReal_re] using
      congrArg Complex.re (QuantumZipper.FwdHolo.sol_zero ha q.coe_nonneg)
  have hEqP : EqOn (fun t : ℝ => segDriver ((j.target i d).curve ω) t.toNNReal) W
      (Icc 0 (p : ℝ)) := fun t ht => hEq ⟨ht.1, ht.2.trans (hpq.trans_lt hqq').le⟩
  have hEq₀ : EqOn (fun t : ℝ => segDriver ((j.target i d).curve ω) t.toNNReal) W
      (Icc 0 ((0 : ℝ≥0) : ℝ)) := fun t ht =>
    hEq ⟨ht.1, ht.2.trans (q.coe_nonneg.trans hqq'.le)⟩
  have hWord₀ := nativeSideWord_of_surviving_real j i d (eS ω) hW hW0 hEq₀ ha₀ hx
    (by simpa only [NNReal.coe_zero, haZero] using hx₀)
  have hWordP := nativeSideWord_of_surviving_real j i d (eS ω) hW hW0 hEqP haP hx hxB
  rw [NNReal.coe_zero, haZero] at hWord₀
  have hInitial' : Tendsto (sideMean i.kappa ((j.target i d).baseChart ω) d.coupledMean v₀)
      (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d (eS ω) 0 ω x)) := by
    refine (hInitialω hω x hx₀).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hzC : ((j.target i d).baseChart ω).2.1 z ∈ (j.target i d).domain ω := by
      rw [← hBase.coe_dom]
      exact hBase.1.inv_mem_dom hz
    dsimp only [sideMean]
    rw [target_kappa_eq, target_harmonic_eq, hHarm (hBase.subset_H hzC)]
  obtain ⟨hv₀, hrep₀⟩ := harmRep_spec hH₀
  obtain ⟨hvB, hrepB⟩ := harmRep_spec (hHB r)
  have hv₀' : InnerProductSpace.HarmonicOnNhd v₀
      (H \ eventFilled j.event (j.target i d).domain (fun _ => ∅) ω) :=
    fun z hz => hv₀ z (by rwa [hSet₀])
  have hrep₀' : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ H \ eventFilled j.event (j.target i d).domain (fun _ => ∅) ω →
      g₀ ω φ = ∫ z, v₀ z * φ z := by
    intro φ hφ
    exact hrep₀ φ (by rwa [hSet₀])
  have hωj : ω ∈ j.event := by rwa [target_event] at hω
  have hHeight := hTransportω r hωj v₀ vB hv₀' hrep₀' hvB hrepB hVisit
    W hW hW0 hChart x a haP _ hInitial'
  rw [hWord₀.trans hWordP.symm] at hHeight
  refine hHeight.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hzOld : (j.referenceVisitChart i d ω (s r)).2.1 z ∈
      H \ j.capacityReference i d (s r) ω := by
    rw [← hOld.coe_dom]
    exact hOld.1.inv_mem_dom hz
  dsimp only [sideMean]
  rw [target_kappa_eq, target_harmonic_eq, hHarm hzOld.1]
  rfl

end InteractingSLE.Sec7.ColCov
