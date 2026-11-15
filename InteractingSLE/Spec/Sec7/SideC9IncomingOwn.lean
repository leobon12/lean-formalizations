/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC9InitialWord
import InteractingSLE.Spec.Sec7.PocketSideInCensusHeight

/-!
# Incoming own heights for every fixed reference mean version

PROVE-SIDE-COLLAR2. Reuse the landed arbitrary-version incoming transport
at deterministic original reference times. One countable event supplies
every reference's own height; SideC8's exact word theorem identifies its
value. Initial heights remain named input. No increment law is reproved.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 LocalSets WholeField Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal
  Sec7.PocketStopWallsFin Sec7.Lemma71C Sec7.Aux119Heights

/-- Every prescribed positive-reference mean has the exact incoming own
height on one event, from the initial mean's own heights. -/
theorem ae_reference_incoming_own_heights_of_initial
    {Ω : Type} [MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
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
    (e : Late.SideData Ω) (hHarm : EqOn d.harmonic d.coupledMean H)
    (s : ℕ → ℝ≥0) {g₀ : Ω → DistOn upperHalfPlaneOpens}
    {gB : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hg₀ : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure g₀)
    (hgB : ∀ r, IsLocalSetMean (j.capacityReference i d (s r))
      (j.target i d).zeroField d.measure (gB r))
    (hInitial : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ,
      x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω)
        (j.target i d).harmonic (harmRep (g₀ ω) (H \ j.capacityReference i d 0 ω)))
        (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d e 0 ω x))) :
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
        (𝓝 (j.nativeSideWord i d e (j.visitCapacity d ω (s r)).toNNReal ω
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
  have hWord₀ := nativeSideWord_of_surviving_real j i d e hW hW0 hEq₀ ha₀ hx
    (by simpa only [NNReal.coe_zero, haZero] using hx₀)
  have hWordP := nativeSideWord_of_surviving_real j i d e hW hW0 hEqP haP hx hxB
  rw [NNReal.coe_zero, haZero] at hWord₀
  have hInitial' : Tendsto (sideMean i.kappa ((j.target i d).baseChart ω) d.coupledMean v₀)
      (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d e 0 ω x)) := by
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

end InteractingSLE.Wire.Current.SideTest
