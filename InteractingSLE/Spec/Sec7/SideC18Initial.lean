/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Collar
import InteractingSLE.Spec.Sec7.SideC15Collar

/-! # The zero-capacity collar in R100's frame

PROVE-SIDE-COLLAR2. Use the actual original-zero reference. Equality
of harmonic representatives supplies the comparison germ, and the same
integer relift in current and reference charts cancels exactly.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current LocalSets PocketStop PocketTraversal Lemma71C PocketStopSide Aux119Heights PocketCoupling
variable {Ω : Type} [MeasurableSpace Ω]

/-- The full initial collar in the relifted frame, on a whole ready
test, from its proved interior native mean formula. -/
theorem initialCollarAtZeroShift_of_meanFormula
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} [IsProbabilityMeasure d.measure]
    (hj : j.Ready d) (e : Late.SideData Ω) (m : Ω → ℤ) (X : ℝ≥0 → Ω → Set ℂ)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : ℕ → ℝ≥0) (r : ℕ) (hr : s r = 0)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    {G : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G)
    (hFormula : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
        chiC (j.target i d).kappa *
          (PocketStopField.shiftChart ((j.target i d).baseChart ω) (m ω)).2.2 z =
      j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) - e.offset) :
    collarAtExcWithChart j i d
      (reliftReferences (e.withVisitReferences i j d hKilled s) m)
      (fun ω => PocketStopField.shiftChart ((j.target i d).baseChart ω) (m ω)) X 0
 := by
  unfold collarAtExcWithChart
  intro target refs zL zR gB hgB g hg
  dsimp only [refs, reliftReferences] at hgB ⊢
  have hRef := j.visit_reference_zero_eq (i := i) hj hRc hLc hKilled e s hr
  have hSet := j.activeCompl_zero_eq_capacityReference (i := i) hj hRc hLc
  have hMeasure : target.measure = d.measure := SideTest.target_measure j i d
  have hg₀ : IsLocalSetMean (j.capacityReference i d 0) target.zeroField d.measure (gB r) := by
    have h := hgB r
    rw [hMeasure, hRef.1, hSet] at h
    exact h
  rw [hMeasure] at hg ⊢
  have hMean := j.ae_initial_reference_eq hj hRc hLc hRm hLm
    hKilled hCoupling hg₀ hg
  have hGCur := hG
  rw [← hSet] at hGCur
  have hFormulaEq := j.ae_initial_reference_eq hj hRc hLc hRm hLm hKilled hCoupling hg₀ hGCur
  filter_upwards [hMean, hFormulaEq, hFormula, hG.2.1] with ω hEq hFormulaEqω hFormulaω hHω hω hq v hv hrep ξ hξ _hX
  have hEqv := hEq v (hSet ▸ hv) (hSet ▸ hrep)
  have hDriven := SideTest.isDrivenCurve_target hj ω hω
  have hBase := j.isDomainChart_baseChart hj hRc hLc hω
  have hlim := ((j.isBoundedHarmonicExtension_initialWordExtension i d ω).2.2 ξ hξ).sub_const e.offset
  have hCurrent := j.isDomainChart_relChart_of_ready hj hRc hLc hω hq
  have hLift := hRef.2 ω hω
  obtain ⟨hGv, hGrep⟩ := harmRep_spec hHω
  have hEqG := hFormulaEqω _ hGv hGrep
  have hPhase := j.initial_phase_window_eq_zero hj hω (e.phase 0 ω) ξ
  have hHeightω : Tendsto (sideMean target.kappa (PocketStopField.shiftChart (target.baseChart ω) (m ω)) target.harmonic
      (harmRep (gB r ω) (H \ j.capacityReference i d 0 ω)))
      (𝓝[H] (ξ : ℂ)) (𝓝 (forceBoundaryData target.kappa target.rhoL target.rhoR
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a 0 ω - segDriver (target.curve ω) 0)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a 0 ω -
          segDriver (target.curve ω) 0) ξ +
        e.phase 0 ω * (Ioo
          (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL 0 ω - segDriver (target.curve ω) 0)
          (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR 0 ω -
            segDriver (target.curve ω) 0)).indicator 1 ξ - e.offset)) := by
    rw [hPhase, add_zero]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hCy : (target.baseChart ω).2.1 y ∈ target.domain ω := hBase.inv_mem hy
    have hComp : (target.baseChart ω).2.1 y ∈ H \ j.capacityReference i d 0 ω := by
      rw [← hSet, ← hCurrent.2.1, ← relChart_zero_inv_of_driven hDriven hy]
      exact mem_image_of_mem _ hy
    dsimp only [sideMean]
    simp only [shiftChart_inv]
    rw [← hEqG hComp, hFormulaω hω _ hCy, hBase.fwd_inv hy]
  let b := forceBoundaryData target.kappa target.rhoL target.rhoR
    (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a 0 ω -
      segDriver (target.curve ω) 0)
    (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a 0 ω -
      segDriver (target.curve ω) 0) ξ +
    refs.phase 0 ω * (Ioo
      (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL 0 ω -
        segDriver (target.curve ω) 0)
      (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR 0 ω -
        segDriver (target.curve ω) 0)).indicator 1 ξ - refs.offset
  refine ⟨r, b, 0, ?_, ?_, ?_, ?_⟩
  · refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hDom : (relChart target.baseChart target.curve 0 ω).2.1 z ∈
        H \ j.capacityReference i d 0 ω := by
      rw [← hSet, ← hCurrent.2.1]
      exact mem_image_of_mem _ hz
    simp only [relChart_shift_inv]
    rw [hRef.1, hSet, hEqv hDom, sub_self]
  · refine hHeightω.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hInv := relChart_zero_inv_of_driven (c := target.baseChart)
      (SideTest.isDrivenCurve_target hj ω hω) hz
    dsimp only [sideMean]
    simp only [shiftChart_inv, relChart_shift_inv]
    rw [hRef.1, hSet, hInv]
    change _ = _ + _ + chiC target.kappa * (_ - 2 * π * m ω)
    rw [hLift]
    simp only [relChart, NNReal.coe_zero, Theorem14.GW2aCont.loewner_zero_lift]
    rfl
  · refine (tendsto_const_nhds (x := (0 : ℝ))).congr' (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [relChart_shift_lift]
    simp only [relChart_shift_inv]
    change 0 = (_ - 2 * π * m ω) - (_ - 2 * π * m ω)
    rw [hLift]
    ring
  · dsimp only [b]
    rw [mul_zero, add_zero]
    rfl


end InteractingSLE.Sec7.SideC18
