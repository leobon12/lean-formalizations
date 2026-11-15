/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC6Sets

/-!
# Initial comparison for arbitrary local-mean versions

PROVE-SIDE-COLLAR2. Equality of the actual initial sets and uniqueness of
local means identify their harmonic representatives on the whole initial
domain, on one event. No residual-law or boundary-height premise is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 LocalSets WholeField Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketStopField
  Sec7.Aux119Heights Sec7.PocketCoupling

/-- Arbitrary versions of the initial current mean and the original-zero
reference have identical harmonic representatives on their whole domain. -/
theorem ae_initial_reference_eq {Ω : Type} [MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} [IsProbabilityMeasure d.measure]
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    {gB g : Ω → DistOn upperHalfPlaneOpens}
    (hgB : IsLocalSetMean (j.capacityReference i d 0)
      (j.target i d).zeroField d.measure gB)
    (hg : IsLocalSetMean
      (activeCompl (j.target i d).event (j.target i d).curve (j.target i d).baseChart 0)
      (j.target i d).zeroField d.measure g) :
    ∀ᵐ ω ∂d.measure, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ j.capacityReference i d 0 ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ j.capacityReference i d 0 ω →
        g ω φ = ∫ z, v z * φ z) →
      EqOn v (harmRep (gB ω) (H \ j.capacityReference i d 0 ω))
        (H \ j.capacityReference i d 0 ω) := by
  rw [activeCompl_zero_eq_capacityReference hj hRc hLc] at hg
  have hA := measurable_original_filling (i := i) hj hRc hLc hRm hLm hKilled 0
  have hOpen := fun ω => (original_filling_regular (i := i) hj 0 ω).2
  have hhm : Measurable (j.target i d).zeroField := by
    rw [target_zeroField]
    exact measurable_centredField hCoupling.2.1 d.coupledMean
  have hEq := ae_mean_apply_eq_on_compl hA hhm hOpen hg hgB
  filter_upwards [hEq, hgB.2.1] with ω hEq hH v hv hrep
  obtain ⟨hvB, hrepB⟩ := harmRep_spec hH
  refine Sec6.eqOn_of_integral_mul_eq (hOpen ω) sdiff_subset hv hvB ?_
  intro φ hφ
  rw [← hrep φ hφ, hEq φ hφ, hrepB φ hφ]

end InteractingSLE.Wire.Current.SideTest
