/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXReference

/-!
# Terminal hull locality reduced to an explicit Gaussian hull-limit theorem

The increasing-limit theorem below is a named, unproved mathematical input.
All CMI-specific stopping, convergence, centering and strict locality arguments
are proved here. The hypothesis concerns actual filled Loewner hulls: replacing
the terminal hull by the closure of the earlier hulls can omit a newly filled pocket.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (fwdHull)
open LQGMetric
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The precise remaining Gaussian local-set closure theorem. It is not
asserted as a theorem: filled hulls at increasing finite capacities approaching
a finite capacity must remain local for the same zero-boundary field. -/
def CMIXHullLocalityLimitStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (h : S → DistOn upperHalfPlaneOpens), IsZeroBoundaryGFF upperHalfPlaneOpens h P →
    ∀ W : ℝ≥0 → S → ℝ, (∀ ω, W 0 ω = 0) → (∀ ω, Continuous (W · ω)) →
    ∀ (s : ℕ → S → ℝ≥0) (t : S → ℝ≥0),
      (∀ ω, Monotone fun n => s n ω) → (∀ n ω, s n ω ≤ t ω) →
      (∀ᵐ ω ∂P, Tendsto (fun n => (s n ω : ℝ≥0∞)) atTop (𝓝 (t ω : ℝ≥0∞))) →
      (∀ n, IsLocalSet (fun ω => fwdHull (Ito.rpath (W · ω)) (s n ω)) h P) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (W · ω)) (t ω)) h P

/-- The original terminal hull locality follows from the Gaussian hull-limit
theorem. Its approximating stops, their locality and convergence need no input. -/
theorem cmiWTerminalHullLocalityStatement_of_hullLimit
    (hlimit : CMIXHullLocalityLimitStatement.{u}) : CMIWTerminalHullLocalityStatement.{u} := by
  intro S mS D C τ hτ hτe
  let _ := D.Q₀_prob
  have hs : IsStoppingTime D.driving τ := fun t => C.driving_le t _ (hτ t)
  have hτf : ∀ᵐ ω ∂D.Q₀, τ ω ≠ ⊤ := hτe.mono fun _ h => h.2
  have hs' : IsStoppingTime D.driving fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
    Coupling.isStoppingTime_untopD hs hτf
  let s : ℕ → S → ℝ≥0 := fun n ω => min ((τ ω).untopD 0) (C.announce n ω)
  let u₀ := LocalExt.bheAt D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ)
    (flowLineRhoR D.κ D.b D.J D.y D.θ) (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt D.κ
    (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
    (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
  have hH : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) QuantumZipper.H :=
    WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hloc : ∀ n, IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) (s n ω))
      (WholeField.centredField D.h' u₀) D.Q₀ := by
    intro n
    have hsn : IsStoppingTime D.driving fun ω => (s n ω : WithTop ℝ≥0) := by
      simpa only [s, WithTop.coe_min] using hs'.min (C.announcing.1 n)
    have hlt : ∀ᵐ ω ∂D.Q₀, (s n ω : ℝ≥0∞) < C.e ω :=
      (C.announcing.2.2.1 n).mono fun ω h =>
        (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt h
    have hl := C.isLocalSet_original_of_lt hsn hlt
    simp only [WithTop.untopD_coe] at hl
    exact WholeField.IsLocalSet.sub_dist hl hH
  have hlim : ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => (s n ω : ℝ≥0∞)) atTop
      (𝓝 (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞)) := by
    filter_upwards [RetAux79.ae_tendsto_of_isAnnouncingSeq C.announcing, hτe] with ω ht hτeω
    have hle : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) ≤ C.e ω := by
      change (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ (C.e ω : WithTop ℝ≥0)
      rw [Coupling.coe_untopD_of_ne_top hτeω.2]
      exact hτeω.1
    simpa only [s, ENNReal.coe_min, min_eq_left hle] using
      (tendsto_const_nhds (x := (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞))).min ht
  have hl := hlimit D.Q₀ (WholeField.centredField D.h' u₀)
    (WholeField.isZeroBoundaryGFF_centredField D.coupling hu₀)
    C.W C.zero C.continuous s (fun ω => (τ ω).untopD 0)
    (fun ω => monotone_const.min (C.announcing.2.1 ω)) (fun _ _ => min_le_left _ _) hlim hloc
  have hadd := Coupling.IsLocalSet.add_dist hl hH
  simpa only [WholeField.centredField, sub_add_cancel] using hadd

end InteractingSLE.Restart.FlowStopIdentCMI
