/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootU19Observe

/-!
# Actual canonical own-chart observations are adapted to the retained stage

Packet PROVE-T14-GW2ROOT2. The original canonical driver and its Borel tip
evaluation through a prescribed cutoff are measurable in the actual full
stage record. Regular-driver record uniqueness supplies the fibre identity;
no observation-measurability or reconstruction hypothesis is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootU19

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- Actual canonical driver/tip coordinates up to a stopped own time are
measurable in the complete retained stage, including exceptional samples. -/
theorem measurable_stageSigma_canonical_observation (hβA : Measurable βA) (hh : Measurable h)
    {P : Measure Ω} (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (spec : ExplSpec) (n : ℕ)
    (j : Fin n) (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ specDelta spec j) :
    Measurable[stageSigma hκ h12p βA c₀ h s W' ζ' spec n] (fun ω =>
      ((canonSpecFam hκ h12p βA c₀ h spec j ω).1 t,
        LP.traceAt t (canonSpecFam hκ h12p βA c₀ h spec j ω).1)) := by
  have hC : Measurable (canonSpecFam hκ h12p βA c₀ h spec j) :=
    measurable_canonFam hκ h12p βA c₀ (specAngle spec) (specDelta spec) spec.1 hβA hh j
  have hCm := measurable_fst.comp hC
  have hObs := ((measurable_pi_apply t).comp hCm).prodMk ((LP.measurable_traceAt t).comp hCm)
  have hstage : Measurable (stageMap hκ h12p βA c₀ h s W' ζ' spec n) :=
    Measurable.of_comap_le (stageSigma_le hβA hh hcf s spec n)
  apply measurable_comap_of_saturated hstage hObs
  intro ω ω' hsame
  have hr := congrFun (congrArg Prod.snd hsame) j
  change recOf (specDelta spec j) (canonSpecFam hκ h12p βA c₀ h spec j ω) =
    recOf (specDelta spec j) (canonSpecFam hκ h12p βA c₀ h spec j ω') at hr
  let u := (specDelta spec j).toNNReal
  have hu : (u : ℝ≥0∞) = specDelta spec j := ENNReal.coe_toNNReal (specDelta_ne_top spec j)
  rw [← hu] at hr
  have hreg := isRegularDriver_canonDrive hκ h12p βA c₀ spec.1
    (specAngle spec) (specDelta spec) (h ω) j
  have hreg' := isRegularDriver_canonDrive hκ h12p βA c₀ spec.1
    (specAngle spec) (specDelta spec) (h ω') j
  have hcanon := canonDrv_eq_of_readRec_eq hreg hreg' hr
  have htu : t ≤ u := ENNReal.coe_le_coe.mp (hu.symm ▸ ht)
  have heq : ∀ q ≤ t, (canonSpecFam hκ h12p βA c₀ h spec j ω).1 q =
      (canonSpecFam hκ h12p βA c₀ h spec j ω').1 q := by
    intro q hq
    have hc := congrArg (fun e : (ℝ≥0 → ℝ) × ℝ≥0∞ => e.1 q) hcanon
    rwa [canonDrv_fst_eq_of_le hreg (hq.trans htu),
      canonDrv_fst_eq_of_le hreg' (hq.trans htu)] at hc
  exact Prod.ext (heq t le_rfl) (LP.traceAt_congr heq)

/-- The same exact adaptedness in the root-test sigma-algebra, for every
root and retained canonical piece through its own cutoff. -/
theorem measurable_rootSigma_canonical_observation (hβA : Measurable βA) (hh : Measurable h)
    {P : Measure Ω} (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (j : Fin ((entryList l).length + 1)) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ specDelta (schedSpecOf r.1 l) j) :
    Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r l] (fun ω =>
      ((canonSpecFam hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω).1 t,
        LP.traceAt t (canonSpecFam hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω).1)) :=
  measurable_stageSigma_canonical_observation hκ h12p βA c₀ h hβA hh
    s W' ζ' hcf (schedSpecOf r.1 l) _ j t ht

end InteractingSLE.Theorem14.GW2TipSystem.RootU19
