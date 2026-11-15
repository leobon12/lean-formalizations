/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceCaps
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceHeights

/-!
# GW4: the mean input from phase constancy and one stopping lifetime

The named remaining analytic input records the phase-word pointwise
martingales and a phase constant on positive times through the cutoff. The
finite caps, their cover and their mean continuity are constructed here.
The through-cutoff clause is explicit: constancy only strictly before `V`
does not by itself identify the stopped endpoint value required by Aux. 122.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H swallowTime)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Supp8.Q3Stop Sec7.PhaseSel Sec7.PhaseSelAdapt MartChar

/-- **Open analytic input.** The actual positive-time phase and its pointwise
martingale means through one stopping cutoff. This does not assert zero phase,
and does not stand for a proof of the boundary-collar representation. -/
structure ComponentPhaseBefore {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) where
  probability : IsProbabilityMeasure ν
  filtration : Filtration ℝ≥0 mΩ
  rightContinuous : filtration.IsRightContinuous
  adapted : StronglyAdapted filtration R
  lifetimeStopping : IsStoppingTime filtration V
  phase : ℝ≥0 → Ω → ℝ
  value : Ω → ℝ
  positive_const : ∀ ω (q : ℝ≥0), 0 < q → (q : ℝ≥0∞) ≤ V ω → phase q ω = value ω
  lattice : ∀ ω, ∃ j : ℤ, value ω = j * phaseStep k
  martingales : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω q, IsBoundedHarmonicExtension
      (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
        (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω) (phase q ω))
      (forceJumpSet (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω)) (U ω q)) →
    ∀ z ∈ H, IsLocalMartingaleBefore filtration ν
      (fun ω => min (swallowTime (wpath R ω) z : WithTop ℝ≥0) (V ω))
      (fun q ω => couplingMean k (wpath R ω) q (U ω q) z)

/-- Construct all finite protected-cap inputs. The seed upper bounds are
separate arguments so the incoming-height calculation can supply them. -/
def ComponentPhaseBefore.toCaps {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (h : ComponentPhaseBefore k c₀ ν X R V)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (hL : typedRhoL (wordType k c₀) (componentSeedL k c₀) ≤ k / 2 - 4)
    (hR : typedRhoR (wordType k c₀) (componentSeedR k c₀) ≤ k / 2 - 4) :
    ComponentPhaseCaps k c₀ ν X R V := by
  have := h.probability
  refine {
    probability := h.probability
    filtration := h.filtration
    rightContinuous := h.rightContinuous
    adapted := h.adapted
    seedL_upper := hL
    seedR_upper := hR
    phase := h.phase
    caps := gw4PhaseCap V
    stopping := isStoppingTime_gw4PhaseCap h.lifetimeStopping,
    cover := Eventually.of_forall (fun _ _ hq => exists_le_gw4PhaseCap hq),
    quantized := ?_
    martingales := ?_
    continuity := ?_ }
  · intro n q ω hq hqcap
    obtain ⟨j, hj⟩ := h.lattice ω
    exact ⟨j, (h.positive_const ω q hq
      ((ENNReal.coe_le_coe.2 hqcap).trans (gw4PhaseCap_le V n ω))).trans hj⟩
  · intro n U hU z hz
    have hm := h.martingales U hU z hz
    have hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) <
        min (swallowTime (wpath R ω) z : WithTop ℝ≥0) (V ω) →
        ContinuousWithinAt (fun q : ℝ≥0 => couplingMean k (wpath R ω) q (U ω q) z)
          (Ici s) s := by
      intro ω s hs
      have hc := continuousWithinAt_of_continuousOn_Icc hz
        (f := fun q : ℝ => couplingMean k (wpath R ω) q (U ω q.toNNReal) z)
        (fun T hT hTV hzT => continuousOn_componentMean_of_positive_phase_const hR0 hRc hU hT
          (fun q hq hqT => h.positive_const ω q hq
            ((ENNReal.coe_le_coe.2 hqT).trans hTV.le)) hzT) hs
      simpa only [Real.toNNReal_coe] using hc
    have hm' := isLocalMartingaleBefore_min_stop hm hrc
      (isStoppingTime_const h.filtration (n : ℝ≥0))
    refine isLocalMartingaleBefore_congr_life (fun ω => ?_) hm'
    change min (min (swallowTime (wpath R ω) z) (V ω)) (n : ℝ≥0∞) =
      min (swallowTime (wpath R ω) z) (gw4PhaseCap V n ω : ℝ≥0∞)
    rw [coe_gw4PhaseCap]
    exact min_assoc _ _ _
  · intro n U hU ω z T hT hTcap hz
    refine continuousOn_componentMean_of_positive_phase_const hR0 hRc hU hT
      (fun q hq hqT => h.positive_const ω q hq ?_) hz
    exact (ENNReal.coe_le_coe.2 (hqT.trans (WithTop.coe_le_coe.1 hTcap))).trans
      (gw4PhaseCap_le V n ω)

/-- The constructed cap data retain exactly the same phase. -/
theorem ComponentPhaseBefore.toCaps_phase {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (h : ComponentPhaseBefore k c₀ ν X R V)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (hL : typedRhoL (wordType k c₀) (componentSeedL k c₀) ≤ k / 2 - 4)
    (hR : typedRhoR (wordType k c₀) (componentSeedR k c₀) ≤ k / 2 - 4) :
    (h.toCaps hR0 hRc hL hR).phase = h.phase := rfl

/-- The actual mean with zero phase, from the incoming heights, positive-time
phase constancy and pointwise martingales. The seed lower bounds are the
already available first partial sums of GW3's word. -/
theorem componentLineMean_of_incoming_phaseBefore {Ω : Type*} [MeasurableSpace Ω]
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)} {u₀ : ℂ → ℝ}
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    {bC : ℝ → ℝ} {JC : Finset ℝ} (hh : IncomingHeightBounds κ bC JC)
    (hJ : c₀.jumps = Sec7.StripSysField.counterflowJumps JC)
    (hc : ∀ y ∉ c₀.jumps, c₀.fn y = Sec7.StripSysField.counterflowData κ bC y)
    (hL : -2 < typedRhoL (wordType (16 / κ) c₀) (componentSeedL (16 / κ) c₀))
    (hR : -2 < typedRhoR (wordType (16 / κ) c₀) (componentSeedR (16 / κ) c₀))
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (h : ComponentPhaseBefore (16 / κ) c₀ ν X R V)
    (hrep : ComponentPhaseRepresentation (16 / κ) c₀ F ν X Wd GT R V u₀ B h.phase) :
    ComponentLineMean (16 / κ) c₀ F ν X Wd GT R V u₀ B := by
  obtain ⟨huL, huR⟩ := typed_seed_upper_of_incoming hκ hh hJ hc
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  exact componentLineMean_of_phaseInputs hk hloc hL hR hR0 hRc
    (h.toCaps hR0 hRc huL huR) hrep

end InteractingSLE.Theorem14.GW4Fix
