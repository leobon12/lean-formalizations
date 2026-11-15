/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryInputs

/-!
# GW4: full boundary representation from incident germs

Locality supplies the harmonic representative and the global logarithmic
growth bound. The existing phase-word Poisson extension and Aux. 29 then
identify the entire mean, retaining all fibers of the physical exceptions.
Only the actual incident germs and continuous inverse extension remain inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Sec7.PhaseSel Sec7.PocketStopSide
  Sec7.Aux119Heights Supp8.Q3Stop LocalSets WholeField MartChar

/-- The full phase-word representation for arbitrary component locality
witnesses follows from their incident boundary germs. The growth, bounded
extension and full-fiber uniqueness obligations are discharged here. -/
theorem componentPhaseRepresentation_of_incidentGerms {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} (hk : 0 < k) {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω}
    [IsProbabilityMeasure ν] {X : Ω → DistOn upperHalfPlaneOpens}
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    {hWm : ∀ r, Measurable (Wd r)} {u₀ : ℂ → ℝ}
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ} {d : ℝ≥0 → Ω → ℝ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (hinc : ComponentIncidentGerms k c₀ F ν X Wd GT R V u₀ B d) :
    ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B d := by
  obtain ⟨hu₀, -, -, hBm, hBc, hBloc, hshape⟩ := hloc
  have hzero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀
  intro t g hg
  have hBl : IsLocalSet (B t) (centredField X u₀) ν :=
    ((isLocalSet_tfae hzero (hBm t) (Eventually.of_forall (hBc t))).out 1 4).1
      (hBloc t).isAvoidanceLocal
  filter_upwards [hg.2.1, Sec6.ae_abs_le_log_global_of_isLocalSetMean hzero (hBm t) hBl hg,
    hinc t g hg, hshape t] with ω hH ⟨K, hK⟩ hi hs hlt
  let q := (lineClock F Wd GT V t ω).toNNReal
  let v := harmRep (g ω) (H \ B t ω)
  obtain ⟨hv, hrep⟩ := harmRep_spec hH
  obtain ⟨Fb, E, hFb, hFbc, hE, hside⟩ := hi hlt
  obtain ⟨M, hM⟩ := hu₀.2.1
  have hlog := log_growth_add_bounded (hK v hv hrep)
    (fun z (hz : z ∈ H \ B t ω) => hM z hz.1)
  have hsum : InnerProductSpace.HarmonicOnNhd (fun z => v z + u₀ z) (H \ B t ω) :=
    fun z hz => (hv z hz).add (hu₀.1 z hz.1)
  rw [hs hlt] at hsum hlog
  obtain ⟨hL, hR⟩ := component_seed_sides (k := k) (c₀ := c₀) (X := X) (V := V)
    hR0 hRc ω q
  have heq := eqOn_couplingMean_of_incident_germs hk
    (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) hL hR (d q ω)
    ((hRc ω).comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hR0 ω)
    q hFb hFbc hsum hlog hE hside
  refine ⟨v, _, hv, hrep,
    isBoundedHarmonicExtension_phaseWordExt hk _ _ hL hR (d q ω), ?_⟩
  intro z hz
  exact heq ((hs hlt) ▸ hz)

end InteractingSLE.Theorem14.GW4Fix
