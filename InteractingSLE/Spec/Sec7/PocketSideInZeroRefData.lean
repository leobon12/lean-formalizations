/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefLaw
import InteractingSLE.Spec.Sec7.SideLCLate

/-!
# An actual original-time reference family for the late side data

PROVE-POCKET-SIDEIN. Install the original-time hulls and their retained
records at relative level zero. The family has the raw-law, prefix and
open-complement properties required by the native late side binders.
The supplied lifts, offsets, phases and other side data are preserved.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketCoupling Sec7.PocketStop LocalSets WholeField WangWu

/-- Use the ambient hulls at the prescribed countable original times as
references. Every field other than the reference level, sets and records
is inherited from the supplied side data. -/
def Late.SideData.withOriginalReferences {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : ℕ → ℝ≥0) : Late.SideData Ω :=
  { e with
    level := 0
    sets := fun r ω => regHull d.driver d.lifetime (s r) ω
    info := fun r => j.originalReferenceInfo d hKilled (s r) }

/-- The installed reference fields are the literal original-time hulls
and records, normalized at zero. -/
theorem Late.SideData.withOriginalReferences_reference_fields {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) (s : ℕ → ℝ≥0) :
    (e.withOriginalReferences j d hKilled s).level = 0 ∧
      (e.withOriginalReferences j d hKilled s).sets =
        (fun r ω => regHull d.driver d.lifetime (s r) ω) ∧
      (e.withOriginalReferences j d hKilled s).info =
        (fun r => j.originalReferenceInfo d hKilled (s r)) := ⟨rfl, rfl, rfl⟩

/-- Installing references preserves the supplied common field frame. -/
theorem Late.SideData.withOriginalReferences_frame {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) (s : ℕ → ℝ≥0) :
    (e.withOriginalReferences j d hKilled s).lift = e.lift ∧
      (e.withOriginalReferences j d hKilled s).phase = e.phase ∧
      (e.withOriginalReferences j d hKilled s).offset = e.offset := ⟨rfl, rfl, rfl⟩

/-- The installed reference is exactly the original-time filled set,
with its own fixed candidate normalization, also off the candidate event. -/
theorem original_references_liveExt {Ω : Type} [MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (e : Late.SideData Ω) (s : ℕ → ℝ≥0) (r : ℕ) :
    let refs := e.withOriginalReferences j d hKilled s
    liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
      (refs.sets r) refs.level = eventFilled (j.target i d).event (j.target i d).domain
        (fun ω => regHull d.driver d.lifetime (s r) ω) :=
  liveExt_zero_eq_eventFilled (Current.SideTest.isDrivenCurve_target hj) _ _

/-- The three native reference obligations hold for this actual family
from the ambient coupling and the walls' source laws. No raw reference law
is a hypothesis. The original times may be any countable family. -/
theorem original_references_facts {Ω : Type} [mΩ : MeasurableSpace Ω]
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
    (hCont : ∀ k ω, Continuous (j.pairWallFamily j d k ω))
    (hStart : ∀ k ω, j.pairWallFamily j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => j.pairWallFamily j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => j.pairWallFamily j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (j.pairWallFamily j d k)
      (centredField d.field d.originalMean) d.measure)
    (e : Late.SideData Ω) (s : ℕ → ℝ≥0) :
    let refs := e.withOriginalReferences j d hKilled s
    ∀ r, locPrefixSigma (refs.info r) (j.target i d).event (j.target i d).curve refs.level ≤ mΩ ∧
      (∀ ω ∈ (j.target i d).event, IsOpen (H \ refs.sets r ω)) ∧
      PocketStopUnionLaw (refs.info r) (j.target i d).measure (j.target i d).event
        (j.target i d).curve (j.target i d).domain (refs.sets r) (j.target i d).zeroField refs.level := by
  dsimp only
  intro r
  obtain ⟨hInfo, _, hRaw⟩ := Current.SideTest.raw_reference_law_at_original_time hj
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal (s r)
  obtain ⟨hA, _, _⟩ := Current.SideTest.original_reference_records hj hCoupling hKilled hLife hCont (s r)
  change locPrefixSigma (j.originalReferenceInfo d hKilled (s r)) (j.target i d).event
      (j.target i d).curve 0 ≤ mΩ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [locPrefixSigma_zero_of_driven hA (Current.SideTest.isDrivenCurve_target hj)]
    exact hInfo
  · intro ω _
    exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      ((continuous_regDrv d.driver d.lifetime ω).comp continuous_real_toNNReal) (s r).coe_nonneg
  · rw [SideTest.target_measure]
    exact hRaw

end InteractingSLE.Wire
