/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Geometry

/-!
# Relative-capacity tip observations from the exact retained stage

Packet PROVE-T14-GW2ROOT2. Compose the proved physical inverse clock with
the Borel physical-tip and boundary-chart readers. Original finite traces
identify the resulting observable with the actual relative boundary tip.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- The actual charted physical tip at a prescribed relative-capacity level,
read from the retained counterflow and stopped physical-piece records. -/
def relativeTipRead (s v u : ℝ≥0) (p : RecData × RecData) : ℂ :=
  boundaryRead s (p.1, physicalTipRead (p.2, RootZ21.forwardClockInverse s v u p))

theorem measurable_relativeTipRead (s v u : ℝ≥0) : Measurable (relativeTipRead s v u) :=
  (measurable_boundaryRead s).comp (measurable_fst.prodMk
    (measurable_physicalTipRead.comp
      (measurable_snd.prodMk (RootZ21.measurable_forwardClockInverse s v u))))

/-- On the original live pre-contact event, the observable is the literal
boundary-chart value at the physical inverse-capacity time. -/
theorem relativeTipRead_eq_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ QuantumZipper.H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    (u : ℝ≥0)
    (hu : (u : ℝ) ≤ RootZ21.forwardCapacity s v
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    relativeTipRead s v u p = relBdry (rdrv p.1) s
      (γ (RootZ21.forwardClockInverse s v u p)) := by
  have hq := (RootZ21.forwardClockInverse_spec_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv u hu).1
  dsimp only
  unfold relativeTipRead
  rw [physicalTipRead_recOf_eq he hγ (lt_min_iff.mp hv).2 hq]
  exact boundaryRead_eq_relBdry s _
    (trace_mem_record_relSafe_before_contact W ζ ω hα hW hW0 hs he hγ hv hq)

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

/-- No continuation after the recorded physical horizon is observed. -/
theorem measurable_stageSigma_relativeTipRead (j : Fin n) (v u : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n]
      (fun ω => relativeTipRead s v u
        (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_relativeTipRead s v u).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j))

theorem measurable_rootSigma_relativeTipRead {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (j : Fin ((entryList l).length + 1)) (v u : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r l]
      (fun ω => relativeTipRead s v u (cfRec s W ζ ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) :=
  measurable_stageSigma_relativeTipRead hκ h12p βA c₀ h s W ζ _ _ j v u

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
