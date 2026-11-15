/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Driver

/-!
# The observable relative driver and the actual retained driver-tip pair

Packet PROVE-T14-GW2ROOT2. The driver is reconstructed from the already
proved Borel relative trace, so no driver witness is selected measurably.
Original trace geometry proves generation and continuity for these readers.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootB23

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6

/-- The actual relative Loewner driver read from the retained records. -/
def relativeDriverRead (s v u : ℝ≥0) (p : RecData × RecData) : ℝ :=
  traceDriverRead (fun q => RootA22.relativeTipRead s v q p) u

theorem measurable_relativeDriverRead (s v u : ℝ≥0) : Measurable (relativeDriverRead s v u) :=
  (measurable_traceDriverRead u).comp
    (measurable_pi_iff.mpr fun q => RootA22.measurable_relativeTipRead s v q)

theorem relativeDriverRead_zero (s v : ℝ≥0) (p : RecData × RecData) :
    relativeDriverRead s v 0 p = 0 := traceDriverRead_zero _

/-- The driver and tip pair, both functions of the actual retained stage. -/
def relativeObservationRead (s v u : ℝ≥0) (p : RecData × RecData) : ℝ × ℂ :=
  (relativeDriverRead s v u p, RootA22.relativeTipRead s v u p)

theorem measurable_relativeObservationRead (s v u : ℝ≥0) :
    Measurable (relativeObservationRead s v u) :=
  (measurable_relativeDriverRead s v u).prodMk (RootA22.measurable_relativeTipRead s v u)

/-- The explicit observable driver generates the actual relative tip
reader and is continuous at every live relative capacity time. -/
theorem relative_readers_generatingTrace_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    let C := (RootZ21.forwardCapacity s v p).toNNReal
    IsGeneratingTrace (fun u => relativeDriverRead s v u p) (C : ℝ≥0∞)
      (fun u => RootA22.relativeTipRead s v u p) ∧
      ContinuousOn (fun u => relativeDriverRead s v u p)
        {u | (u : ℝ≥0∞) < (C : ℝ≥0∞)} ∧
      ∀ u : ℝ, u.toNNReal < C →
        ContinuousAt (fun t : ℝ => relativeDriverRead s v t.toNNReal p) u := by
  obtain ⟨V, hV0, hVc, hgen, _⟩ :=
    RootA22.exists_relativeTipRead_generatingTrace_before_contact
      W ζ ω hα hW hW0 hζ hsH he hγ hv
  have hc := hVc.mono fun t (ht : (t : ℝ≥0∞) <
    ((RootZ21.forwardCapacity s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).toNNReal : ℝ≥0∞)) => ht.le
  refine ⟨isGeneratingTrace_traceDriverRead hgen hc hV0,
    continuousOn_traceDriverRead hgen hc hV0, ?_⟩
  intro u hu
  exact (continuousAt_traceDriverRead hgen hc hV0
    (ENNReal.coe_lt_coe.mpr hu)).comp continuous_real_toNNReal.continuousAt

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

theorem measurable_stageSigma_relativeObservationRead (j : Fin n) (v u : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n]
      (fun ω => relativeObservationRead s v u
        (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_relativeObservationRead s v u).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j))

theorem measurable_rootSigma_relativeObservationRead {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (j : Fin ((entryList l).length + 1)) (v u : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r l]
      (fun ω => relativeObservationRead s v u (cfRec s W ζ ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) :=
  measurable_stageSigma_relativeObservationRead hκ h12p βA c₀ h s W ζ _ _ j v u

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootB23
