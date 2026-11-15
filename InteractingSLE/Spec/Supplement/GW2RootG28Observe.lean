/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Sample

/-!
# Observing the actual pair through a random geometric failure buffer

Packet PROVE-T14-GW2ROOT2. The observation uses the landed past-entry
gate and the constructed random buffer. Both the killed sample and
the gated observation are Borel in the exact supplied stopped records.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6 RootD25 RootE26

/-- The observed pair, gated by past entry and the random physical buffer. -/
def bufferedObservationRead (a s v b : ℝ≥0) (m : ℕ) (q : ℝ≥0)
    (p : RecData × RecData) : ℝ × ℂ :=
  if q < contactBuffer s v b m p then crossedObservationRead a s v q p else (0, 0)

theorem measurable_bufferedObservationRead (a s v b : ℝ≥0) (m : ℕ) (q : ℝ≥0) :
    Measurable (bufferedObservationRead a s v b m q) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_contactBuffer s v b m))
    (measurable_crossedObservationRead a s v q) measurable_const

/-- On a protected original prefix the reader is exactly the actual
observation after physical entry and before the random failure buffer. -/
theorem bufferedObservationRead_eq_actual {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hsH : α s ∈ H) {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) e.2)
    {a : ℝ≥0} (ha : 0 < a) (b : ℝ≥0) (m : ℕ) {q : ℝ≥0} (hq : q ≤ v) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    bufferedObservationRead a s v b m q p =
      if entryPhysical a s v p < q ∧ q < contactBuffer s v b m p then
        physicalObservationRead a s v q p else (0, 0) := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  have heq := cutoffObservationRead_eq_actual
    W ζ ω hα hW hW0 hζ hsH he hγ hv ha hq (contactBuffer s v b m p)
  exact heq

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

theorem measurable_stageSigma_bufferedSample (j : Fin n) (a v b : ℝ≥0) (m : ℕ) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      bufferedSample a s v b m (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_bufferedSample a s v b m).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j))

theorem measurable_stageSigma_bufferedObservationRead (j : Fin n)
    (a v b : ℝ≥0) (m : ℕ) (q : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      bufferedObservationRead a s v b m q
        (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_bufferedObservationRead a s v b m q).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j))

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
