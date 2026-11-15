/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideFinalComparison
import InteractingSLE.Spec.Sec7.PocketStopSideComparison

/-!
# The pocket side limit through marked reference unions

PROVE-STRIPSYS38. The original side-limit comparison is now proved without field
determination of the stopped counterflow or the reference hulls. The remaining
probabilistic premise is the history-marked law of each reference union, retaining
both sets. Its production at the left stop T⁰(q) and the maximum with an ordinary
reference stop is the determination-free STRIPSYS37 route. No conditional
independence of the two sets given the field is assumed here.

The physical reference cover, its heights and phase alignment still have their
original exact type. This theorem does not assert that the strip system supplies
those inputs or every marked reference-union law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop Aux119Heights

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The unchanged `PocketStopSideLimit`, from the physical reference cover and
joint marked locality, with both determination hypotheses removed. -/
theorem pocketStopSideLimit_of_marked_referenceCover
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {c : Ω → Chart}
    {a : ℝ} {u : ℂ → ℝ} {K : Ω → Set ℂ} {q : ℝ≥0}
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h₀ P)
    (hKunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (K ω)) z))
    {B : ι → Ω → Set ℂ} (hBm : ∀ i, Measurable[mΩ, hittingSigma] (B i))
    (hBloc : ∀ i, IsLocalSet (B i) h₀ P)
    (hPairLocal : ∀ i, WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap K hittingSigma ⊔ MeasurableSpace.comap (B i) hittingSigma)
      (fun ω => K ω ∪ B i ω) h₀ P)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (B i ω)) z))
    {gB : ι → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (B i) h₀ P (gB i))
    {liftB : ι → Ω → ℂ → ℝ}
    (hcover : PocketStopBoundaryCover κ ρL ρR P A γ xL xR c a u K q B gB liftB) :
    PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q := by
  intro g hg
  have hcmp := fun i => ae_tendsto_sub_of_marked_union hh₀ hKm (hBm i)
    hKloc (hBloc i) (hPairLocal i) hKunb (hBunb i) hg (hgB i)
  have hcmpAll := ae_all_iff.2 hcmp
  have hrep : ∀ᵐ ω ∂P, ∀ i, IsHarmonicDistOn (gB i ω) (H \ B i ω) :=
    ae_all_iff.2 fun i => (hgB i).2.1
  unfold PocketStopBoundaryCover at hcover
  filter_upwards [hcmpAll, hrep, hcover] with ω hωcmp hωrep hωcover
    hωA hq v hv hvr ξ hξ
  obtain ⟨i, p, b, d, hpK, hpB, hBK, hKB, hinv, hheight, hlift, hword⟩ :=
    hωcover hωA hq ξ hξ
  obtain ⟨hvB, hvBr⟩ := harmRep_spec (hωrep i)
  have hzero := hωcmp i v (harmRep (gB i ω) (H \ B i ω)) hv hvr hvB hvBr
    p hpK hpB hBK hKB
  have hheight' := tendsto_map'_iff.1 hheight
  have hlift' := tendsto_map'_iff.1 hlift
  have hsum := (hzero.comp hinv).add (hheight'.add (hlift'.const_mul (chiC κ)))
  rw [zero_add, hword] at hsum
  exact hsum.congr fun y => by
    dsimp only [Function.comp_def]
    ring

end InteractingSLE.Sec7.PocketStopSide
