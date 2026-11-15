/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMean
import InteractingSLE.Spec.Sec7.SideHeightBoxProb
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# The pocket side limit from a countable family of boundary references

Packet PROVE-STRIPSYS38. Aux. lemmas 35–36 compare the stopped union mean with
single-wall means and old counterflow means. Proposition 3.8 supplies the comparison
simultaneously for a countable reference family; the reference is selected afterward.

`PocketStopBoundaryCover` records the remaining physical boundary cover and coordinate
calculation: a common physical point, local agreement of the sets, approach through the
common complement, the reference's own height, the inherited lift difference, and the
word-height identity. It is an explicit, unproved geometric input for the strip system.
In particular its last identity requires the actual phase `d = 0`; this module does
not establish Aux. lemma 122's hypotheses for the pocket process.

`pocketStopSideLimit_of_referenceCover` proves the comparison and transport step for
every version of the stopped mean. It applies to any chart, including STRIPSYS35's
shifted canonical chart. This is a conditional helper, not a proof of the strip-system
`PocketStopSideLimit`. No Theorem 1.2/1.3 is used (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop Aux119Heights

section Cover

variable {Ω ι : Type*}

/-- The physical reference cover needed for the side limit at one relative capacity
time. The reference means and lifts are specified independently of the stopped mean.
The constants `b` and `d` are the reference height and transition argument at the
chosen incident boundary piece. Constructing these witnesses for the strip pocket
(including the last, exact word-height identity) remains a mathematical obligation. -/
def PocketStopBoundaryCover (κ : ℝ) {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (c : Ω → Chart)
    (a : ℝ) (u : ℂ → ℝ) (K : Ω → Set ℂ) (q : ℝ≥0)
    (B : ι → Ω → Set ℂ) (gB : ι → Ω → DistOn upperHalfPlaneOpens)
    (liftB : ι → Ω → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
    ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
      ∃ (i : ι) (p : ℂ) (b d : ℝ),
        p ∈ K ω ∪ {z : ℂ | z.im = 0} ∧ p ∈ B i ω ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, B i ω ∩ ball p r ⊆ K ω) ∧
        (∃ r > 0, K ω ∩ ball p r ⊆ B i ω) ∧
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ))
          (𝓝[H \ (K ω ∪ B i ω)] p) ∧
        Tendsto (fun z => harmRep (gB i ω) (H \ B i ω) z + u z + chiC κ * liftB i ω z)
          (map (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ))) (𝓝 b) ∧
        Tendsto (fun z => (relChart c γ q ω).2.2 z - liftB i ω z)
          (map (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ))) (𝓝 d) ∧
        b + chiC κ * d = forceBoundaryData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a

end Cover

section Comparison

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Proposition 3.8 transfers the reference heights to every stopped-mean version,
on one event for the entire countable family. The boundary cover is a separate input;
this theorem does not assert that the strip system supplies it. -/
theorem pocketStopSideLimit_of_referenceCover
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {c : Ω → Chart}
    {a : ℝ} {u : ℂ → ℝ} {K : Ω → Set ℂ} {q : ℝ≥0}
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h₀ P)
    (hKdet : MeasurableSpace.comap K hittingSigma ≤
      aeSigma (MeasurableSpace.comap h₀ inferInstance) P)
    (hKunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (K ω)) z))
    {B : ι → Ω → Set ℂ} (hBm : ∀ i, Measurable[mΩ, hittingSigma] (B i))
    (hBloc : ∀ i, IsLocalSet (B i) h₀ P)
    (hBdet : ∀ i, MeasurableSpace.comap (B i) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h₀ inferInstance) P)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (B i ω)) z))
    {gB : ι → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (B i) h₀ P (gB i))
    {liftB : ι → Ω → ℂ → ℝ}
    (hcover : PocketStopBoundaryCover κ ρL ρR P A γ xL xR c a u K q B gB liftB) :
    PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q := by
  intro g hg
  have hcmp := fun i => SideHeightBox.ae_tendsto_sub_of_locals hh₀ hKm (hBm i)
    hKloc (hBloc i) hKdet (hBdet i) hKunb (hBunb i) hg (hgB i)
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

end Comparison

end InteractingSLE.Sec7.PocketStopSide
