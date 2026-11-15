/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmXferC
import InteractingSLE.Spec.Supplement.GW2PsmRestart
import InteractingSLE.Spec.Supplement.GW2PsmPairP

/-!
# GW2's open lines: the Claim(k) step from the prefix's pairing at the entry's end

Packet PROVE-GW2-STAGEMEAN, R121 round. **`claim_of_prefix_pair`**: let `(r, l', a')` be the prefix of the history
`e :: l'` with a candidate of `e`'s angle whose cap reaches past `e`'s end, and `δ` the entry's duration. If every
local-set mean of the prefix's union at `δ` pairs, on an event `G` of the history's success, as the explicit stage mean
`stgMeanR … a₀' q U' u₀ σa'` (what `pair_root0` gives at the prefix), and on `G` the word's mean is `U'` shifted by
`specOffset κ − σa'` (the explored identity) with the history's stage start `a₀' + q` reading the complement of the
history's union, then every local-set mean of the history's union at its start pairs on `G` as
`stgMeanR … (a₀' + q) 0 (mean of the word) u₀ (specOffset κ)` — the stage-start form of Claim(k) for `e :: l'`.

Ingredients: the transfer `ae_mean_eq_cons`, the inclusion `schedUnionS_cons_subset`, the restart `stgMeanR_restart`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open LocalSets WholeField Restart Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Rd GW2JointKernel

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **A local-set mean of a corrected union exists.** -/
theorem exists_mean_schedUnionS (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) (t : ℝ≥0) :
    ∃ g, IsLocalSetMean (GW2Sdi.schedUnionS c r l a t) (centredField c.h u₀) c.P g := by
  have hh := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hloc := isHistoryAvoidanceLocal_stgF h12 h13 c r l a hr0 (Gm.timeOrdered_of_pairwise_lt hord) hu₀ t
  have h : IsGermConditionalLaw (GW2Sdi.schedUnionS c r l a t) (centredField c.h u₀) c.P :=
    ((isLocalSet_tfae hh (GW2Sdi.measurable_schedUnionS c r l a t)
      (ae_of_all _ fun ω => GW2Sdi.schedUnionS_subset_isOpen c r l a t ω)).out 1 3).1 hloc.isAvoidanceLocal
  exact h

/-- **The Claim(k) step**: the prefix's pairing at the entry's end gives the history's stage-start pairing. -/
theorem claim_of_prefix_pair (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l'))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    {G : Set Ω} (hGS : ∀ ω ∈ G, oldSuccess c r (e :: l') ω)
    {R : ℝ≥0 → Ω → ℝ} {a₀' q : Ω → ℝ≥0} {U' : Ω → ℂ → ℝ} {σa' : ℝ} {Wd : Ω → BoundaryWord}
    (hP : ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (GW2Sdi.schedUnionS c r l' a' δ) (centredField c.h u₀) c.P g → ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r l' a' δ ω →
        g ω φ = ∫ z, stgMeanR c.κ (Supp8.GB6.gb6Rec c.s c.W c.ζ ω) (fun u => R u ω) (a₀' ω) (q ω : ℝ) (U' ω) u₀ σa' z *
          φ z)
    (hsamp : ∀ᵐ ω ∂c.P, ω ∈ G → Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧
      (∀ z ∈ H, (Wd ω).mean z = U' ω z + (specOffset c.κ - σa')) ∧
      H \ GW2Sdi.schedUnionS c r (e :: l') a 0 ω ⊆
        ((stgChart (Supp8.RelSafeS.relChart (Supp8.GB6.gb6Rec c.s c.W c.ζ ω)) (fun u => R u ω)
          (a₀' ω + q ω)).dom : Set ℂ))
    (g₀ : Ω → DistOn upperHalfPlaneOpens)
    (hg₀ : IsLocalSetMean (GW2Sdi.schedUnionS c r (e :: l') a 0) (centredField c.h u₀) c.P g₀)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r (e :: l') a 0 ω →
      g₀ ω φ = ∫ z, stgMeanR c.κ (Supp8.GB6.gb6Rec c.s c.W c.ζ ω) (fun u => R u ω) (a₀' ω + q ω) 0
        (Wd ω).mean u₀ (specOffset c.κ) z * φ z := by
  obtain ⟨g, hg⟩ := exists_mean_schedUnionS h12 h13 c r l' a' hr0 hord' hu₀ δ
  have hX := ae_mean_eq_cons h12 h13 c r e l' a a' hr0 hord hord' hθ hcap δ hδ hu₀ hg hg₀
  filter_upwards [hP g hg φ, hX, hsamp, Gm.ae_futureJoined_trace h13 c r] with ω h1 h2 h3 h4 hG hsupp
  obtain ⟨hRc, hR0, hW, hdom⟩ := h3 hG
  have hS := hGS ω hG
  have hsub : H \ GW2Sdi.schedUnionS c r (e :: l') a 0 ω ⊆ H \ GW2Sdi.schedUnionS c r l' a' δ ω := by
    refine sdiff_subset_sdiff_right (schedUnionS_cons_subset c r e l' a a' δ ω fun hs => ?_)
    exact schedUnionS_cons_eq c r e l' a a' ω hord hord' hs (h4 (e :: l') a hs).1
      (h4 l' a' (oldSuccess_of_cons c r e l' ω hs)).1 hθ hcap δ hδ
  rw [← h2 hS, h1 hG (hsupp.trans hsub)]
  congr 1
  funext z
  by_cases hz : z ∈ tsupport φ
  · rw [stgMeanR_restart c.κ _ hRc hR0 (a₀' ω) (q ω) (U₀ := (Wd ω).mean) (σa := specOffset c.κ)
      (fun z hz => hW z hz) (hdom (hsupp hz))]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end InteractingSLE.Theorem14.GW2Psm
