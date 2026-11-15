/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KbBase
import InteractingSLE.Spec.Supplement.SB2OmWord

/-!
# Claim(k)'s base (GEOM2 round 12): the stage-start data in word form

Packet PROVE-GW2-GEOM2, round 12. `claim_base_root0` takes the stage-start data `U₀` through the identity
`U₀ = G + (σa − specOffset κ − θ_root χ)` for the flowed joint word. The word map gives `U₀` as a word mean: the stage
word of the history `l = []` is the stop word of the root word at the root piece's relative record, raised by the
candidate's angle. This file closes the gap:

* **`eqOn_flowed_stopWord`**: a bounded harmonic extension of a word's angle-`θ` data flowed by a driver `D` to `a` is
  the stop word's mean at any record reading `D` up to `a`, plus `θχ` (GEOM2's `SB.Om.eqOn_explored_mean` with the
  record positions read off `D`);
* **`claim_base_root0_word`**: Claim(k) at `l = []` (root `0`) with `σa = specOffset κ + θa χ` and the stage-start data
  `U₀ = (stopWord κ (jw, θ_root, rec')).mean + θa χ` for a record `rec'` of the version's driver up to `a₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Kb

open GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 GW2JointKernel
open Supp8.Q3Rel (invHull)
open Supp8.Q3Chain (flowedData flowedJumps)

/-- **The flowed data of a word is its stop word at a record of the flowing driver** (plus `θχ`). -/
theorem eqOn_flowed_stopWord {κ θ : ℝ} (c : BoundaryWord) {D : ℝ → ℝ} {a : ℝ} (r : RecData) (hrt : rtime r = a)
    (hrd : EqOn (rdrv r) D (Icc 0 a)) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (flowedData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
        (flowLineXR c.fn c.jumps 0) D a)
      (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) D a) G) :
    EqOn G (fun z => (stopWord κ (c, θ, r)).mean z + θ * chiC κ) H := by
  subst hrt
  have e1 : ∀ x, markPos D (rtime r) x = markPos (rdrv r) (rtime r) x :=
    Sec7.StripSideHeightProb.markPos_congr fun y hy => (hrd hy).symm
  have e2 : ∀ x, markPosL D (rtime r) x = markPosL (rdrv r) (rtime r) x :=
    Sec7.StripSideHeightProb.markPosL_congr fun y hy => (hrd hy).symm
  have hG' := hG
  simp only [flowedData, flowedJumps, e1, e2] at hG'
  exact SB.Om.eqOn_explored_mean c r hG'

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (a : ℕ)

/-- **Claim(k) at `l = []` (root `0`), with the stage-start data in word form.** -/
theorem claim_base_root0_word (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hr0 : rootPt r.1 = 0) {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r [] a 0) (schedUnionS c r [] a 0) (centredField c.h u₀) c.P)
    {G : Set Ω} (hGs : ∀ ω ∈ G, oldSuccess c r [] ω) {R : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0} {θa σa : ℝ}
    (hσa : σa = specOffset c.κ + θa * chiC c.κ) {U₀ : Ω → ℂ → ℝ}
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G →
      c.α ω c.s ∈ H ∧
      (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r [], c.α ω v * schedTr c r [] a ω u + 1 ≠ 0) ∧
      Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧ A 0 ω = 0 ∧
      ContinuousOn (fun u => A u ω) (Icc 0 (historyTime c r [])) ∧
      (∀ u ≤ historyTime c r [], H \ (invHull (fun q : ℝ => c.W q.toNNReal ω) c.s ∪
          fwdHull (fun q : ℝ => schedW c r [] a q.toNNReal ω) u) =
        (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω))) ∧
      ∃ rec' : RecData, rtime rec' = (A (historyTime c r []) ω : ℝ) ∧
        EqOn (rdrv rec') (Ito.rpath fun q => R q ω) (Icc 0 (A (historyTime c r []) ω : ℝ)) ∧
        ∀ z ∈ H, U₀ ω z = (stopWord c.κ (jw c.κ cw c.s c.W c.ζ ω, (rootEntry r.1).1, rec')).mean z +
          θa * chiC c.κ)
    (g₀ : Ω → DistOn upperHalfPlaneOpens)
    (hg₀ : IsLocalSetMean (schedUnionS c r [] a 0) (centredField c.h u₀) c.P g₀) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionS c r [] a 0 ω →
      g₀ ω φ = ∫ z, (couplingMean c.κ (Ito.rpath (GW2Rd.stgDrv (fun q => R q ω) (A (historyTime c r []) ω))) 0
          (U₀ ω) ((GW2Rd.stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω)
            (A (historyTime c r []) ω)).1 z) - u₀ z - σa -
        chiC c.κ * (GW2Rd.stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω)
          (A (historyTime c r []) ω)).2.2 z) * φ z := by
  refine claim_base_root0 c r a h12 h13 hr0 hcw hu₀ hloc₀ hGs ?_ g₀ hg₀ φ
  filter_upwards [hread] with ω hω hωG
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, rec', hrt, hrd, hU⟩ := hω hωG
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun G' hG' z hz => ?_⟩
  have hG := eqOn_flowed_stopWord _ rec' hrt hrd hG' hz
  simp only at hG
  rw [hU z hz, hσa]
  linarith

end InteractingSLE.Theorem14.GW2Kb
