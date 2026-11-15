/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmPre

/-!
# GW2's open lines: Claim(k) and the separable pieces of its induction, as statements

Packet PROVE-GW2-STAGEMEAN, R121 round. Interfaces for the Claim(k) induction (root `0`):

* **`ClaimAt`**: the stage-start pairing of a corrected root-`x` instance for one word type (the `hclaim` input of
  `pair_inst` / `meanX_inst`);
* **`PrefixLifeStatement`** (R1) and **`PrefixContactStatement`** (R2): the prefix candidate of an entry's angle is
  alive and its trace has not touched the counterflow up to the entry's end, on the history's success (pieces offered
  to PROVE-GW2-RELDET; see the STAGEMEAN handoff, "For RELDET").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Rd GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal

/-- **Claim(k) at a corrected root-`x` instance and one word type**: every local-set mean of the instance's union at
stage time `0` pairs, on the live event with a positive cap, as the stage-start mean `stgMeanR … 0` with the
instance's typed data (`bheProc` at clock `0`). -/
def ClaimAt {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) (w : WordType) : Prop :=
  ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
    IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B 0) (centredField c.h ch.u₀) c.P g₀ →
    ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
      ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r l a GT hA ch).B 0 ω →
      g₀ ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω)
        (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
        (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
            ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
              relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
            ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
              relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
        ch.u₀ ch.σa z * φ z

/-- **(R1) The prefix candidate of an entry's angle is alive up to the entry's end** on the history's success. -/
def PrefixLifeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ), candidateAngle c r a' = (e.1 : ℝ) →
    historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a' → ∀ ω : Ω,
    oldSuccess c r (e :: l') ω →
      ((historyTime c r (e :: l') - historyTime c r l' : ℝ≥0) : ℝ≥0∞) < candLife c r l' a' ω

/-- **(R2) The prefix candidate's trace has not touched the counterflow up to the entry's end** when the history's
trace has not (on the history's success, almost surely). -/
def PrefixContactStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ), candidateAngle c r a' = (e.1 : ℝ) →
    historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a' →
    ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω →
      (historyTime c r (e :: l') : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r (e :: l') a) c.α ω →
      (historyTime c r (e :: l') : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω

end InteractingSLE.Theorem14.GW2Psm
