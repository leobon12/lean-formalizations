/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfGood
import InteractingSLE.Spec.Supplement.SB2NfEnd
import InteractingSLE.Spec.Supplement.SB2NeStop

/-!
# F2b′'s root: the relative facts at a sample (statement, for PROVE-T14-SB2LIFT, D77)

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). **`RootRelFactsStatement`**: the root analogue of
`Ne.relFacts_of_good` (SB2NeStop). At a sample with the walk facts, a launch of B's stage `ℓ` and the root's geometry
`RootGeo` for the offset `x` (SB2NfGood), D34's heights clause at the seed `R = max (A ∩ ℝ)` for a word `β`, the
regularity of B's regularized piece, the agreement of the regularized runs with the actual ones, and the physical
facts of `Ne.ae_walk_phys` and `ae_walk_end_right` (SB2NfEnd) at the sample, the root's relative curve
`canonCurve (retX) x (rPc) (rLife)` has the relative facts `Nd.RelFactsAt` for the record word `cw` (with
`cw ω = shiftW x β`), and at a finite relative lifetime its trace converges to a bad relative point right of the seed.

Consumed by NOJUMP's root stops (`StopG` over `RootObj.ρM`). Owner of the proof: PROVE-T14-SB2LIFT (D77).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Nd Ne

/-- **Named statement (the root's relative facts at a sample; PROVE-AUX61-NOJUMP's, proof owned by
PROVE-T14-SB2LIFT, D77).** -/
def RootRelFactsStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (ω : Ω),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b jumps →
    WalkGood κ b jumps E u l k ω →
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
    ∀ x : ℝ, RootGeo κ b jumps E u l k ℓ ω x →
    ∀ (β : BoundaryWord), Nb.HeightClause κ b jumps (fillH (retX κ b jumps E u l k ℓ ω))
      ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) β →
    ∀ (cw : Ω → BoundaryWord) (types : Set WordType), cw ω = BoundaryWord.shiftW x β →
      angleWordType κ (-(Real.pi / 2)) (cw ω) ∈ types →
    GW1P.PieceRegular (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).1
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
    (∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) →
    -- `Ne.ae_walk_phys` at the sample
    stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) =
        stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) ∉
        closure (origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        ∀ x : ℝ, pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t = x →
          stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) < x →
          x ∉ closure (origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)))) ∧
      ((StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ ⊤ →
        ∃ x : ℝ, pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2.toNNReal = x ∧
          x ∈ origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))) →
    -- `ae_walk_end_right` at the sample
    (∀ (sh : ℝ≥0) (R' : ℝ), (sh : ℝ≥0∞) < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) < R' →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) sh = R' →
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ ⊤ → ∀ x : ℝ,
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2.toNNReal = x →
        x ∈ origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)) → R' < x) →
    RelFactsAt κ (-(Real.pi / 2)) cw types (canonCurve (retX κ b jumps E u l k ℓ ω) x (rPc κ b jumps E u l k ℓ ω)
        (rLife κ b jumps E u l k ℓ ω)) ω ∧
      (capLife (canonCurve (retX κ b jumps E u l k ℓ ω) x (rPc κ b jumps E u l k ℓ ω)
          (rLife κ b jumps E u l k ℓ ω)) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
        Tendsto (capTrace (canonCurve (retX κ b jumps E u l k ℓ ω) x (rPc κ b jumps E u l k ℓ ω)
          (rLife κ b jumps E u l k ℓ ω))) (𝓝[<] (capLife (canonCurve (retX κ b jumps E u l k ℓ ω) x
            (rPc κ b jumps E u l k ℓ ω) (rLife κ b jumps E u l k ℓ ω))).toNNReal) (𝓝 (y : ℂ)) ∧
        Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (cellXR κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
          (typedRhoL (angleWordType κ (-(Real.pi / 2)) (cw ω)))
          (typedRhoR (angleWordType κ (-(Real.pi / 2)) (cw ω))) (y : ℂ))

end InteractingSLE.Theorem14.SB.Nf
