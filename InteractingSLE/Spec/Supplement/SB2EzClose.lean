/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2EzStep
import InteractingSLE.Spec.Supplement.SB2YnZero
import InteractingSLE.Spec.Supplement.SB2FuBranch

/-!
# (P1), hcan, hTL and the step from Theorems 1.2–1.3 alone (D89, D90)

Packet PROVE-SB2-CANON, round 10. The three branches of the step are now all proved:

* the zero branch, widened (**`sb2LowerZeroBranchWStatement_of_thms`**): SB2LIFT's `Sz.zero_piece_rootE` (D89), with
  the line facts of CONDFIN's family at `ℓ` (GEOM2's `Gj.hloc_rootLine`) and the invariant's root facts as its `hLR`;
* the base selector: `Cz.sb2LowerBaseSelectorStatement_of_thms` (SB2LIFT's `Sz.baseSelector_usable`);
* the root branch in root-event form: F3LAW's `Fu.sb2LowerRootEvBranchStatement` (D90).

The final theorems, from Theorems 1.2–1.3 only:

* **`sb2LowerStageStepStatement_closed`**: the step `Cz.SB2LowerStageStepStatement` (ASSEMBLE7's `hstep`);
* **`lawInU_closed`**: (P1), `Cz.SB2LowerStageLawInUStatement`;
* **`sb2LowerStageCanonStatement_closed`**: hcan, `Mz.SB2LowerStageCanonStatement` (ASSEMBLE7's
  `Wire.theorem14Statement_closedS` takes exactly it, at `T14Asm7.h12 T14Asm7.h13`);
* **`sb2LowerTailLiftExStatement_closed`**: the top's hTL, with the top's `hdet` (closed by ROOTX's
  `Ro.sb2LowerRootDetWStatement_closed`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Lv Lk Mf Ms

/-- **The widened zero branch of the step** (Theorems 1.2–1.3): SB2LIFT's `Sz.zero_piece_rootE`. -/
theorem sb2LowerZeroBranchWStatement_of_thms (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerZeroBranchWStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀
    𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  obtain ⟨hA₁m, -, -, -, -, -, -, -, hA₁c, -⟩ := hfam 0
  have hloc := Gj.hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ h𝓖 hfam
  exact Sz.zero_piece_rootE (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h12 h13 h12₀ h13₀ hκ hκ4
    hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hwℓ hwℓ₂ (h𝓖 0)
    (by filter_upwards [stmt6Sets_of_rootSets hfam 0] with ω h1 using h1.1) (h𝓖' 0)
    (by filter_upwards [stmt6Sets_of_rootSets hfam' 0] with ω h1 using h1.1) hu₀ hA₁m hA₁c hloc hst hRF

/-- **(P1)'s induction step** (ASSEMBLE7's `hstep`), from Theorems 1.2–1.3 alone. -/
theorem sb2LowerStageStepStatement_closed (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerStageStepStatement.{u} :=
  sb2LowerStageStepStatement_of_branchesW h12 h13 h12₀ h13₀ (sb2LowerZeroBranchWStatement_of_thms h12 h13 h12₀ h13₀)
    (sb2LowerBaseSelectorStatement_of_thms h12 h13 h12₀ h13₀) (Fu.sb2LowerRootEvBranchStatement h12 h13 h12₀ h13₀)

/-- **(P1)** (`Cz.SB2LowerStageLawInUStatement`), from Theorems 1.2–1.3 alone. -/
theorem lawInU_closed (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerStageLawInUStatement.{u} :=
  lawInU_of_step h12 h13 h12₀ h13₀ (sb2LowerStageStepStatement_closed h12 h13 h12₀ h13₀)

/-- **hcan** (`Mz.SB2LowerStageCanonStatement`), from Theorems 1.2–1.3 alone. -/
theorem sb2LowerStageCanonStatement_closed (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) :
    Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  sb2LowerStageCanonStatement_of_step h12 h13 h12₀ h13₀ (sb2LowerStageStepStatement_closed h12 h13 h12₀ h13₀)

/-- **The top's hTL**, from Theorems 1.2–1.3 and the top's `hdet` (closed by ROOTX's
`Ro.sb2LowerRootDetWStatement_closed`). -/
theorem sb2LowerTailLiftExStatement_closed (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hdet : Ch.SB2LowerRootDetWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  Cg.sb2LowerTailLiftExStatement_of_rest h12 h13 h12₀ h13₀
    (Lk.sb2LowerGeomRestV6 h12 h13 h12₀ h13₀ (Lk.sb2LowerStartDataStatement_of_thms h12 h13 h12₀ h13₀))
    (sb2LowerStageCanonStatement_closed h12 h13 h12₀ h13₀)
    (Ch.sb2LowerRelPosWRootStatement_of_det h12 h13 h12₀ h13₀ hdet)

end InteractingSLE.Theorem14.SB.Cz
