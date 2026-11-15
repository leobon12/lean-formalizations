/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CcStep
import InteractingSLE.Spec.Supplement.SB2CcRoot
import InteractingSLE.Spec.Supplement.SB2YmZero
import InteractingSLE.Spec.Supplement.SB2YmSel

/-!
# (P1), hcan and hTL from the entrance law and the root-positivity walk fact (D86)

Packet PROVE-SB2-CANON, round 9. The step's three branch statements (`SB2CcStmt`) are discharged:

* **`sb2LowerZeroBranchStatement_of_thms`**: SB2LIFT's widened zero piece `Sz.zero_piece_root` (8a10b5ad5), with the
  line facts of CONDFIN's family at `ℓ` (GEOM2's `Gj.hloc_rootLine`) and the invariant's root facts as its `hLR`;
* **`sb2LowerBaseSelectorStatement_of_thms`**: SB2LIFT's `Sz.baseSelector_usable` on NOJUMP's walk facts;
* the root branch: `rootBranch_of_rootEv` from `sb2LowerRootEvBranchStatement_of_entr` (F3LAW's entrance law
  `Ca.SB2LowerRootEntranceLawStatement`, D85 (A2), consumed as stated) and the walk fact `SB2LowerRootPosStatement`.

Hence **`lawInU_of_entr`** ((P1) in the form `Cz.SB2LowerStageLawInUStatement`),
**`sb2LowerStageCanonStatement_of_entr`** (hcan) and **`sb2LowerTailLiftExStatement_of_entr`** (the top's hTL, with the
top's `hdet`, closed by ROOTX's `Ro.sb2LowerRootDetWStatement_closed`).

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

/-- **The zero branch of the step** (Theorems 1.2–1.3): SB2LIFT's `Sz.zero_piece_root`. -/
theorem sb2LowerZeroBranchStatement_of_thms (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerZeroBranchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀
    𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  obtain ⟨hA₁m, -, -, -, -, -, -, -, hA₁c, -⟩ := hfam 0
  have hloc := Gj.hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ h𝓖 hfam
  exact Sz.zero_piece_root (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h12 h13 h12₀ h13₀ hκ hκ4
    hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hwℓ hwℓ₂ (h𝓖 0)
    (by filter_upwards [stmt6Sets_of_rootSets hfam 0] with ω h1 using h1.1) (h𝓖' 0)
    (by filter_upwards [stmt6Sets_of_rootSets hfam' 0] with ω h1 using h1.1) hu₀ hA₁m hA₁c hloc hst hRF

/-- **The base selector** (Theorems 1.2–1.3): SB2LIFT's `Sz.baseSelector_usable`. -/
theorem sb2LowerBaseSelectorStatement_of_thms (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerBaseSelectorStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu _ hlθ _ hleft _ ℓ' hwℓ' 𝓖' h𝓖'
  exact Sz.baseSelector_usable hb hE hER hu hlθ k ℓ' hwℓ'
    (Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft) h𝓖'

/-- **(P1) from the entrance law and the root-positivity walk fact** (Theorems 1.2–1.3). -/
theorem lawInU_of_entr (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hA2 : Ca.SB2LowerRootEntranceLawStatement.{u})
    (hpos : SB2LowerRootPosStatement.{u}) : SB2LowerStageLawInUStatement.{u} :=
  lawInU_of_branches h12 h13 h12₀ h13₀ (sb2LowerZeroBranchStatement_of_thms h12 h13 h12₀ h13₀)
    (sb2LowerBaseSelectorStatement_of_thms h12 h13 h12₀ h13₀)
    (rootBranch_of_rootEv (sb2LowerRootEvBranchStatement_of_entr h12 h13 h12₀ h13₀ hA2) hpos)

/-- **hcan from the entrance law and the root-positivity walk fact** (Theorems 1.2–1.3). -/
theorem sb2LowerStageCanonStatement_of_entr (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hA2 : Ca.SB2LowerRootEntranceLawStatement.{u})
    (hpos : SB2LowerRootPosStatement.{u}) :
    Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  sb2LowerStageCanonStatement_of_lawU h12 h13 h12₀ h13₀ (lawInU_of_entr h12 h13 h12₀ h13₀ hA2 hpos)

/-- **The top's hTL from the entrance law, the root-positivity walk fact and the top's `hdet`** (Theorems 1.2–1.3;
`hdet` is closed by ROOTX's `Ro.sb2LowerRootDetWStatement_closed`). -/
theorem sb2LowerTailLiftExStatement_of_entr (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hA2 : Ca.SB2LowerRootEntranceLawStatement.{u})
    (hpos : SB2LowerRootPosStatement.{u})
    (hdet : Ch.SB2LowerRootDetWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  Cg.sb2LowerTailLiftExStatement_of_rest h12 h13 h12₀ h13₀
    (Lk.sb2LowerGeomRestV6 h12 h13 h12₀ h13₀ (Lk.sb2LowerStartDataStatement_of_thms h12 h13 h12₀ h13₀))
    (sb2LowerStageCanonStatement_of_entr h12 h13 h12₀ h13₀ hA2 hpos)
    (Ch.sb2LowerRelPosWRootStatement_of_det h12 h13 h12₀ h13₀ hdet)

end InteractingSLE.Theorem14.SB.Cz
