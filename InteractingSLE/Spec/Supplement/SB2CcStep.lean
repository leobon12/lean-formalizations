/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CcStmt
import InteractingSLE.Spec.Supplement.SB2CcGlue
import InteractingSLE.Spec.Supplement.SB2CcLaunch
import InteractingSLE.Spec.Supplement.SB2CbStep
import InteractingSLE.Spec.Supplement.SB2CbBase
import InteractingSLE.Spec.Supplement.SB2FsSel
import InteractingSLE.Spec.Supplement.SB2ChWit

/-!
# (P1)'s induction step: the glue of the four branches and its coverage (D86)

Packet PROVE-SB2-CANON, round 9. **`sb2LowerStageStepStatement_of_branches`**: the step
`Cz.SB2LowerStageStepStatement` (`StageInv ℓ → StageInv (ℓ + 2)` between flow stages) from

* the base branch at `ℓ + 2` (`base_branch`, proved) and SB2LIFT's selector for its event
  (`SB2LowerBaseSelectorStatement`, D86);
* the tail branch (`tail_branch`, proved) on 6E's live event `F`, a selector by F3LAW's `Fs.selector_of_prev`;
* the root branch (`SB2LowerRootBranchStatement`: CONDFIN's root piece, D85);
* SB2LIFT's zero branch (`SB2LowerZeroBranchStatement`, D86),

glued in this order (`stageLawOn_glue4`). The coverage of `stageEvent (ℓ + 2)`: a launch at `ℓ + 2` follows a launch
at `ℓ` (`launch_of_launch_add_two`). Off the base event `relOff ≤ ℓ` (`relOff` is even, `Lk.relOff_even`) and the
sample is not a zero root at `ℓ`. It lies in the tail event if `relOff < ℓ` and `ζ_ℓ > 0`, in the root selector if
`relOff = ℓ` and `ζ_ℓ > 0`, and in the zero event otherwise. The root facts at `ℓ + 2` are the base's (the glued word
is the base word on the base selector).

Then **`lawInU_of_branches`** ((P1) in the form `Cz.SB2LowerStageLawInUStatement`),
**`sb2LowerStageCanonStatement_of_branches`** (hcan) and **`sb2LowerTailLiftExStatement_of_branches`** (the top's
hTL, with the top's `hdet` — closed by ROOTX's `Ro.sb2LowerRootDetWStatement_closed` — through
`Ch.sb2LowerRelPosWRootStatement_of_det`).

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

/-- **(P1)'s induction step from its zero, base-selector and root branches** (Theorems 1.2–1.3). -/
theorem sb2LowerStageStepStatement_of_branches (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroBranchStatement.{u})
    (hQ : SB2LowerBaseSelectorStatement.{u}) (hR : SB2LowerRootBranchStatement.{u}) :
    SB2LowerStageStepStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ hinv
    u₀ hu₀ 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  have hℓe : ℓ % 2 = 0 := ((flow_iff b jumps _ true ℓ).1 hwℓ).1
  -- CONDFIN's line family at `ℓ` and the invariant there
  obtain ⟨𝓖, A₁, A₂B, A₂, h𝓖, hfam⟩ :=
    Cx.exists_rootLineFamily (P := P) (u := u) (l := l) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ hu₀
  obtain ⟨C, β, S, hst, hC, hRF⟩ := hinv u₀ hu₀ 𝓖 A₁ A₂B A₂ h𝓖 hfam
  -- the four pieces at `ℓ + 2` and their selectors
  obtain ⟨βB, SB, hB, hRFB⟩ := base_branch h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlp hlθ hLw k (ℓ + 2)
    hleft hwℓ₂ hu₀ h𝓖' hfam'
  obtain ⟨Qs, hQ1, hQ2, hQiff⟩ := hQ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk
    (ℓ + 2) hwℓ₂ 𝓖' (h𝓖' 0)
  obtain ⟨F, βT, ST, hFm, hFiff, hT⟩ := tail_branch h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlp hlθ hLw k ℓ
    hleft hwℓ hwℓ₂ hu₀ h𝓖 hfam hst hC (h𝓖' 0) (by filter_upwards [stmt6Sets_of_rootSets hfam' 0] with ω h1 using h1.1)
  obtain ⟨hF1, hF2⟩ := Fs.selector_of_prev hwℓ hwℓ₂ (h𝓖 0) (h𝓖' 0) hFm
  obtain ⟨Rs, DR, βR, SR, hRst, hR1, hR2, hRsub, hRcov⟩ := hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l
    k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀ 𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  have hZst := hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀
    𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  obtain ⟨β', S', hglue, hβB⟩ := stageLawOn_glue4 hQ1 hQ2 hF1 hF2 hR1 hR2 hB hT hRst hZst
  refine ⟨_, β', S', hglue, ?_, ?_⟩
  · -- the coverage
    filter_upwards [hQiff, hFiff, hRsub, hRcov, hC] with ω hq hf hrs hrc hc hS
    obtain ⟨hup, hl2⟩ := hS
    have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none :=
      launch_of_launch_add_two _ hl2
    have hSℓ : ω ∈ stageEvent κ b jumps E u l k ℓ := ⟨hup, hl⟩
    have hev := Lk.relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
    refine mem_glue4 (fun h => hq.1 h) (fun _ h => h) (fun _ _ h => hrs h) (fun hnq hnf hnr => ?_)
    have hnot := fun h => hnq (hq.2 ⟨hup, h⟩)
    refine ⟨hc hSℓ, hl, ?_, fun h => hnot (Or.inr ⟨by omega, h.2⟩)⟩
    by_contra hζ
    have hpos : 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := pos_iff_ne_zero.2 hζ
    rcases Nat.lt_or_ge (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ℓ with hlt | hge
    · exact hnf (hf.2 ⟨hSℓ, hlt, hpos⟩)
    · have hle : ¬ ℓ + 2 ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) := fun h => hnot (Or.inl h)
      have heq : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ := by omega
      exact hnr (hrc hSℓ heq (fun hz => hnot (Or.inr ⟨by omega, hz⟩)) hpos)
  · -- the root facts at `ℓ + 2`: the base's
    filter_upwards [hRFB, hQiff] with ω h1 h2 hS ho
    rw [hβB ω (h2.2 ⟨hS.1, Or.inl ho⟩)]
    exact h1 hS (Or.inl ho)

/-- **(P1) from its zero, base-selector and root branches** (Theorems 1.2–1.3). -/
theorem lawInU_of_branches (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroBranchStatement.{u})
    (hQ : SB2LowerBaseSelectorStatement.{u}) (hR : SB2LowerRootBranchStatement.{u}) :
    SB2LowerStageLawInUStatement.{u} :=
  lawInU_of_step h12 h13 h12₀ h13₀ (sb2LowerStageStepStatement_of_branches h12 h13 h12₀ h13₀ hZ hQ hR)

/-- **hcan from (P1)'s branches** (Theorems 1.2–1.3). -/
theorem sb2LowerStageCanonStatement_of_branches (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroBranchStatement.{u})
    (hQ : SB2LowerBaseSelectorStatement.{u}) (hR : SB2LowerRootBranchStatement.{u}) :
    Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  sb2LowerStageCanonStatement_of_step h12 h13 h12₀ h13₀
    (sb2LowerStageStepStatement_of_branches h12 h13 h12₀ h13₀ hZ hQ hR)

/-- **The top's hTL from (P1)'s branches and the top's `hdet`** (Theorems 1.2–1.3; `hdet` is closed by ROOTX's
`Ro.sb2LowerRootDetWStatement_closed`). -/
theorem sb2LowerTailLiftExStatement_of_branches (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroBranchStatement.{u})
    (hQ : SB2LowerBaseSelectorStatement.{u}) (hR : SB2LowerRootBranchStatement.{u})
    (hdet : Ch.SB2LowerRootDetWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  Cg.sb2LowerTailLiftExStatement_of_rest h12 h13 h12₀ h13₀
    (Lk.sb2LowerGeomRestV6 h12 h13 h12₀ h13₀ (Lk.sb2LowerStartDataStatement_of_thms h12 h13 h12₀ h13₀))
    (sb2LowerStageCanonStatement_of_branches h12 h13 h12₀ h13₀ hZ hQ hR)
    (Ch.sb2LowerRelPosWRootStatement_of_det h12 h13 h12₀ h13₀ hdet)

end InteractingSLE.Theorem14.SB.Cz
