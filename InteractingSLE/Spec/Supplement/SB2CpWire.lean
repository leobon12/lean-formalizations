/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CpStmt
import InteractingSLE.Spec.Supplement.SB2CqPkg
import InteractingSLE.Spec.Supplement.SB2CzTop
import InteractingSLE.Spec.Supplement.SB2YjMain
import InteractingSLE.Spec.Supplement.SB2CxFam
import InteractingSLE.Spec.Supplement.SB2FoInp
import InteractingSLE.Spec.Supplement.SB2CgTop
import InteractingSLE.Spec.Supplement.SB2CyWord
import InteractingSLE.Spec.Supplement.SB2JeAS
import InteractingSLE.Spec.Supplement.SB2YdStart
import InteractingSLE.Spec.Supplement.SB2NeRoot9E

/-!
# hcan and the top's hTL from the four remaining stage inputs (D77 item 2)

Packet PROVE-SB2-CANON, round 6. Theorems 1.2–1.3 as hypotheses (R48), and exactly four named inputs:

* F3LAW's (P1) law, `Cz.SB2LowerStageLawInStatement` (D76);
* CONDFIN's K2 at the tails, `Cz.SB2LowerTailK2Statement` (D77 item 1);
* GEOM2's `Ct.SB2LowerRootIdentStatement` (D70), and NOJUMP's root statement `Ne.SB2LowerRootVersionStatement9E` (only
  through GEOM2's proof of the former).

* **`sb2LowerStagePkgStatement_of_inputs`**: the per-stage package `Cz.SB2LowerStagePkgStatement` (round 1's named
  statement). At a flow stage: CONDFIN's line family (`Cx.exists_rootLineFamily`; joint set `A₂J`, Statement6's set
  premise by **`stmt6Sets_of_rootSets`**), F3LAW's law for it, SB2LIFT's
  proved Statement6 (`Sx.sb2LowerStageVersionStatement6E`) for the law's word, the conditional law at the offset
  (`Fo.ae_lawx_of_mvLaw`), CONDFIN's K2, and (P2)–(P4) by `Cz.pkgTail_of_k2`.
* **`sb2LowerStageCanonStatement_of_inputs`**: hcan, `Mz.SB2LowerStageCanonStatement`
  (`Cz.sb2LowerStageCanonStatement_of_pkg`).
* **`sb2LowerTailLiftExStatement_of_inputs`**: the top's hTL, `Lk.SB2LowerTailLiftExStatement`, by CONDFIN's
  `Cg.sb2LowerTailLiftExStatement_of_rest` with LIFTSET's proved v6 input (`Lk.sb2LowerGeomRestV6` on SB2LIFT's proved
  start data `Lk.sb2LowerStartDataStatement_of_thms`), hcan above, and the root from GEOM2's statement
  (`Cy.sb2LowerRelPosWRootStatement_of_ident`); **`sb2LowerTailLiftExStatement_of_inputs9E`**: the same with GEOM2's
  result in the form `Ne.SB2LowerRootVersionStatement9E → Ct.SB2LowerRootIdentStatement` and NOJUMP's statement;
  **`sb2LowerRootDetWStatement_of_inputs`**: the top's `hdet` from GEOM2's statement (for
  `Wire.theorem14Statement_oneG`, whose SB2(2) inputs are `hcan` and `hdet`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets Lv Ms Mf Lk Lu Mx Mz

/-- **Statement6's set premises from CONDFIN's line family** (`A₁ t` and the joint set `A₂J t` as filled versions; the
two fields of `Cx.RootSetsAt` that say so). -/
theorem stmt6Sets_of_rootSets {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {u₀ : ℂ → ℝ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (hfam : ∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂J t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω := fun t => by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hform, -, -, -, -, -, hformJ, -⟩ := hfam t
  filter_upwards [hform, hformJ] with ω h1 h2
  exact ⟨h1.1, h2⟩

/-- **The per-stage package from F3LAW's (P1) law and CONDFIN's K2 at the tails** (Theorems 1.2–1.3). -/
theorem sb2LowerStagePkgStatement_of_inputs (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hP1 : SB2LowerStageLawInStatement.{u}) (hK2 : SB2LowerTailK2Statement.{u} h12p) :
    SB2LowerStagePkgStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hflow).1
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  -- the joint line family and F3LAW's law for it
  obtain ⟨𝓖, A₁, A₂B, A₂, h𝓖, hfam⟩ :=
    Cx.exists_rootLineFamily (P := P) (u := u) (l := l) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hflow hu₀
  have hA := stmt6Sets_of_rootSets hfam
  obtain ⟨K', G', Y, β, M, types, hlaw, hβ, hcovL, htypes, hcovAll, hmeanP, hheightP⟩ :=
    hP1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow 𝓖 A₁ A₂ h𝓖 hA
  have hlaw' := hlaw
  obtain ⟨-, -, -, -, -, -, -, hβ𝓜, hsort, hM0, hMb, -⟩ := hlaw'
  -- SB2LIFT's Statement6 for the law's word
  have h6 := sb2LowerStageVersionStatement6_of_6E (Sx.sb2LowerStageVersionStatement6E h12 h13 h12₀ h13₀)
  obtain ⟨K, x₀, pc, tL, relLife, F, hKm, hKc, hKp, hKF, hx₀, hF, hpc, htL, hent, hFae, hS⟩ :=
    h6 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft ℓ 𝓖 A₁ A₂ h𝓖 hA β types hβ
      hsort htypes u₀ hu₀ (hmeanP u₀ hu₀) hheightP
  have hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    filter_upwards [hFae] with ω h1 hω using (h1.1 hω).1.2
  have hcover : ∀ᵐ ω ∂P, ω ∈ F →
      angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω)) ∈ types := by
    filter_upwards [hFl, hcovAll] with ω h1 h2 hω using h2 (h1 hω) (x₀ ω)
  obtain ⟨S, hcl, hleAll, hlife⟩ := hS hcover
  -- the word's conditional law at the offset, and K2
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ G' := by
    filter_upwards [hFl, hcovL] with ω h1 h2 hω using h2 (h1 hω)
  have hlawK := Fo.ae_lawx_of_mvLaw hh.1 hle0 hlaw hKm hKc hKp hx₀ hF hFG hKF
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ𝓜)
  have hk2 := hK2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft ℓ hℓ u₀ hu₀ 𝓖 A₁
    A₂B A₂ h𝓖 hfam F K x₀ β types pc tL relLife S hKm hKc hKp hKF hx₀ hF hpc htL hent hFae hc hsort hlawK
    (hmeanP u₀ hu₀) htypes hcover M hM0 hMb (hleAll 0) hlife
  -- the retained set on launches
  have hAL : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → A₁ 0 ω = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    filter_upwards [hA 0, Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ] with ω h1 h2 hl
    rw [h1.1]; exact (h2 hl).2.2.2.2
  -- (P2)–(P4)
  obtain ⟨x₀', T, hx₀', hT, hTcov, hfacts⟩ := pkgTail_of_k2 h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu
    hlθ k ℓ hleft hℓ hflow hlaw hcovL hAL h𝓖 hA hKm hKc hKp hKF hx₀ hF hent hFae htypes hcover S hcl (hleAll 0) hc
    hlawK hk2
  -- the marks
  obtain ⟨hE', -, -⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮 : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ :=
    (Mz.stageMarks_mono (Nat.le_succ ℓ)).trans (sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 (ℓ + 1)))
  have h𝒮𝓖 : Ms.stageMarks κ b jumps E u l k ℓ ≤ 𝓖 0 := by
    rw [h𝓖 0]
    refine sup_le_sup le_rfl ?_
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := -(Real.pi / 2)) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ ℓ)
  have hsm : Ms.stageMarks κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 0 :=
    le_inf h𝒮 (h𝒮𝓖.trans (le_aeSigma _ P))
  exact ⟨lineFiltC P 𝓖 0, A₁ 0, K', G', Y, β, M, x₀', T, hsm, hle0, hlaw, hβ, hcovL, hAL, hx₀', hT, hTcov,
    hfacts⟩

/-- **hcan** (`Mz.SB2LowerStageCanonStatement`) from F3LAW's (P1) law and CONDFIN's K2 at the tails
(Theorems 1.2–1.3). -/
theorem sb2LowerStageCanonStatement_of_inputs (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hP1 : SB2LowerStageLawInStatement.{u}) (hK2 : SB2LowerTailK2Statement.{u} h12p) :
    Mz.SB2LowerStageCanonStatement.{u} h12p :=
  sb2LowerStageCanonStatement_of_pkg h12p h13 h13₀ (sb2LowerStagePkgStatement_of_inputs h12p h12 h13 h12₀ h13₀ hP1 hK2)

/-- **The top's hTL** (`Lk.SB2LowerTailLiftExStatement`) from F3LAW's (P1) law, CONDFIN's K2 at the tails and GEOM2's
root identification (Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_inputs (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hP1 : SB2LowerStageLawInStatement.{u})
    (hK2 : SB2LowerTailK2Statement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  Cg.sb2LowerTailLiftExStatement_of_rest h12 h13 h12₀ h13₀
    (Lk.sb2LowerGeomRestV6 h12 h13 h12₀ h13₀ (Lk.sb2LowerStartDataStatement_of_thms h12 h13 h12₀ h13₀))
    (sb2LowerStageCanonStatement_of_inputs _ h12 h13 h12₀ h13₀ hP1 hK2)
    (Cy.sb2LowerRelPosWRootStatement_of_ident h12 h13 h12₀ h13₀ hI)

/-- **The top's hTL with GEOM2's root identification read from NOJUMP's root statement** (Theorems 1.2–1.3; the four
inputs of D77 item 2). -/
theorem sb2LowerTailLiftExStatement_of_inputs9E (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hP1 : SB2LowerStageLawInStatement.{u})
    (hK2 : SB2LowerTailK2Statement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hI : Ne.SB2LowerRootVersionStatement9E.{u} →
      Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (h9 : Ne.SB2LowerRootVersionStatement9E.{u}) : Lk.SB2LowerTailLiftExStatement.{u} :=
  sb2LowerTailLiftExStatement_of_inputs h12 h13 h12₀ h13₀ hP1 hK2 (hI h9)

/-- **The root determination `hdet`** (`Ch.SB2LowerRootDetWStatement`, the top's other SB2(2) input) from GEOM2's root
identification (CONDFIN's `Cy.sb2LowerRootCanonXStatement_of_ident`, `Cy.sb2LowerRootDetWStatement_of_canonX`). -/
theorem sb2LowerRootDetWStatement_of_inputs (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Ch.SB2LowerRootDetWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  Cy.sb2LowerRootDetWStatement_of_canonX h12 h13 h12₀ h13₀
    (Cy.sb2LowerRootCanonXStatement_of_ident h12 h13 h12₀ h13₀ hI)

end InteractingSLE.Theorem14.SB.Cz
