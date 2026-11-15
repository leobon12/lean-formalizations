/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CcClose

/-!
# (P1)'s step with the widened zero branch (D89): no walk fact

Packet PROVE-SB2-CANON, round 10 (D89). SB2LIFT widens its zero piece `Sz.zero_piece_root` to the empty relative tail
at `relOff = ℓ` off a zero root (`ζ_ℓ ≤ entrR`: piece `ℓ` adds nothing before `R`, the hull is unchanged). With it,
the step's coverage needs no walk fact:

* **`SB2LowerZeroBranchWStatement`**: the zero branch with the event's lifetime clause
  `ζ_ℓ = 0 ∨ (upper launch ∧ relOff = ℓ ∧ ¬ ZeroRoot ∧ ζ_ℓ ≤ entrR)` (SB2LIFT's `Sz.zero_piece_rootE`, D89);
* **`sb2LowerStageStepStatement_of_branchesW`**: the step from that branch, the base selector and the root branch in
  root-event form. A launch at `ℓ` with `relOff = ℓ`, not a zero root, of positive lifetime, is either in the root
  event (`entrR < ζ_ℓ`) or in the widened zero event (`ζ_ℓ ≤ entrR`);
The closed forms (no input besides Theorems 1.2–1.3) are in `SB2EzClose`.

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

/-- **Named statement (SB2LIFT's, D89): the zero branch widened to the empty relative tail.**
`Cz.SB2LowerZeroBranchStatement` with the event's lifetime clause `ζ_ℓ = 0` widened to
`ζ_ℓ = 0 ∨ (upper launch ∧ relOff = ℓ ∧ ¬ ZeroRoot ∧ ζ_ℓ ≤ entrR)` (SB2LIFT's `Sz.zero_piece_rootE`): at
`relOff = ℓ` off a zero root, piece `ℓ` adds nothing before `R`, so the hull is unchanged. -/
def SB2LowerZeroBranchWStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k →
    ∀ ℓ : ℕ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t)) →
    ∀ (C : Set Ω) (β : Ω → BoundaryWord) (S : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ C) →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
          Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) →
    ∀ (𝓖' : Filtration ℝ≥0 mΩ) (A₁' A₂B' A₂' : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖' t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k (ℓ + 2) t u₀ (A₁' t) (A₂B' t) (A₂' t)) →
    Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁'
      (C ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∨
          (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
            relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
            ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≤ Nd.entrR κ b jumps E u l k ℓ ω)) ∧
        ¬ (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
          Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))}) β S

/-- **(P1)'s induction step from the widened zero branch, the base selector and the root branch in root-event form**
(Theorems 1.2–1.3). -/
theorem sb2LowerStageStepStatement_of_branchesW (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroBranchWStatement.{u})
    (hQ : SB2LowerBaseSelectorStatement.{u}) (hR : SB2LowerRootEvBranchStatement.{u}) :
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
  obtain ⟨Rs, DR, βR, SR, hRst, hR1, hR2, hRiff, hRsub⟩ := hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l
    k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀ 𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  have hZst := hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀
    𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  obtain ⟨β', S', hglue, hβB⟩ := stageLawOn_glue4 hQ1 hQ2 hF1 hF2 hR1 hR2 hB hT hRst hZst
  refine ⟨_, β', S', hglue, ?_, ?_⟩
  · -- the coverage
    filter_upwards [hQiff, hFiff, hRiff, hRsub, hC] with ω hq hf hri hrs hc hS
    obtain ⟨hup, hl2⟩ := hS
    have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none :=
      launch_of_launch_add_two _ hl2
    have hSℓ : ω ∈ stageEvent κ b jumps E u l k ℓ := ⟨hup, hl⟩
    have hev := Lk.relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
    refine mem_glue4 (fun h => hq.1 h) (fun _ h => h) (fun _ _ h => hrs (hri.1 h)) (fun hnq hnf hnr => ?_)
    have hnot := fun h => hnq (hq.2 ⟨hup, h⟩)
    refine ⟨hc hSℓ, hl, ?_, fun h => hnot (Or.inr ⟨by omega, h.2⟩)⟩
    by_cases hζ : (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0
    · exact Or.inl hζ
    have hpos : 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := pos_iff_ne_zero.2 hζ
    rcases Nat.lt_or_ge (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ℓ with hlt | hge
    · exact absurd (hf.2 ⟨hSℓ, hlt, hpos⟩) hnf
    · have hle : ¬ ℓ + 2 ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) := fun h => hnot (Or.inl h)
      have heq : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ := by omega
      have hnZ := fun hz => hnot (Or.inr ⟨by omega, hz⟩)
      exact Or.inr ⟨hup, heq, hnZ, not_lt.1 fun hlt => hnr (hri.2 ⟨hSℓ, heq, hnZ, hlt⟩)⟩
  · -- the root facts at `ℓ + 2`: the base's
    filter_upwards [hRFB, hQiff] with ω h1 h2 hS ho
    rw [hβB ω (h2.2 ⟨hS.1, Or.inl ho⟩)]
    exact h1 hS (Or.inl ho)

end InteractingSLE.Theorem14.SB.Cz
