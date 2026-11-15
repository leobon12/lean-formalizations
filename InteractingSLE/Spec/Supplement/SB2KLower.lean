/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLzAdm

/-!
# SB2(2) in the admissible entry form (ruling R99): the word half and the law half

Packet PROVE-T14-SB2FIN5. Ruling R99 makes `Lz.SB2LowerLaunchEntryAdmStatement` (PROVE-T14-SBLEAVES5) SB2(2)'s target:
R93's entry form plus the source's clause that the old groups left of the upper tip are admissible (supplement p. 632,
`source/spec/p625-671.md` L141, (SB2.1)). Its proof (pp. 631–633) has two independent halves, which this file
separates, with the entry point fixed to `m = −e_R` (`Lu.upperEntry`; the entry clause is FIN4's
`Lu.ae_isRightEntryValue_upperEntry`):

* the **word** (`SB2LowerWordStatement`): `e_R ≥ 0`, the admissibility of the relative word left of the upper tip, and
  SB2(2)'s active word on `(m, 0)` — properties of the boundary data of the conditional field read in the launch
  chart ("The active word and the one branch", reflected; (SB2.1));
* the **law** (`SB2LowerLawStatement`): the lifted lower tail is a staged history of the conditional field, regular,
  adding only right records, with the pathwise link ("Initial and optional Gaussian kernels", the BW3a/BW3 restarts,
  the reconstructed clocks);
* **`sb2LowerLaunchEntryAdmStatement_of_word_law`**: the two give R99's target.

Wiring only; no named input is used beyond the two halves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lz

open Lx Lu Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw

/-- **SB2(2)'s word half** (named input; supplement p. 632, "For the second assertion reflect this construction"
and (SB2.1)): at almost every launch of the upper schedule program the right entry `e_R` is `≥ 0`, and for every
witness `(b', jumps', h')` of the launch clause, with `m = −e_R`, the relative data are admissible for the lower
flow left of the upper tip and carry SB2(2)'s active word on `(m, 0)`. -/
def SB2LowerWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      (∀ᵐ ω₀ ∂P, ω₀ ∈ upperLaunchSet κ b jumps E u l k → 0 ≤ upperEntry κ b jumps E u l k ω₀) ∧
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
            (∀ y, y ≤ m → y ∉ affJumps 1 m jumps' →
              -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ)) ∧
            IsActiveHighWord κ b jumps u l b' jumps' m

/-- **SB2(2)'s law half** (named input; supplement pp. 631–633, "Initial and optional Gaussian kernels" through
"complete marked field–history laws"): at almost every launch of the upper schedule program and for every witness
`(b', jumps', h')`, with `m = −e_R`, the lower walk's tail lifted into the launch chart is a staged history of the
conditional field (frame `affField m h'`), regular, adding only right records, and pathwise equal to the actual lower
walk outside the filled upper prefix. -/
def SB2LowerLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
            IsStagedHistory κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' jumps' m) EL ∧
            StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (relLowerSpec b' jumps' m) EL ∧
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              WalkRightAdds κ (affData 1 m b') (affJumps 1 m jumps') (fun _ => EL) ω) ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
                  relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ∧
                relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ⊆
                  lowerWalkSet κ b jumps E ω

/-- **SB2(2) in the admissible entry form (R99) from its word and law halves**: `m := −e_R`, the entry clause from
`Lu.ae_isRightEntryValue_upperEntry`. -/
theorem sb2LowerLaunchEntryAdmStatement_of_word_law (hw : SB2LowerWordStatement.{u})
    (hl : SB2LowerLawStatement.{u}) : SB2LowerLaunchEntryAdmStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  obtain ⟨hnn, hword⟩ := hw κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hnn, hword, hl κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    ae_isRightEntryValue_upperEntry (hER _ (isBoundaryContinuedProgram_upperSpec hlθ)) k]
    with ω₀ hnn₀ hword₀ hlaw₀ hent₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  have hF := mem_upperLaunchSet hlaunch
  have hent := hent₀ hF
  rw [upperLaunchChart_eq hlaunch] at hent
  obtain ⟨hadm, hact⟩ := hword₀ c θ hlaunch b' J' h' hb' hT' hG' _ rfl
  obtain ⟨EL, hst, hreg, hra, hlink⟩ := hlaw₀ c θ hlaunch b' J' h' hb' hT' hG' _ rfl
  refine ⟨-upperEntry κ b jumps E u l k ω₀, EL, neg_nonpos.2 (hnn₀ hF), hadm, ?_, hact, hst, hreg, hra, hlink⟩
  rw [neg_neg]
  exact hent

end InteractingSLE.Theorem14.SB.Lz
