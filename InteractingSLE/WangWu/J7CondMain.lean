/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J7Cond
import InteractingSLE.WangWu.J5ChartClause

/-!
# Wang–Wu at `κ = 4`: `Chamber4JointStatement` from the seed three-line space and the chamber clause

Packet PROVE-WW-B23. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867). `WangWu.Chamber4.Chamber4JointStatement` (PROVE-WW-B20) is Proposition 4.24's chamber pair on
one space: the chamber chart data with the coupling clause of `SLE₄(ρL; ρR)` ((J3)–(J5)), the pulled-back field
`h_ψ`, the locality of the hulls for `h_ψ` (J6), and the conditioning data `Q` with (i)–(iii) (J7). This file delivers
it from two named inputs, the exact `κ = 4` twins of the specification's Lemma 7.1 inputs
(`Sec7.Lemma72E.lemma71JointStatement_of_clause`: three-curve space + `PocketClauseStatement`):

* **`SeedThreeSpaceStatement`** (J1, Proposition 4.19 and Lemma 4.21): for `ρL, ρR > −2` a seed three-line space
  (`SeedThree.IsSeedThreeSpace`, WW-B22) with base weights `(ρL + 2; ρR + 2)` and wall heights
  `u₁ = −λ(ρR + 2) < 0 < u₂ = λ(ρL + 2)` ("Choose `a, b` sufficiently large that the seed lines at heights `u₁, 0, u₂`
  are all non-boundary-intersecting");
* **`ChamberClauseStatement`** (J5, Proposition 4.20 stopped / three lines): on every seed three-line space, a chamber
  construction (`Sec7.Lemma71K.IsPocketConstruction`), a `σ(β, α)`-measurable branch `n` and the fixed-time chart
  coupling clause of the word `(u₂/λ − 2; −u₁/λ − 2)` in the filtration of the walls and the mapped middle prefix —
  the hypothesis `hcf` of WW-B22's `SeedThree.isChamberChartData_of_isPocketConstruction` (WW-B22 derives it from the
  prime-end premise, `SeedThree.isChartCouplingCharFunConst_of_primeEnd_three`).

**`chamber4JointStatement_of_clause`**: the chamber chart data are WW-B22's
`SeedThree.isChamberChartData_of_isPocketConstruction`; (J6) is `isLocalSet_hull_three`; (J7) (i) is
`isAEDeterminedBy_field_seed`, (ii) is `Sec7.Lemma72B.isAEDeterminedBy_killedHistory_of_le_curves` (the chamber
filtration lies in the completed σ-algebra of the three lines, which are field-determined), (iii) is `indepFun_three`.
With `Chamber4.twoSeedGraphInput_four_of_joint` this gives `LP.TwoSeedGraphInput 4` from the two inputs.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Real

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.WangWu.ChamberCond

open Sec7 Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71K MartChar SeedThree LawUnique

/-- **Named input (J1): the seed three-line space of Proposition 4.24** (Wang–Wu L1816–1867, "Choose `a, b` sufficiently
large that the seed lines at heights `u₁, 0, u₂` are all non-boundary-intersecting"; `u₂ = λ(ρL + 2)`,
`u₁ = −λ(ρR + 2)`). For `ρL, ρR > −2`, some probability space carries a GFF `h` with the two-seed data of
`(ρL + 2; ρR + 2)` and its three seed lines at heights `u₂ > 0 > u₁` and `0` (left wall `β`, right wall `α`, middle
line `γ`), forming a three-line space: almost surely ordered (Proposition 4.19) and with no common arc of the middle
line and a wall (Lemma 4.21). WW-B22's `SeedThree.isSeedThreeSpace_of_seed` reduces it to these two facts on the
space of `SeedField.exists_seedLineSpace`. -/
def SeedThreeSpaceStatement : Prop :=
  ∀ ρL ρR : ℝ, -2 < ρL → -2 < ρR →
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ),
      IsSeedThreeSpace (ρL + 2) (ρR + 2) (-(wwLambda * (ρR + 2))) (wwLambda * (ρL + 2)) P h u₀ β α γ

/-- **Named input (J5): the chamber clause on every seed three-line space** (Wang–Wu Proposition 4.24: "The
conditional field `H = (h|_C) ∘ ψ⁻¹` is a GFF in `ℍ` with boundary values `λ − u₂ = −λ(1 + ρL)` on `ℝ₋`,
`−λ − u₁ = λ(1 + ρR)` on `ℝ₊`. Proposition 4.20 applies at every stopping time in the filtration enlarged by the walls.
Therefore the transformed middle line `X` satisfies the local Markov coupling with these values"). On every seed
three-line space with wall heights `u₁ < 0 < u₂` there are a chamber construction `(C, c, γ')`, a `σ(β, α)`-measurable
branch shift `n` and constants `a', k` for which the chart coupling clause of the two-seed word
`(u₂/λ − 2; −u₁/λ − 2)` holds at fixed times in the prefix filtration of the walls and the mapped middle segment, with
the chart `shiftLift c n` (the `κ = 4` twin of `Sec7.Lemma72E.PocketClauseStatement`). -/
def ChamberClauseStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (rL rR u₁ u₂ : ℝ)
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ),
    IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ →
    ∃ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ) (n : Ω → ℤ) (a' k : ℝ),
      IsPocketConstruction P β α γ C c γ' ∧
      Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      IsChartCouplingCharFunConst 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2) P
        (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
        (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
        (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
        (fun ω => shiftLift (c ω) (n ω)) a' k h

/-- The seed weights read off the wall heights `u₂ = λ(ρL + 2)`, `u₁ = −λ(ρR + 2)`. -/
theorem seed_weights (ρL ρR : ℝ) :
    wwLambda * (ρL + 2) / wwLambda - 2 = ρL ∧ -(-(wwLambda * (ρR + 2))) / wwLambda - 2 = ρR := by
  have hl : wwLambda ≠ 0 := wwLambda_pos.ne'
  constructor
  · rw [mul_div_cancel_left₀ _ hl]
    ring
  · rw [neg_neg, mul_div_cancel_left₀ _ hl]
    ring

/-- **`Chamber4.Chamber4JointStatement` from the seed three-line space and the chamber clause** (see the module
docstring). Conditional helper. -/
theorem chamber4JointStatement_of_clause (hsp : SeedThreeSpaceStatement.{u}) (hcl : ChamberClauseStatement.{u}) :
    Chamber4.Chamber4JointStatement.{u} := by
  intro ρL ρR hL hR _
  obtain ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, hS⟩ := hsp ρL ρR hL hR
  obtain ⟨C, c, γ', n, a', k, hpc, hn, hcf⟩ := hcl P _ _ _ _ h u₀ β α γ hS
  obtain ⟨e1, e2⟩ := seed_weights ρL ρR
  rw [e1, e2] at hcf
  have hT : IsThreeLineSpace P h u₀ β α γ := hS.2.2.2.2.2.2.1
  have hT' := hT
  obtain ⟨-, -, -, hβ62, hα62, hγ62, -⟩ := hT'
  obtain ⟨h𝓖, hnull, hγ', hW0, hc, hWa, hK, hh, hcc, hdom, hfwd, hliftm, hliftc, hcf', hCm', hfwd', hliftm', hfr,
    hle⟩ := isChamberChartData_of_isPocketConstruction hT hpc hn hcf
  have hlc : ∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (shiftLift (c ω) (n ω)).dom := hliftc
  have ht : ∀ ω, IsChartTransport (shiftLift (c ω) (n ω)) 1 a' k (h ω)
      (chartField (shiftLift (c ω) (n ω)) a' k (h ω)) := fun ω =>
    isChartTransport_chartField (hcc ω) (hlc ω) a' k (h ω)
  set Q := Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h with hQdef
  have hQm : Measurable Q := measurable_pocketRecord_three hT hpc hn
  have hrec := isAEDeterminedBy_field_seed hS hcc hCm' hfwd' hliftm' hliftc hfr ht
  have hind := indepFun_three (κ := 4) (by norm_num) (by norm_num) hL hR hT hpc hn hcf
  refine ⟨Ω, mΩ, P, hP, _, h𝓖, γ', fun s ω => segDriver (γ' ω) s, fun ω => capLife (γ' ω), h,
    fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω), fun ω => shiftLift (c ω) (n ω), a', k,
    ULift.{u} (((ℝ≥0 → ℂ) × (ℝ≥0 → ℂ)) × (TestOn upperHalfPlaneOpens → ℝ)), inferInstance,
    fun ω => ULift.up (Q ω), hnull, hγ', hW0, hc, hWa, hK, hh, hcc, hdom, hfwd, hliftm, hliftc, hcf', ht,
    fun τ hτ hτT => isLocalSet_hull_three hT hpc hn hcf τ hτ hτT, measurable_up.comp hQm, ?_, ?_, ?_⟩
  · obtain ⟨g, hg, hhg⟩ := hrec
    exact ⟨fun p => g (ULift.down p.1, p.2), hg.comp (measurable_down.comp measurable_fst |>.prodMk measurable_snd),
      hhg⟩
  · exact Lemma72B.isAEDeterminedBy_killedHistory_of_le_curves hh hβ62 hα62 hγ62 hle hWa hc _
  · exact hind.comp measurable_id measurable_up

/-- **`LP.TwoSeedGraphInput 4` from the seed three-line space and the chamber clause**
(`Chamber4.twoSeedGraphInput_four_of_joint` after `chamber4JointStatement_of_clause`). Conditional helper. -/
theorem twoSeedGraphInput_four_of_clause (hsp : SeedThreeSpaceStatement.{u}) (hcl : ChamberClauseStatement.{u}) :
    LP.TwoSeedGraphInput.{u} 4 :=
  Chamber4.twoSeedGraphInput_four_of_joint (chamber4JointStatement_of_clause hsp hcl)

end InteractingSLE.WangWu.ChamberCond
