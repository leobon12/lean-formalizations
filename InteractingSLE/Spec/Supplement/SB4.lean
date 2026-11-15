/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB5
import InteractingSLE.Spec.Supplement.SBWire

/-!
# Theorem SB4: the common-seed assertion from the distinct-seed one; the frontiers from two SB4 clauses

Packet PROVE-T14-SB2. Theorem SB4 (supplement p. 634, `source/spec/p625-671.md` L171–L174) has three clauses: the
common-seed assertion (and its reflection), the same-connector assertion, and the distinct-seed version. The
common-seed clause is the distinct-seed clause at `u = 0` (resp. `v = 0`), where the bridge `(u, 0)` is empty and its
hypotheses are vacuous:

* **`sb4Statement_of_distinctSeed`**: `SB4Statement` from `SB4DistinctSeedStatement`;
* **`sbFrontierStatement_of_sb4`**: `SBFrontierStatement` from Lemma GW2, Lemma GW0's forward implication, the two
  SB4 clauses `SB4DistinctSeedStatement` and `SB4InitialArcStatement` (the same-connector clause on the initial
  forced arc), and GW1's properness (`sbFrontierStatement_of_sb` with `sb5Statement_of_inputs`);
* `boundaryWalks_frontiers_of_sb4`: the frozen frontiers conclusion in provider shape from the same inputs and GW2a.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-- An empty bridge `(0, 0)` satisfies every condition. -/
theorem forall_mem_Ioo_self {p : ℝ → Prop} : ∀ x ∈ Ioo (0 : ℝ) 0, p x := fun _ hx =>
  absurd (hx.1.trans hx.2) (lt_irrefl _)

/-- **Theorem SB4, common seed, from its distinct-seed version** (supplement p. 634): the common-seed assertion and
its reflection are the distinct-seed assertions with `u = 0` and `v = 0`, whose bridge `(0, 0)` is empty. -/
theorem sb4Statement_of_distinctSeed (hDS : SB4DistinctSeedStatement.{u}) : SB4Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE l hl h41
  have H := hDS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE l hl h41
  exact ⟨fun hθ => H.1 0 le_rfl hθ forall_mem_Ioo_self fun _ _ => forall_mem_Ioo_self,
    fun hθ => H.2 0 le_rfl hθ forall_mem_Ioo_self fun _ _ => forall_mem_Ioo_self⟩

/-- **The frontiers of Theorem 1.4 from two clauses of SB4** (the sewn barriers): `SBFrontierStatement` from Lemma GW2,
Lemma GW0's forward implication (ambient counterflow admissibility, SB5.1), SB4's distinct-seed clause, SB4's
same-connector clause on the initial forced arc, and GW1's properness. -/
theorem sbFrontierStatement_of_sb4 (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hDS : SB4DistinctSeedStatement.{u}) (hIA : SB4InitialArcStatement.{u}) (hprop : GW1ProperStatement.{u}) :
    SBFrontierStatement.{u} :=
  sbFrontierStatement_of_sb hGW2 (sb4Statement_of_distinctSeed hDS) (sb5Statement_of_inputs hGW0 hIA hDS) hprop

/-- **Theorem 1.4, frontiers** (`IsCenteredCounterflowDriver.boundaryWalks_frontiers`), provider shape, from Lemma
GW2a, Lemma GW2, Lemma GW0's forward implication, the two SB4 clauses and GW1's properness (conditional helper; not
the provider). -/
theorem boundaryWalks_frontiers_of_sb4 (hGW2a : GW2aContainmentStatement.{u})
    (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u}) (hDS : SB4DistinctSeedStatement.{u})
    (hIA : SB4InitialArcStatement.{u}) (hprop : GW1ProperStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption) :
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) :=
  boundaryWalks_frontiers_of_sb hGW2a hGW2 (sb4Statement_of_distinctSeed hDS) (sb5Statement_of_inputs hGW0 hIA hDS)
    hprop hκ hκ4 hb hh hcf hζ' hE

end SB

end Theorem14

end InteractingSLE
