/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14Inputs
import InteractingSLE.Spec.Supplement.SBWeights
import InteractingSLE.WangWu.MeanIdentChamber
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Frozen.Spec.IsSchedule
import InteractingSLE.Frozen.Spec.scheduleProgram
import InteractingSLE.Frozen.Spec.lowerArcRoots

/-!
# Supplement §28: the sewn barriers SB1–SB5 and the frontier input of Theorem 1.4

Packet PROVE-T14-SB (specification supplement §28, `source/spec/p625-671.md` L100–L196, pp. 629–635; the separate
statement "SB", L227, p. 637; and §7.4.3, p. 421: "SB1–SB5 prove the joined barriers … Unrestricted exhaustion then
identifies the actual frontiers").

**Statements, on the frozen carriers of the Theorem 1.4 surface.** `R` is the angle-`−π/2` boundary walk of GW1
(`boundaryWalkSpec b jumps (−π/2) true`), `L` the angle-`π/2` walk (`boundaryWalkSpec b jumps (π/2) false`); "on the
closed left of `R`" is "disjoint from `rightSideOf R`", and "on the closed right of `L`" is "disjoint from
`leftSideOf L`" (the sides used by the frozen frontier anchor). An angle-`θ` flow sees a boundary height `H` as the
left cumulative weight `Sec4.cumWeightLeft κ (H + θχ)` and the right one `Sec4.cumWeightRight κ (H + θχ)`; an open
constant-height interval of `(u, v)` is read through its points off `jumps` (the data are locally constant there).

* `SB1Statement` — Lemma SB1 (an admissible and protected middle word), p. 630;
* `SB3Statement` — Lemma SB3 (a constant upper flow stays to the left of the walk), p. 633, both seed versions;
* `SB4Statement` — Theorem SB4 (the sewn lower barrier), p. 634: the common-seed assertion and its reflection
  ("Reflecting gives the upper-walk barrier");
* `SB4DistinctSeedStatement` — SB4's distinct-seed version, p. 634, and its reflection;
* `SB5Statement` — Corollary SB5 (both barriers for an initial low-arc root), p. 635;
* `SBStatement` — the separate statement SB of p. 637 ("every member of the minimal countable `Θ`-angle family in GW2
  lies on the closed left of `R` and on the closed right of `L`");
* `GW1ProperStatement` — GW1's properness (p. 618: "a field-determined continuous injective proper curve `R`"): the
  physical sets of both walks are relatively closed in `ℍ`.

Lemma SB2 (the two erasures) is a conditional identification of the remaining flows in the conditional field of the
random domain `D_A = ℍ \ fill(A)`; the project has no carrier for that field yet (the same carriers as BW1/BR4a,
PROVE-T14-GW3), so it is not stated here.

**Proved.**
* `sbStatement_of_sb4_sb5 : SB4Statement → SB5Statement → SBStatement` — SB from its two sources (p. 637 and SB5's
  proof): root-`0` schedules by SB4 and its reflection, with (SB4.1) supplied by `SB.sb41_of_mem_Ioo`; forced arcs
  `[0, v]` are real, hence on no side; root-`v` schedules by SB5; countably many schedules and roots on one event.
* `sbFrontierStatement_of_inputs : GW2LightConeStatement → SBStatement → GW1ProperStatement → SBFrontierStatement`
  — "unrestricted exhaustion then identifies the actual frontiers" (p. 421): the completed counterflow range is the
  closure of the GW2 family and `0`; the open right side of a relatively closed `R` misses the family, hence its
  closure (`isOpen_rightSideOf`, `closure_inter_eq_empty`).
* `sbFrontierStatement_of_sb : GW2LightConeStatement → SB4Statement → SB5Statement → GW1ProperStatement →
  SBFrontierStatement`.
* `closure_physSet_inter_H_subset`, `gw1ProperStatement_of_pieces : GW1PieceProperStatement → GW1ProperStatement` —
  a staged history's physical set is relatively closed in `ℍ` once its ordinary pieces are (root and connectors are
  real; finitely many pieces).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

open Sec4

/-! ### The statements -/

/-- **Lemma SB1** (an admissible and protected middle word; supplement p. 630). Let `0 < κ < 4` and `h` a GFF on `ℍ`
with piecewise-constant data `b`. Consider the canonical ordinary flows `η_L` of angle `φ = −π/2` from the lower seed
`v` and `η_U` of angle `ψ > φ` from the upper seed `u < v`, with nonempty initial lifetimes. Suppose every lower-flow
left cumulative weight on `(u, v)` is `> −2`, and on each open constant-height middle interval either the upper-flow
right cumulative weight is `> −2` or the lower-flow left cumulative weight is `≥ c_κ = κ/2 − 2`. Then almost surely
every pair of their finite available prefixes, including terminal ones, has the ordered proper completions of W0
(`η_U` on the closed left of `η_L`). -/
def SB1Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ u v ψ : ℝ, u < v → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u v, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u v, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (ηL ηU : Ω → ℝ≥0 → ℂ) (ζL ζU : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps v (-(Real.pi / 2)) P h ηL ζL → IsFlowLine κ b jumps u ψ P h ηU ζU →
      (∀ᵐ ω ∂P, 0 < ζL ω) → (∀ᵐ ω ∂P, 0 < ζU ω) →
      ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζL ω → (c : ℝ≥0∞) ≤ ζU ω →
        HasOrderedProperCompletions (ηL ω) a (ηU ω) c

/-- **Lemma SB3** (a constant upper flow stays to the left of the walk; supplement p. 633), in the setting of
Theorem 1.4. Let `R` be the completed lower walk (from `0`) and `η` the maximal angle-`ψ` flow (`ψ > −π/2`) from a
seed `u ≤ 0`, with nonempty lifetime; if `u < 0`, assume the original word on `(u, 0)` satisfies SB1's hypotheses.
Then almost surely the whole available range of `η` lies on the closed left of `R`. -/
def SB3Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      ∀ᵐ ω ∂P, η ω '' {t | (t : ℝ≥0∞) ≤ ζ ω} ∩
        rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅

/-- **Theorem SB4** (the sewn lower barrier; supplement p. 634), common-seed assertion and its reflection, in the
setting of Theorem 1.4. For a prescribed finite own angle schedule `l` from the walks' seed `0` (switch times
increasing) with `ψ_j > φ = −π/2` and `|ψ_i − ψ_j| < 2λ/χ` (SB4.1), every finite available history of the schedule
is almost surely on the closed left of the actual lower walk `R`; reflecting, for `ψ_j < π/2` and (SB4.1) it is on
the closed right of the actual upper walk `L`. (Angles stay in `[−π/2, π/2]`, the range of the staged histories `E`
of the Theorem 1.4 surface.) -/
def SB4Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      ((∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
            (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      ((∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
            (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅)

/-- **Theorem SB4, the distinct-seed version** (supplement p. 634) and its reflection, in the setting of Theorem 1.4.
The upper schedule may start at `u ≤ 0` (the lower walk's seed is `0`), provided every lower left group on `(u, 0)`
is admissible and SB1's hybrid condition holds there for every angle of the schedule; its entire available history
is then almost surely on the closed left of `R`. Reflected: a schedule from `v ≥ 0` with every upper-walk right
group on `(0, v)` admissible and the reflected hybrid condition there is on the closed right of `L`. -/
def SB4DistinctSeedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨u, true, scheduleProgram 0 l⟩
            (fun k => E ⟨u, true, scheduleProgram 0 l⟩ k ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩
            (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅)

/-- **Corollary SB5** (both barriers for an initial low-arc root; supplement p. 635), in the setting of Theorem 1.4.
Let `v > 0` be a root on the initial forced lower boundary arc (the lower extreme is immediately inadmissible at `0`
on the right, `b(0⁺) − πχ/2 ≤ −λ`, and every original jump `x ∈ (0, v]` keeps the outward height low,
`b(x⁺) − πχ/2 ≤ −λ`; cf. `lowerArcRoots`), and let every prescribed schedule angle lie in `(−π/2, π/2)`. Then almost
surely the schedule from `v` lies on the closed left of the completed lower walk and on the closed right of the
completed upper walk, including every finite available endpoint. -/
def SB5Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ v : ℝ, 0 < v →
      PiecewiseConstantBoundaryData.rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ PiecewiseConstantBoundaryData.jumpSet b jumps, 0 < x → x ≤ v →
        PiecewiseConstantBoundaryData.rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ᵐ ω ∂P,
        ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
            rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅ ∧
          ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩
              (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ∩
            leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅

/-- **The sewn-barrier input SB** (supplement p. 637: "every member of the minimal countable `Θ`-angle family in GW2
lies on the closed left of `R` and on the closed right of `L`. This includes a seed in the interior of an immediate
low real arc"), in the setting of Theorem 1.4, for every countable angle set `Θ ⊂ (−π/2, π/2)` and every countable
schedule-time set `Q`: almost surely the GW2 family (`boundaryLightConeFamily`) misses the open right side of `R`
and the open left side of `L`. -/
def SBStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable → ∀ Q : Set ℝ≥0, Q.Countable →
      ∀ᵐ ω ∂P,
        boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∩
            rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅ ∧
          boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∩
            leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅

/-- **GW1's properness** (supplement p. 618: "There is a field-determined continuous injective proper curve `R`
from `x` to `y`"; §28, p. 629: "A lower walk in this section means an actual finite simple proper concatenation"),
in the setting of Theorem 1.4: almost surely the physical sets of both walks are relatively closed in `ℍ` (the range
of a proper curve is closed). -/
def GW1ProperStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω ∂P,
        closure (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) ∩ H ⊆
          ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ∧
        closure (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) ∩ H ⊆
          ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)

/-! ### The sides of a relatively closed set -/

/-- `ℍ \ A` is open when `A` is relatively closed in `ℍ`. -/
theorem isOpen_H_diff {A : Set ℂ} (hA : closure A ∩ H ⊆ A) : IsOpen (H \ A) := by
  have hEq : H \ A = H \ closure A := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨hz, fun hc => hzA (hA ⟨hc, hz⟩)⟩
    · rintro ⟨hz, hzA⟩
      exact ⟨hz, fun ha => hzA (subset_closure ha)⟩
  rw [hEq]
  exact QuantumZipper.isOpen_H.sdiff isClosed_closure

/-- The right side of a relatively closed set is open: it is a union of components of the open set `ℍ \ A`. -/
theorem isOpen_rightSideOf {A : Set ℂ} (hA : closure A ∩ H ⊆ A) : IsOpen (rightSideOf A) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  exact ⟨connectedComponentIn (H \ A) z, fun w hw => WangWu.mem_rightSideOf_of_mem_connectedComponentIn hz hw,
    (isOpen_H_diff hA).connectedComponentIn, mem_connectedComponentIn hz.1⟩

/-- The left side of a relatively closed set is open. -/
theorem isOpen_leftSideOf {A : Set ℂ} (hA : closure A ∩ H ⊆ A) : IsOpen (leftSideOf A) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  exact ⟨connectedComponentIn (H \ A) z, fun w hw => WangWu.mem_leftSideOf_of_mem_connectedComponentIn hz hw,
    (isOpen_H_diff hA).connectedComponentIn, mem_connectedComponentIn hz.1⟩

/-- A set missing an open set `U` has its closure missing `U`. -/
theorem closure_inter_eq_empty {S U : Set ℂ} (hU : IsOpen U) (h : S ∩ U = ∅) : closure S ∩ U = ∅ := by
  rw [← not_nonempty_iff_eq_empty, closure_inter_open_nonempty_iff hU, not_nonempty_iff_eq_empty]
  exact h

/-- A real point is not in `ℍ`. -/
theorem ofReal_notMem_H (x : ℝ) : (x : ℂ) ∉ H := by
  simp [QuantumZipper.H]

/-! ### GW1's properness, piece by piece -/

/-- **The physical set of a staged history is relatively closed in `ℍ` once its ordinary pieces are**: the root and
the recorded connectors are real, so their closures miss `ℍ`, and there are finitely many pieces. -/
theorem closure_physSet_inter_H_subset {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hp : ∀ p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1,
      closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2) :
    closure (ExplState.physSet κ b jumps spec D) ∩ H ⊆ ExplState.physSet κ b jumps spec D := by
  have hreal : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  rintro z ⟨hzc, hzH⟩
  have hzH' : 0 < z.im := hzH
  simp only [ExplState.physSet] at hzc ⊢
  rw [closure_union, closure_union] at hzc
  rcases hzc with (h0 | hpcs) | harc
  · rw [closure_singleton, mem_singleton_iff] at h0
    subst h0
    simp at hzH'
  · have hfin := Set.Finite.closure_biUnion (s := {p | p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1})
      (List.finite_toSet _) (fun p => p.1.tipSet p.2.1 p.2.2)
    have hpcs' : z ∈ ⋃ p ∈ {p | p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1},
        closure (p.1.tipSet p.2.1 p.2.2) := hfin ▸ hpcs
    simp only [mem_iUnion, mem_ofPred_eq] at hpcs'
    obtain ⟨p, hp', hz⟩ := hpcs'
    exact Or.inl (Or.inr (mem_biUnion hp' (hp p hp' ⟨hz, hzH⟩)))
  · have hsub : closure (⋃ a ∈ (ExplState.run κ b jumps spec D spec.2.2.length).2.1,
        ((↑) : ℝ → ℂ) '' a) ⊆ {z : ℂ | z.im = 0} := by
      refine closure_minimal ?_ hreal
      simp only [iUnion_subset_iff]
      rintro a - - ⟨x, -, rfl⟩
      simp
    have := hsub harc
    simp only [mem_ofPred_eq] at this
    linarith

/-- **GW1's properness for the ordinary pieces** (p. 618; the remaining content of `GW1ProperStatement`): almost
surely the physical set of every ordinary piece of both walks is relatively closed in `ℍ`. -/
def GW1PieceProperStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω ∂P,
        (∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length).1,
          closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2) ∧
        ∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
            (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length).1,
          closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2

/-- GW1's properness for the walks from properness of their ordinary pieces. -/
theorem gw1ProperStatement_of_pieces (hp : GW1PieceProperStatement.{u}) : GW1ProperStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  filter_upwards [hp κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω hω
  exact ⟨closure_physSet_inter_H_subset hω.1, closure_physSet_inter_H_subset hω.2⟩

/-! ### Countability of the GW2 family -/

/-- The finite schedules with angles in a countable `Θ` and times in a countable `Q` form a countable set. -/
theorem countable_setOf_isSchedule {Θ : Set ℝ} {Q : Set ℝ≥0} (hΘ : Θ.Countable) (hQ : Q.Countable) :
    {l : List (ℝ × ℝ≥0) | IsSchedule Θ Q l}.Countable := by
  have := (hΘ.prod hQ).to_subtype
  refine (countable_range (List.map (Subtype.val : (Θ ×ˢ Q : Set (ℝ × ℝ≥0)) → ℝ × ℝ≥0))).mono fun l hl => ?_
  refine ⟨l.attach.map fun p => ⟨p.1, hl.1 p.1 p.2⟩, ?_⟩
  rw [List.map_map]
  exact List.attach_map_subtype_val l

/-- The roots of GW2 are rational, hence countably many. -/
theorem countable_lowerArcRoots (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : (lowerArcRoots κ b jumps).Countable := by
  unfold lowerArcRoots
  split_ifs
  · refine (countable_range ((↑) : ℚ → ℝ)).mono fun v hv => ?_
    obtain ⟨⟨q, hq⟩, -⟩ := hv
    exact ⟨q, hq.symm⟩
  · exact countable_empty

/-- A root of GW2 is a root on the initial forced lower arc, in the sense of SB5. -/
theorem lowArc_of_mem_lowerArcRoots {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {v : ℝ} (hv : v ∈ lowerArcRoots κ b jumps) :
    0 < v ∧ PiecewiseConstantBoundaryData.rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ ∧
      ∀ x ∈ PiecewiseConstantBoundaryData.jumpSet b jumps, 0 < x → x ≤ v →
        PiecewiseConstantBoundaryData.rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
  unfold lowerArcRoots at hv
  split_ifs at hv with h0
  · exact ⟨hv.2.1, h0, hv.2.2⟩
  · exact absurd hv (notMem_empty v)

/-! ### SB from SB4 and SB5 -/

/-- **SB from SB4 and SB5** (supplement p. 637 with SB4–SB5): the root-`0` schedules of the GW2 family satisfy
(SB4.1) (`sb41_of_mem_Ioo`), so SB4 and its reflection place them on the closed left of `R` and the closed right of
`L`; a forced arc `[0, v]` is real, so on neither open side; a schedule from a root `v` is covered by SB5. There are
countably many schedules and roots, so one probability-one event serves them all. -/
theorem sbStatement_of_sb4_sb5 (h4 : SB4Statement.{u}) (h5 : SB5Statement.{u}) : SBStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE Θ hΘ hΘc Q hQc
  have hS := countable_setOf_isSchedule hΘc hQc
  have hV := countable_lowerArcRoots κ b jumps
  have hA := (ae_ball_iff hS).2 fun l (hl : l ∈ {l | IsSchedule Θ Q l}) => by
    have hang : ∀ p ∈ l, p.1 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := fun p hp => hΘ (hl.1 p hp).1
    obtain ⟨hR, hL⟩ := h4 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE l hl.2
      fun p hp q hq => sb41_of_mem_Ioo hκ hκ4 (hang p hp) (hang q hq)
    exact (hR fun p hp => ⟨(hang p hp).1, (hang p hp).2.le⟩).and
      (hL fun p hp => ⟨(hang p hp).1.le, (hang p hp).2⟩)
  have hB := (ae_ball_iff hV).2 fun v (hv : v ∈ lowerArcRoots κ b jumps) =>
    (ae_ball_iff hS).2 fun l (hl : l ∈ {l | IsSchedule Θ Q l}) => by
      obtain ⟨hv0, h0, hjv⟩ := lowArc_of_mem_lowerArcRoots hv
      exact h5 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE v hv0 h0 hjv l hl.2 fun p hp => hΘ (hl.1 p hp).1
  filter_upwards [hA, hB] with ω hA hB
  constructor
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hzF, hzR⟩ := hz
    simp only [boundaryLightConeFamily, mem_union, mem_iUnion, mem_image] at hzF
    rcases hzF with ⟨l, hl, hzl⟩ | ⟨v, hv, ⟨x, -, rfl⟩ | ⟨l, hl, hzl⟩⟩
    · exact (eq_empty_iff_forall_notMem.1 (hA l hl).1) z ⟨hzl, hzR⟩
    · exact ofReal_notMem_H x hzR.1.1
    · exact (eq_empty_iff_forall_notMem.1 (hB v hv l hl).1) z ⟨hzl, hzR⟩
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hzF, hzL⟩ := hz
    simp only [boundaryLightConeFamily, mem_union, mem_iUnion, mem_image] at hzF
    rcases hzF with ⟨l, hl, hzl⟩ | ⟨v, hv, ⟨x, -, rfl⟩ | ⟨l, hl, hzl⟩⟩
    · exact (eq_empty_iff_forall_notMem.1 (hA l hl).2) z ⟨hzl, hzL⟩
    · exact ofReal_notMem_H x hzL.1.1
    · exact (eq_empty_iff_forall_notMem.1 (hB v hv l hl).2) z ⟨hzl, hzL⟩

/-! ### The frontier input of Theorem 1.4 -/

/-- **The frontier input from GW2, SB and GW1's properness** (p. 421: "SB1–SB5 prove the joined barriers …
Unrestricted exhaustion then identifies the actual frontiers"). Take the countable dense angle set
`Θ = (−π/2, π/2) ∩ ℚ`. GW2 gives a countable `Q` with completed counterflow range `= closure (family ∪ {0})`; SB puts
the family off the open right side of `R`; that side is open because `R` is relatively closed in `ℍ` (GW1), so it
misses the closure as well; and `0 ∉ ℍ`. The same for `L`. -/
theorem sbFrontierStatement_of_inputs (hGW2 : GW2LightConeStatement.{u}) (hSB : SBStatement.{u})
    (hprop : GW1ProperStatement.{u}) : SBFrontierStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  have hΘ : Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ) ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    inter_subset_left
  have hΘc : (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)).Countable :=
    (countable_range _).mono inter_subset_right
  have hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo
  obtain ⟨Q, hQc, -, -, hQ⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hΘ hΘc hΘd
  filter_upwards [hQ E hE, hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _ hΘ hΘc Q hQc,
    hprop κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω hω hsb hpr
  rw [← hω]
  refine ⟨closure_inter_eq_empty (isOpen_rightSideOf hpr.1) ?_, closure_inter_eq_empty (isOpen_leftSideOf hpr.2) ?_⟩
  · rw [union_inter_distrib_right, hsb.1, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzR⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact ofReal_notMem_H 0 (by simpa using hzR.1.1)
  · rw [union_inter_distrib_right, hsb.2, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzL⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact ofReal_notMem_H 0 (by simpa using hzL.1.1)

/-- **The frontier input of Theorem 1.4 from SB4, SB5, GW1's properness and GW2** (the source's route: SB1–SB5 give
the barriers, GW2 the exhaustion). -/
theorem sbFrontierStatement_of_sb (hGW2 : GW2LightConeStatement.{u}) (h4 : SB4Statement.{u})
    (h5 : SB5Statement.{u}) (hprop : GW1ProperStatement.{u}) : SBFrontierStatement.{u} :=
  sbFrontierStatement_of_inputs hGW2 (sbStatement_of_sb4_sb5 h4 h5) hprop

end SB

end Theorem14

end InteractingSLE
