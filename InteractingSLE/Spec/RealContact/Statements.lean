/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Inputs
import InteractingSLE.Frozen.Spec.IsFirstContact

/-!
# Theorem 1.5's critical-angle clauses at every contact: target statements (ruling R124)

Orchestrator-owned interface file (ruling R124; workers import it and never edit it).

Paper, Theorem 1.5 (p. 30):
* (i) "If, in addition, `θ₂ − θ₁ < πκ/(4 − κ)`, then `η₁` and `η₂` can bounce off of each other; otherwise the paths
  almost surely do not intersect (except possibly at their starting point)";
* (iii) "If, in addition, `θ₁ − θ₂ < πκ/(4 − κ)`, then `η₁` and `η₂` can bounce off of each other; otherwise the paths
  almost surely do not subsequently intersect".

The specification (p. 5) restricts both clauses to interior available contacts, and the released supplementary
theorems `AuditFix.criticalOrderedNoInteriorPoint_holds` and `AuditFix.criticalCrossingNoLaterInteriorPoint_holds`
prove that scope. The statements below cover every contact of the closed available paths: real points, seeds and
terminal values included.

**The exception for common terminal points.** Neither clause can exclude a point that is terminal for both paths.
Take `x₂ < x₁ < z`, `θ₂ − θ₁ ∈ [πκ/(4 − κ), 4π/(4 − κ))` and data `b = −λ − θ₂χ` on `(−∞, x₂)`, `λ − θ₂χ` on `(x₂, z)`,
`λ(κ/2 − 3) − θ₂χ` on `(z, ∞)`. Then both flow lines end at `z` almost surely (errata A9; worked out in
`planning/RULINGS.md` R124). So the conclusions allow that case, and nothing else beyond the common starting point
(clause (i)) or the first contact (clause (iii)).

## Statements

* `CriticalOrderedContactStatement` — clause (i) at every contact;
* `CriticalCrossingContactStatement` — clause (iii) at every contact;
* `G7GB7aFirstHitRealStatement` — the probabilistic core (packet PROVE-RC-HIT): the first-hit exclusion of
  `Theorem15D5.G7GB7aFirstHitStatement` without its restriction to hits in `ℍ`, and with the hit allowed at the second
  path's terminal time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RealContact

open Theorem15D5

/-- **Theorem 1.5 (i), critical angles, at every contact** (paper p. 30: "otherwise the paths almost surely do not
intersect (except possibly at their starting point)"). For `x₂ ≤ x₁`, `θ₁ < θ₂` and `θ₂ − θ₁ ≥ πκ/(4 − κ)`: almost
surely, every common point `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`; real points and terminal
values included) is either the common starting point (`x₁ = x₂` and `s = t = 0`) or terminal for both paths
(`s = ζ₁` and `t = ζ₂`). The second exception cannot be dropped (errata A9). -/
def CriticalOrderedContactStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ ≤ x₁) (_hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (_hcrit : Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      (x₁ = x₂ ∧ s = 0 ∧ t = 0) ∨ ((s : ℝ≥0∞) = ζ₁ ω ∧ (t : ℝ≥0∞) = ζ₂ ω)

/-- **Theorem 1.5 (iii), critical angles, at every contact** (paper p. 30: "otherwise the paths almost surely do not
subsequently intersect"). For `x₂ < x₁`, `θ₂ < θ₁ < θ₂ + π` and `θ₁ − θ₂ ≥ πκ/(4 − κ)`: almost surely, every common
point `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`; real points and terminal values included) is
either the first contact or terminal for both paths (`s = ζ₁` and `t = ζ₂`). -/
def CriticalCrossingContactStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ < x₁) (_hθ : θ₂ < θ₁) (_hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (_hcrit : Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t ∨ ((s : ℝ≥0∞) = ζ₁ ω ∧ (t : ℝ≥0∞) = ζ₂ ω)

/-- **The first-hit exclusion at every point and up to the terminal time** (packet PROVE-RC-HIT). This is
`Theorem15D5.G7GB7aFirstHitStatement` with two changes:
* the hit point `η₁(x)` may be real (the hypothesis `η₁ ω x ∈ QuantumZipper.H` is dropped);
* the hit time `t` may be the second path's terminal time (`t ≤ ζ₂` instead of `t < ζ₂`).

Setting as there: `η₁` is the lower-angle flow from `x₁`, `η₂` the higher-angle flow from `x₂ ≤ x₁`, and the exposed
first left side has outward cumulative weight at least `κ/2 − 2` for the angle-`θ₂` path ((7.12D.1)). Almost surely,
given W5's ordered proper completions and the increasing strict contacts: at own cutoffs `u < ζ₁`, `r < ζ₂` with
`η₂(r)` off `A = η₁([0, u])`, the second path's future has no first new contact with `A` at a point `η₁(x)`, `x < u`, at
any time `t ∈ (r, ζ₂]`. Mathematically (specification pp. 543–544, extended to the boundary): at a real hit the chart
point of the hit is either inside an open interval of the exposed side (excluded by GB7a for the conditional flow) or
a mark of the conditional word whose outward cumulative weight exceeds `κ/2 − 4` (excluded by G12 for the conditional
flow, `Supp9.G12FlowStatement`); both exclusions include the conditional flow's terminal stop. -/
def G7GB7aFirstHitRealStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        StrictContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) →
        ∀ u r : ℝ≥0, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → η₂ ω r ∉ η₁ ω '' Icc 0 u →
          ∀ t x : ℝ≥0, r < t → (t : ℝ≥0∞) ≤ ζ₂ ω → x < u → η₂ ω t = η₁ ω x →
            (∀ t' : ℝ≥0, r < t' → t' < t → η₂ ω t' ∉ η₁ ω '' Icc 0 u) →
            False

/-- The real-point first-hit exclusion implies the landed interior one. -/
theorem g7GB7aFirstHitStatement_of_real (hR : G7GB7aFirstHitRealStatement.{u}) :
    G7GB7aFirstHitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hW Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hW P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂] with ω hω
  intro hord hinc u r hu hr hrA t x hrt ht hxu hhit _ hfirst
  exact hω hord hinc u r hu hr hrA t x hrt ht.le hxu hhit hfirst

end RealContact

end InteractingSLE
