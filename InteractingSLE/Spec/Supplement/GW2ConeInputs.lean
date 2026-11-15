/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14Inputs
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# Lemma GW2 (light-cone exhaustion): its steps, stated exactly from the supplement

Packet PROVE-T14-CONE. **Lemma GW2** (supplement §25, `source/spec/p577-624.md` L989–L1038, pp. 621–623):

> Let the complete ambient counterflow have every original side cumulative sum greater than `−2`. Fix a countable
> dense set `Θ ⊂ (−π/2, π/2)`. There is a deterministic countable dense schedule set `Q` and an explicit countable
> family of finite admissible angle histories, allowed to start with a forced original-boundary arc, whose closed
> union is the entire completed counterflow range. […] One sufficient family is the following. Include all available
> finite `Θ` schedules from `x` with switch and terminal times in `Q`. If the lower extreme is immediately
> inadmissible, also take every fixed original rational point `v` in its first low right boundary arc, retain the arc
> `[x, v]`, and take all available finite `Θ` schedules of that conditional field from `v`, with times in `Q`. An
> attempted schedule is retained only through its actual available portion; no prescribed switch is performed after
> an earlier threshold. Add the initial and terminal points, and close the union.

The named input `Theorem14.GW2LightConeStatement` (`Spec/Theorem14Inputs.lean`) is this lemma for the frozen family
`boundaryLightConeFamily`, with Lemma GW0 supplying the hypothesis (infinite counterflow lifetime). Its proof in the
supplement has four parts; the three probabilistic ones are stated here as named statements, each in exactly the
setting of `GW2LightConeStatement` (`0 < κ < 4`, a GFF `h` on `ℍ` with piecewise-constant data `b`, the centred
counterflow `W'` with almost surely infinite lifetime, a staged-history family `E` for every boundary-continued
program). `GW2Cone.lean` proves `GW2LightConeStatement` from them and Theorem 1.3.

* `GW2ScheduleContainmentStatement` (`⊆`, the schedules from `0`): "Ordinary-root schedules use GB6 directly"
  (p. 621, ¶2 of the proof); GW2a (p. 623) in the GW2 convention.
* `GW2ForcedArcStatement` (`⊆`, the arcs `[0, v]`): "For a boundary root `v`, BR6 forces the whole initial arc
  `[x, v]`" (p. 621). Proved from BR6 in `GW2ConeArc.lean`.
* `GW2ArcScheduleContainmentStatement` (`⊆`, the schedules from `v`): "BR4a gives the full conditional pair targeted
  at `v` … GB7 … GB6 places each available prefix in this conditional counterflow range" (p. 621).
* `GW2TipExhaustionStatement` (`⊇`): GB9a's schedule `Q` (p. 621, ¶1: "one deterministic dense countable `Q` for
  which all switching and terminal tips of successful schedules are interior") and the exhaustion at an interior tip
  ("An initial positive interior prefix always exists", "The central-band experiment under only `S > −2`",
  pp. 621–623: "proves that `p` belongs to its closure").

The remaining part — "Finally use the countable bounded interior-tip stopping times … Boundary time has zero
occupation, so these tip times are dense … Continuity and the continuous terminal limit put the entire completed
counterflow range in the closed family. Together with containment, this proves the asserted equality" (p. 623) — and
"Intersect these countably many events before taking the closure. Properness makes the completed ambient range closed"
(p. 621) are proved in `GW2Cone.lean`.

**Reading of the statements.**
* *GW2 convention.* The family's histories have `gw2 = true` (frozen `ExplSpec`): "retained only through its actual
  available portion; no prescribed switch is performed after an earlier threshold". The frozen
  `GW2aContainmentStatement` covers the histories with `gw2 = false` only. A staged history of a `gw2 = true` spec is a
  different random object from one of the corresponding `gw2 = false` spec (`E` is indexed by the spec), so the
  containment of the GW2 histories is a separate statement; its proof in the supplement is GW2a's induction ("GB6
  places each available prefix …"), truncated at the first threshold.
* *Schedules.* A schedule is a finite list of (angle, time) pairs with strictly increasing times
  (`IsSchedule`, `scheduleProgram`). The containment statements are stated for every angle in `[−π/2, π/2]` (GW2a's
  range) and every strictly increasing list of times, which includes every `IsSchedule Θ Q` for every `Q`.
* *Interior tip.* The counterflow is `R(γ)` for the trace `γ` of `W'` in the chart `R(z) = −1/z`
  (frozen `IsCenteredCounterflowDriver`); its current tip at time `s` is interior iff `γ(s) ∈ ℍ`, and then it is
  `−γ(s)⁻¹`. The exhaustion statement is stated at every fixed time `s` (a bounded stopping time), on the event of an
  interior tip, for every process `γ` that almost surely generates `W'` (generating traces are unique: they are the
  radial limits of the inverse Loewner maps).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Cone

/-- **Named statement: GW2's containment for the schedules from the original target** (p. 621, proof ¶2:
"Ordinary-root schedules use GB6 directly. Intersect these countably many events before taking the closure";
Lemma GW2a, p. 623, for the GW2 convention): every finite angle schedule from the root `0`, with angles in
`[−π/2, π/2]` and strictly increasing times, run in the GW2 convention (`gw2 = true`: retained through its actual
available portion), is almost surely contained in the completed counterflow range. -/
def GW2ScheduleContainmentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ l : List (ℝ × ℝ≥0), (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) →
        l.Pairwise (fun p q => p.2 < q.2) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
            (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω)

/-- **Named statement: GW2's forced initial arcs** (p. 621, proof ¶2: "For a boundary root `v`, BR6 forces the whole
initial arc `[x, v]`"; p. 622: "The initial arcs `[x, v]` are forced by BR6"): for every root `v` of the first low
right boundary arc (`lowerArcRoots`), the original-boundary arc `[0, v]` is almost surely contained in the completed
counterflow range. -/
def GW2ForcedArcStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v ∈ lowerArcRoots κ b jumps,
      ∀ᵐ ω ∂P, ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ counterflowCompletedRange (fun t => W' t ω)

/-- **Named statement: GW2's containment for the schedules from a boundary root** (p. 621, proof ¶2: "BR4a gives the
full conditional pair targeted at `v`. That arc has no random field projection. GB7 gives a simple finite angle
history in the current domain, and GB6 places each available prefix in this conditional counterflow range in reverse
first-visit order. The same conclusion holds at a finite endpoint by continuity"): for every root `v` of the first
low right boundary arc (`lowerArcRoots`), every finite angle schedule from `v`, with angles in `[−π/2, π/2]` and
strictly increasing times, run in the GW2 convention, is almost surely contained in the completed counterflow range. -/
def GW2ArcScheduleContainmentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ v ∈ lowerArcRoots κ b jumps, ∀ l : List (ℝ × ℝ≥0),
        (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) → l.Pairwise (fun p q => p.2 < q.2) →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩
            (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω)

/-- **Named statement: GW2's exhaustion at an interior counterflow tip** (pp. 621–623). There is a deterministic
countable dense schedule set `Q ⊂ (0, ∞)` (GB9a's ordered-time-vector Tonelli argument, p. 621, proof ¶1: "one
deterministic dense countable `Q` for which all switching and terminal tips of successful schedules are interior")
such that for every staged-history family `E`, every process `γ` that almost surely generates the counterflow driver
`W'` (the counterflow is `R(γ)`, `R(z) = −1/z`), and every time `s` (a bounded counterflow stopping time), almost
surely on the event that the current counterflow tip `p = −γ(s)⁻¹` is interior (`γ(s) ∈ ℍ`), `p` lies in the closure of
the GW2 family ("An initial positive interior prefix always exists"; "The central-band experiment under only
`S > −2`" with CS3, GB8, GB9 and DS1–DS3; p. 623: "The inverse joint chart therefore brings the selected countable
family arbitrarily close to `p`. Letting the sum of the error probabilities decrease to zero proves that `p` belongs to
its closure"). -/
def GW2TipExhaustionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
          ∀ s : ℝ≥0, ∀ᵐ ω ∂P, γ ω s ∈ H →
            -(γ ω s)⁻¹ ∈ closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω))

end GW2Cone

end Theorem14

end InteractingSLE
