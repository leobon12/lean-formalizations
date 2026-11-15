/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4a

/-!
# Proposition BW1: the full terminal-prefix first-contact law (statement)

Packet PROVE-T14-BR4. Supplement §25, **Proposition BW1** (`source/spec/p577-624.md` L830–L865, pp. 613–615):

> Let the original counterflow `η` from `y` to `x` in a Jordan domain have a finite force word whose every side partial
> sum is greater than `−2`, with its complete continuous trace and full marked field coupling. In the flow coordinate
> `(D, x, y) = (ℍ, 0, ∞)`, let `α` be a simple ordinary flow of constant angle `θ ∈ [−π/2, π/2]`. Retain its full
> marked history `A = α[0, σ]` at a finite available own stopping time with finite continuous endpoint
> `q ∈ ℝ \ {0}`. Assume `q` is the current extreme real record on the side of this contact. In particular this includes
> a finite original continuation threshold, with its already proved terminal raw-range kernel. […] Let `U` be the
> unbounded own component of `ℍ \ A`, with its selected active prime end over `q`, and put `T = inf{t : η(t) ∈ A}`.
> Conditional on the marked terminal history `A`, the actual prefix `η[0, T]` is the complete counterflow of the
> conditional component field in `U`, from `y` to that prime end over `q`. Its relative capacity lifetime is infinite;
> `T` is finite in the original counterflow clock and `η(T) = q`. The assertion includes the full component field–path
> coupling, all finite relative optional kernels, and the marked limiting kernel.

**Reading** (on PROVE-T14-SB2's carriers, `SB2Remainder`).
* The original counterflow is the frozen centred counterflow `W'` of `h` (`0 < κ < 4`, Jordan domain `ℍ`, `x = 0`,
  `y = ∞`); "every side partial sum is greater than `−2`" is its infinite lifetime (Lemma GW0).
* `α` with its full marked history at a finite own stop with real endpoint at the extreme record "on the side of this
  contact", in the case named by the source ("a finite original continuation threshold") and used by GW1–GW2a ("At a
  finite threshold `q_j`, apply BW1"): the first piece of a frozen staged history launched at `0` (angle
  `θ ∈ [−π/2, π/2]`, own stop `min t ζ`), on the event that it ends at a continuation threshold on side `r` (status
  *thr* `some r`, `EndsAtThresholdSide`); its endpoint `q` is the state's current point (the new record), and `A` is its
  physical set (root and piece, `SB.prefixPhysSet … 1`). "Conditional on the marked terminal history" is conditioning
  on `pastSigma … 1`. Being universally quantified over probability spaces, the statement applies equally to the
  conditional fields of later stages.
* "the complete counterflow of the conditional component field in `U`, from `y` to that prime end over `q`" with "the
  full component field–path coupling, all finite relative optional kernels, and the marked limiting kernel": the
  frozen centred counterflow coupling of the conditional field read in the state's chart `g_A − W` (the chart after the
  piece, `U → ℍ`, `∞ ↦ ∞`, prime end over `q ↦ 0`: "The terminal geometric correspondence gives `W = b = g_A(q)`"),
  `SB.IsCondCounterflowDriverOn`.
* "relative capacity lifetime is infinite", "`T` is finite […] and `η(T) = q`", and the relative clock ("Relative
  capacity is adapted, continuous and strictly increasing"): `ζ_r = ∞`, `T < ∞` with physical tip `q` at `T`, and a
  continuous strictly increasing clock `ℓ` onto `[0, T)` under which the relative physical tips (through the chart and
  the inversion) are the original ones.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace BW1

/-- The state has stopped at a finite continuation threshold on the side `r` (`true`: right, `false`: left): status
*thr* `some r`. -/
def EndsAtThresholdSide (s : ExplState) (r : Bool) : Prop :=
  s.2.2.2.2.2.1 = (Sum.inr (Sum.inr (Sum.inl (some r))) : ExplStatus)

/-- The chart of a state (after its last piece: `g_A − W` in the original coordinate). -/
def stateChart (s : ExplState) : Chart := s.2.2.2.2.1

/-- The current point of a state (at a threshold: the new extreme real record `q`). -/
def statePoint (s : ExplState) : ℝ := s.2.2.2.2.2.2.1

/-- **Named statement: Proposition BW1** (supplement pp. 613–615), for the first piece of a staged history at a finite
continuation threshold. For `0 < κ < 4`, a GFF `h` with piecewise-constant data, its centred counterflow `W'` with
infinite lifetime, and a staged history whose first instruction is a flow at angle `θ ∈ [−π/2, π/2]` from `0`, for
each side `r` there are a driver `W_r` with lifetime `ζ_r` and a clock `ℓ` such that
* conditionally on the retained history (`pastSigma … 1`), on the event that the first piece ends at a threshold on
  side `r`, `W_r` drives the centred counterflow of the conditional field read in the state's chart `g_A − W`;
* each `ℓ(u)` is measurable, and almost surely on that event: `ζ_r = ∞`, the first time `T` at which the original
  physical counterflow tip lies in `A` (root and piece) is finite with tip `q` (the state's point), and `ℓ` is a
  continuous strictly increasing clock onto `[0, T)` under which the relative physical tips are the original ones. -/
def BW1Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ (θ : ℝ), θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) →
    ∀ (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      IsStagedHistory κ b jumps P h ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ E →
    ∀ r : Bool,
      ∃ (Wr : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
        SB.IsCondCounterflowDriverOn (mΩ := mΩ) κ (pastSigma κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ E 1) P
          {ω | EndsAtThresholdSide
            (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1) r} h
          (fun ω => stateChart (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1))
          Wr ζr ∧
        (∀ s, Measurable fun ω => ℓ ω s) ∧
        ∀ᵐ ω ∂P, EndsAtThresholdSide
            (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1) r →
          ζr ω = ⊤ ∧
          firstTipTime infinitySourceChart (fun s => W' s ω)
              (SB.prefixPhysSet κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1) < ⊤ ∧
          infinitySourceChart.tipAt (fun s => W' s ω)
            (firstTipTime infinitySourceChart (fun s => W' s ω)
              (SB.prefixPhysSet κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1)).toNNReal
            (statePoint (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1)) ∧
          Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
          range (ℓ ω) = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω)
            (SB.prefixPhysSet κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1)} ∧
          ∀ (s : ℝ≥0) (z : ℂ),
            ((stateChart (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1)).trans
              infinitySourceChart).tipAt (fun s => Wr s ω) s z ↔
            infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω s) z

end BW1

end Theorem14

end InteractingSLE
