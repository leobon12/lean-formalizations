/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# Corollary BR4a: the full own-history field coupling of the retargeted counterflow (statement)

Packet PROVE-T14-BR4. Supplement §24, **Corollary BR4a** (`source/spec/p577-624.md` L755–L776, p. 610), in the
counterflow setting in which Theorem 1.4's proof applies it (Lemma GW2, p. 621: "For a boundary root `v`, BR6 forces the
whole initial arc `[x, v]` and BR4a gives the full conditional pair targeted at `v`. That arc has no random field
projection"; p. 622: "BR4a supplies the complete pair through `T_v` in the original field frame, including the old
target `x` as a genuine mark"; Corollary BW2, p. 616; Lemma GW2a, p. 623).

> The preceding target change transports the full marked field–history coupling, not only the driving marginal. […]
> This calculation retains the original literal or centered field frame; no new additive constant is chosen. […]
> The original and transformed stopped histories recover each other, every force label, and both half-plane-capacity
> clocks. The clock is continuous, adapted and strictly increasing […] makes the relative lifetime infinite as in
> BR4 […] Thus every finite relative-horizon full field–history law is the canonical one for the word in BR4.
> Countable projective consistency, or Aux. 9 after spherical compactification, identifies the entire canonical pair.
> Its finite optional kernels and complete-history marked martingale limit are the transported kernels.

**Reading.** The counterflow is the frozen centred counterflow `W'` of the field `h` (`IsCenteredCounterflowDriver`, from
`∞` to the original target `0`, read in the inversion `R(z) = −1/z`), with infinite lifetime (Lemma GW0: its word is
admissible). BR4/BR4a's hypothesis is the almost-sure finite hit of the new target `v ≠ 0` (a physical real point).
Changing the target from `0` to `v` in the counterflow chart is the Möbius map `ψ` of BR4a; in physical coordinates it
is reading the same field `h` in the frame recentred at `v` (`Chart.id.recenter v`, derivative `1`, lift `0`: "no new
additive constant is chosen"), followed by the same inversion. Thus the conclusion "the transformed prefix with the
transformed field is the canonical complete pair of the retargeted word (old target retained as a genuine mark)" is:
the field `h_v` read at `v` and a driver `W_v` form a frozen centred counterflow coupling (`IsCenteredCounterflowDriver`:
field–history coupling with every optional kernel; its boundary data carry the old target `0 − v` as a mark), with
infinite lifetime, and the retargeted physical curve is the original one through its first visit to `v`: a continuous
strictly increasing clock `ℓ` maps `[0, ∞)` onto `[0, T_v)`, and the tips agree (`tipAt`).

## Main definitions

* `Chart.tipAt c W t z`: the physical tip of the Loewner chain of `W` at time `t`, read through the chart `c`, is `z`
  (the radial limit defining the frozen `Chart.tipSet`);
* `firstTipTime c W S`: the first time the physical tip lies in `S` (`⊤` if never);
* **`BR4aStatement`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

/-- **The physical tip at time `t`** of the Loewner chain driven by `W`, read through the chart `c`, is `z`: the radial
limit `lim_{y↓0} c⁻¹(f_t(iy)) = z` (the defining limit of the frozen `Chart.tipSet`). -/
def Chart.tipAt (c : Chart) (W : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : Prop :=
  Tendsto (fun y : ℝ => c.2.1 (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) t (y * Complex.I))) (𝓝[>] 0)
    (𝓝 z)

theorem Chart.tipSet_eq_tipAt (c : Chart) (W : ℝ≥0 → ℝ) (s : ℝ≥0∞) :
    c.tipSet W s = {z | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ s ∧ c.tipAt W t z} := rfl

/-- The first time the physical tip of the chain of `W`, read through `c`, lies in `S` (`⊤` if it never does). -/
def firstTipTime (c : Chart) (W : ℝ≥0 → ℝ) (S : Set ℂ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ∃ z ∈ S, c.tipAt W t z), (t : ℝ≥0∞)

namespace Theorem14

namespace BR4a

/-- **Named statement: Corollary BR4a** (supplement p. 610), in the counterflow setting of Theorem 1.4. For
`0 < κ < 4`, a GFF `h` with piecewise-constant data, its centred counterflow `W'` with infinite lifetime, and a real
point `v ≠ 0` visited by the counterflow at a finite time almost surely (BR4's hypothesis), there are a field `h_v`
(the field `h` read in the frame recentred at `v`, with the flow rule and no new additive constant), a driver `W_v`
with lifetime `ζ_v` and a clock `ℓ` such that
* `(h_v, W_v, ζ_v)` is a frozen centred counterflow coupling ("the full marked field–history coupling", "every finite
  relative-horizon full field–history law is the canonical one for the word in BR4", "Its finite optional kernels and
  complete-history marked martingale limit are the transported kernels");
* almost surely `ζ_v = ∞` ("the relative lifetime infinite as in BR4");
* almost surely `ℓ` is continuous and strictly increasing with each `ℓ(u)` measurable, its range is `[0, T_v)` for the
  first visit `T_v` of the original counterflow to `v`, and the retargeted physical tip at `u` (through
  `recenter v` and the inversion) is the original physical tip at `ℓ(u)` ("The original and transformed stopped
  histories recover each other, every force label, and both half-plane-capacity clocks. The clock is continuous,
  adapted and strictly increasing"). -/
def BR4aStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v : ℝ, v ≠ 0 → (∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) →
      ∃ (hv : Ω → DistOn upperHalfPlaneOpens) (Wv : ℝ≥0 → Ω → ℝ) (ζv : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
        (∀ ω, IsChartTransport (Chart.id.recenter v) 1 0 (chiC κ) (h ω) (hv ω)) ∧
        IsCenteredCounterflowDriver κ P hv Wv ζv ∧
        (∀ u, Measurable fun ω => ℓ ω u) ∧
        ∀ᵐ ω ∂P, ζv ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
          range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) <
            firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)}} ∧
          ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.recenter v).trans infinitySourceChart).tipAt (fun s => Wv s ω) r z ↔
            infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z

end BR4a

end Theorem14

end InteractingSLE
