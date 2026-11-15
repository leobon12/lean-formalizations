/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Low

/-!
# Lemma 7.16: fixed boundary points are not hit (from Lemma G12)

Packet PROVE-RLC-G. Specification §7.3, Lemma 7.16 (`source/spec/p289-336.md` L641–L650, pp. 331–332): "Suppose that
`η ∼ SLE_κ(ρ^L; ρ^R)` in `ℍ` from `0` to `∞` with `ρ^L > −2` and `ρ^R ∈ (−2, κ/2 − 2)` where the force points are
located at `0⁻` and `0⁺`, respectively. […] In particular, for any `x ∈ ∂ℍ \ {0}`, the probability that `η` hits `x`
is zero." This is the fixed-point avoidance used in Lemma G8's proof (supplement p. 500: "Lemma 7.16 excludes `q = x`";
"fixed-point avoidance in Lemma 7.16 excludes the specified point").

**Proof here.** Not the source's iterated-flow-line argument: a fixed real point `x > 0` is a passive (zero-weight)
mark, and the cumulative right weight up to it is the seed weight `ρ^R > −2 > κ/2 − 4`; Lemma G12 (proved:
`Supp7.G12Low.ae_trace_ne_right_of_exists`, PROVE-G12B/C) says such a point is almost surely never visited, on the
whole closed lifetime. The left side is the left form of G12. So the hypothesis `ρ^R < κ/2 − 2` is not needed, and both
weights may be anywhere above `κ/2 − 4` (`Lemma716.ae_trace_ne_twoForce`).

The first assertion of the lemma (the boundary set `η ∩ ℝ` has Lebesgue measure zero) is **not** formalized here: it
needs joint measurability of the trace in `(ω, t)`, which the evolution predicate does not supply; Lemma G8 uses only
the point assertion.

Main results:

* `Lemma716.ae_trace_ne_twoForce`: the two-force evolution (`nL = nR = 1`, marks at `0⁻`, `0⁺`) does not hit a fixed
  `x ≠ 0` when both weights exceed `κ/2 − 4`;
* **`Lemma716.ae_trace_ne`**: Lemma 7.16's point assertion with the source's hypotheses;
* `Lemma716.ae_flowLine_ne_right`, `Lemma716.ae_flowLine_ne_left`: the flow-line form (a real point beyond the seed
  whose outward cumulative weight exceeds `−2` is almost surely not visited), as G8 applies it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Lemma716

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **A two-force evolution does not hit a fixed boundary point** (Lemma G12 with a passive mark). For the integrated
`SLE_κ(ρ^L; ρ^R)` evolution with force points at `0⁻`, `0⁺` (`0 < κ < 4`) and both weights `> κ/2 − 4`, and a
continuous generating trace, a fixed `x ≠ 0` is almost surely never visited on `[0, ζ]`. -/
theorem ae_trace_ne_twoForce [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) {ρL ρR : Fin 1 → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω))
    (hL : κ / 2 - 4 < ρL 0) (hR : κ / 2 - 4 < ρR 0) {x : ℝ} (hx : x ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ x := by
  have hord : IsOrderedForceWord (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · refine Supp7.G12Low.ae_trace_ne_left_of_exists hκ hκ4 hord hE hη hneg ⟨0, hneg⟩ ?_
    have e : Finset.univ.filter (fun i : Fin 1 => x ≤ (fun _ : Fin 1 => (0 : ℝ)) i) = Finset.univ :=
      Finset.filter_true_of_mem fun (i : Fin 1) _ => (hneg.le : x ≤ (fun _ : Fin 1 => (0 : ℝ)) i)
    rw [e, Fin.sum_univ_one]
    exact hL
  · refine Supp7.G12Low.ae_trace_ne_right_of_exists hκ hκ4 hord hE hη hpos ⟨0, hpos⟩ ?_
    have e : Finset.univ.filter (fun i : Fin 1 => (fun _ : Fin 1 => (0 : ℝ)) i ≤ x) = Finset.univ :=
      Finset.filter_true_of_mem fun (i : Fin 1) _ => (hpos.le : (fun _ : Fin 1 => (0 : ℝ)) i ≤ x)
    rw [e, Fin.sum_univ_one]
    exact hR

/-- **Lemma 7.16** (point assertion, p. 331): for `η ∼ SLE_κ(ρ^L; ρ^R)` from `0` to `∞` with force points at `0⁻`,
`0⁺`, `ρ^L > −2` and `ρ^R ∈ (−2, κ/2 − 2)` (`0 < κ < 4`), for any `x ∈ ∂ℍ \ {0}` the probability that `η` hits `x`
is zero. -/
theorem ae_trace_ne [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) {ρL ρR : Fin 1 → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω))
    (hL : -2 < ρL 0) (hR : -2 < ρR 0) (_hR' : ρR 0 < κ / 2 - 2) {x : ℝ} (hx : x ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ x :=
  ae_trace_ne_twoForce hκ hκ4 hE hη (by linarith) (by linarith) hx

/-- **Lemma 7.16 for a flow line, right of the seed**: a real point `y > x` whose outward right cumulative weight
`(b(y⁺) + θχ)/λ − 1` exceeds `−2` is almost surely never visited (Lemma G12, `Supp7.g12FlowStatement`). -/
theorem ae_flowLine_ne_right {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ y : ℝ} (hxy : x < y)
    (hS : -2 < Sec4.cumWeightRight κ (PiecewiseConstantBoundaryData.rightLim b y + θ * QuantumZipper.chiC κ))
    {S : Type u} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (h : S → LQGMetric.DistOn upperHalfPlaneOpens) (hh : IsGFFWithBoundaryData P h b jumps)
    (η : S → ℝ≥0 → ℂ) (ζ : S → ℝ≥0∞) (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y :=
  (Supp7.g12FlowStatement.{u} κ hκ hκ4 b jumps hb x θ y P h hh η ζ hη).1 hxy (by linarith)

/-- **Lemma 7.16 for a flow line, left of the seed**: a real point `y < x` whose outward left cumulative weight
`−(b(y⁻) + θχ)/λ − 1` exceeds `−2` is almost surely never visited. -/
theorem ae_flowLine_ne_left {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ y : ℝ} (hyx : y < x)
    (hS : -2 < Sec4.cumWeightLeft κ (PiecewiseConstantBoundaryData.leftLim b y + θ * QuantumZipper.chiC κ))
    {S : Type u} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (h : S → LQGMetric.DistOn upperHalfPlaneOpens) (hh : IsGFFWithBoundaryData P h b jumps)
    (η : S → ℝ≥0 → ℂ) (ζ : S → ℝ≥0∞) (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y :=
  (Supp7.g12FlowStatement.{u} κ hκ hκ4 b jumps hb x θ y P h hh η ζ hη).2 hyx (by linarith)

end Lemma716

end InteractingSLE
