/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76Exit
import InteractingSLE.Spec.Sec7.Lemma76Kernel
import InteractingSLE.Spec.Restart.ClockFlow

/-!
# Lemma 7.6 from the restart kernel at good rational stops

Packet PROVE-LEMMA76D. Specification §7.2, proof of Lemma 7.6 (pp. 267–270).

PROVE-LEMMA76C reduced Lemma 7.6 to `Lemma76KernelStatement`: the restart kernel at the stops `r ∧ ζ₁`, `t ∧ ζ₂` for
**every** configuration, including a first path stopped at its lifetime and a real second tip, where the retained
chart machinery does not apply. This file replaces it by the kernel at **good configurations at deterministic stops**
only, which suffices by the stop reduction of `Lemma76Exit.lean`:

* `IsRightSideWord`: the heights of the chart datum on the right side of the first prefix (the chart points `y`
  with `ψ(y) ∈ α([0, a))` beyond the first tip's chart position): `λ − θ₁χ`, or a junction whose right value `c`
  has `c + θ₁χ > −λ`; such points are positive (Aux. 60). With `isAdmissibleRight_side` / `_junction` they are
  admissible (`isAdmissibleRight_of_isRightSideWord`).
* `Lemma76KernelLtStatement` (named intermediate statement): at deterministic stops `(a, b)`, a restart kernel as in
  `Lemma76KernelStatement`, whose pathwise clause is required only at a good configuration (`IsDisjointPair`) with a
  forbidden exit witnessed by the first tip;
* `ae_not_visit_admissible`: under such a kernel, almost surely the chart path visits no admissible right point (GB7a
  and G12 under each conditional law, integrated back; PROVE-LEMMA76C's argument as a lemma);
* **`lemma76RightStatement_of_kernelLt`**, **`lemma76Statement_of_kernelLt`**: Lemma 7.6 from
  `Lemma76KernelLtStatement`, through the rational stop reduction
  (`exists_rat_isDisjointPair_of_not_firstExitBarrier`);
* `lemma76KernelStatement_of_right`, `lemma76KernelStatement_of_kernelLt`: PROVE-LEMMA76C's `Lemma76KernelStatement`
  follows (its pathwise clause concerns only the null event where the barrier fails).

The kernel statement itself is reduced to the conditional-determination input in `Lemma76Kernel2Det.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec7

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open Restart

/-! ### The right side of the first prefix in the chart -/

/-- **The heights of the chart datum on the right side of the first prefix** (proof of Lemma 7.6, p. 269: the
exposed right side has transformed height `b_* = λ + (θ₂ − θ₁)χ`, and the junction `V^α_R` with the original real
boundary has right value `c` with `c + θ₁χ > −λ`; Aux. lemma 60 places these chart points in `(0, ∞)`). For a chart
inverse `ψ` and a datum `c`: every real `y` with `ψ(y) = α(u)`, `u < a`, such that a chart preimage `w` of the first
tip `α(a)` lies strictly between `0` and `y`, is positive, and either is not a jump of `c` with `c(y) = λ − θ₁χ`,
or is a jump with right value `rightLim c y`, `rightLim c y + θ₁χ > −λ`. -/
def IsRightSideWord (κ θ₁ : ℝ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (ψ : ℂ → ℂ) (c : BoundaryWord) : Prop :=
  ∀ y w : ℝ, ψ w = α a → (0 < w ∧ w < y ∨ y < w ∧ w < 0) → ∀ u : ℝ≥0, u < a → ψ y = α u →
    0 < y ∧ ((y ∉ c.jumps ∧ c.fn y = sleLambda κ - θ₁ * chiC κ) ∨
      (y ∈ c.jumps ∧ -sleLambda κ < rightLim c.fn y + θ₁ * chiC κ))

/-- The right-side points of the datum are admissible for the angle-`θ₂` path (`θ₁ < θ₂ + π`). -/
theorem isAdmissibleRight_of_isRightSideWord {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ₁ < θ₂ + Real.pi) {α : ℝ≥0 → ℂ} {a : ℝ≥0} {ψ : ℂ → ℂ} {c : BoundaryWord}
    (hW : IsRightSideWord κ θ₁ α a ψ c) {y w : ℝ} (hw : ψ w = α a) (hwy : 0 < w ∧ w < y ∨ y < w ∧ w < 0)
    {u : ℝ≥0} (hua : u < a) (hy : ψ y = α u) :
    0 < y ∧ IsAdmissibleRight κ θ₂ c.fn c.jumps y := by
  obtain ⟨hy0, h | h⟩ := hW y w hw hwy u hua hy
  · exact ⟨hy0, isAdmissibleRight_side hκ hκ4 hθ.le h.1 h.2⟩
  · exact ⟨hy0, isAdmissibleRight_junction hκ hκ4 hθ h.1 h.2⟩

/-! ### No visit of an admissible point under a restart kernel -/

/-- **Under a restart kernel whose conditional laws are a GFF with the datum and its angle-`θ` flow line from `0`,
almost surely the chart path visits no admissible right point of the datum** (Aux. 64 and 66: GB7a at interval
points and G12 at jump points under each conditional law, integrated through the kernel). -/
theorem ae_not_visit_admissible {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {S : Type} [MeasurableSpace S]
    {H : S → LQGMetric.DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} {M : Set Ω}
    {β : Ω → BoundaryWord} {X : Ω → S} {K : Kernel BoundaryWord S} (hKm : IsMarkovKernel K)
    (hU : Measurable U) (hΓ : ∀ s : ℝ≥0, Measurable fun x => Γ x s)
    (hc : ∀ x, ContinuousOn (Γ x) {s | (s : ℝ≥0∞) ≤ U x}) (hM : MeasurableSet M) (hβ : Measurable β)
    (hX : Measurable X) (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    (hker : ∀ᵐ c ∂(P.restrict M).map β,
      IsGFFWithBoundaryData (K c) H c.fn c.jumps ∧ IsFlowLine κ c.fn c.jumps 0 θ (K c) H Γ U) :
    ∀ᵐ ω ∂P, ω ∈ M → ¬ ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ U (X ω) ∧ ∃ y : ℝ, 0 < y ∧ Γ (X ω) s = y ∧
      IsAdmissibleRight κ θ (β ω).fn (β ω).jumps y := by
  -- interval points: GB7a under each conditional law
  have hI : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ M → ¬ (β ω ∈ Supp7.goodInterval κ θ q.1 q.2 ∧
      X ω ∈ {s | Supp7.VisitsStrip (Γ s) (U s) q.1 q.2}) := fun q =>
    Supp7.ae_not_mem_prod_of_compProd_eq hM hβ hX hlaw (Supp7.measurableSet_goodInterval _ _ _ _)
      (Supp7.measurableSet_visitsStrip hU hΓ hc _ _) (by
        filter_upwards [hker] with c hc' hcA
        exact Supp7.measure_visitsStrip_eq_zero Supp8.gb7aFlowStatement hκ hκ4 hc'.1 hc'.2 hcA)
  -- jump points: G12 under each conditional law
  have hJ : ∀ q : ℕ × ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∉
      {p : BoundaryWord × S | p.1 ∈ goodJunction κ θ q.1 q.2 ∧ (p.1.2.1 q.1, p.2) ∈ visitPointSet Γ U} := by
    intro q
    have hmeas : Measurable fun p : BoundaryWord × S => (p.1.2.1 q.1, p.2) :=
      (((measurable_pi_apply q.1).comp (measurable_fst.comp measurable_snd)).comp measurable_fst).prodMk
        measurable_snd
    refine ae_not_mem_of_compProd_eq hM hβ hX hlaw
      (((measurableSet_goodJunction _ _ _ _).preimage measurable_fst).inter
        ((measurableSet_visitPointSet hU hΓ hc).preimage hmeas)) ?_
    filter_upwards [hker] with c hc'
    by_cases hcA : c ∈ goodJunction κ θ q.1 q.2
    · exact measure_mono_null (fun s hs => hs.2) (measure_visitPoint_eq_zero hκ hκ4 hc'.1 hc'.2 hcA)
    · have : Prod.mk c ⁻¹' {p : BoundaryWord × S | p.1 ∈ goodJunction κ θ q.1 q.2 ∧
          (p.1.2.1 q.1, p.2) ∈ visitPointSet Γ U} = ∅ := by
        ext s; simp [hcA]
      rw [this, measure_empty]
  filter_upwards [ae_all_iff.2 hI, ae_all_iff.2 hJ] with ω hIω hJω hωM
  rintro ⟨s, hsU, y, hy0, hΓy, hadm⟩
  rcases hadm with ⟨hyJ, hw⟩ | ⟨hyJ, hw⟩
  · obtain ⟨q, hcA, hyq⟩ := exists_goodInterval_of_admissible hy0 hyJ hw
    refine hIω q hωM ⟨hcA, s, hsU, ?_⟩
    rw [hΓy]
    simp only [mem_ofPred_eq, Complex.ofReal_im, le_refl, Complex.ofReal_re, true_and]
    exact hyq
  · obtain ⟨q, hcA, hqy⟩ := exists_goodJunction_of_admissible hy0 hyJ hw
    refine hJω q hωM ⟨hcA, s, hsU, ?_⟩
    rw [hΓy, hqy]

/-! ### The restart kernel at good configurations, and Lemma 7.6 -/

/-- **Named intermediate statement: the restart kernel of Lemma 7.6 at deterministic stops `(a, b)`.** Setting of
`Lemma76Statement` (`x₂ < x₁`, `θ₁ < θ₂ + π`). A canonical space `S` with measurable coordinates (chart field `H`,
chart path `Γ` continuous on its closed available interval, lifetime `U`), a measurable event `M`, datum `β`, restart
variable `X` and Markov kernel `K` such that
* `K` disintegrates `(β, X)` on `M`;
* for almost every datum `c`, under `K c`, `H` is a GFF with datum `c` and `Γ` its angle-`θ₂` flow line from `0`;
* almost surely, at a good configuration (`Lemma76Exit.IsDisjointPair`) with a forbidden first exit witnessed by the
  first tip, `ω ∈ M` and the chart path visits an admissible right point of the datum.

Unlike `Lemma76KernelStatement`, nothing is asked at the lifetime of the first path or at a real second tip. Reduced
in `Lemma76Kernel2Det.lean` to the conditional-determination input `Lemma76CondDetStatement`. -/
def Lemma76KernelLtStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ a r : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ : S → ℝ≥0 → ℂ)
      (U : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord) (X : Ω → S) (K : Kernel BoundaryWord S),
      Measurable H ∧ Measurable U ∧ (∀ s : ℝ≥0, Measurable fun x => Γ x s) ∧
      (∀ x, ContinuousOn (Γ x) {s | (s : ℝ≥0∞) ≤ U x}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β,
        IsGFFWithBoundaryData (K c) H c.fn c.jumps ∧ IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) H Γ U) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) a (η₂ ω) (ζ₂ ω) r →
        (∃ e v : ℝ≥0, (e : ℝ≥0∞) ≤ ζ₂ ω ∧ IsForbiddenExit (η₁ ω) a (η₂ ω) r e v a (lowerArc x₂ x₁)) →
        ω ∈ M ∧ ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ U (X ω) ∧ ∃ y : ℝ, 0 < y ∧ Γ (X ω) s = y ∧
          IsAdmissibleRight κ θ₂ (β ω).fn (β ω).jumps y

/-- **The first half of Lemma 7.6 from the restart kernel at good configurations**: at each pair of rational stops,
a forbidden exit at a good configuration would be a visit of an admissible point (`Lemma76KernelLtStatement`), which
has probability zero (`ae_not_visit_admissible`); every failed barrier at the stops `r ∧ ζ₁`, `t ∧ ζ₂` gives such a
rational pair (`Lemma76Exit.exists_rat_isDisjointPair_of_not_firstExitBarrier`). -/
theorem lemma76RightStatement_of_kernelLt (hK : Lemma76KernelLtStatement.{u}) : Lemma76RightStatement.{u} := by
  intro κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t
  have hq : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P,
      Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) (q.1 : ℝ).toNNReal (η₂ ω) (ζ₂ ω) (q.2 : ℝ).toNNReal →
      ¬ ∃ e v : ℝ≥0, (e : ℝ≥0∞) ≤ ζ₂ ω ∧ IsForbiddenExit (η₁ ω) (q.1 : ℝ).toNNReal (η₂ ω) (q.2 : ℝ).toNNReal
        e v (q.1 : ℝ).toNNReal (lowerArc x₂ x₁) := by
    intro q
    obtain ⟨S, _, H, Γ, U, M, β, X, K, -, hU, hΓ, hc, hM, hβ, hX, hKm, hlaw, hker, hpath⟩ :=
      hK κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ (q.1 : ℝ).toNNReal (q.2 : ℝ).toNNReal
    filter_upwards [hpath, ae_not_visit_admissible hκ hκ4 hKm hU hΓ hc hM hβ hX hlaw hker] with ω h1 h2
      hpair hex
    obtain ⟨hωM, hvis⟩ := h1 hpair hex
    exact h2 hωM hvis
  filter_upwards [ae_all_iff.2 hq, Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hω hp₁ hp₂
  by_contra hbar
  obtain ⟨q₁, q₂, hpair, e, v, he, hex⟩ :=
    Lemma76Exit.exists_rat_isDisjointPair_of_not_firstExitBarrier hp₁ hp₂ (coe_truncAt_le _ _) hbar
  exact hω (q₁, q₂) hpair ⟨e, v, he, hex⟩

/-- **Lemma 7.6 (`Lemma76Statement`, both halves) from the restart kernel at good configurations** (the swapped half
by reflection, `lemma76Statement_of_right`). -/
theorem lemma76Statement_of_kernelLt (hK : Lemma76KernelLtStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_right (lemma76RightStatement_of_kernelLt hK)

/-- **PROVE-LEMMA76C's named input follows from Lemma 7.6's first half.** Its pathwise clause concerns only the event
where the barrier fails, which is null by `Lemma76RightStatement`; any kernel (here on the empty event) witnesses it.
So `Lemma76KernelStatement` carries no content beyond `Lemma76RightStatement`, which `lemma76RightStatement_of_kernelLt`
proves from the kernel at good configurations. -/
theorem lemma76KernelStatement_of_right (hR : Lemma76RightStatement.{u}) : Lemma76KernelStatement.{u} := by
  intro κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t
  refine ⟨Unit, inferInstance, fun _ => 0, fun _ _ => 0, fun _ => 0, ∅, fun _ => (0, fun _ => 0, fun _ => 0),
    fun _ => (), Kernel.const _ (Measure.dirac ()), measurable_const, measurable_const,
    fun _ => measurable_const, fun _ => continuousOn_const, MeasurableSet.empty, measurable_const,
    measurable_const, inferInstance, by simp, by simp, ?_⟩
  filter_upwards [hR κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t] with ω hω hn
  exact absurd hω hn

/-- **PROVE-LEMMA76C's named input from the restart kernel at good configurations.** -/
theorem lemma76KernelStatement_of_kernelLt (hK : Lemma76KernelLtStatement.{u}) : Lemma76KernelStatement.{u} :=
  lemma76KernelStatement_of_right (lemma76RightStatement_of_kernelLt hK)

end Sec7

end InteractingSLE
