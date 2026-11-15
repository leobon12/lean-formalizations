/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76ESide

/-!
# Lemma 7.6's conditional-determination input with the deterministic side claims removed

Packet PROVE-LEMMA76E. PROVE-LEMMA76D's named input `Lemma76CondDetStatement` bundles, inside `IsRightSideWord`, two
claims that are not about the conditional law:

* **Aux. lemma 60** (the right-side chart points are positive), proved in `Lemma76ESide.lean`
  (`Lemma76E.pos_of_inv_mem_fst`);
* **the junction continuation inequality** (spec p. 269: "If `c` is the original field height immediately to the right
  of `x_R`, its swallowed right force sum is `(c + θ₁χ)/λ − 1`. Continuation implies that this sum is greater than
  `−2`, hence `c + θ₁χ > −λ`. This also covers `u_R = 0`, using admissibility of the starting right force group"), a
  pathwise property of one flow line, stated as `FlowLineJunctionStatement` and proved in `Lemma76EJunction.lean`.

This file states what is left of the input once those are removed:

* `IsRightSideHeights`: the heights of the conditional boundary datum at the right-side chart points `y > w` (beyond
  the chart position `w > 0` of the first tip): `λ − θ₁χ` off its jumps; at a jump, either right value `λ − θ₁χ` or
  the junction, whose physical point `x_R = ψ(y)` is the rightmost real point of the first prefix and whose right value
  is the original data `b(x_R⁺)` (the untouched real boundary, hydrodynamic chart);
* `isRightSideWord_of_heights`: positivity, the junction inequality and the heights give `IsRightSideWord`;
* `Lemma76CondDetHeightsStatement`: `Lemma76CondDetStatement` with `IsRightSideHeights` in place of `IsRightSideWord`
  (the conditional-law content only: (R1), the heights, (Det));
* **`lemma76CondDetStatement_of_heights`**: `Lemma76CondDetStatement` from `FlowLineJunctionStatement` and
  `Lemma76CondDetHeightsStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE

namespace Sec7

open LQGMetric Restart Supp7
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- **The heights of the conditional datum on the right side of the first prefix** (proof of Lemma 7.6, p. 269), in
the retained chart `ψ` based at the second tip: for every chart point `y` beyond a positive chart position `w` of the
first tip `α(a)` with `ψ(y) = α(u)`, `u < a`, either `y` is not a jump of `c` and `c(y) = λ − θ₁χ` (the exposed right
side), or `y` is a jump of `c` and its right value is `λ − θ₁χ`, or `ψ(y) = α(u)` is the rightmost real point `x_R` of
the first prefix (the junction `V^α_R`) and the right value is the original data `b(x_R⁺)`. -/
def IsRightSideHeights (κ θ₁ : ℝ) (b : ℝ → ℝ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (ψ : ℂ → ℂ) (c : BoundaryWord) : Prop :=
  ∀ y w : ℝ, ψ w = α a → 0 < w → w < y → ∀ u : ℝ≥0, u < a → ψ y = α u →
    (y ∉ c.jumps ∧ c.fn y = sleLambda κ - θ₁ * chiC κ) ∨
      (y ∈ c.jumps ∧ (rightLim c.fn y = sleLambda κ - θ₁ * chiC κ ∨
        ((α u).im = 0 ∧ (∀ s ≤ a, (α s).im = 0 → (α s).re ≤ (α u).re) ∧ rightLim c.fn y = rightLim b (α u).re)))

/-- **The junction continuation inequality for flow lines** (proof of Lemma 7.6, p. 269): almost surely, whenever
the angle-`θ` flow line from `x` visits, before its lifetime, a real point that is the rightmost real point of its
range so far, the original data immediately right of that point satisfies `b(x_R⁺) + θχ > −λ` (the swallowed right
force sum `(b(x_R⁺) + θχ)/λ − 1` exceeds `−2`, by the threshold condition of the driving evolution). -/
def FlowLineJunctionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → (η ω u).im = 0 →
        (∀ s ≤ u, (η ω s).im = 0 → (η ω s).re ≤ (η ω u).re) →
        -sleLambda κ < rightLim b (η ω u).re + θ * chiC κ

/-- **Positivity, the junction inequality and the heights give the right-side word.** -/
theorem isRightSideWord_of_heights {κ θ₁ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {α : ℝ≥0 → ℂ} {a : ℝ≥0}
    {ψ : ℂ → ℂ} {c : BoundaryWord} (hpos : ∀ w : ℝ, ψ w ∈ α '' Icc 0 a → 0 < w)
    (hjunc : ∀ u : ℝ≥0, u < a → (α u).im = 0 → (∀ s ≤ a, (α s).im = 0 → (α s).re ≤ (α u).re) →
      -sleLambda κ < rightLim b (α u).re + θ₁ * chiC κ)
    (hH : IsRightSideHeights κ θ₁ b α a ψ c) : IsRightSideWord κ θ₁ α a ψ c := by
  intro y w hw hwy u hua hy
  have hw0 : 0 < w := hpos w ⟨a, ⟨zero_le, le_rfl⟩, hw.symm⟩
  have hy0 : 0 < y := hpos y ⟨u, ⟨zero_le, hua.le⟩, hy.symm⟩
  have hwy' : w < y := by
    rcases hwy with h | h
    · exact h.2
    · exact absurd h.2 (not_lt.2 hw0.le)
  refine ⟨hy0, ?_⟩
  rcases hH y w hw hw0 hwy' u hua hy with h | ⟨hJ, h | ⟨him, hmax, hR⟩⟩
  · exact Or.inl h
  · refine Or.inr ⟨hJ, ?_⟩
    rw [h]
    have := Sec4.sleLambda_pos hκ
    linarith
  · exact Or.inr ⟨hJ, by rw [hR]; exact hjunc u hua him hmax⟩

/-- **Named input: the conditional-law content of Lemma 7.6 at a good disjoint pair** — `Lemma76CondDetStatement`
with the right-side heights `IsRightSideHeights` (the junction's right value identified with the original data) in
place of `IsRightSideWord`: (R1) for the retained chart field given `𝒢` on `M`, the right-side heights, and (Det) for
the second continuation's canonical retained clock. **Not proved in Lean.** -/
def Lemma76CondDetHeightsStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRightSideHeights κ θ₁ b (η₁ ω) d.u (d.inv ω) (β ω) ∧
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          (F₂ ((β ω, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s =
            decPath (F₂ ((β ω, 0), hd.chartField κ h ω)) s

/-- **Aux. lemma 60 in the retained chart of a good disjoint pair**: at a good configuration with the retained data
agreeing with the two paths, every real point of the retained chart inverse on the first prefix is positive. -/
theorem pos_of_retChart {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω}
    {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hx : x₂ < x₁) (hG : ω ∈ d.G) (a₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (a₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ d.u β ζ₂ d.r) :
    ∀ w : ℝ, d.inv ω w ∈ α '' Icc 0 d.u → 0 < w := by
  have hωE := mem_E_of_isDisjointPair hd hG a₁ a₂ hpair
  obtain ⟨-, hC⟩ := hd.isRetChart hωE
  have e₁ : EqOn (d.η₁ ω) α (Icc 0 d.u) := fun s hs => a₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) β (Icc 0 d.r) := fun t ht => a₂ t ht.2
  have hdom : activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r = activeDomain α d.u β d.r := activeDomain_congr_Icc e₁ e₂
  have h0₂ : (d.η₂ ω 0).im = 0 := by rw [a₂ 0 zero_le, Sec7.IsPathGood.zero hp₂]; simp
  have hbij := hC.bijOn h0₂
  have hreal := hC.inv_notMem h0₂
  rw [hdom] at hbij hreal
  have hψ0 : d.inv ω 0 = β d.r := by rw [hC.inv_zero h0₂, a₂ d.r le_rfl]
  exact fun w hw => Lemma76E.pos_of_inv_mem_fst hp₁ hp₂ hx hpair hbij hreal hC.continuousOn_inv hψ0
    hC.2.2.2.2.2.2.2.2.2.1 hw

/-- **`Lemma76CondDetStatement` from the junction inequality and the conditional-law content.** At a good
configuration, Aux. lemma 60 (`pos_of_retChart`) and the junction inequality of the first flow line turn the heights
into the right-side word (`isRightSideWord_of_heights`); (R1) and (Det) are passed through. -/
theorem lemma76CondDetStatement_of_heights (hJ : FlowLineJunctionStatement.{u})
    (hD : Lemma76CondDetHeightsStatement.{u}) : Lemma76CondDetStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  refine ⟨𝒢, M, β, hM, hβ, hsort, hR1, ?_⟩
  filter_upwards [hpath, hag, hJ κ hκ hκ4 b jumps hb x₁ θ₁ P h η₁ ζ₁ hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hω hagω hjω hp₁ hp₂ hpair
  obtain ⟨hωM, hH, hlife, hdet⟩ := hω hpair
  obtain ⟨hG, a₁, a₂⟩ := hagω hpair.1 hpair.2.1
  refine ⟨hωM, isRightSideWord_of_heights hκ (pos_of_retChart hd hp₁ hp₂ hx hG a₁ a₂ hpair) ?_ hH, hlife, hdet⟩
  intro u hu him hmax
  have huζ : (u : ℝ≥0∞) < ζ₁ ω := lt_trans (ENNReal.coe_lt_coe.2 hu) hpair.1
  exact hjω u huζ him fun s hs => hmax s (hs.trans hu.le)

end Sec7

end InteractingSLE
