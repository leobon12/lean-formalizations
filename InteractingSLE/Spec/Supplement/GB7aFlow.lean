/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Sec4.Heights

/-!
# Lemma GB7a for a flow line: an open boundary interval of cumulative weight at least `c` is not visited

Packet PROVE-G7GB7A (Theorem 1.5's interface 4, follow-up note D.5 item 4: "GB7a's exclusion of an open
original-boundary interval whose outward cumulative is at least `c = κ/2 − 2`"). Source: specification supplement
§8.7, Lemma GB7a (`source/spec/p529-576.md`, p. 523): "Let `0 < κ < 4` and let a complete finite-force flow be
continued only through its original lifetime, including its continuous finite terminal value. On an open
original-real interval `I` suppose its cumulative weight is constant and at least `c_κ = κ/2 − 2`. Then its trace
does not visit `I`."

For the angle-`θ` flow line from `x` of a field with piecewise-constant boundary data `b`, the cumulative weight of
the flow-line force word at a point `y > x` off the jumps is `(b(y) + θχ)/λ − 1 = cumWeightRight κ (b y + θχ)` (the
seed group `((b(x⁺) + θχ)/λ − 1)` plus the jumps `(b(z⁺) − b(z⁻))/λ` up to `y` telescope), and at `y < x` it is
`−(b(y) + θχ)/λ − 1 = cumWeightLeft κ (b y + θχ)`. So the interval `I = (a, a')`, on one side of the seed, has
constant cumulative weight exactly when `b` is constant on `I` off the jump candidates.

* `GB7aFlowStatement`: Lemma GB7a on the frozen carriers (named input, **not proved in Lean**; its source proof uses
  Lemma G12 and Aux. lemmas 61–64).
* `GB7aFlowStatement.ae_forall` (proved): the countable exhaustion, almost surely simultaneously for all points `y`
  off the jumps whose cumulative weight is at least `c` (rational intervals).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp8

/-- **Named input: Lemma GB7a for a flow line** (supplement §8.7, p. 523). For `0 < κ < 4`, piecewise-constant
boundary data `b`, the angle-`θ` flow line `η` from `x` with available lifetime `ζ`, and an open interval
`I = (a, a')` on one side of the seed on which `b` equals `v` off the jump candidates: if `I` lies right of the
seed and its cumulative weight `cumWeightRight κ (v + θχ)` is at least `c = κ/2 − 2`, then almost surely the trace
on `[0, ζ]` (finite terminal value included) does not visit `I`; symmetrically on the left with
`cumWeightLeft κ (v + θχ)`. **Not proved in Lean.** -/
def GB7aFlowStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ a a' v : ℝ, (∀ y ∈ Ioo a a', y ∉ jumps → b y = v) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      (x ≤ a → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (v + θ * QuantumZipper.chiC κ) →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo a a', η ω t ≠ y) ∧
      (a' ≤ x → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (v + θ * QuantumZipper.chiC κ) →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo a a', η ω t ≠ y)

/-- A point off a finite set lies in a rational open interval which avoids the set and stays strictly on the side of
a given point `x ≠ y`. -/
theorem exists_rat_Ioo_avoid (J : Finset ℝ) {y x : ℝ} (hyJ : y ∉ J) (hxy : x ≠ y) :
    ∃ q₁ q₂ : ℚ, y ∈ Ioo (q₁ : ℝ) q₂ ∧ (∀ z ∈ Ioo (q₁ : ℝ) q₂, z ∉ J) ∧
      (x < y → x ≤ q₁) ∧ (y < x → (q₂ : ℝ) ≤ x) := by
  have hopen : IsOpen ((J : Set ℝ)ᶜ ∩ {x}ᶜ) :=
    (J.finite_toSet.isClosed.isOpen_compl).inter isClosed_singleton.isOpen_compl
  have hmem : y ∈ (J : Set ℝ)ᶜ ∩ {x}ᶜ := ⟨hyJ, fun h => hxy (h.symm ▸ rfl)⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen y hmem
  -- shrink to half the distance to `x`, so that the interval stays on one side of `x`
  set δ := min ε (|y - x| / 2) with hδ
  have hδpos : 0 < δ := lt_min hε (half_pos (abs_pos.2 (sub_ne_zero.2 hxy.symm)))
  obtain ⟨q₁, hq₁l, hq₁r⟩ := exists_rat_btwn (show y - δ < y by linarith)
  obtain ⟨q₂, hq₂l, hq₂r⟩ := exists_rat_btwn (show y < y + δ by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδx : δ ≤ |y - x| / 2 := min_le_right _ _
  refine ⟨q₁, q₂, ⟨hq₁r, hq₂l⟩, fun z hz hzJ => ?_, fun hlt => ?_, fun hlt => ?_⟩
  · have hzb : z ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2]
    exact (hball hzb).1 hzJ
  · rw [abs_of_pos (sub_pos.2 hlt)] at hδx
    linarith
  · rw [abs_of_neg (sub_neg.2 hlt)] at hδx
    linarith

/-- **GB7a, almost surely for every point at once** (countable exhaustion by rational intervals). Almost surely,
the flow line on `[0, ζ]` visits no real point `y` off the jumps whose cumulative weight is at least
`c = κ/2 − 2`: right of the seed `cumWeightRight κ (b y + θχ) ≥ c`, left of it `cumWeightLeft κ (b y + θχ) ≥ c`. -/
theorem GB7aFlowStatement.ae_forall (hGB : GB7aFlowStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y : ℝ, y ∉ jumps →
      (x < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b y + θ * QuantumZipper.chiC κ) → η ω t ≠ y) ∧
      (y < x → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b y + θ * QuantumZipper.chiC κ) → η ω t ≠ y) := by
  -- one event per rational interval
  have hq : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P,
      ((∀ z ∈ Ioo (q.1 : ℝ) q.2, z ∉ jumps) → x ≤ q.1 →
        κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (q.1 : ℝ) q.2, η ω t ≠ y) ∧
      ((∀ z ∈ Ioo (q.1 : ℝ) q.2, z ∉ jumps) → (q.2 : ℝ) ≤ x →
        κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (q.1 : ℝ) q.2, η ω t ≠ y) := by
    intro q
    by_cases hJ : ∀ z ∈ Ioo (q.1 : ℝ) q.2, z ∉ jumps
    · by_cases hne : (q.1 : ℝ) < q.2
      · have hmid : ((q.1 + q.2 : ℝ) / 2) ∈ Ioo (q.1 : ℝ) q.2 := ⟨by linarith, by linarith⟩
        have hconst : ∀ y ∈ Ioo (q.1 : ℝ) q.2, y ∉ jumps → b y = b ((q.1 + q.2 : ℝ) / 2) :=
          fun y hy _ => Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb
            (fun z hzJ hz => hJ z hz hzJ) hmid hy
        obtain ⟨hR, hL⟩ := hGB κ hκ hκ4 b jumps hb x θ q.1 q.2 _ hconst P h hh η ζ hη
        by_cases hxR : x ≤ q.1 ∧
            κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ)
        · by_cases hxL : (q.2 : ℝ) ≤ x ∧
              κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ)
          · filter_upwards [hR hxR.1 hxR.2, hL hxL.1 hxL.2] with ω h1 h2
            exact ⟨fun _ _ _ => h1, fun _ _ _ => h2⟩
          · filter_upwards [hR hxR.1 hxR.2] with ω h1
            exact ⟨fun _ _ _ => h1, fun _ h2 h3 => absurd ⟨h2, h3⟩ hxL⟩
        · by_cases hxL : (q.2 : ℝ) ≤ x ∧
              κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ)
          · filter_upwards [hL hxL.1 hxL.2] with ω h2
            exact ⟨fun _ h1 h3 => absurd ⟨h1, h3⟩ hxR, fun _ _ _ => h2⟩
          · exact Eventually.of_forall fun ω =>
              ⟨fun _ h1 h3 => absurd ⟨h1, h3⟩ hxR, fun _ h2 h3 => absurd ⟨h2, h3⟩ hxL⟩
      · -- empty interval
        refine Eventually.of_forall fun ω => ⟨fun _ _ _ t _ y hy => ?_, fun _ _ _ t _ y hy => ?_⟩ <;>
          exact absurd (hy.1.trans hy.2) hne
    · exact Eventually.of_forall fun ω => ⟨fun h' => absurd h' hJ, fun h' => absurd h' hJ⟩
  filter_upwards [ae_all_iff.2 hq] with ω hω t ht y hyJ
  refine ⟨fun hxy hw => ?_, fun hxy hw => ?_⟩
  · obtain ⟨q₁, q₂, hy, hJ, hR, -⟩ := exists_rat_Ioo_avoid jumps hyJ hxy.ne
    have hmid : ((q₁ + q₂ : ℝ) / 2) ∈ Ioo (q₁ : ℝ) q₂ := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    have hby : b y = b ((q₁ + q₂ : ℝ) / 2) :=
      Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb (fun z hzJ hz => hJ z hz hzJ) hmid hy
    rw [hby] at hw
    exact ((hω (q₁, q₂)).1 hJ (hR hxy) hw) t ht y hy
  · obtain ⟨q₁, q₂, hy, hJ, -, hL⟩ := exists_rat_Ioo_avoid jumps hyJ hxy.ne'
    have hmid : ((q₁ + q₂ : ℝ) / 2) ∈ Ioo (q₁ : ℝ) q₂ := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    have hby : b y = b ((q₁ + q₂ : ℝ) / 2) :=
      Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb (fun z hzJ hz => hJ z hz hzJ) hmid hy
    rw [hby] at hw
    exact ((hω (q₁, q₂)).2 hJ (hL hxy) hw) t ht y hy

end Supp8

end InteractingSLE
