/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockAssembly

/-!
# `FirstContactKernelCanonStatement` with the W8.1 clocks supplied

Packet PROVE-RESTART-CPL5. CPL4 reduced the D.5 restart interface to `FirstContactKernelCanonStatement`, whose
content was (i) the W8.1 relative capacity clocks with measurable chart paths, (ii) (R1) (Lemma 7.8's conditional
law) and (iii) (R2′) (the chart paths are flow lines of the chart field under the disintegrated kernel). Item (i) is
now proved (`exists_canonClock`: Aux. lemma 76, Proposition 6.12 for the mapped continuation, capacity additivity,
measurable capacities and inverse clocks). What remains is the named input `FirstContactKernelClockStatement`:

* the same binders, with the chart field fixed to CPL4's canonical one and the chart paths/lifetimes fixed to **any
  measurable versions of the canonical capacity-time chart paths** (`PairData.IsCanonClock`);
* the conclusion `IsFirstContactKernelRest`: the conjuncts of `IsFirstContactKernelData` other than the measurability
  and continuity of the chart paths (the retained σ-algebra `𝒢`, the meeting branch `M` and the sorted datum `β`,
  (R1), the disintegrating kernel `K` and (R2′)), and that the first contacts with two nonempty continuations lie in
  `M`.

So exactly (R1) and (R2′) (with their σ-algebra, branch and kernel) remain: Lemma 7.8's kernel and the restart.

## Main results

* `IsFirstContactKernelRest`, `FirstContactKernelClockStatement`;
* **`firstContactKernelCanonStatement_of_clock`**: `Aux25Statement → Lemma77Statement →
  FirstContactKernelClockStatement → FirstContactKernelCanonStatement`;
* `firstContactRestartLimStatement_of_clock`: the D.5 interface `Theorem15D5.FirstContactRestartLimStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

/-- **The kernel data without the chart-path regularity**: `IsFirstContactKernelData` minus the measurability and
continuity of `γᵢ`, `Uᵢ` (same binder order `(𝒢) {mΩ}`): the retained history `𝒢`, the meeting branch `M`, the sorted
datum `β`, a measurable extra coordinate `Y`, (R1) on `Ω`, the disintegrating kernel `K` and (R2′). -/
def IsFirstContactKernelRest (κ θ₁ θ₂ : ℝ) {Ω : Type*} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (M : Set Ω) (β : Ω → BoundaryWord) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) {E : Type*} [MeasurableSpace E] (Y : Ω → E)
    (K : Kernel BoundaryWord (RestartSpace × E)) : Prop :=
  𝒢 ≤ mΩ ∧ MeasurableSet[𝒢] M ∧ Measurable[𝒢] β ∧ (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧ Measurable Y ∧
    (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ) ∧
    IsMarkovKernel K ∧
    (P.restrict M).map (fun ω => (β ω, (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω))) =
      (P.restrict M).map β ⊗ₘ K ∧
    ∀ᵐ c ∂(P.restrict M).map β,
      IsFlowLine κ c.fn c.jumps 0 θ₁ (K c) (fun s => s.1.field) (fun s => s.1.path₁) (fun s => s.1.life₁) ∧
      IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) (fun s => s.1.field) (fun s => s.1.path₂) (fun s => s.1.life₂)

/-- **Named input: Lemma 7.8's kernel and the restart in the canonical chart with the W8.1 clocks** (Lemma 7.8,
p. 290; Theorem W8, pp. 538–541). For two flow lines as in `FirstContactKernelCanonStatement`, any measurable pair
data `d` agreeing with them, the canonical chart field `Hc`, and **any measurable versions `γᵢ`, `Uᵢ` of the
canonical chart paths in relative capacity time** (`PairData.IsCanonClock`), there are a retained σ-algebra `𝒢`, a
meeting branch `M` containing almost surely every first contact with two nonempty continuations, a sorted datum
`β` and a kernel `K` with (R1) and (R2′) (`IsFirstContactKernelRest`). -/
def FirstContactKernelClockStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) →
    ∀ Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens, Hc = hd.chartField κ h →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) →
      (∀ t, Measurable fun ω => γ₂ ω t) → Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∃ (𝒢 : MeasurableSpace Ω) (M : Set Ω) (β : Ω → BoundaryWord) (E : Type) (_ : MeasurableSpace E) (Y : Ω → E)
      (K : Kernel BoundaryWord (RestartSpace × E)),
      IsFirstContactKernelRest κ θ₁ θ₂ 𝒢 P M β Hc γ₁ γ₂ U₁ U₂ Y K ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω → ω ∈ M

/-- **`FirstContactKernelCanonStatement` from the clock-supplied named input**: the W8.1 clocks, their measurability,
the continuity of the chart paths and the pathwise clock data are proved (`exists_canonClock`). -/
theorem firstContactKernelCanonStatement_of_clock (hA : Theorem15.Aux25Statement.{u})
    (h77 : Supp10.Lemma77Statement.{u}) (hR : FirstContactKernelClockStatement.{u}) :
    FirstContactKernelCanonStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae Hc hHc
  obtain ⟨γ₁, γ₂, U₁, U₂, m₁, m₂, mU₁, mU₂, c₁, c₂, hcanon, hclock⟩ :=
    exists_canonClock hA h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
  obtain ⟨𝒢, M, β, E, mE, Y, K, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hM⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae Hc hHc γ₁ γ₂ U₁ U₂
      m₁ m₂ mU₁ mU₂ hcanon
  refine ⟨𝒢, M, β, γ₁, γ₂, U₁, U₂, E, mE, Y, K,
    ⟨h1, h2, h3, h4, m₁, m₂, mU₁, mU₂, h5, ae_of_all _ fun ω _ => ⟨c₁ ω, c₂ ω⟩, h6, h7, h8, h9⟩, ?_⟩
  filter_upwards [hM, hclock] with ω hω hc s₀ t₀ hfc hs ht
  exact ⟨hω s₀ t₀ hfc hs ht, hc s₀ t₀ hfc hs ht⟩

/-- **The D.5 restart-with-limits interface from the clock-supplied named input** (with CPL3–CPL4's reductions):
Aux. lemma 25, Lemma 7.7 and `FirstContactKernelClockStatement` give `Theorem15D5.FirstContactRestartLimStatement`. -/
theorem firstContactRestartLimStatement_of_clock (hA : Theorem15.Aux25Statement.{u})
    (h77 : Supp10.Lemma77Statement.{u}) (hR : FirstContactKernelClockStatement.{u}) :
    Theorem15D5.FirstContactRestartLimStatement.{u} :=
  firstContactRestartLimStatement_of_canon h77 hA (firstContactKernelCanonStatement_of_clock hA h77 hR)

end Restart

end InteractingSLE
