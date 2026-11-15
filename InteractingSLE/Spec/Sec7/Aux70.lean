/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoHist
import InteractingSLE.Spec.Sec7.Aux70Select
import InteractingSLE.Spec.Sec7.InteractionProbLemma77
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Spec.Restart.ClockTrace
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Aux. lemma 70 from the single-path side heights and the chart geometry of a reverse arc

Packet PROVE-LEMMA76 (specification §7.2, Aux. lemma 70, p. 274, `source/spec/p241-288.md#aux-70`): "Assume the
single-path, history-marked GFF couplings and field determination used in Lemma 7.7, with `0 < κ < 4` and
`θ₁ < θ₂ + π`. Almost surely, the first-coordinate projection of the set of minimal contacts from Aux. lemma 68
contains no nondegenerate interval."

## The proof (pp. 274–276), and where each step is

1. "Work on a probability-one event on which the single-path conditional-mean laws, the local-set union law and its
   boundary comparison hold for every pair of rational stopped parameters" — `TwoHist.lean` (the union law and
   Proposition 3.8 at deterministic stops, from Lemma 7.5 and Aux. lemma 56) and `SinglePathSideHeightStatement`
   (the single-path laws), for all rational pairs at once (countable intersection, below).
2. "Choose a rational number `qᵢ < Tᵢ` for each path […] The intersection of the two stopped ranges is exactly `J`.
   […] The common subarc contains an open subarc in `ℍ` […] the two stopped ranges agree in a physical neighborhood
   of `J₀`" — `Aux70Select.lean` (deterministic, proved).
3. "Aux. lemma 69 puts the common side incident to the unbounded union component on the right of the first trace and
   the left of the second. […] Aux. lemma 57 gives argument lift zero for the derivative of each such transition map"
   — `ReverseArcChartStatement` (deterministic planar geometry: Aux. lemma 69, the prime-end boundary
   correspondence of the two single-path charts on the exposed side, Aux. lemma 57 for the transitions).
4. "The single-path coupling gives, in the `gᵢ` coordinate, height `λ − θ₁χ` on the right side of the first trace and
   height `−λ − θ₂χ` on the left side of the second" — `SinglePathSideHeightStatement`.
5. "The common-arc form of Proposition 3.8 says that `M − Mᵢ` tends to zero at `J₀` from the common exposed side […]
   The same conditional harmonic function therefore has the two constant boundary values `λ − θ₁χ = −λ − θ₂χ`
   […] contrary to the assumed strict inequality" — the assembly `aux70Statement_of_inputs` (proved), with the
   landed `sleLambda_sub_ne`.

## The two named inputs (not proved here)

* **`SinglePathSideHeightStatement`** (step 4): for the angle-`θ` flow line from `x` stopped at a deterministic time
  `q < ζ`, every harmonic representative `v` of the local-set mean of `η([0, q]) ∩ ℍ` (centred field `h − 𝔥₀`)
  satisfies `v + 𝔥₀ + χ arg f_q′(· − x) → λ − θχ` along every approach to a non-tip trace point `η(t₀) ∈ ℍ` in the
  unbounded component on which the centred Loewner map `f_q(· − x)` tends to a positive real, and `→ −λ − θχ` when it
  tends to a negative real. This is the single-path coupling (Theorem 1.1) read on the local-set mean (Aux. lemma
  56's identification of the retained conditional law), the bounded harmonic extension of the force data being `λ`
  on the image `(0, V^R − W)` of the right side and `−λ` on the image of the left side. It is item (b) of
  `planning/handoffs/PROVE-PRIMEEND.md` ("the single-path means in pointwise form"), in the boundary-value form used
  here.
* **`ReverseArcChartStatement`** (step 3, deterministic).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6

universe u

/-! ### The named inputs -/

/-- **Named input: the single-path side heights** (specification §7.2, proof of Aux. lemma 70, p. 275: "The
single-path coupling gives, in the `gᵢ` coordinate, height `λ − θ₁χ` on the right side of the first trace and height
`−λ − θ₂χ` on the left side of the second"; Theorem 1.1 with Aux. lemma 56). For the angle-`θ` flow line `η` from `x`
with driving function `W` (its translate `η − x` is the generating trace of `W`), a cap `m`, a deterministic stop
`q ≤ m`, a version `ηc` of the capped flow line and a version `g` of the local-set mean of `ηc([0, q]) ∩ ℍ` for the
centred field `h − 𝔥₀`: almost surely on `{q < ζ}`, for every harmonic representative `v` of `g`, every trace point
`η(t₀) ∈ ℍ` with `t₀ < q`, every nontrivial approach `F` to it inside the unbounded component of `ℍ \ η([0, q])`
along which the centred Loewner map `f_q(· − x)` tends to a real `y`: if `y > 0` (the right side), then
`v + 𝔥₀ + χ arg f_q′(· − x) → λ − θχ` along `F`; if `y < 0` (the left side), it tends to `−λ − θχ`. Here
`arg f_q′ = Im logDerivFwd`, the branch of the frozen coupling mean (`couplingMean`). **Not proved in Lean.** -/
def SinglePathSideHeightStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
    ∀ W : ℝ≥0 → Ω → ℝ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ → ∀ m q : ℝ≥0, q ≤ m →
    ∀ ηc : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (ηc ω)) → (∀ t, Measurable fun ω => ηc ω t) →
      (∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (Restart.capTime m (ζ ω) t)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < q → η ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η ω '' Icc 0 q)] (η ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) q (z - x)) F (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im) F
            (𝓝 (sleLambda κ - θ * QuantumZipper.chiC κ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im) F
            (𝓝 (-sleLambda κ - θ * QuantumZipper.chiC κ)))

/-- **Named input: the chart geometry of a stopped reverse common arc** (deterministic; specification §7.2, Aux.
lemma 69, p. 273, and the proof of Aux. lemma 70, p. 275: "Aux. lemma 69 puts the common side incident to the
unbounded union component on the right of the first trace and the left of the second. It is also exposed in each
individual complement. Consequently its `gᵢ` image is an open real interval […] Aux. lemma 57 gives argument lift
zero for the derivative of each such transition map, with normalization inherited from infinity"). Two simple Loewner
traces `α` from `x₁` and `β` from `x₂ < x₁` (drivers `W₁`, `W₂`), stopped at `q₁ < ζ₁` and `q₂ < ζ₂`, whose stopped
ranges meet exactly in the reverse common arc `J = α([σ₁, q₁]) = β([σ₂, q₂])` (`β ∘ f = α`, `f` decreasing), which
contains an interior point: then some point `α(s)`, `σ₁ < s < q₁`, of `J ∩ ℍ` is approached from the unbounded
component `D` of `ℍ \ (α([0, q₁]) ∪ β([0, q₂]))` along a nontrivial filter on which the first centred Loewner map
tends to a positive real (the right side of `α`), the second to a negative real (the left side of `β`), and the two
derivative-argument branches `Im logDerivFwd` differ by a quantity tending to `0`. **Not proved in Lean.** -/
def ReverseArcChartStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ), x₂ < x₁ → ∀ (W₁ W₂ : ℝ≥0 → ℝ) (ζ₁ ζ₂ : ℝ≥0∞),
    IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁) → ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁} → W₁ 0 = 0 →
    IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂) → ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂} → W₂ 0 = 0 →
    InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁} → InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂} →
    ∀ (q₁ q₂ σ₁ σ₂ s₀ : ℝ≥0) (f : ℝ≥0 → ℝ≥0), (q₁ : ℝ≥0∞) < ζ₁ → (q₂ : ℝ≥0∞) < ζ₂ → σ₁ < s₀ → s₀ < q₁ →
      σ₂ < q₂ → ContinuousOn f (Icc σ₁ q₁) → StrictAntiOn f (Icc σ₁ q₁) → f σ₁ = q₂ → f q₁ = σ₂ →
      (∀ s ∈ Icc σ₁ q₁, β (f s) = α s) → α '' Icc 0 q₁ ∩ β '' Icc 0 q₂ ⊆ α '' Icc σ₁ q₁ → α s₀ ∈ H →
    ∃ s ∈ Ioo σ₁ q₁, α s ∈ H ∧ ∃ F : Filter ℂ, F.NeBot ∧
      F ≤ 𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] (α s) ∧ ∃ y₁ y₂ : ℝ, 0 < y₁ ∧ y₂ < 0 ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)) F (𝓝 (y₁ : ℂ)) ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)) F (𝓝 (y₂ : ℂ)) ∧
      Tendsto (fun z => (QuantumZipper.logDerivFwd (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)).im -
        (QuantumZipper.logDerivFwd (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)).im) F (𝓝 0)

/-! ### Deterministic helpers -/

section Helpers

/-- A stop at time `0` contributes nothing in `ℍ` for a path from a real seed. -/
theorem image_le_zero_inter_H {γ : ℝ≥0 → ℂ} (h0 : (γ 0).im = 0) :
    γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} ∩ H = ∅ := by
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro z ⟨⟨t, ht, rfl⟩, hz⟩
  have ht0 : t = 0 := by
    have : (t : ℝ≥0∞) ≤ 0 := ht
    exact_mod_cast le_antisymm this zero_le
  rw [ht0] at hz
  exact absurd h0 (ne_of_gt hz)

/-- The explored set of a pair stopped at `(a, b)`. -/
theorem explored_pair {Ω : Type*} (ηs : Fin 2 → Ω → ℝ≥0 → ℂ) (a b : ℝ≥0∞) (ω : Ω) :
    explored ηs (fun i _ => (![a, b] : Fin 2 → ℝ≥0∞) i) ω =
      (ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ a} ∪ ηs 1 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ b}) ∩ H := by
  ext z
  simp only [explored, mem_inter_iff, mem_iUnion, Fin.exists_fin_two, mem_union, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- The explored set of a pair with the second path stopped at `0` is the first prefix. -/
theorem explored_pair_left {Ω : Type*} (ηs : Fin 2 → Ω → ℝ≥0 → ℂ) (a : ℝ≥0∞) {ω : Ω}
    (h1 : (ηs 1 ω 0).im = 0) :
    explored ηs (fun i _ => (![a, 0] : Fin 2 → ℝ≥0∞) i) ω = ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ a} ∩ H := by
  rw [explored_pair, union_inter_distrib_right, image_le_zero_inter_H h1, union_empty]

/-- The explored set of a pair with the first path stopped at `0` is the second prefix. -/
theorem explored_pair_right {Ω : Type*} (ηs : Fin 2 → Ω → ℝ≥0 → ℂ) (b : ℝ≥0∞) {ω : Ω}
    (h0 : (ηs 0 ω 0).im = 0) :
    explored ηs (fun i _ => (![0, b] : Fin 2 → ℝ≥0∞) i) ω = ηs 1 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ b} ∩ H := by
  rw [explored_pair, union_inter_distrib_right, image_le_zero_inter_H h0, empty_union]

/-- On the stops below the cap and the lifetime, the capped path has the range of the path. -/
theorem image_capped_eq {γ γc : ℝ≥0 → ℂ} {m : ℝ≥0} {ζ : ℝ≥0∞} (hγc : ∀ t, γc t = γ (Restart.capTime m ζ t))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ min ζ m) :
    γc '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} = γ '' Icc 0 q := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htq : t ≤ q := by exact_mod_cast ht
    refine ⟨t, ⟨zero_le, htq⟩, ?_⟩
    rw [hγc, Restart.capTime_of_le m ζ ((ENNReal.coe_le_coe.2 htq).trans hq)]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, show (t : ℝ≥0∞) ≤ q from ENNReal.coe_le_coe.2 ht.2, ?_⟩
    rw [hγc, Restart.capTime_of_le m ζ ((ENNReal.coe_le_coe.2 ht.2).trans hq)]

/-- **Proposition 3.8 for the two single prefixes**: if the union mean differs from each single-prefix mean by
harmonic functions tending to `0` at `z₀`, the two single-prefix means differ by a function tending to `0` there. -/
theorem tendsto_sub_of_union_means {O A₁ A₂ : Set ℂ} (hO : IsOpen O) (hO₁ : O ⊆ H \ A₁) (hO₂ : O ⊆ H \ A₂)
    {g g₁ g₂ : DistOn upperHalfPlaneOpens} {v₁ v₂ ua ub : ℂ → ℝ}
    (hv₁ : InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁))
    (hv₁r : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ → g₁ φ = ∫ z, v₁ z * φ z)
    (hv₂ : InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂))
    (hv₂r : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ → g₂ φ = ∫ z, v₂ z * φ z)
    (hua : InnerProductSpace.HarmonicOnNhd ua O)
    (huar : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ - g₁ φ = ∫ z, ua z * φ z)
    (hub : InnerProductSpace.HarmonicOnNhd ub O)
    (hubr : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ - g₂ φ = ∫ z, ub z * φ z) {z₀ : ℂ}
    (ha : Tendsto ua (𝓝[O] z₀) (𝓝 0)) (hb : Tendsto ub (𝓝[O] z₀) (𝓝 0)) :
    Tendsto (fun z => v₁ z - v₂ z) (𝓝[O] z₀) (𝓝 0) := by
  have hOH : O ⊆ H := fun z hz => (hO₁ hz).1
  have hc : ∀ {v : ℂ → ℝ} {U : Set ℂ}, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hv₁O : InnerProductSpace.HarmonicOnNhd v₁ O := fun z hz => hv₁ z (hO₁ hz)
  have hv₂O : InnerProductSpace.HarmonicOnNhd v₂ O := fun z hz => hv₂ z (hO₂ hz)
  have heq : EqOn (fun z => v₁ z - v₂ z) (fun z => ub z - ua z) O := by
    refine eqOn_of_integral_mul_eq hO hOH (hv₁O.sub hv₂O) (hub.sub hua) fun φ hφ => ?_
    have i₁ := integrable_mul_test hO (hc hv₁O) φ hφ
    have i₂ := integrable_mul_test hO (hc hv₂O) φ hφ
    have i₃ := integrable_mul_test hO (hc hub) φ hφ
    have i₄ := integrable_mul_test hO (hc hua) φ hφ
    have e₁ : ∫ z, (v₁ z - v₂ z) * φ z = (∫ z, v₁ z * φ z) - ∫ z, v₂ z * φ z := by
      rw [← integral_sub i₁ i₂]; congr 1; funext z; ring
    have e₂ : ∫ z, (ub z - ua z) * φ z = (∫ z, ub z * φ z) - ∫ z, ua z * φ z := by
      rw [← integral_sub i₃ i₄]; congr 1; funext z; ring
    rw [e₁, e₂, ← hv₁r φ (hφ.trans hO₁), ← hv₂r φ (hφ.trans hO₂), ← hubr φ hφ, ← huar φ hφ]
    ring
  have hlim : Tendsto (fun z => ub z - ua z) (𝓝[O] z₀) (𝓝 0) := by
    simpa using hb.sub ha
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz using (heq hz).symm

/-- **The contradiction of Aux. lemma 70** (p. 275): one harmonic function with two boundary values. If
`v₁ − v₂ → 0`, `L₁ − L₂ → 0`, `v₁ + u₀ + χL₁ → a₁` and `v₂ + u₀ + χL₂ → a₂` along a nontrivial filter, then
`a₁ = a₂`. -/
theorem eq_of_side_limits {F : Filter ℂ} [F.NeBot] {v₁ v₂ u₀ L₁ L₂ : ℂ → ℝ} {χ a₁ a₂ : ℝ}
    (h12 : Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0)) (hL : Tendsto (fun z => L₁ z - L₂ z) F (𝓝 0))
    (h₁ : Tendsto (fun z => v₁ z + u₀ z + χ * L₁ z) F (𝓝 a₁))
    (h₂ : Tendsto (fun z => v₂ z + u₀ z + χ * L₂ z) F (𝓝 a₂)) : a₁ = a₂ := by
  have hd := h₁.sub h₂
  have hd' : Tendsto (fun z => (v₁ z + u₀ z + χ * L₁ z) - (v₂ z + u₀ z + χ * L₂ z)) F (𝓝 0) := by
    have := h12.add (hL.const_mul χ)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun z => ?_
    ring
  exact sub_eq_zero.1 (tendsto_nhds_unique hd hd')

end Helpers

/-! ### The assembly -/

section Assembly

/-- The stops of the first prefix alone. -/
abbrev stop₁ (r : ℚ) : Fin 2 → ℝ≥0∞ := ![(((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞), 0]

/-- The stops of the second prefix alone. -/
abbrev stop₂ (r : ℚ) : Fin 2 → ℝ≥0∞ := ![0, (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)]

theorem max_stop_comm (r₁ r₂ : ℚ) :
    (fun (i : Fin 2) (_ : Unit) => max (stop₂ r₂ i) (stop₁ r₁ i)) =
      fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i) := by
  funext i _
  exact max_comm _ _

/-- **Aux. lemma 70 from the single-path side heights and the chart geometry of a reverse arc** (a conditional
helper; the two named inputs are not proved, see the module docstring). Lemma 7.5 and Aux. lemma 56 at first
entrance times are the named inputs of the landed first-contact locality. -/
theorem aux70Statement_of_inputs (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hside : SinglePathSideHeightStatement.{u})
    (hgeom : ReverseArcChartStatement) : Aux70Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ m
  classical
  set χ := QuantumZipper.chiC κ with hχ
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  set hc' := WholeField.centredField h u₀ with hc'def
  obtain ⟨ηs, hc, h0, hηm, hdet, hloc, hfr, him, hs₁, hs₂⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη₁ hη₂ hu₀ (m : ℝ≥0)
  have hx0 : ∀ i, ((![(x₁ : ℂ), (x₂ : ℂ)] : Fin 2 → ℂ) i).im = 0 := by
    intro i; fin_cases i <;> simp
  have hηs0 : ∀ i ω, (ηs i ω 0).im = 0 := fun i ω => by rw [h0 i ω]; exact hx0 i
  -- the drivers
  obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
  obtain ⟨_, _, W₂, _, _, _, -, hcoup₂, htr₂⟩ := id hη₂
  have hinj₁ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hinj₂ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  -- the local sets and their means at every rational stop
  have hloc' : ∀ s : Fin 2 → ℝ≥0∞, IsLocalSet (explored ηs fun i _ => s i) hc' P := fun s =>
    isLocalSet_explored_const hh0 hc h0 hηm hdet hloc hfr s
  have hmean : ∀ s : Fin 2 → ℝ≥0∞, ∃ g, IsLocalSetMean (explored ηs fun i _ => s i) hc' P g := fun s =>
    IsLocalSet.exists_isLocalSetMean hh0 (measurable_explored_const hc hηm s) (hloc' s)
  choose G hG using hmean
  -- the pathwise sets
  have hA₁ : ∀ (r : ℚ) ω, explored ηs (fun i _ => stop₁ r i) ω =
      ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H := fun r ω =>
    explored_pair_left ηs _ (hηs0 1 ω)
  have hA₂ : ∀ (r : ℚ) ω, explored ηs (fun i _ => stop₂ r i) ω =
      ηs 1 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H := fun r ω =>
    explored_pair_right ηs _ (hηs0 0 ω)
  -- the single-path side heights at every rational stop
  have hN₁ : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) →
      ((((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) →
        G (stop₁ r) ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < (r : ℝ).toNNReal → η₁ ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η₁ ω '' Icc 0 (r : ℝ).toNNReal)] (η₁ ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)) F
          (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)).im) F
            (𝓝 (sleLambda κ - θ₁ * χ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)).im) F
            (𝓝 (-sleLambda κ - θ₁ * χ)))) := by
    intro r
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · have hg : IsLocalSetMean (fun ω => ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) hc' P
          (G (stop₁ r)) := by
        have e : (fun ω => ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) =
            explored ηs (fun i _ => stop₁ r i) := funext fun ω => (hA₁ r ω).symm
        rw [e]
        exact hG _
      filter_upwards [hside κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ W₁ htr₁ u₀ hu₀ (m : ℝ≥0)
        (r : ℝ).toNNReal hrm (ηs 0) (hc 0) (hηm 0) hs₁ (G (stop₁ r)) hg] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  have hN₂ : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) →
      ((((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) →
        G (stop₂ r) ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < (r : ℝ).toNNReal → η₂ ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η₂ ω '' Icc 0 (r : ℝ).toNNReal)] (η₂ ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)) F
          (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)).im) F
            (𝓝 (sleLambda κ - θ₂ * χ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)).im) F
            (𝓝 (-sleLambda κ - θ₂ * χ)))) := by
    intro r
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · have hg : IsLocalSetMean (fun ω => ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) hc' P
          (G (stop₂ r)) := by
        have e : (fun ω => ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) =
            explored ηs (fun i _ => stop₂ r i) := funext fun ω => (hA₂ r ω).symm
        rw [e]
        exact hG _
      filter_upwards [hside κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ W₂ htr₂ u₀ hu₀ (m : ℝ≥0)
        (r : ℝ).toNNReal hrm (ηs 1) (hc 1) (hηm 1) hs₂ (G (stop₂ r)) hg] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  -- Proposition 3.8 at every rational pair
  have hmc : ∀ r₁ r₂ : ℚ, (fun (i : Fin 2) (_ : Ω) => max (stop₂ r₂ i) (stop₁ r₁ i)) =
      fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i) := fun _ _ => by
    funext i _
    exact max_comm _ _
  have hPa : ∀ r₁ r₂ : ℚ, ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω →
        G (fun i => max (stop₁ r₁ i) (stop₂ r₂ i)) ω φ - G (stop₁ r₁) ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored ηs (fun i _ => stop₁ r₁ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored ηs (fun i _ => stop₂ r₂ i) ω ∩ ball z₀ r ⊆ explored ηs (fun i _ => stop₁ r₁ i) ω) →
        Tendsto u (𝓝[H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω] z₀) (𝓝 0) := by
    intro r₁ r₂
    have hg : IsLocalSetMean (explored ηs fun i _ => max (stop₂ r₂ i) (stop₁ r₁ i)) hc' P
        (G (fun i => max (stop₁ r₁ i) (stop₂ r₂ i))) := by
      rw [hmc]
      exact hG _
    have := ae_tendsto_sub_explored_const hh0 hc h0 hx0 hηm hdet hloc hfr him (stop₂ r₂) (stop₁ r₁) hg (hG _)
    rw [hmc] at this
    exact this
  have hPb : ∀ r₁ r₂ : ℚ, ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω →
        G (fun i => max (stop₁ r₁ i) (stop₂ r₂ i)) ω φ - G (stop₂ r₂) ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored ηs (fun i _ => stop₂ r₂ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored ηs (fun i _ => stop₁ r₁ i) ω ∩ ball z₀ r ⊆ explored ηs (fun i _ => stop₂ r₂ i) ω) →
        Tendsto u (𝓝[H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω] z₀) (𝓝 0) := fun r₁ r₂ =>
    ae_tendsto_sub_explored_const hh0 hc h0 hx0 hηm hdet hloc hfr him (stop₁ r₁) (stop₂ r₂) (hG _) (hG _)
  -- the probability-one event
  filter_upwards [hs₁, hs₂, htr₁, htr₂, hcoup₁.1.2.2.2.2, hcoup₂.1.2.2.2.2, hinj₁, hinj₂, ae_all_iff.2 hN₁,
    ae_all_iff.2 hN₂, ae_all_iff.2 fun r₁ => ae_all_iff.2 (hPa r₁), ae_all_iff.2 fun r₁ => ae_all_iff.2 (hPb r₁),
    ae_all_iff.2 fun r => (hG (stop₁ r)).2.1, ae_all_iff.2 fun r => (hG (stop₂ r)).2.1]
    with ω ha₁ ha₂ ht₁ ht₂ hp₁ hp₂ hi₁ hi₂ hn₁ hn₂ hpa hpb hr₁ hr₂
  by_contra hrev
  set T₁ := truncTime (ζ₁ ω) m with hT₁
  set T₂ := truncTime (ζ₂ ω) m with hT₂
  -- pathwise regularity of the stopped paths
  have hcont : ∀ {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {x : ℝ},
      IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x) →
      ContinuousOn (η ω) (Icc 0 (truncTime (ζ ω) m)) := fun {η ζ W x} ht => by
    have hc : ContinuousOn (fun t => (η ω t - x) + x) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} :=
      ht.2.1.add continuousOn_const
    simp only [sub_add_cancel] at hc
    exact hc.mono (Icc_truncTime_subset _ m)
  have hcont₁ := hcont ht₁
  have hcont₂ := hcont ht₂
  have hinjI₁ : InjOn (η₁ ω) (Icc 0 T₁) := hi₁.mono (Icc_truncTime_subset _ m)
  have hinjI₂ : InjOn (η₂ ω) (Icc 0 T₂) := hi₂.mono (Icc_truncTime_subset _ m)
  have hdense : ∀ a c : ℝ≥0, a < c → c ≤ T₁ → ∃ s ∈ Ioo a c, η₁ ω s ∈ H := fun a c hac hcT =>
    Restart.IsGeneratingTrace.exists_mem_H_add ht₁ hp₁.2.2.2.1 hp₁.1 hac
      ((ENNReal.coe_le_coe.2 hcT).trans (coe_truncTime_le _ m))
  obtain ⟨r₁, r₂, σ₁, σ₂, s₀, f, hq₁T, hq₂T, hσs₀, hs₀q, hσ₂q, hfc, hfa, hfσ, hfq, hfeq, hover, hs₀H⟩ :=
    exists_rat_reverseArc hcont₁ hcont₂ hinjI₁ hinjI₂ hdense hrev
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  -- the stops are strictly available and below the cap
  have hTle : ∀ ζ : ℝ≥0∞, ((truncTime ζ m : ℝ≥0) : ℝ≥0∞) = min ζ (((m : ℝ≥0)) : ℝ≥0∞) := fun ζ => by
    rw [coe_truncTime, ENNReal.coe_natCast]
  have hq₁min : (q₁ : ℝ≥0∞) ≤ min (ζ₁ ω) ((m : ℝ≥0) : ℝ≥0∞) := by
    rw [← hTle]; exact ENNReal.coe_le_coe.2 hq₁T.le
  have hq₂min : (q₂ : ℝ≥0∞) ≤ min (ζ₂ ω) ((m : ℝ≥0) : ℝ≥0∞) := by
    rw [← hTle]; exact ENNReal.coe_le_coe.2 hq₂T.le
  have hq₁ζ : (q₁ : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_lt_coe.2 hq₁T).trans_le (coe_truncTime_le _ m)
  have hq₂ζ : (q₂ : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_lt_coe.2 hq₂T).trans_le (coe_truncTime_le _ m)
  have hq₁m : q₁ ≤ (m : ℝ≥0) := by
    have := hq₁min.trans (min_le_right _ _)
    exact_mod_cast this
  have hq₂m : q₂ ≤ (m : ℝ≥0) := by
    have := hq₂min.trans (min_le_right _ _)
    exact_mod_cast this
  -- the chart geometry of the reverse arc
  obtain ⟨s, hsI, hsH, F, hFne, hF, y₁, y₂, hy₁, hy₂, hf₁, hf₂, hL⟩ :=
    hgeom (η₁ ω) (η₂ ω) x₁ x₂ hx (fun t => W₁ t ω) (fun t => W₂ t ω) (ζ₁ ω) (ζ₂ ω) ht₁ hp₁.2.2.2.1 hp₁.1 ht₂
      hp₂.2.2.2.1 hp₂.1 hi₁ hi₂ q₁ q₂ σ₁ σ₂ s₀ f hq₁ζ hq₂ζ hσs₀ hs₀q hσ₂q hfc hfa hfσ hfq hfeq hover hs₀H
  have := hFne
  obtain ⟨ρ, hρ, hagree⟩ := local_agree_of_reverseArc hcont₁ hcont₂ hinjI₁ hinjI₂ hq₁T.le hq₂T.le hfc hfa hfσ hfq
    hfeq hover hsI
  -- the pathwise sets
  have hA₁ω : explored ηs (fun i _ => stop₁ r₁ i) ω = η₁ ω '' Icc 0 q₁ ∩ H := by
    rw [hA₁, image_capped_eq ha₁ hq₁min]
  have hA₂ω : explored ηs (fun i _ => stop₂ r₂ i) ω = η₂ ω '' Icc 0 q₂ ∩ H := by
    rw [hA₂, image_capped_eq ha₂ hq₂min]
  have hUω : explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω =
      (η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H) := by
    rw [← explored_const_union (stop₁ r₁) (stop₂ r₂) ω, hA₁ω, hA₂ω]
  have hsI' : s ∈ Icc σ₁ q₁ := Ioo_subset_Icc_self hsI
  have hσI : σ₁ ∈ Icc σ₁ q₁ := ⟨le_rfl, hsI'.1.trans hsI'.2⟩
  have hfs : f s < q₂ := hfσ ▸ hfa hσI hsI' hsI.1
  have hz₂ : η₂ ω (f s) = η₁ ω s := hfeq s hsI'
  have hz₀₁ : η₁ ω s ∈ η₁ ω '' Icc 0 q₁ ∩ H := ⟨⟨s, ⟨zero_le, hsI.2.le⟩, rfl⟩, hsH⟩
  have hz₀₂ : η₁ ω s ∈ η₂ ω '' Icc 0 q₂ ∩ H := ⟨⟨f s, ⟨zero_le, hfs.le⟩, hz₂⟩, hsH⟩
  have hsub₂₁ : (η₂ ω '' Icc 0 q₂ ∩ H) ∩ ball (η₁ ω s) ρ ⊆ η₁ ω '' Icc 0 q₁ ∩ H := by
    rintro z ⟨⟨hz, hzH⟩, hzb⟩
    have : z ∈ η₂ ω '' Icc 0 q₂ ∩ ball (η₁ ω s) ρ := ⟨hz, hzb⟩
    rw [← hagree] at this
    exact ⟨this.1, hzH⟩
  have hsub₁₂ : (η₁ ω '' Icc 0 q₁ ∩ H) ∩ ball (η₁ ω s) ρ ⊆ η₂ ω '' Icc 0 q₂ ∩ H := by
    rintro z ⟨⟨hz, hzH⟩, hzb⟩
    have : z ∈ η₁ ω '' Icc 0 q₁ ∩ ball (η₁ ω s) ρ := ⟨hz, hzb⟩
    rw [hagree] at this
    exact ⟨this.1, hzH⟩
  -- Proposition 3.8 at the point
  obtain ⟨ua, hua, huar, hual⟩ := hpa r₁ r₂
  obtain ⟨ub, hub, hubr, hubl⟩ := hpb r₁ r₂
  rw [hUω] at hua huar hual hub hubr hubl
  rw [hA₁ω, hA₂ω] at hual hubl
  have hla := hual (η₁ ω s) (Or.inl hz₀₁) ⟨ρ, hρ, hsub₂₁⟩
  have hlb := hubl (η₁ ω s) (Or.inl hz₀₂) ⟨ρ, hρ, hsub₁₂⟩
  -- harmonic representatives of the two single-prefix means
  obtain ⟨v₁, hv₁, hv₁r⟩ := hr₁ r₁
  obtain ⟨v₂, hv₂, hv₂r⟩ := hr₂ r₂
  have hO : IsOpen (H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H))) := by
    rw [← hUω]
    exact isOpen_H_diff_explored_of_frozen (fun i => hc i ω) (fun i => hfr i ω)
  have hO₁ : H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H)) ⊆ H \ explored ηs (fun i _ => stop₁ r₁ i) ω := by
    rw [hA₁ω]; exact sdiff_subset_sdiff_right subset_union_left
  have hO₂ : H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H)) ⊆ H \ explored ηs (fun i _ => stop₂ r₂ i) ω := by
    rw [hA₂ω]; exact sdiff_subset_sdiff_right subset_union_right
  have h12 := tendsto_sub_of_union_means hO hO₁ hO₂ hv₁ hv₁r hv₂ hv₂r hua huar hub hubr hla hlb
  -- the approach lies off the union
  have hfillsub : ∀ {K : Set ℂ}, H \ fillH K ⊆ H \ (K ∩ H) := fun {K} z hz =>
    ⟨hz.1, fun hzK => hz.2 ⟨hzK.2, Or.inl (subset_closure hzK.1)⟩⟩
  have hFO : F ≤ 𝓝[H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H))] (η₁ ω s) := by
    refine hF.trans (nhdsWithin_mono _ ?_)
    rw [← union_inter_distrib_right]
    exact hfillsub
  have hF₁ : F ≤ 𝓝[H \ fillH (η₁ ω '' Icc 0 q₁)] (η₁ ω s) :=
    hF.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_left)))
  have hF₂ : F ≤ 𝓝[H \ fillH (η₂ ω '' Icc 0 q₂)] (η₂ ω (f s)) := by
    rw [hz₂]
    exact hF.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_right)))
  -- the single-path side heights
  rw [hA₁ r₁ ω] at hv₁ hv₁r
  rw [hA₂ r₂ ω] at hv₂ hv₂r
  have h₁ := (hn₁ r₁ hq₁m hq₁ζ v₁ hv₁ hv₁r s hsI.2 hsH F hFne hF₁ y₁ hf₁).1 hy₁
  have h₂ := (hn₂ r₂ hq₂m hq₂ζ v₂ hv₂ hv₂r (f s) hfs (hz₂ ▸ hsH) F hFne hF₂ y₂ hf₂).2 hy₂
  exact sleLambda_sub_ne hκ hκ4 hθ (eq_of_side_limits (h12.mono_left hFO) hL h₁ h₂)

end Assembly

end Sec7

end InteractingSLE
