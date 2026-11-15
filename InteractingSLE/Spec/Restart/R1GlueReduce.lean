/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1GlueMain
import InteractingSLE.Spec.Restart.KernelClock
import InteractingSLE.Impl.PiecewiseConstant

/-!
# `FirstContactKernelClockStatement` with (R1)'s locality, gluing and chart measurability supplied

Packet PROVE-RESTART-CPL7. PROVE-RESTART-CPL5 reduced the D.5 restart interface to `FirstContactKernelClockStatement`:
(R1) and (R2′) with their σ-algebra `𝒢`, meeting branch `M`, datum `β` and kernel `K`. Here `𝒢`, `M` and (R1) are
supplied (`R1GlueMain.lean`): `𝒢 = retSigma d P` (the two labelled histories stopped at the first contact, completed by
null sets), `M = meetSet d` (a first contact with two nonempty continuations), and (R1) on `M` from Lemma 7.5,
Lemma 7.7, Aux. lemma 56 at first entrances and Lemma 7.8's mean identification on every box. What remains is the
named input `FirstContactWordKernelStatement`:

* **Lemma 7.8's word and mean formula**: a `𝒢`-measurable datum `β`, sorted on `M`, whose word mean is the chart
  transport of the conditional mean on every box (`IsBoxMeanIdentification`);
* **the restart kernel (R2′)**: a kernel `K` disintegrating `(Hc, γ₁, U₁, γ₂, U₂, Y)` over `β` on `M`, under which the
  chart paths are flow lines of the chart field (Lemma 7.8's continuation assertion, W8).

## Main results

* `FirstContactWordKernelStatement`;
* **`firstContactKernelClockStatement_of_word`**: `Lemma75Statement → Lemma77Statement →
  RetainedRangeEntranceStatement →
  FirstContactWordKernelStatement → FirstContactKernelClockStatement`;
* `firstContactRestartLimStatement_of_word`: the D.5 interface `Theorem15D5.FirstContactRestartLimStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

/-- **Named input: Lemma 7.8's word and mean formula, and the restart kernel (R2′)** (Lemma 7.8, pp. 290–295; Theorem
W8, pp. 538–541). Binders of `FirstContactKernelClockStatement` (two flow lines, measurable pair data `d` agreeing with
them, the canonical chart field `Hc`, measurable versions of the canonical capacity-time chart paths), and a bounded
harmonic extension `u₀` of the boundary data: there are a datum `β`, measurable for the retained σ-algebra
`retSigma d P` and sorted on the meeting branch `meetSet d`, satisfying Lemma 7.8's mean identification on every box
(`IsBoxMeanIdentification`), a measurable extra coordinate `Y` and a Markov kernel `K` disintegrating the restart
variable over `β` on `meetSet d`, under which the two chart paths are the flow lines of angles `θ₁`, `θ₂` of the chart
field with boundary data `β` ((R2′)). -/
def FirstContactWordKernelStatement : Prop :=
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
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∃ (β : Ω → BoundaryWord) (E : Type) (_ : MeasurableSpace E) (Y : Ω → E)
      (K : Kernel BoundaryWord (RestartSpace × E)),
      Measurable[retSigma d P] β ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) ∧
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β ∧ Measurable Y ∧ IsMarkovKernel K ∧
      (P.restrict (meetSet d)).map
          (fun ω => (β ω, (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω))) =
        (P.restrict (meetSet d)).map β ⊗ₘ K ∧
      ∀ᵐ c ∂(P.restrict (meetSet d)).map β,
        IsFlowLine κ c.fn c.jumps 0 θ₁ (K c) (fun s => s.1.field) (fun s => s.1.path₁) (fun s => s.1.life₁) ∧
        IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) (fun s => s.1.field) (fun s => s.1.path₂) (fun s => s.1.life₂)

/-- **`FirstContactKernelClockStatement` from the word-and-kernel input**: the retained σ-algebra, the meeting branch,
(R1) (Lemma 7.7's marked locality glued over the bounded boxes, the chart from the retained histories, Lemma 7.8's
conditional law in the chart) and the membership of the first contacts are proved. -/
theorem firstContactKernelClockStatement_of_word (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u})
    (hW : FirstContactWordKernelStatement.{u}) : FirstContactKernelClockStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae Hc hHc
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨β, E, mE, Y, K, hβ, hsort, hmean, hY, hK, hdis, hflow⟩ :=
    hW κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae Hc hHc γ₁ γ₂ U₁ U₂
      hγ₁ hγ₂ hU₁ hU₂ hcanon u₀ hu₀
  refine ⟨retSigma d P, meetSet d, β, E, mE, Y, K,
    ⟨retSigma_le P, hd.measurableSet_meetSet P, hβ, hsort, hY, fun φ => ?_, hK, hdis, hflow⟩,
    ae_mem_meetSet hζ₁ hζ₂ hae⟩
  subst hHc
  exact ae_condExp_cexp_chartField_eq_gaussCF_meetSet hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
    hu₀ hβ hmean φ

/-- **The D.5 restart-with-limits interface from the word-and-kernel input** (with CPL3–CPL5's reductions). -/
theorem firstContactRestartLimStatement_of_word (hA : Theorem15.Aux25Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hW : FirstContactWordKernelStatement.{u}) :
    Theorem15D5.FirstContactRestartLimStatement.{u} :=
  firstContactRestartLimStatement_of_clock hA hL77 (firstContactKernelClockStatement_of_word hL75 hL77 hA56 hW)

end Restart

end InteractingSLE
