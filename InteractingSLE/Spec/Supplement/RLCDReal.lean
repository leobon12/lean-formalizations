/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCMain
import InteractingSLE.Spec.Supplement.RLCDG3

/-!
# The real joint chart at a retained pair (the chart's injectivity over untouched real points)

Packet PROVE-RLC-D, part (4) (i). Source: Lemma G7's proof (supplement p. 497: "An untouched original-real point has a
trace-free upper half-neighborhood […] The map `φ` extends analytically by reflection across such an interval") and the
regular-point clause of the first-contact chart (Aux. 80).

PROVE-RLC-C's chart-level named input `RLC.RetainedChartRealCompletionStatement` asks, at an ordinary retained pair,
for the joint chart `RLC.IsRealJointChart`: the conjuncts of PROVE-RLC-A's `RLC.IsJointRetainedChart` that the
real-contact argument uses, **plus** the injectivity of the chart over genuine original-real points
(`ψ y = ψ y'`, `ψ y` real and off the retained union `A` ⇒ `y = y'`). RLC-A's carrier dropped that clause. Here it is
re-exposed from the retained chart of the restart: every point off the prefixes is a regular chart point
(`Supp7.isChartRegularPoint_of_notMem`), so its fibre in `ℍ̄` is a single point (`Supp7.eq_of_inv_eq_of_notMem`).

* `RealJointChartStatement`: the restart carrier (canonical space, kernel, restart coordinates, the datum's GFF and
  flow lines) with, almost surely at an ordinary retained pair, one chart `ψ` that is a real joint chart and in which
  the datum's word has the canonical heights on the exposed sides (`Supp7.IsRetainedWord`);
* **`realJointChartStatement_of_restart`** (from `Supp7.RetainedPairRestartStatement`) and
  **`realJointChartStatement_of_param`** (from Theorems 1.2 (param), 1.3 and PROVE-CONDDET's two-tip input; R43/R48:
  downstream of Theorem 1.2, for Theorem 1.5 only).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart

/-- A real point lies in the closed upper half-plane. -/
theorem ofReal_mem_Hbar (y : ℝ) : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp

/-- **The restart carrier with the real joint chart**: `RLC.JointRetainedChartStatement` with, at an ordinary retained
pair, one chart `ψ` that is a real joint chart (`IsRealJointChart`: in particular injective over genuine original-real
points) and in which the datum's word has the canonical heights on the exposed sides (`Supp7.IsRetainedWord`). -/
def RealJointChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H₀ Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H₀ c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H₀ Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H₀ Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        ω ∈ M ∧ ∃ ψ : ℂ → ℂ,
          IsRealJointChart (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r (Γ₁ (X ω)) (Γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω)) ψ ∧
          IsRetainedWord κ θ₁ θ₂ (η₁ ω) u (η₂ ω) r ψ (β ω).1

/-- **The real joint chart from the retained-pair restart** (`Supp7.RetainedPairRestartStatement`): the proof of
`RLC.jointRetainedChartStatement_of_restart`, keeping the regular-point clause of the retained chart, which gives the
injectivity of the chart over every point off the retained union (`Supp7.eq_of_inv_eq_of_notMem`). -/
theorem realJointChartStatement_of_restart (hR : RetainedPairRestartStatement.{u}) :
    RealJointChartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  refine ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, ?_⟩
  filter_upwards [hpath, hag] with ω hω hagω hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, -, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩, hword⟩ :=
    hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  refine ⟨hMω, d.inv ω, ⟨?_, ?_, hC.continuousOn_inv, hC.2.2.2.2.2.2.2.2.2.1, ?_,
    ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, fun s hs => ⟨hpth₁ s hs, hH₁ s hs⟩⟩,
    ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, fun s hs => ⟨hpth₂ s hs, hH₂ s hs⟩⟩, ?_⟩, hword⟩
  · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
  · rw [← htip]; exact hC.inv_zero hg.2.2.2.2.2.1
  · intro y y' he _ hA
    have hK : d.inv ω (y : ℂ) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
      rw [prefixSet_congr_Icc e₁ e₂]; exact hA
    exact ofReal_injective (eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1
      (ofReal_mem_Hbar y) (ofReal_mem_Hbar y') he hK)

/-- **The real joint chart from Theorems 1.2 (param), 1.3 and PROVE-CONDDET's two-tip P-side input**
`Restart.RetainedCanonCondDetStatement` (R43/R48: downstream of Theorem 1.2; for Theorem 1.5 only). -/
theorem realJointChartStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetStatement.{u}) :
    RealJointChartStatement.{u} :=
  realJointChartStatement_of_restart
    (retainedPairRestartStatement_of_clock (retainedKernelClockStatement_of_param h12p h13 hD))

end RLC

end InteractingSLE
