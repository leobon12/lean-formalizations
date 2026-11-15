/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.KernelFlow
import InteractingSLE.Spec.Restart.R1GlueReduce
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# The first-contact restart kernel (R2′) from the general restart kernel

Packet PROVE-RESTARTKERNEL. PROVE-RESTART-CPL7 reduced the first-contact restart to the named input
`Restart.FirstContactWordKernelStatement`: Lemma 7.8's word with its mean formula on every box, and the restart kernel
(R2′) — a Markov kernel disintegrating the restart variable `(mk' Hc γ₁ U₁ γ₂ U₂, Y)` over the word on the meeting
branch,
under which the chart paths are the angle-`θ₁`, angle-`θ₂` flow lines of the chart field from `0`.

Here the kernel (R2′) is proved by the general restart kernel (`KernelFlow.lean`): `K` is the conditional law of the
restart variable given the word on `meetSet d` (`Y` trivial); (R1) on `meetSet d` is CPL7's
`ae_condExp_cexp_chartField_eq_gaussCF_meetSet` (Lemma 7.5, Lemma 7.7, Aux. lemma 56 at first entrances — now proved,
`WholeField.retainedRangeEntranceStatement` — and the box mean identification); and the flow lines under `K c` follow
from `ae_isFlowLine_of_codeMatch` once the canonical clocks match the canonical flow codes of the chart field.

What remains is the named input **`FirstContactCondDetStatement`**, about `P` only: Lemma 7.8's word with its box
mean identification (as in `FirstContactWordKernelStatement`), and **(Det)**: for any canonical flow codes `F₁, F₂`,
almost surely on the meeting branch each canonical chart path `γᵢ` with its lifetime `Uᵢ` is the decoded canonical
flow code of the chart field with the word (W8's proof, p. 541).

## Main results

* `FirstContactCondDetStatement` (named input);
* **`firstContactWordKernelStatement_of_condDet`**: `Lemma75Statement → Lemma77Statement → FlowCodeStatement →
  FirstContactCondDetStatement → FirstContactWordKernelStatement`;
* `firstContactKernelClockStatement_of_condDet`: the same for CPL5's `FirstContactKernelClockStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

open LQGMetric

/-- **Named input: Lemma 7.8's word and mean formula, and the determination identity of the continuations**
(Lemma 7.8, pp. 290–295; Theorem W8's proof, pp. 539–541). Binders of `FirstContactWordKernelStatement`, and any
canonical flow codes `F₁` (angle `θ₁`), `F₂` (angle `θ₂`). There is a datum `β`, measurable for the retained
σ-algebra `retSigma d P` and sorted on the meeting branch `meetSet d`, satisfying Lemma 7.8's mean identification on
every box, such that almost surely on `meetSet d` each canonical chart path `γᵢ` with lifetime `Uᵢ` is the decoded
canonical flow code of the chart field with the word `β` from the seed `0` ((Det)). -/
def FirstContactCondDetStatement : Prop :=
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
    ∀ F₁ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsFlowCode κ θ₁ F₁ → IsFlowCode κ θ₂ F₂ →
    ∃ β : Ω → BoundaryWord,
      Measurable[retSigma d P] β ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) ∧
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β ∧
      ∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsCodeMatch (F₁ ((β ω, 0), Hc ω)) (γ₁ ω) (U₁ ω) ∧ IsCodeMatch (F₂ ((β ω, 0), Hc ω)) (γ₂ ω) (U₂ ω)

/-- A path that matches a code is continuous on its lifetime. -/
theorem IsCodeMatch.continuousOn {p : (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    {U : ℝ≥0∞} (hm : IsCodeMatch p γ U) : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ U} := by
  have hc := continuousOn_decPath p
  rw [← hm.1] at hc
  exact hc.congr fun t ht => hm.2 t ht

/-- The coded restart point of a matched path matches the same code (first path). -/
theorem isCodeMatch_path₁_mk' {p : (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞} {γ₁ γ₂ : ℝ≥0 → ℂ}
    {U₁ U₂ : ℝ≥0∞} (f : LQGMetric.DistOn upperHalfPlaneOpens) (hm : IsCodeMatch p γ₁ U₁) :
    IsCodeMatch p (RestartSpace.mk' f γ₁ U₁ γ₂ U₂).path₁ (RestartSpace.mk' f γ₁ U₁ γ₂ U₂).life₁ :=
  ⟨hm.1, fun t ht => by
    rw [RestartSpace.path₁_mk' f hm.continuousOn γ₂ U₂ ht]
    exact hm.2 t ht⟩

/-- The coded restart point of a matched path matches the same code (second path). -/
theorem isCodeMatch_path₂_mk' {p : (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞} {γ₁ γ₂ : ℝ≥0 → ℂ}
    {U₁ U₂ : ℝ≥0∞} (f : LQGMetric.DistOn upperHalfPlaneOpens) (hm : IsCodeMatch p γ₂ U₂) :
    IsCodeMatch p (RestartSpace.mk' f γ₁ U₁ γ₂ U₂).path₂ (RestartSpace.mk' f γ₁ U₁ γ₂ U₂).life₂ :=
  ⟨hm.1, fun t ht => by
    rw [RestartSpace.path₂_mk' f γ₁ U₁ hm.continuousOn ht]
    exact hm.2 t ht⟩

/-- **The first-contact restart kernel (R2′) from the general restart kernel**: Lemma 7.5, Lemma 7.7, canonical flow
codes and the word-and-determination input give `FirstContactWordKernelStatement` (Aux. lemma 56 at first entrances is
`WholeField.retainedRangeEntranceStatement`). -/
theorem firstContactWordKernelStatement_of_condDet (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hF : FlowCodeStatement) (hD : FirstContactCondDetStatement.{u}) :
    FirstContactWordKernelStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae Hc hHc
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon u₀ hu₀
  obtain ⟨F₁, hF₁⟩ := hF κ θ₁ hκ hκ4
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨β, hβ, hsort, hmean, hdet⟩ := hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae Hc hHc γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon u₀ hu₀ F₁ F₂ hF₁ hF₂
  have hR1 := fun φ => ae_condExp_cexp_chartField_eq_gaussCF_meetSet hL75 hL77
    WholeField.retainedRangeEntranceStatement hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hβ hmean φ
  subst hHc
  have hβm : Measurable β := hβ.mono (retSigma_le P) le_rfl
  have hM := hd.measurableSet_meetSet P
  have hMm : MeasurableSet (meetSet d) := retSigma_le P _ hM
  have hHcm : Measurable (hd.chartField κ h) := hd.measurable_chartField κ hh.1
  set X : Ω → RestartSpace × Unit := fun ω =>
    (RestartSpace.mk' (hd.chartField κ h ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), ()) with hXdef
  have hXm : Measurable X :=
    (RestartSpace.measurable_mk' hHcm hγ₁ hγ₂ hU₁ hU₂).prodMk measurable_const
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P (meetSet d) hβm hXm
  have hco := isRestartCoordinates_restartSpace
  have hHm : Measurable fun s : RestartSpace × Unit => s.1.field := measurable_fst.comp measurable_fst
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word (retSigma_le P) hM hβ (w := fun c => c)
    measurable_id hsort hXm (H := fun s : RestartSpace × Unit => s.1.field) hHm hlaw hR1
  have hfl₁ := ae_isFlowLine_of_codeMatch hMm hβm hXm hlaw (w := fun c => c) measurable_id
    (x := fun _ => (0 : ℝ)) measurable_const hHm (Γ := fun s : RestartSpace × Unit => s.1.path₁)
    (fun t => (hco.2.2.2.1 t).comp measurable_fst) (hco.2.1.comp measurable_fst)
    (fun s => hco.2.2.2.2.2.1 s.1) hF₁ hgff (by
      filter_upwards [hdet] with ω hω hωM
      exact isCodeMatch_path₁_mk' _ (hω hωM).1)
  have hfl₂ := ae_isFlowLine_of_codeMatch hMm hβm hXm hlaw (w := fun c => c) measurable_id
    (x := fun _ => (0 : ℝ)) measurable_const hHm (Γ := fun s : RestartSpace × Unit => s.1.path₂)
    (fun t => (hco.2.2.2.2.1 t).comp measurable_fst) (hco.2.2.1.comp measurable_fst)
    (fun s => hco.2.2.2.2.2.2 s.1) hF₂ hgff (by
      filter_upwards [hdet] with ω hω hωM
      exact isCodeMatch_path₂_mk' _ (hω hωM).2)
  refine ⟨β, Unit, inferInstance, fun _ => (), K, hβ, hsort, hmean, measurable_const, hK, hlaw, ?_⟩
  filter_upwards [hfl₁, hfl₂] with c h1 h2
  exact ⟨h1, h2⟩

/-- **CPL5's `FirstContactKernelClockStatement` from the general restart kernel** (through CPL7's reduction). -/
theorem firstContactKernelClockStatement_of_condDet (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hF : FlowCodeStatement) (hD : FirstContactCondDetStatement.{u}) :
    FirstContactKernelClockStatement.{u} :=
  firstContactKernelClockStatement_of_word hL75 hL77 WholeField.retainedRangeEntranceStatement
    (firstContactWordKernelStatement_of_condDet hL75 hL77 hF hD)

end Restart

end InteractingSLE
