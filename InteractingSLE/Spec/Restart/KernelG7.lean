/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.KernelFlow
import InteractingSLE.Spec.Supplement.G7Restart

/-!
# The retained-pair restart kernel (Lemma G7) from the general restart kernel

Packet PROVE-RESTARTKERNEL. PROVE-G7B reduced Lemma G7 to the named input `Supp7.RetainedKernelClockStatement`: a
canonical space, a retained kernel `K` over a datum `β = (word, first tip position)`, under which the chart field is a
GFF with the word and the two chart paths are flow lines (the first from the tip position, the second from `0`), and
almost surely at an ordinary retained pair the kernel coordinates of the canonical restart variable are the canonical
chart field and agree with the canonical relative capacity clocks `γᵢ` up to their stops `Vᵢ`.

Here the kernel part is proved by the general restart kernel (`Kernel.lean`, `KernelFlow.lean`):

* the canonical space is `RestartSpace`; the restart variable is `X = (Hc, F₁(β, Hc), F₂((β.1, 0), Hc))`, the chart
  field together with the **canonical flow codes of the chart field** (G7B's caveat (d): the coordinates beyond the
  stops are chosen by a measurable flow-line map of the chart field, "determination");
* `K` is the conditional law of `X` given `β` on `M`; (R1) gives the GFF, and the continuation coordinates of `X` are
  the canonical flows *by construction*, so `ae_isFlowLine_of_codeMatch` gives both flow lines under `K c`.

What remains is the named input **`RetainedCondDetStatement`**, a statement about `P` only (no kernel): a σ-algebra
`𝒢` (the retained histories), a `𝒢`-measurable datum `β` with sorted word and positive tip position on a `𝒢`-event
`M`, (R1) — the conditional characteristic functional of the chart field given `𝒢` is the Gaussian one of the word on
`M` — and almost surely at an ordinary retained pair: `ω ∈ M`, the outer word (`IsRetainedWord`), and **(Det)**: for
any canonical flow codes `F₁`, `F₂`, each canonical clock `γᵢ` is, up to its stop `Vᵢ`, the decoded canonical flow of
the chart field (W8's proof, p. 541: "Universal finite-force determination now identifies each actual conditional
future … as the canonical flow of the same conditional field").

## Main results

* `RetainedCondDetStatement` (named input);
* **`retainedKernelClockStatement_of_condDet`**: `FlowCodeStatement → RetainedCondDetStatement →
  Supp7.RetainedKernelClockStatement`;
* `retainedPairRestartStatement_of_condDet`: Lemma G7's `RetainedPairRestartStatement` (with G7B's clocks).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

open LQGMetric Supp7

/-- **Named input: the retained pair's conditional field, outer word and determination identity** (Lemma G7, pp.
497–498; Theorem W8's proof, pp. 539–541; Aux. lemmas 85–86 for the word). Binders of
`Supp7.RetainedKernelClockStatement` (two flow lines, retained data `d`, the canonical relative capacity clocks
`γᵢ`, `Vᵢ`), and any canonical flow codes `F₁` (angle `θ₁`) and `F₂` (angle `θ₂`). There are a sub-σ-algebra `𝒢`, a
`𝒢`-event `M` and a `𝒢`-measurable datum `β = (word, tip position)` such that:
* on `M` the word is sorted and the tip position is positive;
* (R1) on `M`, conditionally on `𝒢`, the chart field has the Gaussian characteristic functional of the word;
* almost surely at an ordinary retained pair: `ω ∈ M`, the outer word `IsRetainedWord` holds, and (Det) each
  canonical clock `γᵢ` agrees up to its stop `Vᵢ` with the decoded canonical flow code of the chart field (from the
  tip position for the first path, from `0` for the second), whose lifetime is at least `Vᵢ`. -/
def RetainedCondDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (V₁ V₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) →
      (∀ t, Measurable fun ω => γ₂ ω t) → Measurable V₁ → Measurable V₂ →
      (∀ ω, ContinuousOn (γ₁ ω) {s | (s : ℝ≥0∞) ≤ V₁ ω}) → (∀ ω, ContinuousOn (γ₂ ω) {s | (s : ℝ≥0∞) ≤ V₂ ω}) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        IsCanonRetClock d η₁ η₂ ζ₁ ζ₂ γ₁ γ₂ V₁ V₂ ω) →
    ∀ F₁ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsFlowCode κ θ₁ F₁ → IsFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord × ℝ),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).1.IsSorted ∧ 0 < (β ω).2) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω).1 φ) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        V₁ ω ≤ (F₁ (β ω, hd.chartField κ h ω)).2 ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → γ₁ ω s = decPath (F₁ (β ω, hd.chartField κ h ω)) s) ∧
        V₂ ω ≤ (F₂ (((β ω).1, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → γ₂ ω s = decPath (F₂ (((β ω).1, 0), hd.chartField κ h ω)) s

/-- **Lemma G7's retained kernel from the general restart kernel**: canonical flow codes and the retained pair's
conditional field, outer word and determination identity give `Supp7.RetainedKernelClockStatement`. -/
theorem retainedKernelClockStatement_of_condDet (hF : FlowCodeStatement)
    (hD : RetainedCondDetStatement.{u}) : RetainedKernelClockStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁ hV₂ hc₁ hc₂ hcanon
  obtain ⟨F₁, hF₁⟩ := hF κ θ₁ hκ hκ4
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁
      hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  set Hc := hd.chartField κ h with hHc
  have hHcm : Measurable Hc := hd.measurable_chartField κ hh.1
  set X : Ω → RestartSpace := fun ω =>
    (Hc ω, F₁ (((β ω).1, (β ω).2), Hc ω), F₂ (((β ω).1, 0), Hc ω)) with hXdef
  have hXm : Measurable X := by
    refine hHcm.prodMk ((hF₁.1.comp ?_).prodMk (hF₂.1.comp ?_))
    · exact ((measurable_fst.comp hβm).prodMk (measurable_snd.comp hβm)).prodMk hHcm
    · exact ((measurable_fst.comp hβm).prodMk measurable_const).prodMk hHcm
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hco := isRestartCoordinates_restartSpace
  -- (R1) under the kernel
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word 𝒢.2 hM hβ measurable_fst
    (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).1) hXm (H := RestartSpace.field)
    measurable_fst hlaw hR1
  -- the two continuations are the canonical flows of the chart field, by construction
  have hfl₁ := ae_isFlowLine_of_codeMatch hMm hβm hXm hlaw measurable_fst measurable_snd
    (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₁) hco.2.2.2.1 hco.2.1
    hco.2.2.2.2.2.1 hF₁ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hfl₂ := ae_isFlowLine_of_codeMatch hMm hβm hXm hlaw measurable_fst (x := fun _ => (0 : ℝ))
    measurable_const (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₂) hco.2.2.2.2.1
    hco.2.2.1 hco.2.2.2.2.2.2 hF₂ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hpos : ∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 :=
    (ae_map_iff (p := fun c : BoundaryWord × ℝ => 0 < c.2) hβm.aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).2
      ((ae_restrict_iff' hMm).2 (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).2))
  refine ⟨RestartSpace, inferInstance, RestartSpace.field, RestartSpace.path₁, RestartSpace.path₂,
    RestartSpace.life₁, RestartSpace.life₂, M, β, X, K, hco, hMm, hβm, hXm, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hgff, hfl₁, hfl₂, hpos] with c ⟨_, hcg⟩ h1 h2 hc
    exact ⟨hc, hcg, h1, h2⟩
  · filter_upwards [hpath] with ω hω hord
    obtain ⟨hωM, hw, hV₁, he₁, hV₂, he₂⟩ := hω hord
    exact ⟨hωM, rfl, hV₁, fun s hs => (he₁ s hs).symm, hV₂, fun s hs => (he₂ s hs).symm, hw⟩

/-- **Lemma G7's `RetainedPairRestartStatement` from the general restart kernel** (with PROVE-G7B's clocks). -/
theorem retainedPairRestartStatement_of_condDet (hF : FlowCodeStatement)
    (hD : RetainedCondDetStatement.{u}) : RetainedPairRestartStatement.{u} :=
  retainedPairRestartStatement_of_clock (retainedKernelClockStatement_of_condDet hF hD)

end Restart

end InteractingSLE
