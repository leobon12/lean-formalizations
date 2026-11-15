/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DChart
import InteractingSLE.Spec.Supplement.G7Measurable

/-!
# Supplement §9: Lemma W2 (both orientations) and W2a's corner case, from Lemma 7.7 and the joint G7 carrier

Packet PROVE-W5-REST. Sources: Lemma W2 and its proof (`source/spec/p529-576.md` L57–L68, pp. 530–531), Lemma W2a's
proof (L130–L139, p. 533), Lemma G7 (`source/spec/p481-528.md` L403–L422, pp. 497–498).

**W2's proof** (p. 531): "Intersect the marked-kernel, protected-collar and finite-word mean identities over every
rational original own stopping pair, before selecting the pair `(r, s)` of W1. At that pair, joint activity and the
proper completions give the canonical finite word […] Condition only on this retained rational pair. For each path
take the own stopping rule which is the minimum of its original available lifetime, […] and its first new contact
with the retained old curve range. […] G7 identifies both actual fresh stopped paths with the canonical flows of the
same conditional finite-word field, in their actual joint field–path law. Their current seeds satisfy `w_β < w_α`
and `θ₁ < θ₂ + π`. Lemma 7.7 consequently gives a common first contact whenever the full stopped histories have a
contact. They contain both `p` and `q`. Their common first point would therefore have first parameter at most `a`
and second parameter at most `v`, contradicting (W1.1). […] Integrate over the retained rational datum and then take
the countable union over all such pairs."

This file formalizes that argument. The conditional law at a retained pair is the named input
`JointRetainedPairStatement` (Lemma G7 applied to both current tips in one common chart; see its docstring); the
first contact is `Supp10.Lemma77Statement` (Theorem 1.5's interface 2, used at universe `0` on the canonical
space). Everything else is proved: the dyadic interior cuts and the ordinary retained pair (`S9DCuts`, with Aux. 90
proved in `S9DActivity`), the measurable chart event (`S9DChart`), the integration over the kernel, and the
countable union.

## Main results

* `ae_not_isFreshLowerRectangle`: almost surely, no dyadic ordinary retained pair has a fresh lower rectangle.
* `w2Statement_of_inputs : … → Supp9.W2Statement`, `w2SwapStatement_of_inputs`, `w2aCornerStatement_of_inputs`.
* `w2aStatement_of_inputs'`: Lemma W2a from Aux. 25, W0a, W0b, Lemma 7.7 and the joint carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9D

open Sec2.Assembly Restart

/-! ### The joint G7 carrier -/

/-- **The pathwise part of Lemma G7 for both current tips in one chart** (Lemma G7, pp. 497–498; Lemma W2's proof,
p. 531). With `D = activeDomain η₁ u η₂ r` and the retained union `A = η₁([0, u]) ∪ η₂([0, r])`:
* `φ` is a common active chart of `D` (at the second tip), `ψ` its inverse on `ℍ` (values off `ℍ` lie off `D`), and
  `H` is the field `h` in the chart (frozen `IsChartTransport`, `σ = 1`, `a = 0`, `k = χ`) for a continuous branch
  `lift` of `arg φ′`;
* for each path, a clock `cᵢ`, strictly increasing on the chart times `[0, σᵢ]`, `σᵢ ≤ Uᵢ`, maps them onto the
  physical continuation after the cut up to and including its first new contact with `A` ("stop on its first new
  contact with the retained curve range `A` […] with its original stopping rule recovered in relative capacity"), and
  `ηᵢ ∘ cᵢ = ψ ∘ Γᵢ` there;
* the chart separates the fresh points: a common physical point of the two continuations that is off `A` has one
  chart preimage (an untouched point off the retained union has a single prime end; this also follows from the chart
  limits along `D` of `Restart.ChartDataLim`). -/
def IsJointRetainedContinuation (κ : ℝ) (h H : LQGMetric.DistOn upperHalfPlaneOpens) (η₁ : ℝ≥0 → ℂ)
    (ζ₁ : ℝ≥0∞) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (r : ℝ≥0) (Γ₁ Γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) :
    Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₁ c₂ : ℝ≥0 → ℝ≥0) (σ₁ σ₂ : ℝ≥0∞),
    IsActiveChart (activeDomain η₁ u η₂ r) (η₂ r) φ ∧
    BijOn ψ QuantumZipper.H (activeDomain η₁ u η₂ r) ∧ (∀ w ∈ QuantumZipper.H, φ (ψ w) = w) ∧
    (∀ w ∉ QuantumZipper.H, ψ w ∉ activeDomain η₁ u η₂ r) ∧
    ContinuousOn lift (activeDomain η₁ u η₂ r) ∧
    (∀ z ∈ activeDomain η₁ u η₂ r,
      deriv φ z = (‖deriv φ z‖ : ℂ) * Complex.exp (Complex.I * (lift z : ℂ))) ∧
    IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H ∧
    σ₁ ≤ U₁ ∧ StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ₁} ∧
    c₁ '' {s | (s : ℝ≥0∞) ≤ σ₁} =
      {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ₁ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η₁ x' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
    σ₂ ≤ U₂ ∧ StrictMonoOn c₂ {s | (s : ℝ≥0∞) ≤ σ₂} ∧
    c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} =
      {y | r ≤ y ∧ (y : ℝ≥0∞) ≤ ζ₂ ∧ ∀ y' : ℝ≥0, r < y' → y' < y → η₂ y' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ₁ → η₁ (c₁ s) = ψ (Γ₁ s)) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ₂ → η₂ (c₂ s) = ψ (Γ₂ s)) ∧
    ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ σ₁ → (s₂ : ℝ≥0∞) ≤ σ₂ → η₁ (c₁ s₁) = η₂ (c₂ s₂) →
      η₁ (c₁ s₁) ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r → Γ₁ s₁ = Γ₂ s₂

/-- **Named input: Lemma G7 for both current tips at a retained pair, as one kernel carrier** (specification
supplement §7.6, Lemma G7, pp. 497–498, applied to both tips as in the proof of Lemma W2, p. 531: "G7 identifies both
actual fresh stopped paths with the canonical flows of the same conditional finite-word field, in their actual joint
field–path law. Their current seeds satisfy `w_β < w_α`"; the canonical finite word is W2's "joint activity and the
proper completions give the canonical finite word by the outer-boundary argument and Aux. 57, 83, 85–86"). Setting of
`Supp9.W2Statement` (W5's flows: `x₂ ≤ x₁`, `θ₁ < θ₂`). For all own cutoffs `(u, r)`: a canonical space `S : Type`
with restart coordinates (chart field `H`, chart continuations `Γ₁`, `Γ₂`, relative lifetimes `U₁`, `U₂`), a
measurable event `M`, a measurable datum `β = (word, w)` and restart variable `X`, and a Markov kernel `K` with
* `K` the conditional law of `X` given `β` on `M`;
* for almost every datum `(c, w)`: `0 < w` (the prime-end order `w_β < w_α` of Aux. lemma 85, with the second tip at
  `0`), and under `K (c, w)` the chart field `H` is a GFF with datum `c`, `Γ₁` (lifetime `U₁`) is its angle-`θ₁` flow
  line from `w` and `Γ₂` (lifetime `U₂`) its angle-`θ₂` flow line from `0`;
* almost surely, at an ordinary retained pair `(u, r)` (`Supp7.IsOrdinaryRetainedPair`), `ω ∈ M` and the joint
  chart continuation `IsJointRetainedContinuation` holds for `X ω`.

It is the two-tip form of `Supp7.G7RetainedPairStatement` (one tip) and the retained-pair analogue of the
first-contact carrier `Restart.FirstContactRestartStatement`. **Not proved in Lean.** -/
def JointRetainedPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        ω ∈ M ∧ IsJointRetainedContinuation κ (h ω) (H (X ω)) (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r
          (Γ₁ (X ω)) (Γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω))

/-! ### The core: Lemma 7.7 at every dyadic retained pair -/

/-- **Pathwise: a fresh lower rectangle at a joint retained continuation is an empty chart lower rectangle at dyadic
corners.** The contacts `α(a) = β(t)`, `α(b) = β(v)` have chart times `s_a < s_b`, `s_v < s_t` and are chart contacts
(the chart separates fresh points off the retained union); a chart contact in `[0, a'] × [0, b']` for dyadic
`a' ∈ (s_a, s_b)`, `b' ∈ (s_v, s_t)` would be a physical contact in the empty rectangle `[u, b) × [r, t)`. -/
theorem exists_chartLowerRect_of_isFreshLowerRectangle {κ : ℝ} {h₀ H₀ : LQGMetric.DistOn upperHalfPlaneOpens}
    {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {u r : ℝ≥0} {Γ₁ Γ₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (hJ : IsJointRetainedContinuation κ h₀ H₀ α ζ₁ u β ζ₂ r Γ₁ Γ₂ U₁ U₂)
    (hF : IsFreshLowerRectangle α ζ₁ u β ζ₂ r) :
    ∃ n k n' k' N : ℕ, ChartLowerRect Γ₁ Γ₂ U₁ U₂ (dyad n k) (dyad n' k') N := by
  obtain ⟨φ, ψ, lift, c₁, c₂, σ₁, σ₂, -, -, -, -, -, -, -, hσ₁, hmono₁, himg₁, hσ₂, hmono₂, himg₂, hpath₁,
    hpath₂, hsep⟩ := hJ
  obtain ⟨a, t, b, v, hua, hab, hbζ, hrv, hvt, htζ, hp, hq, hf1, hf2, hno⟩ := hF
  have ha : a ∈ c₁ '' {s | (s : ℝ≥0∞) ≤ σ₁} := by
    rw [himg₁]
    exact ⟨hua.le, (ENNReal.coe_le_coe.2 hab.le).trans hbζ, fun x' h1 h2 => hf1 x' h1 (h2.trans hab)⟩
  have hb : b ∈ c₁ '' {s | (s : ℝ≥0∞) ≤ σ₁} := by
    rw [himg₁]
    exact ⟨(hua.trans hab).le, hbζ, fun x' h1 h2 => hf1 x' h1 h2⟩
  have hv : v ∈ c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} := by
    rw [himg₂]
    exact ⟨hrv.le, (ENNReal.coe_le_coe.2 hvt.le).trans htζ, fun y' h1 h2 => hf2 y' h1 (h2.trans hvt)⟩
  have ht : t ∈ c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} := by
    rw [himg₂]
    exact ⟨(hrv.trans hvt).le, htζ, fun y' h1 h2 => hf2 y' h1 h2⟩
  obtain ⟨sa, hsa, hca⟩ := ha
  obtain ⟨sb, hsb, hcb⟩ := hb
  obtain ⟨sv, hsv, hcv⟩ := hv
  obtain ⟨st, hst, hct⟩ := ht
  have hsab : sa < sb := (hmono₁.lt_iff_lt hsa hsb).1 (by rw [hca, hcb]; exact hab)
  have hsvt : sv < st := (hmono₂.lt_iff_lt hsv hst).1 (by rw [hcv, hct]; exact hvt)
  have hc1 : Γ₁ sa = Γ₂ st := hsep sa st hsa hst (by rw [hca, hct]; exact hp) (by rw [hca]; exact hf1 a hua hab)
  have hc2 : Γ₁ sb = Γ₂ sv := hsep sb sv hsb hsv (by rw [hcb, hcv]; exact hq)
    (by rw [hcb, hq]; exact hf2 v hrv hvt)
  obtain ⟨a', ⟨⟨n, k⟩, rfl⟩, ha'1, ha'2⟩ := exists_dyadSet_btwn hsab
  obtain ⟨b', ⟨⟨n', k'⟩, rfl⟩, hb'1, hb'2⟩ := exists_dyadSet_btwn hsvt
  obtain ⟨N, hN⟩ := exists_nat_ge (max sb st)
  have hsbN : sb ≤ (N : ℝ≥0) := (le_max_left _ _).trans hN
  have hstN : st ≤ (N : ℝ≥0) := (le_max_right _ _).trans hN
  refine ⟨n, k, n', k', N, ?_, ⟨sa, st, zero_le, ha'1.le, hb'2.le, hstN, (hsa : (sa : ℝ≥0∞) ≤ σ₁).trans hσ₁,
    (hst : (st : ℝ≥0∞) ≤ σ₂).trans hσ₂, hc1⟩, ⟨sb, sv, ha'2.le, hsbN, zero_le, hb'1.le,
    (hsb : (sb : ℝ≥0∞) ≤ σ₁).trans hσ₁, (hsv : (sv : ℝ≥0∞) ≤ σ₂).trans hσ₂, hc2⟩⟩
  rintro ⟨x, y, -, hxa', -, hyb', -, -, hxy⟩
  have hxσ : (x : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 (hxa'.trans ha'2.le)).trans hsb
  have hyσ : (y : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 (hyb'.trans hb'2.le)).trans hst
  have hxu : u ≤ c₁ x := by
    have : c₁ x ∈ c₁ '' {s | (s : ℝ≥0∞) ≤ σ₁} := mem_image_of_mem c₁ hxσ
    rw [himg₁] at this
    exact this.1
  have hyr : r ≤ c₂ y := by
    have : c₂ y ∈ c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} := mem_image_of_mem c₂ hyσ
    rw [himg₂] at this
    exact this.1
  have hxb : c₁ x < b := hcb ▸ hmono₁ hxσ hsb (lt_of_le_of_lt hxa' ha'2)
  have hyt : c₂ y < t := hct ▸ hmono₂ hyσ hst (lt_of_le_of_lt hyb' hb'2)
  exact hno (c₁ x) (c₂ y) hxu hxb hyr hyt (by rw [hpath₁ x hxσ, hpath₂ y hyσ, hxy])

/-- **The core of Lemmas W2 and W2a**: almost surely, at no dyadic pair of cuts which is an ordinary retained pair do
the fresh portions contain an empty lower rectangle. At each retained pair the conditional continuations are flow
lines of one GFF from `w > 0` (angle `θ₁`) and `0` (angle `θ₂`) under the kernel (`JointRetainedPairStatement`),
so Lemma 7.7 (on the canonical space) excludes the measurable chart event `ChartLowerRect` kernel-almost surely; it
integrates back, and the countably many pairs and corners are intersected. -/
theorem ae_not_isFreshLowerRectangle (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ u ∈ dyadSet, ∀ r ∈ dyadSet, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ¬ IsFreshLowerRectangle (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r := by
  have key : ∀ u r : ℝ≥0, ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ¬ IsFreshLowerRectangle (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r := by
    intro u r
    obtain ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, hpath⟩ :=
      hJ κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
    have hev : ∀ n k n' k' N : ℕ, ∀ᵐ ω ∂P, ω ∈ M →
        X ω ∈ {s | ChartLowerRect (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) (dyad n' k') N}ᶜ := by
      intro n k n' k' N
      refine ae_mem_of_compProd_eq hM hβ hX hlaw (measurableSet_chartLowerRect hcoord n k n' k' N).compl ?_
      filter_upwards [hcond] with c hc
      obtain ⟨hw, hG, hf₁, hf₂⟩ := hc
      have h77c := h77 κ hκ hκ4 c.1.fn c.1.jumps (BoundaryWord.isPiecewiseConstantBoundaryData c.1) c.2 0 θ₁ θ₂
        hw (by linarith [Real.pi_pos]) (K c) H hG Γ₁ Γ₂ U₁ U₂ hf₁ hf₂
      filter_upwards [h77c] with s hs
      exact not_chartLowerRect (fun hcon => by
        obtain ⟨s₀, t₀, hfc, -, -⟩ := hs hcon
        exact ⟨s₀, t₀, hfc⟩) _ _ _
    have hall : ∀ᵐ ω ∂P, ∀ n k n' k' N : ℕ, ω ∈ M →
        X ω ∈ {s | ChartLowerRect (Γ₁ s) (Γ₂ s) (U₁ s) (U₂ s) (dyad n k) (dyad n' k') N}ᶜ :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun n' => ae_all_iff.2 fun k' =>
        ae_all_iff.2 fun N => hev n k n' k' N
    filter_upwards [hall, hpath] with ω hω hωp hord hfresh
    obtain ⟨hMω, hJω⟩ := hωp hord
    obtain ⟨n, k, n', k', N, hR⟩ := exists_chartLowerRect_of_isFreshLowerRectangle hJω hfresh
    exact hω n k n' k' N hMω hR
  filter_upwards [ae_all_iff.2 fun p : (ℕ × ℕ) × (ℕ × ℕ) => key (dyad p.1.1 p.1.2) (dyad p.2.1 p.2.2)]
    with ω hω u hu r hr
  obtain ⟨⟨n, k⟩, rfl⟩ := hu
  obtain ⟨⟨n', k'⟩, rfl⟩ := hr
  exact hω ((n, k), (n', k'))

/-! ### Assembly -/

/-- **The pathwise facts of W5's two flow lines hold almost surely**: continuity, injectivity (Aux. lemma 25), values
in `ℍ̄`, no real subarcs, real ordered seeds, and the seed alternative (a common seed, or W0a). -/
theorem ae_pathFacts (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, PathFacts (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) := by
  have hW0a' : ∀ᵐ ω ∂P, x₂ < x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂) := by
    by_cases hlt : x₂ < x₁
    · filter_upwards [hW0a κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hlt hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
        with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hlt
  filter_upwards [Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₁, Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₂,
    Supp7.ae_im_nonneg_of_isFlowLine hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₂,
    ae_exists_mem_H_of_isFlowLine hη₁, ae_exists_mem_H_of_isFlowLine hη₂,
    Supp9.ae_apply_zero_of_isFlowLine hη₁, Supp9.ae_apply_zero_of_isFlowLine hη₂, hW0a']
    with ω c₁ c₂ i₁ i₂ m₁ m₂ n₁ n₂ z₁ z₂ ha
  refine ⟨c₁, c₂, i₁, i₂, m₁, m₂, n₁, n₂, by rw [z₁]; simp, by rw [z₂]; simp, by rw [z₁, z₂]; simpa using hx,
    fun h1 h2 => ?_⟩
  rcases hx.lt_or_eq with hlt | heq
  · obtain ⟨hv₂, hv₁⟩ := ha hlt h1 h2
    exact Or.inr ⟨fun t ht => by rw [z₁]; exact hv₂ t ht, fun s hs => by rw [z₂]; exact hv₁ s hs⟩
  · exact Or.inl (by rw [z₁, z₂, heq])

/-- **Lemma W2** (a backwards first loss is excluded by first-contact restart, p. 530), from Aux. lemma 25, W0a,
Lemma 7.7 (on the canonical space) and the joint G7 carrier. -/
theorem w2Statement_of_inputs (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u}) : Supp9.W2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [ae_pathFacts h25 hW0a hκ hκ4 hb hx hθ hh hη₁ hη₂,
    ae_not_isFreshLowerRectangle h77 hJ hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hF hcore hW1
  obtain ⟨r, hr, s, hs, hord, hfresh⟩ := exists_dyad_cuts_of_isW1Configuration hF hW1
  exact hcore r hr s hs hord hfresh

/-- **Lemma W2 with the paths exchanged** (p. 530), from the same inputs. -/
theorem w2SwapStatement_of_inputs (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u}) : Supp9.W2SwapStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [ae_pathFacts h25 hW0a hκ hκ4 hb hx hθ hh hη₁ hη₂,
    ae_not_isFreshLowerRectangle h77 hJ hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hF hcore hW1
  obtain ⟨r, hr, s, hs, hord, hfresh⟩ := exists_dyad_cuts_of_isW1ConfigurationSwap hF hW1
  exact hcore r hr s hs hord hfresh

/-- **Lemma W2a's corner case** (p. 533), from the same inputs. -/
theorem w2aCornerStatement_of_inputs (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u}) :
    Supp9.W2aCornerStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [ae_pathFacts h25 hW0a hκ hκ4 hb hx hθ hh hη₁ hη₂,
    ae_not_isFreshLowerRectangle h77 hJ hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hF hcore hC
  obtain ⟨r, hr, s, hs, hord, hfresh⟩ := exists_dyad_cuts_of_isW2aCornerConfiguration hF hC
  exact hcore r hr s hs hord hfresh

/-- **Lemma W2a** (p. 533) from Aux. lemma 25, W0a, W0b, Lemma 7.7 and the joint G7 carrier. -/
theorem w2aStatement_of_inputs' (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0})
    (hJ : JointRetainedPairStatement.{u}) : Supp9.W2aStatement.{u} :=
  Supp9.w2aStatement_of_inputs h25 hW0a hW0b (w2Statement_of_inputs h25 hW0a h77 hJ)
    (w2SwapStatement_of_inputs h25 hW0a h77 hJ) (w2aCornerStatement_of_inputs h25 hW0a h77 hJ)

/-- **Theorem W5** (the input of Theorem 1.5) with W2 and W4 discharged: from Aux. lemma 25, W0a, W0b, Lemma 7.7, the
joint G7 carrier, and W5's two local comparisons. -/
theorem w5Statement_of_inputs' (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hLF : Supp9.W5LocalFrameStatement.{u}) :
    Theorem15.W5Statement.{u} :=
  Supp9B.w5Statement_of_inputs_of_aux25 h25 hW0a hW0b (w2Statement_of_inputs h25 hW0a h77 hJ) hCS hLF

end Supp9D

end InteractingSLE
