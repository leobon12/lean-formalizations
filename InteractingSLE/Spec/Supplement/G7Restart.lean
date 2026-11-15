/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RestartMeas

/-!
# `RetainedPairRestartStatement` with the relative capacity clocks supplied

Packet PROVE-G7B. PROVE-G7 reduced Lemma G7 and the joint retained-pair carrier to the named input
`RetainedPairRestartStatement` (`G7RetainedReduce.lean`), whose content is (i) the W8.1 relative capacity clocks of
both continuations up to their first new contact with the retained union (`IsRetainedClock`), (ii) Lemma G7's
conditional law (the retained kernel, the chart field, the flow-line law of the continuations under the kernel) and
(iii) the outer word (`IsRetainedWord`). This file proves (i) and leaves (ii)–(iii):

* `canonRetPath`, `canonRetLife` (`G7RestartPath.lean`): the canonical retained clock of a continuation;
  `IsCanonRetClock`: given random chart paths and lifetimes are the canonical ones;
* `isRetainedClock_of_ordinary` (pathwise): at an ordinary retained pair the canonical clocks of both continuations
  satisfy `IsRetainedClock` in the canonical chart inverse (seed, confinement, relative domains, the terminal point,
  Proposition 6.12 and capacity additivity: `G7Clock*.lean`);
* `exists_retClock`: measurable chart paths and lifetimes, continuous on their lifetimes, which are almost surely the
  canonical ones at every ordinary retained pair;
* the named input **`RetainedKernelClockStatement`**: the conclusion of `RetainedPairRestartStatement` with the
  clocks replaced by agreement with *any* measurable versions of the canonical clocks;
* **`retainedPairRestartStatement_of_clock`**: `RetainedKernelClockStatement → RetainedPairRestartStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### The canonical clocks of a retained pair -/

/-- The chart position of the first tip `η₁(u)`: the real part of the forward chart limit there. -/
def tipPos {Ω : Type*} (d : RetData Ω) (η₁ : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ :=
  (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re

/-- **Chart paths and lifetimes are the canonical retained clocks** at `ω`: the second continuation in the retained
chart, the first in the chart translated by the first tip's position, both read in relative capacity time, up to their
first new contact with the retained union `η₁([0, u]) ∪ η₂([0, r])`. -/
def IsCanonRetClock {Ω : Type*} (d : RetData Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (V₁ V₂ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  V₁ ω = canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → γ₁ ω s =
      canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) s) ∧
    V₂ ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → γ₂ ω s =
      canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s

/-! ### The named input -/

/-- **Named input: the retained-pair kernel with the canonical relative capacity clocks** (Lemma G7, pp. 497–498,
for both current tips, as in Lemma W2's proof, p. 531; Aux. lemmas 85–86 for the outer word). Binders of
`RetainedPairRestartStatement`, and any measurable chart paths `γᵢ` and lifetimes `Vᵢ`, continuous on their
lifetimes, which almost surely at an ordinary retained pair are the canonical retained clocks (`IsCanonRetClock`).
Conclusion: the canonical space, retained kernel and conditional law of `RetainedPairRestartStatement`, and almost
surely at an ordinary retained pair: `ω ∈ M`, the chart field coordinate is the canonical chart field, each chart path
coordinate agrees with `γᵢ` up to its stop `Vᵢ` (which precedes its lifetime), and the outer word holds.
**Not proved in Lean.** -/
def RetainedKernelClockStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
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
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ H (X ω) = hd.chartField κ h ω ∧
        V₁ ω ≤ U₁ (X ω) ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → Γ₁ (X ω) s = γ₁ ω s) ∧
        V₂ ω ≤ U₂ (X ω) ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → Γ₂ (X ω) s = γ₂ ω s) ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1

/-! ### The canonical clocks at an ordinary retained pair (pathwise) -/

section Pathwise

variable {α β η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {u r : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **Both continuations of an ordinary retained pair satisfy `IsRetCont`** (second path in the retained chart,
first path in the chart translated by its tip position `w₁`). -/
theorem isRetCont_of_ordinary (hg : IsRetGood α u β r) (hC : IsRetChart α u β r φ ψ lift)
    (hφ : ∃ x₀ : ℝ, ∀ z, φ z = ConformalImage.mapOut (fillH (prefixSet α u β r)) z - x₀)
    (hp₁ : IsPathGood η₁ ζ₁ x₁) (hp₂ : IsPathGood η₂ ζ₂ x₂) (hα : ∀ s ≤ u, α s = η₁ s) (hβ : ∀ t ≤ r, β t = η₂ t)
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) :
    IsRetCont η₂ ζ₂ x₂ r (α '' Icc 0 u) φ ψ ∧
      Tendsto φ (𝓝[activeDomain α u β r] (η₁ u)) (𝓝 ((limUnder (𝓝[activeDomain α u β r] (η₁ u)) φ).re : ℂ)) ∧
      IsRetCont η₁ ζ₁ x₁ u (β '' Icc 0 r) (fun z => φ z - (limUnder (𝓝[activeDomain α u β r] (η₁ u)) φ).re)
        (fun w => ψ (w + (limUnder (𝓝[activeDomain α u β r] (η₁ u)) φ).re)) := by
  have e₁ : EqOn α η₁ (Icc 0 u) := fun s hs => hα s hs.2
  have e₂ : EqOn β η₂ (Icc 0 r) := fun t ht => hβ t ht.2
  have hdom : activeDomain α u β r = activeDomain η₁ u η₂ r := activeDomain_congr_Icc e₁ e₂
  have hi₁ : α '' Icc 0 u = η₁ '' Icc 0 u := image_congr e₁
  have hi₂ : β '' Icc 0 r = η₂ '' Icc 0 r := image_congr e₂
  have hpa : α u = η₁ u := hα u le_rfl
  have hpb : β r = η₂ r := hβ r le_rfl
  obtain ⟨hu, hr, hH₁, hH₂, hO₂, hO₁, hcl₁, hcl₂, -⟩ := hord
  have hR₂ := isRetCont_snd hg hC hφ hp₂ hβ hr (by rw [hpb]; exact hH₂) (by rw [hpb, hi₁]; exact hO₂)
    (by rw [hpb, hdom]; exact hcl₂)
  have hne₁ : ∀ s < u, α s ≠ α u := fun s hs he => by
    rw [hα s hs.le, hpa] at he
    exact hs.ne (hp₁.1 ((ENNReal.coe_le_coe.2 hs.le).trans hu.le) hu.le he)
  obtain ⟨w₁, hw₁, hR₁⟩ := isRetCont_fst hg hC hφ hp₁ hα hu (by rw [hpa]; exact hH₁) (by rw [hpa, hi₂]; exact hO₁)
    (by rw [hpa, hdom]; exact hcl₁) hne₁
  rw [hpa] at hw₁
  have hne : (𝓝[activeDomain α u β r] (η₁ u)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, hdom]; exact hcl₁
  have hlim : limUnder (𝓝[activeDomain α u β r] (η₁ u)) φ = (w₁ : ℂ) := hw₁.limUnder_eq
  rw [hlim, Complex.ofReal_re]
  exact ⟨hR₂, hw₁, hR₁⟩

/-- **The canonical clocks satisfy the clock relation at an ordinary retained pair.** -/
theorem isRetainedClock_of_ordinary (hg : IsRetGood α u β r) (hC : IsRetChart α u β r φ ψ lift)
    (hφ : ∃ x₀ : ℝ, ∀ z, φ z = ConformalImage.mapOut (fillH (prefixSet α u β r)) z - x₀)
    (hp₁ : IsPathGood η₁ ζ₁ x₁) (hp₂ : IsPathGood η₂ ζ₂ x₂) (hα : ∀ s ≤ u, α s = η₁ s) (hβ : ∀ t ≤ r, β t = η₂ t)
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) :
    IsRetainedClock η₁ ζ₁ u (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) ψ
        (canonRetPath (activeDomain α u β r) φ η₁ ζ₁ u (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
          (limUnder (𝓝[activeDomain α u β r] (η₁ u)) φ).re)
        (canonRetLife (activeDomain α u β r) φ η₁ ζ₁ u (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
          (limUnder (𝓝[activeDomain α u β r] (η₁ u)) φ).re) ∧
      IsRetainedClock η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) ψ
        (canonRetPath (activeDomain α u β r) φ η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) 0)
        (canonRetLife (activeDomain α u β r) φ η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) 0) := by
  obtain ⟨hR₂, -, hR₁⟩ := isRetCont_of_ordinary hg hC hφ hp₁ hp₂ hα hβ hord
  have e₁ : EqOn α η₁ (Icc 0 u) := fun s hs => hα s hs.2
  have e₂ : EqOn β η₂ (Icc 0 r) := fun t ht => hβ t ht.2
  have hK : IsCompact (prefixSet α u β r) := isCompact_prefixSet' hg.1 hg.2.1
  have hpre : prefixSet α u β r = η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r := prefixSet_congr_Icc e₁ e₂
  have hD : activeDomain α u β r = H \ fillH (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) := by
    rw [activeDomain_eq hK.isClosed, hpre]
  have hi₁ : α '' Icc 0 u = η₁ '' Icc 0 u := image_congr e₁
  have hi₂ : β '' Icc 0 r = η₂ '' Icc 0 r := image_congr e₂
  refine ⟨isRetainedClock_canon hR₁ (by rw [hi₂, union_comm]) hD,
    isRetainedClock_canon hR₂.shift_zero (by rw [hi₁]) hD⟩

end Pathwise

theorem canonRetPath_zero (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) :
    canonRetPath D φ η ζ a K 0 = fun s => contPath D φ η a (contLife η ζ a K)
      (invClock (chartClock (contPath D φ η a (contLife η ζ a K))) (contLife η ζ a K) s) := by
  have hz : (fun z => φ z - ((0 : ℝ) : ℂ)) = φ := funext fun z => by simp
  funext s
  rw [canonRetPath, hz, Complex.ofReal_zero, add_zero]

theorem canonRetLife_zero (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) :
    canonRetLife D φ η ζ a K 0 =
      capLife (chartClock (contPath D φ η a (contLife η ζ a K))) (contLife η ζ a K) := by
  have hz : (fun z => φ z - ((0 : ℝ) : ℂ)) = φ := funext fun z => by simp
  rw [canonRetLife, hz]

/-! ### Measurable canonical clocks -/

section Random

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The canonical retained clocks, measurably**: measurable chart paths and lifetimes, continuous on their
lifetimes, which almost surely at every ordinary retained pair are the canonical retained clocks. -/
theorem exists_retClock (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (V₁ V₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) ∧
      (∀ t, Measurable fun ω => γ₂ ω t) ∧ Measurable V₁ ∧ Measurable V₂ ∧
      (∀ ω, ContinuousOn (γ₁ ω) {s | (s : ℝ≥0∞) ≤ V₁ ω}) ∧ (∀ ω, ContinuousOn (γ₂ ω) {s | (s : ℝ≥0∞) ≤ V₂ ω}) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        IsCanonRetClock d η₁ η₂ ζ₁ ζ₂ γ₁ γ₂ V₁ V₂ ω := by
  classical
  obtain ⟨η₁', hm₁, ha₁⟩ := exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨η₂', hm₂, ha₂⟩ := exists_measurable_version_of_isFlowLine hη₂
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  -- the almost sure good event and a measurable full-measure part of it
  set Good : Set Ω := {ω | IsPathGood (η₁ ω) (ζ₁ ω) x₁ ∧ IsPathGood (η₂ ω) (ζ₂ ω) x₂ ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω t = η₂ ω t) ∧
      ((d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)} with hGood
  have haeGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, ha₁, ha₂, hag] with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  set G' : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG'
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable P _).compl
  have hG'sub : G' ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G'} = toMeasurable P Goodᶜ := by ext ω; simp [hG']
    rw [this, measure_toMeasurable]
    exact ae_iff.1 haeGood
  -- the events of the two continuations
  set E₂ : Set Ω := G' ∩ d.E ∩ {ω | (d.u : ℝ≥0∞) < ζ₁ ω} ∩ {ω | (d.r : ℝ≥0∞) < ζ₂ ω} with hE₂
  set E₁ : Set Ω := E₂ ∩ (d.E ∩ {ω | d.η₁ ω d.u ∈ H} ∩ {ω | d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r} ∩
    {ω | d.η₁ ω d.u ∈ closure (d.D ω)}) with hE₁
  have hE₂m : MeasurableSet E₂ := ((hG'm.inter hd.measurableSet_E).inter
    (measurableSet_lt measurable_const hζ₁)).inter (measurableSet_lt measurable_const hζ₂)
  have hE₁m : MeasurableSet E₁ := hE₂m.inter hd.measurableSet_tipEvent
  have hE₁₂ : E₁ ⊆ E₂ := inter_subset_left
  -- pathwise facts on the events
  have hbase : ∀ ω ∈ E₂, IsRetGood (d.η₁ ω) d.u (d.η₂ ω) d.r ∧
      IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) ∧
      (∃ x₀ : ℝ, ∀ z, d.fwd ω z = ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀) ∧
      d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := by
    rintro ω ⟨⟨⟨-, hωE⟩, -⟩, -⟩
    obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
    refine ⟨hd.good ω (RetData.E_subset_G hωE), hC, ⟨x₀, fun z => ?_⟩, hd.D_of_mem hωE⟩
    show d.g ω z - d.shift ω = _
    rw [hx₀, RetData.g, RetData.K_of_mem hωE]
  have hagE : ∀ ω ∈ E₂, IsPathGood (η₁ ω) (ζ₁ ω) x₁ ∧ IsPathGood (η₂ ω) (ζ₂ ω) x₂ ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω t = η₂ ω t) ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t := by
    rintro ω ⟨⟨⟨hωG, -⟩, hu⟩, hr⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hG'sub hωG
    obtain ⟨-, h6, h7⟩ := h5 hu hr
    exact ⟨h1, h2, h3, h4, h6, h7⟩
  have hβ' : ∀ ω ∈ E₂, ∀ t ≤ d.r, d.η₂ ω t = η₂' ω t := fun ω hω t ht => by
    obtain ⟨-, -, -, e₂, -, a₂⟩ := hagE ω hω
    exact (a₂ t ht).trans (e₂ t ((ENNReal.coe_le_coe.2 ht).trans hω.2.le)).symm
  have hα' : ∀ ω ∈ E₂, ∀ s ≤ d.u, d.η₁ ω s = η₁' ω s := fun ω hω s hs => by
    obtain ⟨-, -, e₁, -, a₁, -⟩ := hagE ω hω
    exact (a₁ s hs).trans (e₁ s ((ENNReal.coe_le_coe.2 hs).trans hω.1.2.le)).symm
  have hR₂ : ∀ ω ∈ E₂, IsRetCont (η₂' ω) (ζ₂ ω) x₂ d.r (d.η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) := by
    intro ω hω
    obtain ⟨hg, hC, hφ, -⟩ := hbase ω hω
    obtain ⟨-, hp₂, -, e₂, -, -⟩ := hagE ω hω
    have hωE : ω ∈ d.E := hω.1.1.2
    refine isRetCont_snd hg hC hφ (IsPathGood.congr hp₂ e₂) (hβ' ω hω) hω.2 hωE.1.1.2 hωE.1.2 ?_
    rw [← hd.DOf_of_mem RetData.E₀_subset_G hωE.1]
    exact hωE.2
  have hDK₂ : ∀ ω ∈ E₂, d.D ω = H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r) := by
    intro ω hω
    obtain ⟨hg, -, -, hD⟩ := hbase ω hω
    rw [hD, activeDomain_eq (isCompact_prefixSet' hg.1 hg.2.1).isClosed, prefixSet,
      image_congr fun t ht => hβ' ω hω t ht.2]
  have hDK₁ : ∀ ω ∈ E₂, d.D ω = H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u) := by
    intro ω hω
    obtain ⟨hg, -, -, hD⟩ := hbase ω hω
    rw [hD, activeDomain_eq (isCompact_prefixSet' hg.1 hg.2.1).isClosed, prefixSet, union_comm,
      image_congr fun s hs => hα' ω hω s hs.2]
  -- the first tip's chart position
  have hR₁' : ∀ ω ∈ E₁, ∃ w₁ : ℝ, Tendsto (d.fwd ω) (𝓝[d.D ω] (d.η₁ ω d.u)) (𝓝 (w₁ : ℂ)) ∧
      IsRetCont (η₁' ω) (ζ₁ ω) x₁ d.u (d.η₂ ω '' Icc 0 d.r) (fun z => d.fwd ω z - w₁)
        (fun w => d.inv ω (w + w₁)) := by
    intro ω hω
    obtain ⟨hg, hC, hφ, hD⟩ := hbase ω hω.1
    obtain ⟨hp₁, -, e₁, -, a₁, -⟩ := hagE ω hω.1
    obtain ⟨⟨⟨-, hH⟩, hO⟩, hcl⟩ := hω.2
    have hu : (d.u : ℝ≥0∞) < ζ₁ ω := hω.1.1.2
    have hne₁ : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u := fun s hs he => by
      rw [a₁ s hs.le, a₁ d.u le_rfl] at he
      exact hs.ne (hp₁.1 ((ENNReal.coe_le_coe.2 hs.le).trans hu.le) hu.le he)
    obtain ⟨w₁, hw₁, hR⟩ := isRetCont_fst hg hC hφ (IsPathGood.congr hp₁ e₁) (hα' ω hω.1) hu hH hO
      (by rw [← hD]; exact hcl) hne₁
    rw [← hD] at hw₁
    exact ⟨w₁, hw₁, hR⟩
  have hlimE : ∀ ω ∈ E₁, ∃ w, Tendsto (d.fwd ω) (𝓝[d.D ω] (d.η₁ ω d.u)) (𝓝 w) := fun ω hω => by
    obtain ⟨w₁, hw₁, -⟩ := hR₁' ω hω
    exact ⟨_, hw₁⟩
  set w : Ω → ℝ := fun ω => (if ω ∈ E₁ then limUnder (𝓝[d.D ω] (d.η₁ ω d.u)) (d.fwd ω) else 0).re with hw
  have hwm : Measurable w := by
    have h1 := hd.measurable_tipLim hE₁m (fun ω hω => hω.2.2) hlimE
    refine Complex.measurable_re.comp ?_
    convert h1 using 2
    split_ifs <;> rfl
  have hwE : ∀ ω ∈ E₁, Tendsto (d.fwd ω) (𝓝[d.D ω] (d.η₁ ω d.u)) (𝓝 (w ω : ℂ)) ∧
      IsRetCont (η₁' ω) (ζ₁ ω) x₁ d.u (d.η₂ ω '' Icc 0 d.r) (fun z => d.fwd ω z - w ω)
        (fun z => d.inv ω (z + w ω)) := by
    intro ω hω
    obtain ⟨w₁, hw₁, hR⟩ := hR₁' ω hω
    have hne : (𝓝[d.D ω] (d.η₁ ω d.u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hω.2.2
    have hww : w ω = w₁ := by
      simp only [hw, hω, ↓reduceIte]
      rw [hw₁.limUnder_eq, Complex.ofReal_re]
    rw [hww]
    exact ⟨hw₁, hR⟩
  -- the measurable stops
  set V₂ : Ω → ℝ≥0∞ := fun ω => (if ω ∈ E₂ then contStop (η₂' ω) (ζ₂ ω) d.r
    (d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) else 0) - d.r with hV₂def
  set V₁ : Ω → ℝ≥0∞ := fun ω => (if ω ∈ E₁ then contStop (η₁' ω) (ζ₁ ω) d.u
    (d.η₂ ω '' Icc 0 d.r ∪ d.η₁ ω '' Icc 0 d.u) else 0) - d.u with hV₁def
  have hV₂m : Measurable V₂ := by
    have h1 := measurable_contStop hE₂m hm₂ hζ₂ d.r hd.meas₁ hd.meas₂ d.u d.r
      (fun ω hω => (hR₂ ω hω).path.continuousOn)
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hbase ω hω).1.1)
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hbase ω hω).1.2.1) fun ω hω => hω.2.le
    have h2 := h1.sub (measurable_const (a := ((d.r : ℝ≥0) : ℝ≥0∞)))
    convert h2 using 1
    funext ω
    simp only [hV₂def, Pi.sub_apply]
    split_ifs <;> rfl
  have hV₁m : Measurable V₁ := by
    have h1 := measurable_contStop hE₁m hm₁ hζ₁ d.u hd.meas₂ hd.meas₁ d.r d.u
      (fun ω hω => (hwE ω hω).2.path.continuousOn)
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hbase ω hω.1).1.2.1)
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hbase ω hω.1).1.1) fun ω hω => hω.1.1.2.le
    have h2 := h1.sub (measurable_const (a := ((d.u : ℝ≥0) : ℝ≥0∞)))
    convert h2 using 1
    funext ω
    simp only [hV₁def, Pi.sub_apply]
    split_ifs <;> rfl
  have hV₂ : ∀ ω ∈ E₂, V₂ ω = contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r) := by
    intro ω hω
    simp only [hV₂def, hω, ↓reduceIte]
    rw [image_congr fun t ht => hβ' ω hω t ht.2]
    rfl
  have hV₁ : ∀ ω ∈ E₁, V₁ ω = contLife (η₁' ω) (ζ₁ ω) d.u (d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u) := by
    intro ω hω
    simp only [hV₁def, hω, ↓reduceIte]
    rw [image_congr fun s hs => hα' ω hω.1 s hs.2]
    rfl
  -- the chart paths in continuation time
  set Γ₂ : Ω → ℝ≥0 → ℂ := fun ω s => if ω ∈ E₂ then contPath (d.D ω) (d.fwd ω) (η₂' ω) d.r (V₂ ω) s else 0
    with hΓ₂def
  set Γ₁ : Ω → ℝ≥0 → ℂ := fun ω s => if ω ∈ E₁ then
    contPath (d.D ω) (fun z => d.fwd ω z - w ω) (η₁' ω) d.u (V₁ ω) s else 0 with hΓ₁def
  have hΓ₂E : ∀ ω ∈ E₂, Γ₂ ω = contPath (H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)) (d.fwd ω) (η₂' ω)
      d.r (contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)) := by
    intro ω hω
    funext s
    simp only [hΓ₂def, hω, ↓reduceIte]
    rw [hDK₂ ω hω, hV₂ ω hω]
  have hΓ₁E : ∀ ω ∈ E₁, Γ₁ ω = contPath (H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u))
      (fun z => d.fwd ω z - w ω) (η₁' ω) d.u
      (contLife (η₁' ω) (ζ₁ ω) d.u (d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u)) := by
    intro ω hω
    funext s
    simp only [hΓ₁def, hω, ↓reduceIte]
    rw [hDK₁ ω hω.1, hV₁ ω hω]
  have hΓ₂m : ∀ s, Measurable fun ω => Γ₂ ω s := by
    intro s
    have h := measurable_contPath hE₂m hd.isOpen_D hd.measurableSet_mem_D hd.measurable_indicator_fwd hm₂ d.r
      hV₂m (fun ω hω => by rw [hV₂ ω hω]; exact (hR₂ ω hω).pos_contLife)
      (fun ω hω r' hr' => by
        rw [hV₂ ω hω] at hr'
        exact (hR₂ ω hω).path.continuousOn.mono fun t ht =>
          (ENNReal.coe_le_coe.2 ht).trans ((coe_add_lt_iff.1 hr').le.trans contStop_le))
      (fun ω hω r' hr' => by
        rw [hV₂ ω hω] at hr'
        rw [hDK₂ ω hω]
        exact (hR₂ ω hω).mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add (coe_add_lt_iff.1 hr').le))
      (fun ω hω r' hr' => by
        rw [hV₂ ω hω] at hr'
        rw [hDK₂ ω hω]
        exact ⟨_, ((hR₂ ω hω).contPath_spec_lt hr').2.1⟩)
      (fun ω hω => by rw [hDK₂ ω hω, hV₂ ω hω]; exact (hR₂ ω hω).continuous_contPath) s
    convert h using 2 with ω
    simp only [hΓ₂def]
    split_ifs <;> rfl
  have hΓ₁m : ∀ s, Measurable fun ω => Γ₁ ω s := by
    intro s
    have h := measurable_contPath (φ := fun ω z => d.fwd ω z - w ω) hE₁m hd.isOpen_D hd.measurableSet_mem_D
      (hd.measurable_indicator_fwd_sub hwm) hm₁ d.u
      hV₁m (fun ω hω => by rw [hV₁ ω hω]; exact (hwE ω hω).2.pos_contLife)
      (fun ω hω r' hr' => by
        rw [hV₁ ω hω] at hr'
        exact (hwE ω hω).2.path.continuousOn.mono fun t ht =>
          (ENNReal.coe_le_coe.2 ht).trans ((coe_add_lt_iff.1 hr').le.trans contStop_le))
      (fun ω hω r' hr' => by
        rw [hV₁ ω hω] at hr'
        rw [hDK₁ ω hω.1]
        exact (hwE ω hω).2.mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add (coe_add_lt_iff.1 hr').le))
      (fun ω hω r' hr' => by
        rw [hV₁ ω hω] at hr'
        rw [hDK₁ ω hω.1]
        exact ⟨_, ((hwE ω hω).2.contPath_spec_lt hr').2.1⟩)
      (fun ω hω => by rw [hDK₁ ω hω.1, hV₁ ω hω]; exact (hwE ω hω).2.continuous_contPath) s
    convert h using 2 with ω
    simp only [hΓ₁def]
    split_ifs <;> rfl
  have hΓ₂c : ∀ ω, Continuous (Γ₂ ω) := fun ω => by
    by_cases hω : ω ∈ E₂
    · rw [hΓ₂E ω hω]; exact (hR₂ ω hω).continuous_contPath
    · have : Γ₂ ω = fun _ => 0 := funext fun s => by simp [hΓ₂def, hω]
      rw [this]; exact continuous_const
  have hΓ₁c : ∀ ω, Continuous (Γ₁ ω) := fun ω => by
    by_cases hω : ω ∈ E₁
    · rw [hΓ₁E ω hω]; exact (hwE ω hω).2.continuous_contPath
    · have : Γ₁ ω = fun _ => 0 := funext fun s => by simp [hΓ₁def, hω]
      rw [this]; exact continuous_const
  obtain ⟨mγ₂, mU₂, cγ₂⟩ := clockData_of_measurable hE₂m hΓ₂c hΓ₂m
    (fun ω hω => by rw [hΓ₂E ω hω]; exact (hR₂ ω hω).contPath_zero) hV₂m
    (fun ω hω => by rw [hΓ₂E ω hω, hV₂ ω hω]; exact (hR₂ ω hω).isClockOn)
    (fun ω hω => by rw [hΓ₂E ω hω]; exact (hR₂ ω hω).continuous_chartClock)
  obtain ⟨mγ₁, mU₁, cγ₁⟩ := clockData_of_measurable hE₁m hΓ₁c hΓ₁m
    (fun ω hω => by rw [hΓ₁E ω hω]; exact (hwE ω hω).2.contPath_zero) hV₁m
    (fun ω hω => by rw [hΓ₁E ω hω, hV₁ ω hω]; exact (hwE ω hω).2.isClockOn)
    (fun ω hω => by rw [hΓ₁E ω hω]; exact (hwE ω hω).2.continuous_chartClock)
  -- the clock data
  set γ₂f : Ω → ℝ≥0 → ℂ := fun ω s => if ω ∈ E₂ then Γ₂ ω (invClock (chartClock (Γ₂ ω)) (V₂ ω) s) else 0
    with hγ₂f
  set U₂f : Ω → ℝ≥0∞ := fun ω => if ω ∈ E₂ then capLife (chartClock (Γ₂ ω)) (V₂ ω) else 0 with hU₂f
  set γ₁f : Ω → ℝ≥0 → ℂ := fun ω s =>
    (if ω ∈ E₁ then Γ₁ ω (invClock (chartClock (Γ₁ ω)) (V₁ ω) s) else 0) + w ω with hγ₁f
  set U₁f : Ω → ℝ≥0∞ := fun ω => if ω ∈ E₁ then capLife (chartClock (Γ₁ ω)) (V₁ ω) else 0 with hU₁f
  refine ⟨γ₁f, γ₂f, U₁f, U₂f, fun t => ?_, fun t => ?_, ?_, ?_, fun ω => ?_, fun ω => ?_, ?_⟩
  · have h := (mγ₁ t).add (Complex.measurable_ofReal.comp hwm)
    convert h using 2 with ω
    simp only [hγ₁f, Pi.add_apply, Function.comp_apply]
    split_ifs <;> rfl
  · convert mγ₂ t using 2 with ω
    simp only [hγ₂f]
    split_ifs <;> rfl
  · convert mU₁ using 2 with ω
    simp only [hU₁f]
    split_ifs <;> rfl
  · convert mU₂ using 2 with ω
    simp only [hU₂f]
    split_ifs <;> rfl
  · by_cases hω : ω ∈ E₁
    · have h := (cγ₁ ω hω).add (continuousOn_const (c := (w ω : ℂ)))
      simp only [hγ₁f, hU₁f, hω, ↓reduceIte]
      exact h
    · simp only [hγ₁f, hU₁f, hω, ↓reduceIte, zero_add]
      exact continuousOn_const
  · by_cases hω : ω ∈ E₂
    · simp only [hγ₂f, hU₂f, hω, ↓reduceIte]
      exact cγ₂ ω hω
    · simp only [hγ₂f, hU₂f, hω, ↓reduceIte]
      exact continuousOn_const
  · -- the canonical identification at ordinary retained pairs
    filter_upwards [hG'ae] with ω hωG' hord
    obtain ⟨-, -, e₁, e₂, hagω⟩ := hG'sub hωG'
    obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
    have hωE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hord
    have hω₂ : ω ∈ E₂ := ⟨⟨⟨hωG', hωE⟩, hord.1⟩, hord.2.1⟩
    have hi₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => a₁ s hs.2
    have hi₂ : d.η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r := image_congr fun t ht => a₂ t ht.2
    have hp : d.η₁ ω d.u = η₁ ω d.u := a₁ d.u le_rfl
    have hDact : d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r := by
      rw [hd.D_of_mem hωE]
      exact activeDomain_congr_Icc (fun s hs => a₁ s hs.2) (fun t ht => a₂ t ht.2)
    have hω₁ : ω ∈ E₁ := ⟨hω₂, ⟨⟨⟨hωE, show d.η₁ ω d.u ∈ H by rw [hp]; exact hord.2.2.1⟩,
      show d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r by rw [hp, hi₂]; exact hord.2.2.2.2.2.1⟩,
      show d.η₁ ω d.u ∈ closure (d.D ω) by rw [hp, hDact]; exact hord.2.2.2.2.2.2.1⟩⟩
    have hK₂ : d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
      rw [hi₁, image_congr fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht.2).trans hord.2.1.le)]
    have hK₁ : d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
      rw [hi₂, image_congr fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs.2).trans hord.1.le), union_comm]
    have hwtip : w ω = tipPos d η₁ ω := by
      simp only [hw, hω₁, ↓reduceIte, tipPos]
      rw [hp]
    have hΓ₂ω : Γ₂ ω = contPath (d.D ω) (d.fwd ω) (η₂' ω) d.r
        (contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)) := by
      funext s
      simp only [hΓ₂def, hω₂, ↓reduceIte]
      rw [hV₂ ω hω₂]
    have hΓ₁ω : Γ₁ ω = contPath (d.D ω) (fun z => d.fwd ω z - w ω) (η₁' ω) d.u
        (contLife (η₁' ω) (ζ₁ ω) d.u (d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u)) := by
      funext s
      simp only [hΓ₁def, hω₁, ↓reduceIte]
      rw [hV₁ ω hω₁]
    have hP₂ : γ₂f ω = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 := by
      rw [← (canonRetPath_congr e₂).1, ← hK₂, canonRetPath_zero]
      funext s
      simp only [hγ₂f, hω₂, ↓reduceIte]
      rw [hΓ₂ω, hV₂ ω hω₂]
    have hL₂ : U₂f ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 := by
      rw [← (canonRetPath_congr e₂).2, ← hK₂, canonRetLife_zero]
      simp only [hU₂f, hω₂, ↓reduceIte]
      rw [hΓ₂ω, hV₂ ω hω₂]
    have hP₁ : γ₁f ω = canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) := by
      rw [← hwtip, ← (canonRetPath_congr e₁).1, ← hK₁]
      funext s
      simp only [hγ₁f, hω₁, ↓reduceIte]
      rw [hΓ₁ω, hV₁ ω hω₁]
      rfl
    have hL₁ : U₁f ω = canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) := by
      rw [← hwtip, ← (canonRetPath_congr e₁).2, ← hK₁]
      simp only [hU₁f, hω₁, ↓reduceIte]
      rw [hΓ₁ω, hV₁ ω hω₁]
      rfl
    exact ⟨hL₁, fun s _ => congrFun hP₁ s, hL₂, fun s _ => congrFun hP₂ s⟩

end Random

/-! ### The reduction -/

/-- **`RetainedPairRestartStatement` from the clock-supplied named input**: the W8.1 relative capacity clocks of both
retained continuations (`isRetainedClock_of_ordinary`), their measurable versions (`exists_retClock`) and the clock
relation in the kernel's chart path coordinates are proved; what remains is `RetainedKernelClockStatement`. -/
theorem retainedPairRestartStatement_of_clock (hR : RetainedKernelClockStatement.{u}) :
    RetainedPairRestartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  obtain ⟨γ₁, γ₂, V₁, V₂, m₁, m₂, mV₁, mV₂, c₁, c₂, hcanon⟩ := exists_retClock hκ hκ4 hη₁ hη₂ hd hag
  obtain ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag γ₁ γ₂ V₁ V₂ m₁ m₂ mV₁ mV₂ c₁
      c₂ hcanon
  refine ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, ?_⟩
  filter_upwards [hpath, hcanon, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, hag] with ω hω hc hg₁ hg₂ hagω hord
  obtain ⟨hMω, hHX, hU₁, hΓ₁, hU₂, hΓ₂, hW⟩ := hω hord
  obtain ⟨hL₁, hP₁, hL₂, hP₂⟩ := hc hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  have hωE := hd.mem_E_of_ordinary hG a₁ a₂ hord
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hωE]⟩
  obtain ⟨k₁, k₂⟩ := isRetainedClock_of_ordinary (hd.good ω (RetData.E_subset_G hωE)) hC hφ hg₁ hg₂ a₁ a₂ hord
  have hD : d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.D_of_mem hωE
  rw [← hD] at k₁ k₂
  have htip : (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re = tipPos d η₁ ω := rfl
  rw [htip] at k₁
  refine ⟨hMω, hHX, k₁.mono (by rw [← hL₁]; exact hU₁) fun s hs => ?_,
    k₂.mono (by rw [← hL₂]; exact hU₂) fun s hs => ?_, hW⟩
  · rw [← hL₁] at hs
    rw [hΓ₁ s hs, hP₁ s hs]
  · rw [← hL₂] at hs
    rw [hΓ₂ s hs, hP₂ s hs]

/-- **Lemma G7 with the outer word from the clock-supplied named input.** -/
theorem g7RetainedPairStatement_of_kernelClock (hR : RetainedKernelClockStatement.{u}) :
    G7RetainedPairStatement.{u} :=
  g7RetainedPairStatement_of_restart (retainedPairRestartStatement_of_clock hR)

/-- **The joint retained-pair carrier from the clock-supplied named input.** -/
theorem jointRetainedPairStatement_of_kernelClock (hR : RetainedKernelClockStatement.{u}) :
    Supp9D.JointRetainedPairStatement.{u} :=
  jointRetainedPairStatement_of_restart (retainedPairRestartStatement_of_clock hR)

end Supp7

end InteractingSLE
