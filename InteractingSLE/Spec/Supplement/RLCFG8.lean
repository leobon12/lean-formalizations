/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCEReal
import InteractingSLE.Spec.Sec7.FlowReflectFlow

/-!
# Lemma G8 (the right-boundary reference frame) with Lemma G9, in the chart; the exterior real case per datum

Packet PROVE-RLC-F. Sources: supplement §7.7–§7.8 (`source/spec/p481-528.md` L437–L510, pp. 499–502): Lemma G8 and
its proof ("a reference and a positive-probability swallow", "small-gap frames and disintegration"), Lemma G9
(completion on the fresh-contact event); W5's real local frame (`source/spec/p529-576.md` L159, p. 535: "On an exterior
right interval the lower-angle cumulative weight `(C + θ₁χ)/λ − 1` is greater than `−2`, since the flow continues at
`p`. It is less than `c_κ`, since otherwise GB7a excludes the visit. Thus G8 supplies the required right-boundary
frame. On an exterior left interval use its reflection […] G7a compares both entire fresh stopped laws under one
density. G9–G10 again supply actual ordered proper completions").

* `G8FrameStatement` (**named input**, Lemma G8 with Lemma G9 in the chart; see its docstring for the exact
  correspondence with items 1–4 of G8 and with G9);
* `ae_frameWeight_of_visit_right`, `ae_frameWeight_of_visit_left`: a visit of a constant interval on the right
  (left) of the seed strictly before the lifetime forces the cumulative weight into `(−2, κ/2 − 2)` (threshold half:
  `RLC.thresholdVisitStatement`; nonhitting half: Lemma GB7a, `Supp8.gb7aFlowStatement`);
* `IsChartCompletable.congr`: completability sees the paths only through their prefixes;
* **`ae_isChartCompletable_of_frame`**: per datum with the canonical seed germs at the chart seeds `0` and `w`, and a
  buffer whose closure meets `ℝ` only in the seed collars and in a set of height `C` inside a compact interval right of
  `w`, the G8 frame (with G9) and Corollary G7a's single-density comparison (`RLC.G3ChartComparisonStatement`, whose
  open set `O` is arbitrary) give the completability of every stopped pair with a common point whose real points lie
  over that set.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Restart

/-! ### Lemma G8 with Lemma G9 -/

/-- **Named input: Lemma G8 (right-boundary reference frame) with Lemma G9 (completion on the fresh-contact event), in
the chart** (supplement §7.7–§7.8, pp. 499–502). Fix `0 < κ < 4`, `θ₁ < θ₂`, chart seeds `w₂ < w₁`, a compact interval
`J = [a, b] ⊂ (w₁, ∞)` and a height `C` with `−2 < r = (C + θ₁χ)/λ − 1 < c_κ = κ/2 − 2`. Then there is a retained
datum, i.e. a finite boundary word `cR` with jump set `Ĵ`, such that:

* (G8 item 1) on nonempty collars `(wᵢ − ε, wᵢ)`, `(wᵢ, wᵢ + ε)` it has the canonical germs `−λ − θᵢχ`, `λ − θᵢχ`,
  and no jump in the collars other than the two seeds;
* (G8 item 2) the whole interval `J` is untouched original-real boundary of height `C`: `cR = C` and no jump on `J`;
* (G8 items 3–4 with G9) for the GFF with data `cR` and its angle-`θ₁` flow from `w₁`, angle-`θ₂` flow from `w₂` (the
  conditional pair of G7 before any new old-range hit; in the chart the old range lies on `ℝ` off `J` and the seeds),
  almost surely every pair of prefixes strictly before the lifetimes whose real points after time `0` lie in `J`
  (so no new old-range hit has occurred) and which have a common point after their seeds (the fresh-contact event of
  G9) is completable: the lifted complete physical tails are proper, injective, ordered with the higher-angle path on
  the left (G9), and avoid each other's current seed (G8 item 4; G9: "The two current seeds are not visited again").

The statement is quantified over every coupling of the GFF with its flow lines (the universal determination of the
finite-force flow lines, as in `G2aReferenceStatement`). **Not proved in Lean** (G8's proof uses Proposition 7.4,
Lemma 7.16, GB1 and Aux. lemmas 85–86, 90 with a disintegration of a positive-probability swallow event; G9's proof uses
the contact order of Aux. lemma 84 / G5 and the chart's boundary extension). -/
def G8FrameStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ w₂ w₁ C a b : ℝ, θ₁ < θ₂ → w₂ < w₁ → w₁ < a → a ≤ b →
    -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) →
    Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2 →
    ∃ (cR : ℝ → ℝ) (Ĵ : Finset ℝ) (ε : ℝ), 0 < ε ∧ IsPiecewiseConstantBoundaryData cR Ĵ ∧
      (∀ x, w₂ - ε < x → x < w₂ → cR x = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
      (∀ x, w₂ < x → x < w₂ + ε → cR x = sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
      (∀ x, w₁ - ε < x → x < w₁ → cR x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
      (∀ x, w₁ < x → x < w₁ + ε → cR x = sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
      (∀ x ∈ Ĵ, |x - w₂| < ε → x = w₂) ∧ (∀ x ∈ Ĵ, |x - w₁| < ε → x = w₁) ∧
      (∀ x ∈ Icc a b, cR x = C ∧ x ∉ Ĵ) ∧
    ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
      (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q Ĥ cR Ĵ →
    ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ cR Ĵ w₁ θ₁ Q Ĥ α₁ ζ₁ → IsFlowLine κ cR Ĵ w₂ θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < ζ₁ x → (s₂ : ℝ≥0∞) < ζ₂ x →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → α₁ x t ∈ H ∨ ((α₁ x t).im = 0 ∧ (α₁ x t).re ∈ Icc a b)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → α₂ x t ∈ H ∨ ((α₂ x t).im = 0 ∧ (α₂ x t).re ∈ Icc a b)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ α₁ x t₁ = α₂ x t₂) →
        IsChartCompletable (α₁ x) s₁ (α₂ x) s₂

/-! ### The weight of a visited exterior interval -/

/-- **A visited interval right of the seed has an admissible, hitting weight** (W5, p. 535): almost surely, if the
angle-`θ` flow from `W` visits `(a, a') ⊂ [W, ∞)` (data `C` there off the jumps) strictly before its lifetime, then
`−2 < (C + θχ)/λ − 1 < κ/2 − 2` (threshold: `RLC.thresholdVisitStatement`; nonhitting: Lemma GB7a). -/
theorem ae_frameWeight_of_visit_right {κ θ W a a' C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : ℝ → ℝ} {J : Finset ℝ}
    (hc : IsPiecewiseConstantBoundaryData c J) (hWa : W ≤ a) (hcC : ∀ y ∈ Ioo a a', y ∉ J → c y = C)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData P H₀ c J)
    (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) (hΓ : IsFlowLine κ c J W θ P H₀ Γ U) :
    ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) < U ω ∧ ∃ y ∈ Ioo a a', Γ ω t = y) →
      -2 < Sec4.cumWeightRight κ (C + θ * QuantumZipper.chiC κ) ∧
        Sec4.cumWeightRight κ (C + θ * QuantumZipper.chiC κ) < κ / 2 - 2 := by
  have T := thresholdVisitStatement κ hκ hκ4 c J hc W θ a a' C hcC P H₀ hH Γ U hΓ
  have G := Supp8.gb7aFlowStatement κ hκ hκ4 c J hc W θ a a' C hcC P H₀ hH Γ U hΓ
  by_cases hlo : -2 < Sec4.cumWeightRight κ (C + θ * QuantumZipper.chiC κ)
  · by_cases hhi : Sec4.cumWeightRight κ (C + θ * QuantumZipper.chiC κ) < κ / 2 - 2
    · exact ae_of_all _ fun _ _ => ⟨hlo, hhi⟩
    · filter_upwards [G.1 hWa (not_lt.1 hhi)] with ω hω hvis
      obtain ⟨t, ht, y, hy, he⟩ := hvis
      exact absurd he (hω t ht.le y hy)
  · filter_upwards [T.1 hWa (not_lt.1 hlo)] with ω hω hvis
    obtain ⟨t, ht, y, hy, he⟩ := hvis
    exact absurd he (hω t ht y hy)

/-- **A visited interval left of the seed has an admissible, hitting weight**: the left form of
`ae_frameWeight_of_visit_right`, with the left cumulative weight `−(C + θχ)/λ − 1`. -/
theorem ae_frameWeight_of_visit_left {κ θ W a a' C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : ℝ → ℝ} {J : Finset ℝ}
    (hc : IsPiecewiseConstantBoundaryData c J) (haW : a' ≤ W) (hcC : ∀ y ∈ Ioo a a', y ∉ J → c y = C)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData P H₀ c J)
    (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) (hΓ : IsFlowLine κ c J W θ P H₀ Γ U) :
    ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) < U ω ∧ ∃ y ∈ Ioo a a', Γ ω t = y) →
      -2 < Sec4.cumWeightLeft κ (C + θ * QuantumZipper.chiC κ) ∧
        Sec4.cumWeightLeft κ (C + θ * QuantumZipper.chiC κ) < κ / 2 - 2 := by
  have T := thresholdVisitStatement κ hκ hκ4 c J hc W θ a a' C hcC P H₀ hH Γ U hΓ
  have G := Supp8.gb7aFlowStatement κ hκ hκ4 c J hc W θ a a' C hcC P H₀ hH Γ U hΓ
  by_cases hlo : -2 < Sec4.cumWeightLeft κ (C + θ * QuantumZipper.chiC κ)
  · by_cases hhi : Sec4.cumWeightLeft κ (C + θ * QuantumZipper.chiC κ) < κ / 2 - 2
    · exact ae_of_all _ fun _ _ => ⟨hlo, hhi⟩
    · filter_upwards [G.2 haW (not_lt.1 hhi)] with ω hω hvis
      obtain ⟨t, ht, y, hy, he⟩ := hvis
      exact absurd he (hω t ht.le y hy)
  · filter_upwards [T.2 haW (not_lt.1 hlo)] with ω hω hvis
    obtain ⟨t, ht, y, hy, he⟩ := hvis
    exact absurd he (hω t ht y hy)

/-! ### Completability along prefix-agreeing paths -/

/-- **Completability sees the paths only through their prefixes.** -/
theorem IsChartCompletable.congr {g₁ g₂ g₁' g₂' : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (h : IsChartCompletable g₁ s₁ g₂ s₂)
    (e₁ : ∀ t ≤ s₁, g₁ t = g₁' t) (e₂ : ∀ t ≤ s₂, g₂ t = g₂' t) : IsChartCompletable g₁' s₁ g₂' s₂ := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hord, hv₁, hv₂⟩ := h
  refine ⟨γ₁, γ₂, ⟨hγ₁.1, hγ₁.2.1, hγ₁.2.2.1, hγ₁.2.2.2.1, fun t ht => (hγ₁.2.2.2.2 t ht).trans (e₁ t ht)⟩,
    ⟨hγ₂.1, hγ₂.2.1, hγ₂.2.2.1, hγ₂.2.2.2.1, fun t ht => (hγ₂.2.2.2.2 t ht).trans (e₂ t ht)⟩, hord, ?_, ?_⟩
  · rw [← e₁ 0 zero_le]; exact hv₁
  · rw [← e₂ 0 zero_le]; exact hv₂

/-- A point at which piecewise constant data have different one-sided germs is a jump candidate. -/
theorem mem_of_germ_ne {g : ℝ → ℝ} {J : Finset ℝ} (hg : IsPiecewiseConstantBoundaryData g J) {y ε u v : ℝ}
    (hε : 0 < ε) (hu : ∀ x, y - ε < x → x < y → g x = u) (hv : ∀ x, y < x → x < y + ε → g x = v) (huv : u ≠ v) :
    y ∈ J := by
  by_contra hy
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hg y hy)
  set r := min (δ / 2) (ε / 2) with hr
  have hr0 : 0 < r := lt_min (half_pos hδ) (half_pos hε)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hrε : r < ε := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
  have h1 : g (y - r) = g y := hball (by rw [Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
  have h2 : g (y + r) = g y := hball (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  rw [hu _ (by linarith) (by linarith)] at h1
  rw [hv _ (by linarith) (by linarith)] at h2
  exact huv (h1.trans h2.symm)

/-! ### The single-density transfer from a reference frame, at one datum -/

/-- **Completability of the stopped chart pair from a reference word and G7a, at one datum** (the transfer of W5's real
local frame, p. 535: "G7a compares both entire fresh stopped laws under one density"). Chart datum: a word `c` with the
canonical seed germs at `0` (angle `θ₂`) and `w` (angle `θ₁`), certified by `SeedGerm`; the angle-`θ₁` flow `Γ₁` from
`w` and the angle-`θ₂` flow `Γ₂` from `0` of its GFF. Reference: a word `cR` (jumps `Ĵ`) with the same canonical germs
on collars of radius `ε` and no other jump there, such that for every GFF with data `cR` almost surely every pair of
prefixes strictly before the lifetimes, with real points after the seeds in `K` and a common point after the seeds, is
completable. Then there is a collar radius `ε₀ > 0` such that for every open `G ⊆ K` on which `c = cR` with no jump of
either word, and every bounded open buffer `V` whose closure meets `ℝ` only within `ε₀` of the seeds or in `G`, almost
surely every pair of prefixes strictly inside the exit times from `V`, with real points after the seeds only in `G`
and with a common point after the seeds, is completable. -/
theorem ae_isChartCompletable_of_ref (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ q q₁ q₂ w ε : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord}
    (hS : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) {cR : ℝ → ℝ} {Ĵ : Finset ℝ} (hε : 0 < ε)
    (hcR : IsPiecewiseConstantBoundaryData cR Ĵ)
    (gL₂ : ∀ x, 0 - ε < x → x < 0 → cR x = -sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (gR₂ : ∀ x, 0 < x → x < 0 + ε → cR x = sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (gL₁ : ∀ x, w - ε < x → x < w → cR x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    (gR₁ : ∀ x, w < x → x < w + ε → cR x = sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    (hĴ₂ : ∀ x ∈ Ĵ, |x - 0| < ε → x = 0) (hĴ₁ : ∀ x ∈ Ĵ, |x - w| < ε → x = w) {K : Set ℝ}
    {S : Type u} [MeasurableSpace S]
    (hRef : ∀ (Q : Measure S) [IsProbabilityMeasure Q] (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ cR Ĵ → ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ cR Ĵ w θ₁ Q Ĥ α₁ ζ₁ → IsFlowLine κ cR Ĵ 0 θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < ζ₁ x → (s₂ : ℝ≥0∞) < ζ₂ x →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → α₁ x t ∈ H ∨ ((α₁ x t).im = 0 ∧ (α₁ x t).re ∈ K)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → α₂ x t ∈ H ∨ ((α₂ x t).im = 0 ∧ (α₂ x t).re ∈ K)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ α₁ x t₁ = α₂ x t₂) →
        IsChartCompletable (α₁ x) s₁ (α₂ x) s₂)
    (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c.fn c.jumps)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c.fn c.jumps w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c.fn c.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (G : Set ℝ) (V : Set ℂ), IsOpen G → G ⊆ K →
      (∀ x ∈ G, c.fn x = cR x ∧ x ∉ c.jumps ∧ x ∉ Ĵ) → IsOpen V → Bornology.IsBounded V →
      (∀ z ∈ closure V, z.im = 0 → |z.re| < ε₀ ∨ |z.re - w| < ε₀ ∨ z.re ∈ G) →
      ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < exitTime V (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) < exitTime V (Γ₂ x) (U₂ x) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → Γ₁ x t ∈ H ∨ ((Γ₁ x t).im = 0 ∧ (Γ₁ x t).re ∈ G)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → Γ₂ x t ∈ H ∨ ((Γ₂ x t).im = 0 ∧ (Γ₂ x t).re ∈ G)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ x t₁ = Γ₂ x t₂) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  have hw : 0 < w := hS.w_pos
  have hq : 0 < q := hS.1
  have hqq₁ : q < q₁ := hS.2.1
  have hq₁w : q₁ < w := hS.2.2.1
  have hwq₂ : w < q₂ := hS.2.2.2.1
  have hlam := Sec4.sleLambda_pos hκ
  have h0Ĵ : (0 : ℝ) ∈ Ĵ := mem_of_germ_ne hcR hε (fun x h1 h2 => gL₂ x h1 h2) (fun x h1 h2 => gR₂ x h1 h2)
    (by intro he; linarith)
  have hwĴ : w ∈ Ĵ := mem_of_germ_ne hcR hε (fun x h1 h2 => gL₁ x h1 h2) (fun x h1 h2 => gR₁ x h1 h2)
    (by intro he; linarith)
  set ε₀ : ℝ := min (min ε q) (min (w - q₁) (min (q₂ - w) (w / 4))) with hε₀
  have e1 : ε₀ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : ε₀ ≤ q := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : ε₀ ≤ w - q₁ := (min_le_right _ _).trans (min_le_left _ _)
  have e4 : ε₀ ≤ q₂ - w := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e5 : ε₀ ≤ w / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε₀ : 0 < ε₀ := lt_min (lt_min hε hq) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  refine ⟨ε₀, hε₀, fun G V hGo hGK hGC hV hVb hVO => ?_⟩
  set J : Finset ℝ := c.jumps with hJ
  have h0J : (0 : ℝ) ∈ J := (hS.mem_jumps_iff hκ (Or.inl ⟨by linarith, hq⟩)).2 (Or.inl rfl)
  have hwJ : w ∈ J := (hS.mem_jumps_iff hκ (Or.inr ⟨hq₁w, hwq₂⟩)).2 (Or.inr rfl)
  set O : Set ℝ := {x | |x| < ε₀ ∨ |x - w| < ε₀ ∨ x ∈ G} with hOdef
  have hO : IsOpen O := (isOpen_lt (continuous_abs.comp continuous_id) continuous_const).union
    ((isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).union hGo)
  -- the datum with the reference values at the two seeds
  set c' : ℝ → ℝ := fun x => if x = 0 ∨ x = w then cR x else c.fn x with hc'
  have hoff : ∀ y ∉ J, c' y = c.fn y := fun y hy => by
    have : ¬ (y = 0 ∨ y = w) := by rintro (rfl | rfl) <;> contradiction
    simp only [hc', this, ite_false]
  have hoff' : ∀ y ∉ (J : Set ℝ), c' y = c.fn y := fun y hy => hoff y hy
  have hpc : IsPiecewiseConstantBoundaryData c' J := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hy (h ▸ h0J)
    have hyw : y ≠ w := fun h => hy (h ▸ hwJ)
    filter_upwards [c.isPiecewiseConstantBoundaryData y hy, eventually_ne_nhds hy0, eventually_ne_nhds hyw]
      with z hz hz0 hzw
    have : ¬ (z = 0 ∨ z = w) := by rintro (h | h) <;> contradiction
    rw [hoff y hy]
    simp only [hc', this, ite_false]
    exact hz
  have hcO : ∀ x ∈ O, c' x = cR x := by
    intro x hx
    by_cases hx0w : x = 0 ∨ x = w
    · simp only [hc', hx0w, ite_true]
    simp only [hc', hx0w, ite_false]
    push Not at hx0w
    rcases hx with hx | hx | hx
    · rw [abs_lt] at hx
      rcases lt_or_gt_of_ne hx0w.1 with hneg | hpos
      · rw [hS.fn_neg (by linarith) hneg, gL₂ x (by linarith) hneg]
      · rw [hS.fn_pos hpos (by linarith), gR₂ x hpos (by linarith)]
    · rw [abs_lt] at hx
      rcases lt_or_gt_of_ne hx0w.2 with hlt | hgt
      · rw [hS.fn_left (by linarith) hlt, gL₁ x (by linarith) hlt]
      · rw [hS.fn_right hgt (by linarith), gR₁ x hgt (by linarith)]
    · exact (hGC x hx).1
  have hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ Ĵ := by
    intro x hx
    rcases hx with hx | hx | hx
    · have hx' := hx
      rw [abs_lt] at hx'
      rw [hS.mem_jumps_iff hκ (Or.inl ⟨by linarith, by linarith⟩)]
      constructor
      · rintro (h | h)
        · rw [h]; exact h0Ĵ
        · exfalso; rw [h] at hx'; linarith [hx'.2]
      · intro hxĴ
        exact Or.inl (hĴ₂ x hxĴ (by rw [sub_zero]; exact lt_of_lt_of_le hx e1))
    · have hx' := hx
      rw [abs_lt] at hx'
      rw [hS.mem_jumps_iff hκ (Or.inr ⟨by linarith, by linarith⟩)]
      constructor
      · rintro (h | h)
        · exfalso; rw [h] at hx'; linarith [hx'.1]
        · rw [h]; exact hwĴ
      · intro hxĴ
        exact Or.inr (hĴ₁ x hxĴ (lt_of_lt_of_le hx e1))
    · exact iff_of_false (hGC x hx).2.1 (hGC x hx).2.2
  have hVO' : ∀ z ∈ closure V, z.im = 0 → z.re ∈ O := fun z hz hz0 => hVO z hz hz0
  have hH' : IsGFFWithBoundaryData Q₀ H₀ c' J := (isGFFWithBoundaryData_congr Q₀ H₀ hoff').2 hH
  have h₁' : IsFlowLine κ c' J w θ₁ Q₀ H₀ Γ₁ U₁ := (isFlowLine_congr_of_eqOn hoff).2 h₁
  have h₂' : IsFlowLine κ c' J 0 θ₂ Q₀ H₀ Γ₂ U₂ := (isFlowLine_congr_of_eqOn hoff).2 h₂
  -- G7a's single-density comparison with the reference
  obtain ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, hagree⟩ :=
    hG3 κ hκ hκ4 c' cR J Ĵ hpc hcR O hO hcO hJO V hV hVb hVO' w 0 θ₁ θ₂ Q₀ H₀ hH' Γ₁ Γ₂ U₁ U₂ h₁' h₂'
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (Z x) with hQ
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    have hint : Integrable Z Q₀ := Integrable.of_integral_ne_zero (by rw [hZ1]; exact one_ne_zero)
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (hZpos.mono fun x hx => hx.le), hZ1, ENNReal.ofReal_one]
  have hPQ : Q₀ ≪ Q := by
    refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp_aemeasurable hZm) ?_
    filter_upwards [hZpos] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne'
  have hRef₀ : ∀ᵐ x ∂Q₀, _ := hPQ.ae_le (hRef Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂)
  filter_upwards [hRef₀, hagree] with x hRx hAx s₁ s₂ hs₁ hs₂ hp₁ hp₂ hcom
  obtain ⟨⟨hT₁, ha₁⟩, ⟨hT₂, ha₂⟩⟩ := hAx
  have e₁ : ∀ t ≤ s₁, Γ₁ x t = α₁ x t := fun t ht => ha₁ t ((ENNReal.coe_le_coe.2 ht).trans hs₁.le)
  have e₂ : ∀ t ≤ s₂, Γ₂ x t = α₂ x t := fun t ht => ha₂ t ((ENNReal.coe_le_coe.2 ht).trans hs₂.le)
  have hζ₁ : (s₁ : ℝ≥0∞) < ζ₁ x := lt_of_lt_of_le (hT₁ ▸ hs₁) (min_le_left _ _)
  have hζ₂ : (s₂ : ℝ≥0∞) < ζ₂ x := lt_of_lt_of_le (hT₂ ▸ hs₂) (min_le_left _ _)
  have hR := hRx s₁ s₂ hζ₁ hζ₂
    (fun t ht hts => by
      rw [← e₁ t hts]
      rcases hp₁ t ht hts with h | ⟨h0, hG⟩
      · exact Or.inl h
      · exact Or.inr ⟨h0, hGK hG⟩)
    (fun t ht hts => by
      rw [← e₂ t hts]
      rcases hp₂ t ht hts with h | ⟨h0, hG⟩
      · exact Or.inl h
      · exact Or.inr ⟨h0, hGK hG⟩)
    (by
      obtain ⟨t₁, t₂, h1, h2, h3, h4, he⟩ := hcom
      exact ⟨t₁, t₂, h1, h2, h3, h4, by rw [← e₁ t₁ h2, ← e₂ t₂ h4]; exact he⟩)
  exact hR.congr (fun t ht => (e₁ t ht).symm) (fun t ht => (e₂ t ht).symm)

/-! ### The exterior right real case at one datum -/

/-- **Completability of the stopped chart pair from the G8 frame (with G9) and G7a, at one datum** (W5's exterior
right real frame, p. 535): `ae_isChartCompletable_of_ref` with the G8 reference for a height `C` with
`−2 < (C + θ₁χ)/λ − 1 < κ/2 − 2` on a compact interval `[a, b]` right of `w`. -/
theorem ae_isChartCompletable_of_frame (hG8 : G8FrameStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ q q₁ q₂ w a b C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {c : BoundaryWord}
    (hS : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) (hwa : w < a) (hab : a ≤ b)
    (hr₁ : -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ))
    (hr₂ : Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c.fn c.jumps)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c.fn c.jumps w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c.fn c.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (G : Set ℝ) (V : Set ℂ), IsOpen G → G ⊆ Icc a b →
      (∀ x ∈ G, c.fn x = C ∧ x ∉ c.jumps) → IsOpen V → Bornology.IsBounded V →
      (∀ z ∈ closure V, z.im = 0 → |z.re| < ε₀ ∨ |z.re - w| < ε₀ ∨ z.re ∈ G) →
      ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < exitTime V (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) < exitTime V (Γ₂ x) (U₂ x) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → Γ₁ x t ∈ H ∨ ((Γ₁ x t).im = 0 ∧ (Γ₁ x t).re ∈ G)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → Γ₂ x t ∈ H ∨ ((Γ₂ x t).im = 0 ∧ (Γ₂ x t).re ∈ G)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ x t₁ = Γ₂ x t₂) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  obtain ⟨cR, Ĵ, ε, hε, hcR, gL₂, gR₂, gL₁, gR₁, hĴ₂, hĴ₁, hJab, hRef⟩ :=
    hG8 κ hκ hκ4 θ₁ θ₂ 0 w C a b hθ hS.w_pos hwa hab hr₁ hr₂
  obtain ⟨ε₀, hε₀, hmain⟩ := ae_isChartCompletable_of_ref hG3 hκ hκ4 hS hε hcR gL₂ gR₂ gL₁ gR₁ hĴ₂ hĴ₁
    (K := Icc a b) (fun Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂ => hRef Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂) Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  refine ⟨ε₀, hε₀, fun G V hGo hGab hGC hV hVb hVO => hmain G V hGo hGab (fun x hx => ?_) hV hVb hVO⟩
  exact ⟨(hGC x hx).1.trans (hJab x (hGab hx)).1.symm, (hGC x hx).2, (hJab x (hGab hx)).2⟩

/-! ### The exterior left real case at one datum, by reflection -/

section Reflect

open Sec7.FlowReflect

theorem reflData_reflData (g : ℝ → ℝ) : reflData (reflData g) = g := by
  funext x; simp [reflData]

theorem reflJumps_reflJumps (J : Finset ℝ) : reflJumps (reflJumps J) = J := by
  ext x; simp [mem_reflJumps]

theorem reflectC_eq_refl (z : ℂ) : LP.reflectC z = Supp9B.refl z := rfl

/-- **Completability from the reflected pair**: if the reflected second prefix and the reflected first prefix (labels
exchanged) are completable, so are the original prefixes (seeds real, `g₂(0) ≤ g₁(0)`). -/
theorem IsChartCompletable.of_reflect {g₁ g₂ : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (h₁0 : (g₁ 0).im = 0)
    (h₂0 : (g₂ 0).im = 0) (hseed : (g₂ 0).re ≤ (g₁ 0).re)
    (h : IsChartCompletable (fun t => LP.reflectC (g₂ t)) s₂ (fun t => LP.reflectC (g₁ t)) s₁) :
    IsChartCompletable g₁ s₁ g₂ s₂ := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hord, hv₁, hv₂⟩ := h
  have hγ₁0 : γ₁ 0 = LP.reflectC (g₂ 0) := hγ₁.2.2.2.2 0 zero_le
  have hγ₂0 : γ₂ 0 = LP.reflectC (g₁ 0) := hγ₂.2.2.2.2 0 zero_le
  have hi₁ : (γ₁ 0).im = 0 := by rw [hγ₁0]; simp [LP.reflectC, h₂0]
  have hi₂ : (γ₂ 0).im = 0 := by rw [hγ₂0]; simp [LP.reflectC, h₁0]
  have hdual := Supp9B.range_subset_closedRightSide (Supp9B.isProperCurve_of_isProperCompletion hγ₁)
    (Supp9B.isProperCurve_of_isProperCompletion hγ₂) hi₁ hi₂
    (by rw [hγ₁0, hγ₂0]; simp only [LP.reflectC, Complex.neg_re, Complex.conj_re]; linarith) hord
  have e₁ : Supp9B.reflectCurve (fun t => LP.reflectC (g₁ t)) = g₁ := by
    funext t; simp [Supp9B.reflectCurve, Supp9B.refl, LP.reflectC]
  have e₂ : Supp9B.reflectCurve (fun t => LP.reflectC (g₂ t)) = g₂ := by
    funext t; simp [Supp9B.reflectCurve, Supp9B.refl, LP.reflectC]
  refine ⟨Supp9B.reflectCurve γ₂, Supp9B.reflectCurve γ₁, ?_, ?_, ?_, ?_, ?_⟩
  · have := Supp9B.isProperCompletion_reflectCurve hγ₂
    rwa [e₁] at this
  · have := Supp9B.isProperCompletion_reflectCurve hγ₁
    rwa [e₂] at this
  · rintro _ ⟨t, rfl⟩
    rcases hdual ⟨t, rfl⟩ with hR | hS
    · exact Or.inl (Supp9B.refl_image_rightSide_subset hγ₂.2.2.1 hi₂ ⟨_, hR, rfl⟩)
    · exact Or.inr (Supp9B.refl_image_seedRayClosure_subset γ₂ ⟨_, hS, rfl⟩)
  · rintro ⟨t, ht⟩
    refine hv₂ ⟨t, ?_⟩
    have := congrArg Supp9B.refl ht
    simp only [Supp9B.reflectCurve, Supp9B.refl_refl] at this
    rw [this]; rfl
  · rintro ⟨t, ht⟩
    refine hv₁ ⟨t, ?_⟩
    have := congrArg Supp9B.refl ht
    simp only [Supp9B.reflectCurve, Supp9B.refl_refl] at this
    rw [this]; rfl

/-- **Completability of the stopped chart pair from the reflected G8 frame (with G9) and G7a, at one datum** (W5's
exterior left real frame, p. 535: "On an exterior left interval use its reflection, with the higher-angle left
cumulative weight"): `ae_isChartCompletable_of_ref` with the reference obtained by reflecting the G8 frame of the
reflected configuration (seeds `−w < 0`, angles `−θ₂ < −θ₁`, interval `[−b, −a]`), for a height `C` on `[a, b]`,
`b < 0`, with `−2 < −(C + θ₂χ)/λ − 1 < κ/2 − 2`. -/
theorem ae_isChartCompletable_of_frame_left (hG8 : G8FrameStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ q q₁ q₂ w a b C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {c : BoundaryWord}
    (hS : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) (hab : a ≤ b) (hb0 : b < 0)
    (hl₁ : -2 < Sec4.cumWeightLeft κ (C + θ₂ * QuantumZipper.chiC κ))
    (hl₂ : Sec4.cumWeightLeft κ (C + θ₂ * QuantumZipper.chiC κ) < κ / 2 - 2)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c.fn c.jumps)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c.fn c.jumps w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c.fn c.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (G : Set ℝ) (V : Set ℂ), IsOpen G → G ⊆ Icc a b →
      (∀ x ∈ G, c.fn x = C ∧ x ∉ c.jumps) → IsOpen V → Bornology.IsBounded V →
      (∀ z ∈ closure V, z.im = 0 → |z.re| < ε₀ ∨ |z.re - w| < ε₀ ∨ z.re ∈ G) →
      ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < exitTime V (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) < exitTime V (Γ₂ x) (U₂ x) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → Γ₁ x t ∈ H ∨ ((Γ₁ x t).im = 0 ∧ (Γ₁ x t).re ∈ G)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → Γ₂ x t ∈ H ∨ ((Γ₂ x t).im = 0 ∧ (Γ₂ x t).re ∈ G)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ x t₁ = Γ₂ x t₂) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  have hw := hS.w_pos
  set χ := QuantumZipper.chiC κ with hχ
  have hwt : Sec4.cumWeightRight κ (-C + -θ₂ * χ) = Sec4.cumWeightLeft κ (C + θ₂ * χ) := by
    unfold Sec4.cumWeightRight Sec4.cumWeightLeft; ring
  obtain ⟨cR', Ĵ', ε, hε, hcR', gL₂', gR₂', gL₁', gR₁', hĴ₂', hĴ₁', hJab', hRef'⟩ :=
    hG8 κ hκ hκ4 (-θ₂) (-θ₁) (-w) 0 (-C) (-b) (-a) (neg_lt_neg hθ) (by linarith) (by linarith) (by linarith)
      (by rw [hwt]; exact hl₁) (by rw [hwt]; exact hl₂)
  set cR : ℝ → ℝ := reflData cR' with hcRdef
  set Ĵ : Finset ℝ := reflJumps Ĵ' with hĴdef
  have hcR : IsPiecewiseConstantBoundaryData cR Ĵ := isPiecewiseConstantBoundaryData_reflData hcR'
  have gL₂ : ∀ x, 0 - ε < x → x < 0 → cR x = -sleLambda κ - θ₂ * χ := fun x h1 h2 => by
    simp only [hcRdef, reflData]; rw [gR₁' (-x) (by linarith) (by linarith)]; ring
  have gR₂ : ∀ x, 0 < x → x < 0 + ε → cR x = sleLambda κ - θ₂ * χ := fun x h1 h2 => by
    simp only [hcRdef, reflData]; rw [gL₁' (-x) (by linarith) (by linarith)]; ring
  have gL₁ : ∀ x, w - ε < x → x < w → cR x = -sleLambda κ - θ₁ * χ := fun x h1 h2 => by
    simp only [hcRdef, reflData]; rw [gR₂' (-x) (by linarith) (by linarith)]; ring
  have gR₁ : ∀ x, w < x → x < w + ε → cR x = sleLambda κ - θ₁ * χ := fun x h1 h2 => by
    simp only [hcRdef, reflData]; rw [gL₂' (-x) (by linarith) (by linarith)]; ring
  have hĴ₂ : ∀ x ∈ Ĵ, |x - 0| < ε → x = 0 := fun x hx hxε => by
    have h := hĴ₁' (-x) (mem_reflJumps.1 hx) (by rw [sub_zero, abs_neg]; rwa [sub_zero] at hxε)
    linarith
  have hĴ₁ : ∀ x ∈ Ĵ, |x - w| < ε → x = w := fun x hx hxε => by
    have h := hĴ₂' (-x) (mem_reflJumps.1 hx) (by rw [show -x - -w = -(x - w) by ring, abs_neg]; exact hxε)
    linarith
  -- the reflected reference property
  have hRef : ∀ (Q : Measure S) [IsProbabilityMeasure Q] (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ cR Ĵ → ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ cR Ĵ w θ₁ Q Ĥ α₁ ζ₁ → IsFlowLine κ cR Ĵ 0 θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < ζ₁ x → (s₂ : ℝ≥0∞) < ζ₂ x →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → α₁ x t ∈ H ∨ ((α₁ x t).im = 0 ∧ (α₁ x t).re ∈ Icc a b)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → α₂ x t ∈ H ∨ ((α₂ x t).im = 0 ∧ (α₂ x t).re ∈ Icc a b)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ α₁ x t₁ = α₂ x t₂) →
        IsChartCompletable (α₁ x) s₁ (α₂ x) s₂ := by
    intro Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂
    have hĤ' := Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hĤ
    rw [hcRdef, hĴdef, reflData_reflData, reflJumps_reflJumps] at hĤ'
    have hβ₁ := Sec7.FlowReflect.IsFlowLine.reflect hcR hα₂
    have hβ₂ := Sec7.FlowReflect.IsFlowLine.reflect hcR hα₁
    rw [hcRdef, hĴdef, reflData_reflData, reflJumps_reflJumps, neg_zero] at hβ₁
    rw [hcRdef, hĴdef, reflData_reflData, reflJumps_reflJumps] at hβ₂
    filter_upwards [hRef' Q _ hĤ' _ _ ζ₂ ζ₁ hβ₁ hβ₂, Supp9.ae_apply_zero_of_isFlowLine hα₁,
      Supp9.ae_apply_zero_of_isFlowLine hα₂] with x hx z₁ z₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ hcom
    have hreal : ∀ (g : S → ℝ≥0 → ℂ) (s : ℝ≥0),
        (∀ t : ℝ≥0, 0 < t → t ≤ s → g x t ∈ H ∨ ((g x t).im = 0 ∧ (g x t).re ∈ Icc a b)) →
        ∀ t : ℝ≥0, 0 < t → t ≤ s → LP.reflectC (g x t) ∈ H ∨
          ((LP.reflectC (g x t)).im = 0 ∧ (LP.reflectC (g x t)).re ∈ Icc (-b) (-a)) := by
      intro g s hp t ht hts
      rcases hp t ht hts with h | ⟨h0, hre⟩
      · exact Or.inl (LP.reflectC_mem_H_iff.2 h)
      · refine Or.inr ⟨by simp [LP.reflectC, h0], ?_⟩
        simp only [LP.reflectC, Complex.neg_re, Complex.conj_re]
        exact ⟨by linarith [hre.2], by linarith [hre.1]⟩
    have hR := hx s₂ s₁ hs₂ hs₁ (hreal α₂ s₂ hp₂) (hreal α₁ s₁ hp₁) (by
      obtain ⟨t₁, t₂, h1, h2, h3, h4, he⟩ := hcom
      exact ⟨t₂, t₁, h3, h4, h1, h2, by rw [he]⟩)
    refine IsChartCompletable.of_reflect (by rw [z₁]; simp) (by rw [z₂]; simp) (by rw [z₁, z₂]; simpa using hw.le)
      hR
  obtain ⟨ε₀, hε₀, hmain⟩ := ae_isChartCompletable_of_ref hG3 hκ hκ4 hS hε hcR gL₂ gR₂ gL₁ gR₁ hĴ₂ hĴ₁
    (K := Icc a b) hRef Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  refine ⟨ε₀, hε₀, fun G V hGo hGab hGC hV hVb hVO => hmain G V hGo hGab (fun x hx => ?_) hV hVb hVO⟩
  have hx' := hJab' (-x) ⟨by linarith [(hGab hx).2], by linarith [(hGab hx).1]⟩
  refine ⟨?_, (hGC x hx).2, fun h => hx'.2 (mem_reflJumps.1 h)⟩
  rw [(hGC x hx).1]
  simp only [hcRdef, reflData, hx'.1, neg_neg]

end Reflect

end RLC

end InteractingSLE
