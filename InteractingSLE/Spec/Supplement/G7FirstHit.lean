/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7Measurable

/-!
# Theorem 1.5's interface 4 (G7 + GB7a at a retained pair) from G7, GB7a and the collar's joint activity

Packet PROVE-G7GB7A. The landed interface `Theorem15D5.G7GB7aFirstHitStatement` (`planning/handoffs/PROVE-T15-D5.md`)
is proved here from three named inputs, each one source step of the proof of Theorem 7.12D (specification
supplement pp. 543–544):

* `Supp7.G7RetainedPairStatement` (Lemma G7 at a retained pair, with the outer word of Aux. 85–86, as a kernel
  carrier; `G7Carrier.lean`);
* `Supp8.GB7aFlowStatement` (Lemma GB7a for one flow line; `GB7aFlow.lean`), applied to the conditional flow line under
  the kernel (universe `0`);
* `Supp7.CollarActivityStatement` (the rational-cut collar's joint activity, deterministic; `G7Carrier.lean`).

## Proof

Fix an outcome with W0's ordered completions for all strict prefixes and increasing strict contacts, and a proposed
first new hit `η₂(t) = η₁(x) ∈ ℍ`, `x < u`, of `η₁([0, u])` after `r`. The completions make both paths injective on
their strict prefixes and continuous there (`injOn_fst_of_completions`, `continuousAt_fst_of_completions`, …).

1. *The retained pair* (`exists_retainedPair`). The collar gives `δ > 0` with joint activity for cutoffs `u'` just
   after `x` and `r'` just before `t`; choose them rational and so close that both tips are interior (continuity).
   The second tip is off `η₁([0, u'])` (the hit is the first after `r < r'`); the first tip is off `η₂([0, r'])`
   (a contact `η₁(u') = η₂(t'')`, `t'' ≤ r' < t`, with `x < u'` contradicts the strict contact order). So
   `(u', r')` is an ordinary retained pair, and `t` is still the first new hit of `η₁([0, u'])` after `r'`.
2. *The chart visit* (`exists_visit_of_isRetainedContinuation`). G7's clock reaches the physical time `t` (no new
   contact with `A = η₁([0, u']) ∪ η₂([0, r'])` in `(r', t)`: none with the first prefix by the first-hit
   property, none with the second prefix by injectivity) at a chart time `s ≤ σ ≤ U` with `ψ(Γ(s)) = η₁(x)`. As
   `η₁(x) ∈ A` is not in the active domain, `Γ(s) ∉ ℍ`; since the conditional path lies in `ℍ̄`, `Γ(s) = y` is real.
   `ψ(y) = η₁(x)` is interior, not a tip (injectivity of `η₁`, `η₂(r') ∉ η₁([0, u'])`) and not an old common point
   (injectivity of `η₂`), so the outer word gives `y ≠ 0`, `y` off the datum's jumps, and outward cumulative weight
   at least `κ/2 − 2`.
3. *Re-integration* (`measure_visitsStrip_eq_zero`, `ae_not_mem_prod_of_compProd_eq`). A rational interval
   `[a, b] ∋ y` free of the datum's jump positions and on the side of `y` puts the datum in `goodInterval` and the
   chart path in the strip event `VisitsStrip`. Under the kernel, for every datum in `goodInterval`, GB7a (for the
   conditional angle-`θ₂` flow line from `0`, its points `y ∈ [a, b]`) and `Γ ∈ ℍ̄` make the strip event null; so the
   product event is null for the joint law, hence almost surely never realized. Countably many rational pairs
   `(u', r')` and intervals `[a, b]` cover all proposed hits.

## Main results

* **`g7GB7aFirstHitStatement_of_inputs`**:
  `G7RetainedPairStatement.{u} → Supp8.GB7aFlowStatement.{0} → CollarActivityStatement → G7GB7aFirstHitStatement.{u}`;
* `exists_retainedPair`, `exists_visit_of_isRetainedContinuation`, `exists_goodInterval_of_visit` (pathwise);
* `measure_visitsStrip_eq_zero` (GB7a under one conditional law).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

open Restart Theorem15D5

/-! ### Consequences of W0's completions for all strict prefixes -/

section Completions

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- The first path is injective on its strict prefixes. -/
theorem injOn_fst_of_completions
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    {c₀ : ℝ≥0} (hc₀ : (c₀ : ℝ≥0∞) < ζ₂) : InjOn η₁ {s | (s : ℝ≥0∞) < ζ₁} := by
  intro s hs s' hs' he
  obtain ⟨α', β', hα, -, -⟩ := hW (max s s') c₀ (by rw [ENNReal.coe_max]; exact max_lt hs hs') hc₀
  have h1 := hα.2.2.2.2 s (le_max_left _ _)
  have h2 := hα.2.2.2.2 s' (le_max_right _ _)
  exact hα.2.1 (h1.trans (he.trans h2.symm))

/-- The second path is injective on its strict prefixes. -/
theorem injOn_snd_of_completions
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    {a₀ : ℝ≥0} (ha₀ : (a₀ : ℝ≥0∞) < ζ₁) : InjOn η₂ {t | (t : ℝ≥0∞) < ζ₂} := by
  intro t ht t' ht' he
  obtain ⟨α', β', -, hβ, -⟩ := hW a₀ (max t t') ha₀ (by rw [ENNReal.coe_max]; exact max_lt ht ht')
  have h1 := hβ.2.2.2.2 t (le_max_left _ _)
  have h2 := hβ.2.2.2.2 t' (le_max_right _ _)
  exact hβ.2.1 (h1.trans (he.trans h2.symm))

/-- The first path is continuous at its strictly available times. -/
theorem continuousAt_fst_of_completions
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    {c₀ : ℝ≥0} (hc₀ : (c₀ : ℝ≥0∞) < ζ₂) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₁) : ContinuousAt η₁ s := by
  obtain ⟨a, hsa, haζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  obtain ⟨α', β', hα, -, -⟩ := hW a c₀ haζ hc₀
  have hev : α' =ᶠ[𝓝 s] η₁ := by
    filter_upwards [Iio_mem_nhds (ENNReal.coe_lt_coe.1 hsa)] with t' ht'
    exact hα.2.2.2.2 t' (le_of_lt ht')
  exact hα.1.continuousAt.congr hev

/-- The second path is continuous at its strictly available times. -/
theorem continuousAt_snd_of_completions
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    {a₀ : ℝ≥0} (ha₀ : (a₀ : ℝ≥0∞) < ζ₁) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ₂) : ContinuousAt η₂ t := by
  obtain ⟨c, htc, hcζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨α', β', -, hβ, -⟩ := hW a₀ c ha₀ hcζ
  have hev : β' =ᶠ[𝓝 t] η₂ := by
    filter_upwards [Iio_mem_nhds (ENNReal.coe_lt_coe.1 htc)] with t' ht'
    exact hβ.2.2.2.2 t' (le_of_lt ht')
  exact hβ.1.continuousAt.congr hev

/-- A continuous path at `s` with `η s ∈ ℍ` stays in `ℍ` at all times within some distance of `s`. -/
theorem exists_pos_forall_mem_H {η : ℝ≥0 → ℂ} {s : ℝ≥0} (hc : ContinuousAt η s) (hs : η s ∈ QuantumZipper.H) :
    ∃ ε > 0, ∀ s' : ℝ≥0, dist s' s < ε → η s' ∈ QuantumZipper.H := by
  have hopen : IsOpen QuantumZipper.H := isOpen_lt continuous_const Complex.continuous_im
  exact Metric.eventually_nhds_iff.1 (hc.eventually (hopen.mem_nhds hs))

end Completions

/-! ### Step 1: a rational ordinary retained pair at a proposed first hit -/

/-- **The retained pair of the collar.** At a proposed first new hit `η₂(t) = η₁(x) ∈ ℍ`, `x < u`, of `η₁([0, u])` after
`r`, under W0's completions and the strict contact order, the collar's joint activity gives rational cutoffs
`u' ∈ (x, u]`, `r' ∈ (r, t)` forming an ordinary retained pair. -/
theorem exists_retainedPair (hCol : CollarActivityStatement) {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    (hO : StrictContactsIncreasing η₁ ζ₁ η₂ ζ₂) {u r t x : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₁) (hrt : r < t)
    (ht : (t : ℝ≥0∞) < ζ₂) (hxu : x < u) (heq : η₂ t = η₁ x) (hH : η₁ x ∈ QuantumZipper.H)
    (hr2 : η₂ r ∉ η₁ '' Icc 0 u) (hfirst : ∀ t' : ℝ≥0, r < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u) :
    ∃ q : ℚ × ℚ, IsOrdinaryRetainedPair η₁ ζ₁ (q.1 : ℝ).toNNReal η₂ ζ₂ (q.2 : ℝ).toNNReal ∧
      x < (q.1 : ℝ).toNNReal ∧ (q.1 : ℝ).toNNReal ≤ u ∧ r < (q.2 : ℝ).toNNReal ∧ (q.2 : ℝ).toNNReal < t := by
  obtain ⟨δ, hδ, hact⟩ := hCol η₁ η₂ ζ₁ ζ₂ hW hO u r t x hu hrt ht hxu heq hH hr2 hfirst
  have hr : (r : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hrt).trans ht
  have hxζ : (x : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hxu).trans hu
  obtain ⟨ε₁, hε₁, hH₁⟩ := exists_pos_forall_mem_H (continuousAt_fst_of_completions hW hr hxζ) hH
  obtain ⟨ε₂, hε₂, hH₂⟩ := exists_pos_forall_mem_H (continuousAt_snd_of_completions hW hu ht)
    (heq.symm ▸ hH)
  have hδr : (0 : ℝ) < δ := hδ
  -- the first cutoff
  obtain ⟨q₁, hq₁l, hq₁r⟩ := exists_rat_btwn (show (x : ℝ) < min (min ((x : ℝ) + δ) ((x : ℝ) + ε₁)) u from
    lt_min (lt_min (by linarith) (by linarith)) (by exact_mod_cast hxu))
  -- the second cutoff
  obtain ⟨q₂, hq₂l, hq₂r⟩ := exists_rat_btwn (show max (max ((t : ℝ) - δ) ((t : ℝ) - ε₂)) r < t from
    max_lt (max_lt (by linarith) (by linarith)) (by exact_mod_cast hrt))
  have hx0 : (0 : ℝ) ≤ x := x.2
  have hr0 : (0 : ℝ) ≤ r := r.2
  have hq₁0 : (0 : ℝ) ≤ q₁ := hx0.trans hq₁l.le
  have hq₂0 : (0 : ℝ) ≤ q₂ := hr0.trans ((le_max_right _ _).trans hq₂l.le)
  set u' := (q₁ : ℝ).toNNReal with hu'
  set r' := (q₂ : ℝ).toNNReal with hr'
  have hu'r : (u' : ℝ) = q₁ := Real.coe_toNNReal _ hq₁0
  have hr'r : (r' : ℝ) = q₂ := Real.coe_toNNReal _ hq₂0
  have hxu' : x < u' := by rw [← NNReal.coe_lt_coe, hu'r]; exact hq₁l
  have hu'δ : u' < x + δ := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, hu'r]
    exact hq₁r.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hu'u : u' ≤ u := by
    rw [← NNReal.coe_le_coe, hu'r]; exact hq₁r.le.trans (min_le_right _ _)
  have hu'ε : dist u' x < ε₁ := by
    rw [NNReal.dist_eq, hu'r, abs_of_pos (by linarith)]
    have := hq₁r.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hrr' : r < r' := by
    rw [← NNReal.coe_lt_coe, hr'r]; exact (le_max_right _ _).trans_lt hq₂l
  have hr't : r' < t := by rw [← NNReal.coe_lt_coe, hr'r]; exact hq₂r
  have hr'δ : t < r' + δ := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, hr'r]
    have := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hq₂l)
    linarith
  have hr'ε : dist r' t < ε₂ := by
    rw [NNReal.dist_eq, hr'r, abs_of_neg (by linarith)]
    have := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hq₂l)
    linarith
  obtain ⟨hact₁, hact₂⟩ := hact u' r' hxu' hu'δ hu'u hrr' hr'δ hr't
  have hu'ζ : (u' : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 hu'u).trans_lt hu
  have hr'ζ : (r' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hr't).trans ht
  refine ⟨(q₁, q₂), ⟨hu'ζ, hr'ζ, hH₁ u' hu'ε, hH₂ r' hr'ε, ?_, ?_, hact₁, hact₂, hW u' r' hu'ζ hr'ζ⟩,
    hxu', hu'u, hrr', hr't⟩
  · exact fun hmem => hfirst r' hrr' hr't (image_mono (Icc_subset_Icc_right hu'u) hmem)
  · rintro ⟨t'', ht'', he⟩
    have ht''ζ : (t'' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 ht''.2).trans_lt hr'ζ
    have := hO x u' t t'' hxζ hu'ζ ht ht''ζ heq.symm he.symm hxu'
    exact absurd (this.trans_le ht''.2) (not_lt.2 hr't.le)

/-! ### Step 2: the chart visit of a real point with weight at least `c` -/

/-- **The chart visit.** At a retained pair `(u', r')` with the pathwise G7 relation and the outer word, a first new hit
`η₂(t) = η₁(x) ∈ ℍ`, `x < u'`, of `η₁([0, u'])` after `r'` is the inverse-chart image of a real chart point
`y = Γ(s)`, `s ≤ U`, which is not `0`, not a jump of the datum, and has outward cumulative weight at least
`κ/2 − 2`. -/
theorem exists_visit_of_isRetainedContinuation {κ θ₂ : ℝ} {h H : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {u' r' : ℝ≥0} {c : BoundaryWord} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hRC : IsRetainedContinuation κ θ₂ h H η₁ u' η₂ ζ₂ r' c Γ U)
    (hIm : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ U → 0 ≤ (Γ s).im)
    (hinj₁ : InjOn η₁ {s | (s : ℝ≥0∞) < ζ₁}) (hinj₂ : InjOn η₂ {t | (t : ℝ≥0∞) < ζ₂})
    (hu' : (u' : ℝ≥0∞) < ζ₁) {t x : ℝ≥0} (hr't : r' < t) (ht : (t : ℝ≥0∞) < ζ₂) (hxu' : x < u')
    (heq : η₂ t = η₁ x) (hH : η₁ x ∈ QuantumZipper.H) (hr2 : η₂ r' ∉ η₁ '' Icc 0 u')
    (hfirst : ∀ t' : ℝ≥0, r' < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u') :
    ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ U ∧ ∃ y : ℝ, Γ s = y ∧ y ≠ 0 ∧ y ∉ c.jumps ∧
      (0 < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn y + θ₂ * QuantumZipper.chiC κ)) ∧
      (y < 0 → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn y + θ₂ * QuantumZipper.chiC κ)) := by
  obtain ⟨φ, ψ, lift, c₂, σ, -, hψ, -, -, -, -, -, hσU, -, himg, hid, hQ⟩ := hRC
  have hxζ : (x : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hxu').trans hu'
  have htmem : t ∈ {t : ℝ≥0 | r' ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧
      ∀ t' : ℝ≥0, r' < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u' ∪ η₂ '' Icc 0 r'} := by
    refine ⟨hr't.le, ht.le, fun t' h1 h2 hmem => ?_⟩
    rcases hmem with hmem | ⟨t₀, ht₀, he⟩
    · exact hfirst t' h1 h2 hmem
    · have ht'ζ : (t' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 h2).trans ht
      have ht₀ζ : (t₀ : ℝ≥0∞) < ζ₂ :=
        (ENNReal.coe_le_coe.2 (ht₀.2.trans h1.le)).trans_lt ht'ζ
      have := hinj₂ ht₀ζ ht'ζ he
      exact absurd (this ▸ ht₀.2) (not_le.2 h1)
  rw [← himg] at htmem
  obtain ⟨s, hs, hcs⟩ := htmem
  have hψs : ψ (Γ s) = η₁ x := by rw [← hid s hs, hcs, heq]
  have hnotH : Γ s ∉ QuantumZipper.H := by
    intro hΓ
    have hD := hψ.mapsTo hΓ
    rw [hψs] at hD
    exact hD.1.2 (Or.inl ⟨x, ⟨zero_le, hxu'.le⟩, rfl⟩)
  have him0 : (Γ s).im = 0 :=
    le_antisymm (not_lt.1 hnotH) (hIm s (hs.trans hσU))
  set y : ℝ := (Γ s).re with hy
  have hΓy : Γ s = (y : ℂ) := Complex.ext (by simp [hy]) (by simp [him0])
  have hψy : ψ y = η₁ x := by rw [← hΓy, hψs]
  have hne1 : ψ y ≠ η₂ r' := by
    rw [hψy]; intro he
    exact hr2 ⟨x, ⟨zero_le, hxu'.le⟩, he⟩
  have hne2 : ψ y ≠ η₁ u' := by
    rw [hψy]; intro he
    exact absurd (hinj₁ hxζ hu' he) (ne_of_lt hxu')
  have hne3 : ψ y ∉ η₁ '' Icc 0 u' ∩ η₂ '' Icc 0 r' := by
    rw [hψy]; rintro ⟨-, t₀, ht₀, he⟩
    have ht₀ζ : (t₀ : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 (ht₀.2.trans hr't.le)).trans_lt ht
    have := hinj₂ ht₀ζ ht (he.trans heq.symm)
    exact absurd (this ▸ ht₀.2) (not_le.2 hr't)
  obtain ⟨hy0, hyJ, hyR, hyL⟩ := hQ y (by rw [hψy]; exact hH) hne1 hne2 hne3
  exact ⟨s, hs.trans hσU, y, hΓy, hy0, hyJ, hyR, hyL⟩

/-! ### Step 3: the rational interval and GB7a under the kernel -/

/-- A real point off the jumps, with outward cumulative weight at least `κ/2 − 2`, lies in a rational interval in
`goodInterval`. -/
theorem exists_goodInterval_of_visit {κ θ : ℝ} {c : BoundaryWord} {y : ℝ} (hy0 : y ≠ 0) (hyJ : y ∉ c.jumps)
    (hyR : 0 < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn y + θ * QuantumZipper.chiC κ))
    (hyL : y < 0 → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn y + θ * QuantumZipper.chiC κ)) :
    ∃ ab : ℚ × ℚ, c ∈ goodInterval κ θ ab.1 ab.2 ∧ y ∈ Icc (ab.1 : ℝ) ab.2 := by
  obtain ⟨q₁, q₂, hy, hJ, hR, hL⟩ := Supp8.exists_rat_Ioo_avoid c.jumps hyJ (x := 0) hy0.symm
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hy.1
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hy.2
  have hpos : ∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i := by
    intro i hi
    have hmem : c.2.1 i ∉ Ioo (q₁ : ℝ) q₂ := fun hm => hJ _ hm (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩)
    rcases le_or_gt (c.2.1 i) q₁ with h | h
    · exact Or.inl (h.trans_lt ha1)
    · have : (q₂ : ℝ) ≤ c.2.1 i := le_of_not_gt fun h' => hmem ⟨h, h'⟩
      exact Or.inr (hb2.trans_le this)
  have hyab : y ∈ Icc (a : ℝ) b := ⟨ha2.le, hb1.le⟩
  have hfn : c.fn y = c.fn a := fn_eq_of_positions hpos hyab
  refine ⟨(a, b), ⟨hpos, ?_⟩, hyab⟩
  rcases lt_or_gt_of_ne hy0 with hneg | hpos'
  · refine Or.inr ⟨hb2.trans_le (hL hneg), ?_⟩
    rw [← hfn]; exact hyL hneg
  · refine Or.inl ⟨(hR hpos').trans_lt ha1, ?_⟩
    rw [← hfn]; exact hyR hpos'

/-- **GB7a under one conditional law**: for a datum in `goodInterval`, the conditional angle-`θ` flow line from `0`
almost surely does not visit the strip over `[a, b]`. -/
theorem measure_visitsStrip_eq_zero (hGB : Supp8.GB7aFlowStatement.{0}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {S : Type} [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q]
    {H : S → LQGMetric.DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} {c : BoundaryWord}
    (hgff : IsGFFWithBoundaryData Q H c.fn c.jumps) (hfl : IsFlowLine κ c.fn c.jumps 0 θ Q H Γ U)
    {a b : ℝ} (hc : c ∈ goodInterval κ θ a b) : Q {s | VisitsStrip (Γ s) (U s) a b} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [Supp8.GB7aFlowStatement.ae_forall hGB hκ hκ4 (BoundaryWord.isPiecewiseConstantBoundaryData c)
    hgff hfl, ae_im_nonneg_of_isFlowLine hfl] with s hGBs hIm
  rintro ⟨t, htU, hz0, hza, hzb⟩
  have him0 : (Γ s t).im = 0 := le_antisymm hz0 (hIm t htU)
  set y : ℝ := (Γ s t).re with hy
  have hΓy : Γ s t = (y : ℂ) := Complex.ext (by simp [hy]) (by simp [him0])
  have hyab : y ∈ Icc a b := ⟨hza, hzb⟩
  have hyJ := goodInterval_notMem_jumps hc hyab
  have hfn := goodInterval_fn_eq hc hyab
  rcases hc.2 with ⟨ha, hw⟩ | ⟨hb, hw⟩
  · rw [← hfn] at hw
    exact (hGBs t htU y hyJ).1 (ha.trans_le hza) hw hΓy
  · rw [← hfn] at hw
    exact (hGBs t htU y hyJ).2 (hzb.trans_lt hb) hw hΓy

/-! ### The interface -/

/-- **Theorem 1.5's interface 4 (G7 + GB7a at a retained pair)** from Lemma G7 at the retained pair (with the outer
word), Lemma GB7a for one flow line, and the collar's joint activity. -/
theorem g7GB7aFirstHitStatement_of_inputs (hG7 : G7RetainedPairStatement.{u}) (hGB : Supp8.GB7aFlowStatement.{0})
    (hCol : CollarActivityStatement) : G7GB7aFirstHitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have hC := fun q : ℚ × ℚ => hG7 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
    (q.1 : ℝ).toNNReal (q.2 : ℝ).toNNReal
  choose S mS H Γ U M β X K hHm hUm hΓm hΓc hM hβ hX hK hlaw hpair hpath using hC
  -- the conditional paths lie in `ℍ̄`
  have E2 : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ M q →
      X q ω ∈ {s | ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U q s → 0 ≤ (Γ q s t).im} := by
    intro q
    let _ := mS q
    have := hK q
    refine Restart.ae_mem_of_compProd_eq (hM q) (hβ q) (hX q) (hlaw q)
      (measurableSet_forall_im_nonneg (hUm q) (hΓm q) (hΓc q)) ?_
    filter_upwards [hpair q] with c hc
    exact ae_im_nonneg_of_isFlowLine hc.2
  -- GB7a, integrated back as a product event
  have E3 : ∀ q ab : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ M q →
      ¬ (β q ω ∈ goodInterval κ θ₂ ab.1 ab.2 ∧
        X q ω ∈ {s | VisitsStrip (Γ q s) (U q s) ab.1 ab.2}) := by
    intro q ab
    let _ := mS q
    have := hK q
    refine ae_not_mem_prod_of_compProd_eq (hM q) (hβ q) (hX q) (hlaw q) (measurableSet_goodInterval _ _ _ _)
      (measurableSet_visitsStrip (hUm q) (hΓm q) (hΓc q) _ _) ?_
    filter_upwards [hpair q] with c hc hcA
    exact measure_visitsStrip_eq_zero hGB hκ hκ4 hc.1 hc.2 hcA
  filter_upwards [ae_all_iff.2 hpath, ae_all_iff.2 E2, ae_all_iff.2 fun q => ae_all_iff.2 (E3 q)]
    with ω hP hI hV
  intro hord hstrict u r hu hr hr2 t x hrt ht hxu heq hHx hfirst
  obtain ⟨q, hret, hxu', hu'u, hrr', hr't⟩ :=
    exists_retainedPair hCol hord hstrict hu hrt ht hxu heq hHx hr2 hfirst
  obtain ⟨hMω, hRC⟩ := hP q hret
  have hinj₁ := injOn_fst_of_completions hord hr
  have hinj₂ := injOn_snd_of_completions hord hu
  have hfirst' : ∀ t' : ℝ≥0, (q.2 : ℝ).toNNReal < t' → t' < t →
      η₂ ω t' ∉ η₁ ω '' Icc 0 (q.1 : ℝ).toNNReal := fun t' h1 h2 hmem =>
    hfirst t' (hrr'.trans h1) h2 (image_mono (Icc_subset_Icc_right hu'u) hmem)
  obtain ⟨s, hsU, y, hΓy, hy0, hyJ, hyR, hyL⟩ :=
    exists_visit_of_isRetainedContinuation hRC (hI q hMω) hinj₁ hinj₂ hret.1 hr't ht hxu' heq hHx
      hret.2.2.2.2.1 hfirst'
  obtain ⟨ab, hcA, hyab⟩ := exists_goodInterval_of_visit hy0 hyJ hyR hyL
  refine hV q ab hMω ⟨hcA, s, hsU, ?_, ?_, ?_⟩
  · rw [hΓy]; simp
  · rw [hΓy]; simpa using hyab.1
  · rw [hΓy]; simpa using hyab.2

end Supp7

end InteractingSLE
