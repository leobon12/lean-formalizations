/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCChart
import InteractingSLE.Spec.Supplement.S9Propagation

/-!
# Lemmas G2 / G2b and G3 as named inputs, and the single-density transfer of completability (part (e))

Packet PROVE-RLC-A, parts (b), (e). Sources: supplement §7.1–§7.3 (`source/spec/p481-528.md` L225–L320, pp. 490–493):
Lemma G1 (simultaneous transfer), Lemma G2 (four-height reference) with G2b (opposite-seed avoidance), Lemma G3
(interior two-tip comparison) and its proof.

* `g2Data`: the four-height boundary data of Lemma G2;
* `G2ReferenceStatement` (**named input**, Lemma G2 with G2b, exactly): the angle-`θ₁` flow from `w₁` and the
  angle-`θ₂` flow from `w₂` of the four-height GFF are complete (`ζ = ∞`), proper, simple, ordered (the higher-angle
  curve on the closed left side), and avoid each other's seeds;
* `G3ChartComparisonStatement` (**named input**, Lemma G3 at a fixed chart datum, in the single-density form of its
  proof): two GFFs on `ℍ` whose piecewise constant data agree near the real part of the closure of a bounded open buffer
  `V`; one positive density `Z` (`E Z = 1`) on the space of the first carries the second's field law, with flow lines
  agreeing with the first's flow lines up to their exits from `V`;
* **`ae_isChartCompletable_of_buffer`**: from both inputs, for the chart pair of a datum with the canonical seed germs
  on an open set containing the real part of the closure of `V`, almost surely every pair of prefixes within the exit
  times from `V` is completable (`IsChartCompletable`). This is G3's conclusion "every measurable order relation
  satisfied by those stopped reference paths is satisfied by the actual stopped pair" for the completability relation:
  the transfer is done on one probability space (`Q = Z·Q₀`), so no measurability of the relation is needed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

/-! ### Exit times and stopped agreement -/

/-- The first time a path is off the buffer `V`, capped by its available lifetime `U`. -/
def exitTime (V : Set ℂ) (γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) : ℝ≥0∞ :=
  min U (⨅ (s : ℝ≥0) (_ : γ s ∉ V), (s : ℝ≥0∞))

/-- Two paths with lifetimes agree up to and including their common exit time from `V`. -/
def StoppedAgree (V : Set ℂ) (γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) (U' : ℝ≥0∞) : Prop :=
  exitTime V γ U = exitTime V γ' U' ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ exitTime V γ U → γ s = γ' s

/-! ### Lemma G2 -/

/-- **The four-height boundary data of Lemma G2** (p. 490): `−λ − θ₂χ` on `(−∞, w₂)`, `λ − θ₂χ` on `(w₂, m)`,
`−λ − θ₁χ` on `(m, w₁)`, `λ − θ₁χ` on `(w₁, ∞)` (values at the three jumps are immaterial). -/
def g2Data (κ θ₁ θ₂ w₂ m w₁ : ℝ) (x : ℝ) : ℝ :=
  if x < w₂ then -sleLambda κ - θ₂ * QuantumZipper.chiC κ
  else if x < m then sleLambda κ - θ₂ * QuantumZipper.chiC κ
  else if x < w₁ then -sleLambda κ - θ₁ * QuantumZipper.chiC κ
  else sleLambda κ - θ₁ * QuantumZipper.chiC κ

/-- The four-height data are piecewise constant with jumps at `w₂, m, w₁`. -/
theorem isPiecewiseConstant_g2Data (κ θ₁ θ₂ w₂ m w₁ : ℝ) :
    IsPiecewiseConstantBoundaryData (g2Data κ θ₁ θ₂ w₂ m w₁) {w₂, m, w₁} := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨h1, h2, h3⟩ := hy
  have e1 : ∀ᶠ z in 𝓝 y, (z < w₂ ↔ y < w₂) := by
    rcases lt_or_gt_of_ne h1 with h | h
    · filter_upwards [eventually_lt_nhds h] with z hz using ⟨fun _ => h, fun _ => hz⟩
    · filter_upwards [eventually_gt_nhds h] with z hz using ⟨fun h' => absurd h' (not_lt.2 hz.le),
        fun h' => absurd h' (not_lt.2 h.le)⟩
  have e2 : ∀ᶠ z in 𝓝 y, (z < m ↔ y < m) := by
    rcases lt_or_gt_of_ne h2 with h | h
    · filter_upwards [eventually_lt_nhds h] with z hz using ⟨fun _ => h, fun _ => hz⟩
    · filter_upwards [eventually_gt_nhds h] with z hz using ⟨fun h' => absurd h' (not_lt.2 hz.le),
        fun h' => absurd h' (not_lt.2 h.le)⟩
  have e3 : ∀ᶠ z in 𝓝 y, (z < w₁ ↔ y < w₁) := by
    rcases lt_or_gt_of_ne h3 with h | h
    · filter_upwards [eventually_lt_nhds h] with z hz using ⟨fun _ => h, fun _ => hz⟩
    · filter_upwards [eventually_gt_nhds h] with z hz using ⟨fun h' => absurd h' (not_lt.2 hz.le),
        fun h' => absurd h' (not_lt.2 h.le)⟩
  filter_upwards [e1, e2, e3] with z hz1 hz2 hz3
  simp only [g2Data, hz1, hz2, hz3]

/-- **Named input: Lemma G2 with Lemma G2b** (supplement §7.2, pp. 490–492, exactly). Fix `0 < κ < 4`,
`w₂ < m < w₁` and `θ₁ < θ₂`. For the GFF `ĥ` on `ℍ` with the four-height data `g2Data` and its angle-`θ₁` flow `α̂₁`
from `w₁` and angle-`θ₂` flow `α̂₂` from `w₂` (in any finite-force coupling), almost surely: both are complete
(`ζ = ∞`) proper simple curves (G2: "These are complete proper simple curves"), `α̂₂` lies on the closed left side of
`α̂₁` (G2: "The higher-angle curve `α̂₂` lies to the left of `α̂₁` in closed Jordan-side order"), and each avoids the
other curve's seed (G2b). **Not proved in Lean** (G2's proof uses Lemma 7.7's first-contact kernel, the elementary
filling fact `Supp7.filling_arc`, Aux. lemmas 57, 79, 94 with Proposition 5.5; G2b uses Aux. lemmas 98, 132). -/
def G2ReferenceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ w₂ m w₁ : ℝ, θ₁ < θ₂ → w₂ < m → m < w₁ →
    ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
      (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ (g2Data κ θ₁ θ₂ w₂ m w₁) ({w₂, m, w₁} : Finset ℝ) →
    ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ (g2Data κ θ₁ θ₂ w₂ m w₁) {w₂, m, w₁} w₁ θ₁ Q Ĥ α₁ ζ₁ →
      IsFlowLine κ (g2Data κ θ₁ θ₂ w₂ m w₁) {w₂, m, w₁} w₂ θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ζ₁ x = ⊤ ∧ ζ₂ x = ⊤ ∧ IsProperCompletion (α₁ x) 0 (α₁ x) ∧
        IsProperCompletion (α₂ x) 0 (α₂ x) ∧ range (α₂ x) ⊆ closedLeftSide (α₁ x) ∧
        (w₂ : ℂ) ∉ range (α₁ x) ∧ (w₁ : ℂ) ∉ range (α₂ x)

/-! ### Lemma G3 -/

/-- **Named input: Lemma G3 at a fixed chart datum, in the single-density form of its proof** (supplement §7.3,
pp. 492–493; with Lemma G1, p. 490, and Corollary G7a's buffers, p. 498). Let `0 < κ < 4`, let `b` (jumps `J`) and
`bR` (jumps `Ĵ`) be piecewise constant data which agree, together with their jump sets, on an open set `O ⊆ ℝ`, and let
`V` be a bounded open buffer whose closure meets `ℝ` only in `O`. Let `H₀` be a GFF with data `b` under `Q₀`, with
angle-`θ₁` and angle-`θ₂` flow lines `Γ₁` from `y₁` and `Γ₂` from `y₂`. Then there are a density `Z > 0` with
`E_{Q₀} Z = 1` (G3's proof: "the one full Cameron–Martin density for adding `f` to the conditional field", `f ∈ H₀¹`
agreeing with `M̂ − M` near the closure of the buffer) and, under `Q = Z·Q₀`, a GFF `Ĥ` with data `bR` and its
flow lines `α̂₁`, `α̂₂` from the same seeds at the same angles such that, `Q₀`-almost surely, each `Γᵢ` agrees with
`α̂ᵢ` up to and including their common exit time from `V` (G3's proof: "Aux. lemmas 61–63 […] Each weighted
field–stopped-path marginal restricted to `U` equals the corresponding reference marginal […] The universal
finite-force determining graph and the restricted-field locality argument written out in Aux. lemma 97 identify the
reference stopped paths as measurable functions of the field restricted to `U`. Lemma G1 now identifies the weighted
joint law"). **Not proved in Lean.** -/
def G3ChartComparisonStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    (∀ x ∈ O, x ∈ J ↔ x ∈ Ĵ) → ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V →
    (∀ z ∈ closure V, z.im = 0 → z.re ∈ O) → ∀ y₁ y₂ θ₁ θ₂ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞),
      IsFlowLine κ b J y₁ θ₁ Q₀ H₀ Γ₁ U₁ → IsFlowLine κ b J y₂ θ₂ Q₀ H₀ Γ₂ U₂ →
    ∃ (Z : S → ℝ) (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens) (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      AEMeasurable Z Q₀ ∧ (∀ᵐ x ∂Q₀, 0 < Z x) ∧ ∫ x, Z x ∂Q₀ = 1 ∧
      IsGFFWithBoundaryData (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) Ĥ bR Ĵ ∧
      IsFlowLine κ bR Ĵ y₁ θ₁ (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) Ĥ α₁ ζ₁ ∧
      IsFlowLine κ bR Ĵ y₂ θ₂ (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) Ĥ α₂ ζ₂ ∧
      ∀ᵐ x ∂Q₀, StoppedAgree V (Γ₁ x) (U₁ x) (α₁ x) (ζ₁ x) ∧ StoppedAgree V (Γ₂ x) (U₂ x) (α₂ x) (ζ₂ x)

/-! ### The transfer -/

/-- **Completability of the stopped chart pair from G2, G2b and G3** (part (e): G3's conclusion for the completability
relation, with G1's single-space transfer). Chart datum: piecewise constant data `c` (jumps `J`) which agree with the
four-height data `g2Data κ θ₁ θ₂ 0 m w` (seeds `0 < m < w`), and have the same jumps, on an open set `O` containing the
real part of the closure of the bounded open buffer `V` (the canonical seed germs). For the GFF with data `c` and its
angle-`θ₁` flow from `w`, angle-`θ₂` flow from `0`, almost surely every pair of prefixes within the exit times from
`V` is completable. -/
theorem ae_isChartCompletable_of_buffer (hG2 : G2ReferenceStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ m w : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (h0m : 0 < m) (hmw : m < w)
    {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {O : Set ℝ} (hO : IsOpen O)
    (hcO : ∀ x ∈ O, c x = g2Data κ θ₁ θ₂ 0 m w x) (hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ ({0, m, w} : Finset ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : ∀ z ∈ closure V, z.im = 0 → z.re ∈ O)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c J)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c J w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime V (Γ₁ x) (U₁ x) →
      (s₂ : ℝ≥0∞) ≤ exitTime V (Γ₂ x) (U₂ x) → IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  obtain ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, hagree⟩ :=
    hG3 κ hκ hκ4 c (g2Data κ θ₁ θ₂ 0 m w) J {0, m, w} hc (isPiecewiseConstant_g2Data κ θ₁ θ₂ 0 m w) O hO hcO hJO
      V hV hVb hVO w 0 θ₁ θ₂ Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
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
  have hRef := hG2 κ hκ hκ4 θ₁ θ₂ 0 m w hθ h0m hmw Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂
  have hRef₀ : ∀ᵐ x ∂Q₀, _ := hPQ.ae_le hRef
  have hz₁ : ∀ᵐ x ∂Q₀, α₁ x 0 = w := hPQ.ae_le (Supp9.ae_apply_zero_of_isFlowLine hα₁)
  have hz₂ : ∀ᵐ x ∂Q₀, α₂ x 0 = 0 := hPQ.ae_le (Supp9.ae_apply_zero_of_isFlowLine hα₂)
  filter_upwards [hRef₀, hagree, hz₁, hz₂] with x hRx hAx hz hz' s₁ s₂ hs₁ hs₂
  obtain ⟨-, -, hc₁, hc₂, hord, hv₁, hv₂⟩ := hRx
  obtain ⟨⟨-, ha₁⟩, ⟨-, ha₂⟩⟩ := hAx
  refine ⟨α₁ x, α₂ x, ⟨hc₁.1, hc₁.2.1, hc₁.2.2.1, hc₁.2.2.2.1, fun t ht => (ha₁ t ?_).symm⟩,
    ⟨hc₂.1, hc₂.2.1, hc₂.2.2.1, hc₂.2.2.2.1, fun t ht => (ha₂ t ?_).symm⟩, hord, ?_, ?_⟩
  · exact (ENNReal.coe_le_coe.2 ht).trans hs₁
  · exact (ENNReal.coe_le_coe.2 ht).trans hs₂
  · have h0 : Γ₁ x 0 = α₁ x 0 := ha₁ 0 (by simp)
    rw [h0, hz]; exact hv₂
  · have h0 : Γ₂ x 0 = α₂ x 0 := ha₂ 0 (by simp)
    rw [h0, hz']; exact_mod_cast hv₁

end RLC

end InteractingSLE
