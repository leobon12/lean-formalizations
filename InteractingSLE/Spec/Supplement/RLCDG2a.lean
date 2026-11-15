/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCMain
import InteractingSLE.Spec.Supplement.RLCDG3
import InteractingSLE.Spec.Supplement.GB7aCmp

/-!
# Completability of the stopped chart pair from a G2a reference (the between-seeds real case, per datum)

Packet PROVE-RLC-D, part (4) (iii), the case "an untouched real interval between the two current seeds" of W5's real
local frame (`source/spec/p529-576.md`, p. 536: "For an interval `J` between the two current seeds […] G2a supplies
complete proper ordered reference curves"), with Corollary G7a's buffers (supplement p. 498) and Lemma G1's
single-space transfer (p. 490).

* **`ae_isChartCompletable_of_buffer_g2a`**: PROVE-RLC-A's `RLC.ae_isChartCompletable_of_buffer` with the four-height
  reference of Lemma G2 replaced by the arbitrary admissible middle word of Lemma G2a. For chart data `c` that agree
  (with their jumps) with a G2a word `g2aData κ θ₁ θ₂ 0 w m` on an open set `O` containing the real part of the closure
  of a bounded open buffer `V` (in W5: the two seed collars and the chart interval of height `C` over the untouched
  real interval), almost surely every pair of prefixes of the datum's flows within their exit times from `V` is
  completable (`IsChartCompletable`). The reference is the G2a pair on the Cameron–Martin space of G3.
* `ae_isChartCompletable_of_buffer_g2a_of_locality`: the same from the flow-line locality input
  (`RLC.FlowLocalityStatement`) and Theorems 1.2 (param) / 1.3 in place of G3
  (`g3ChartComparisonStatement_of_locality`).

Ruling R52 (Astra's shortcut note `source/external/AstraIG1/ig1_shortcuts_audited.txt`, §5, lines 453–585):

* `midWord`, `isPiecewiseConstant_g2aData_midWord`, **`ae_isChartCompletable_of_middle`**: the reference availability
  (the note's Prop. 5.2) in the explicit instance of its §5.3 — the middle word `λ − θ₂χ | C | −λ − θ₁χ` keeps the
  canonical seed germs and the visited height `C`, all three values lie in `I = (−λ − θ₂χ, λ − θ₁χ)`, and G2a + G3 give
  the completability of the stopped pair;
* `ThresholdVisitStatement` (**named input**, the continuation-threshold half of Lemma 5.1: no visit strictly before the
  lifetime where the cumulative weight is `≤ −2`) and **`ae_admissible_of_visit`** (the note's **Lemma 5.1**: a visit of
  a middle interval of height `C` by either flow strictly before its lifetime forces `−λ − θ₂χ < C < λ − θ₁χ`), with
  the nonhitting half from Lemma GB7a (`Supp8.gb7aFlowStatement`, proved). R52: Lemma 5.1 sits after GB7a and before W5.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

/-- **Completability of the stopped chart pair from G2a (+ its opposite-seed avoidance) and G3**, for chart data that
agree with a G2a word on an open set containing the real part of the closure of the buffer `V`. -/
theorem ae_isChartCompletable_of_buffer_g2a (hG2a : G2aReferenceStatement.{u})
    (hG3 : G3ChartComparisonStatement.{u}) {κ θ₁ θ₂ w : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (hw : 0 < w)
    {m : ℝ → ℝ} {Jm : Finset ℝ} (hJm : ∀ j ∈ Jm, 0 < j ∧ j < w)
    (hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ 0 w m) (insert 0 (insert w Jm)))
    (hgL : ∃ ε > 0, ∀ x, 0 < x → x < 0 + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (hgR : ∃ ε > 0, ∀ x, w - ε < x → x < w → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    (hbd : ∀ x, 0 < x → x < w → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
      m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {O : Set ℝ} (hO : IsOpen O)
    (hcO : ∀ x ∈ O, c x = g2aData κ θ₁ θ₂ 0 w m x) (hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ insert 0 (insert w Jm))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : ∀ z ∈ closure V, z.im = 0 → z.re ∈ O)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c J)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c J w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime V (Γ₁ x) (U₁ x) →
      (s₂ : ℝ≥0∞) ≤ exitTime V (Γ₂ x) (U₂ x) → IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  obtain ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, hagree⟩ :=
    hG3 κ hκ hκ4 c (g2aData κ θ₁ θ₂ 0 w m) J (insert 0 (insert w Jm)) hc hpc O hO hcO hJO
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
  have hRef := hG2a κ hκ hκ4 θ₁ θ₂ 0 w hθ hw m Jm hJm hpc hgL hgR hbd Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂
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
    rw [h0, hz]; exact_mod_cast hv₂
  · have h0 : Γ₂ x 0 = α₂ x 0 := ha₂ 0 (by simp)
    rw [h0, hz']; exact_mod_cast hv₁

/-- **The same from flow-line locality and Theorems 1.2 (param) / 1.3** in place of G3 (R43/R48: for Theorem 1.5
only). -/
theorem ae_isChartCompletable_of_buffer_g2a_of_locality (hG2a : G2aReferenceStatement.{0})
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0})
    (hloc : FlowLocalityStatement.{0}) {κ θ₁ θ₂ w : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (hw : 0 < w)
    {m : ℝ → ℝ} {Jm : Finset ℝ} (hJm : ∀ j ∈ Jm, 0 < j ∧ j < w)
    (hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ 0 w m) (insert 0 (insert w Jm)))
    (hgL : ∃ ε > 0, ∀ x, 0 < x → x < 0 + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (hgR : ∃ ε > 0, ∀ x, w - ε < x → x < w → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    (hbd : ∀ x, 0 < x → x < w → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
      m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {O : Set ℝ} (hO : IsOpen O)
    (hcO : ∀ x ∈ O, c x = g2aData κ θ₁ θ₂ 0 w m x) (hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ insert 0 (insert w Jm))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : ∀ z ∈ closure V, z.im = 0 → z.re ∈ O)
    {S : Type} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c J)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c J w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime V (Γ₁ x) (U₁ x) →
      (s₂ : ℝ≥0∞) ≤ exitTime V (Γ₂ x) (U₂ x) → IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ :=
  ae_isChartCompletable_of_buffer_g2a hG2a (g3ChartComparisonStatement_of_locality h12p h13 hloc) hκ hκ4 hθ hw
    hJm hpc hgL hgR hbd hc hO hcO hJO hV hVb hVO Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂

/-! ### The explicit three-piece middle word (R52: Astra's shortcut note, §5.3) -/

/-- **The three-piece middle word of the shortcut note's §5.3**: `λ − θ₂χ` left of `a`, the visited height `C` on
`[a, b)`, `−λ − θ₁χ` from `b` (with `w₂ = 0 < a < b < w₁ = w` in the chart). All three values lie in
`I = (−λ − θ₂χ, λ − θ₁χ)` when `C` does. -/
def midWord (κ θ₁ θ₂ a b C : ℝ) (x : ℝ) : ℝ :=
  if x < a then sleLambda κ - θ₂ * QuantumZipper.chiC κ
  else if x < b then C else -sleLambda κ - θ₁ * QuantumZipper.chiC κ

theorem eventually_lt_iff_of_ne {y p : ℝ} (h : y ≠ p) : ∀ᶠ z in 𝓝 y, (z < p ↔ y < p) := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [eventually_lt_nhds h] with z hz using ⟨fun _ => h, fun _ => hz⟩
  · filter_upwards [eventually_gt_nhds h] with z hz using ⟨fun h' => absurd h' (not_lt.2 hz.le),
      fun h' => absurd h' (not_lt.2 h.le)⟩

/-- The G2a data with the three-piece middle word are piecewise constant with jumps `0, w, a, b`. -/
theorem isPiecewiseConstant_g2aData_midWord (κ θ₁ θ₂ w a b C : ℝ) :
    IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ 0 w (midWord κ θ₁ θ₂ a b C)) (insert 0 (insert w {a, b})) := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨h0, hw, ha, hb⟩ := hy
  filter_upwards [eventually_lt_iff_of_ne h0, eventually_lt_iff_of_ne hw, eventually_lt_iff_of_ne ha,
    eventually_lt_iff_of_ne hb] with z h1 h2 h3 h4
  simp only [g2aData, midWord, h1, h2, h3, h4]

/-- **Completability of the stopped chart pair across an untouched middle interval** (R52, the shortcut note's
Prop. 5.2 in the instance of its §5.3): for chart data with seeds `0 < w` that agree, on an open set `O` containing
the real part of the closure of the buffer `V`, with the G2a word whose middle is the three-piece word
`λ − θ₂χ | C | −λ − θ₁χ` (breaks `0 < a < b < w`), and an admissible visited height
`−λ − θ₂χ < C < λ − θ₁χ` (Lemma 5.1), almost surely every pair of prefixes within the exit times from `V` is
completable. In W5's use, `O` is the union of the two seed collars and a neighbourhood of the chart interval of height
`C`, with `a`, `b` chosen outside it. -/
theorem ae_isChartCompletable_of_middle (hG2a : G2aReferenceStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ w a b C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (ha : 0 < a) (hab : a < b) (hbw : b < w)
    (hC : -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {O : Set ℝ} (hO : IsOpen O)
    (hcO : ∀ x ∈ O, c x = g2aData κ θ₁ θ₂ 0 w (midWord κ θ₁ θ₂ a b C) x)
    (hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ insert 0 (insert w ({a, b} : Finset ℝ)))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : ∀ z ∈ closure V, z.im = 0 → z.re ∈ O)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c J)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c J w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime V (Γ₁ x) (U₁ x) →
      (s₂ : ℝ≥0∞) ≤ exitTime V (Γ₂ x) (U₂ x) → IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  have hlam := Sec4.sleLambda_pos hκ
  have hθχ : θ₁ * QuantumZipper.chiC κ < θ₂ * QuantumZipper.chiC κ :=
    mul_lt_mul_of_pos_right hθ (Sec4.chiC_pos hκ hκ4)
  refine ae_isChartCompletable_of_buffer_g2a hG2a hG3 hκ hκ4 hθ (ha.trans (hab.trans hbw)) (Jm := {a, b}) ?_
    (isPiecewiseConstant_g2aData_midWord κ θ₁ θ₂ w a b C) ⟨a, ha, fun x _ hx => ?_⟩
    ⟨w - b, sub_pos.2 hbw, fun x hx _ => ?_⟩ (fun x _ _ => ?_) hc hO hcO hJO hV hVb hVO Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ⟨ha, hab.trans hbw⟩
    · exact ⟨ha.trans hab, hbw⟩
  · simp only [midWord, show x < a by linarith, ↓reduceIte]
  · simp only [midWord, show ¬ x < a by linarith, show ¬ x < b by linarith, ↓reduceIte]
  · simp only [midWord]
    split_ifs
    · constructor <;> linarith
    · exact hC
    · constructor <;> linarith

/-! ### Lemma 5.1 of the shortcut note (R52): a visited middle interval is admissible -/

/-- **Named input: no visit strictly before the lifetime where the cumulative weight is at most `−2`** (the
continuation threshold, Definition 2.1 / Theorem 2.2: the lifetime is the first time the driver meets a mark group of
cumulative weight `≤ −2`, and a visit of the trace to a real point `y` makes the driver meet the group of marks between
the seed and `y`; cf. GB7a's pathwise half `GB7a.rightCmpPath_of_visit`, which produces the collision at the first
visit). Shape of `Supp8.GB7aFlowStatement`: on an open interval `(a, a')` on one side of the seed where the data are
constant `v`, a cumulative weight `≤ −2` forbids every visit at a time strictly before the lifetime. **Not proved in
Lean.** -/
def ThresholdVisitStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ a a' v : ℝ, (∀ y ∈ Ioo a a', y ∉ jumps → b y = v) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      (x ≤ a → Sec4.cumWeightRight κ (v + θ * QuantumZipper.chiC κ) ≤ -2 →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y ∈ Ioo a a', η ω t ≠ y) ∧
      (a' ≤ x → Sec4.cumWeightLeft κ (v + θ * QuantumZipper.chiC κ) ≤ -2 →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y ∈ Ioo a a', η ω t ≠ y)

/-- **Lemma 5.1 of the shortcut note (R52; admissibility of a visited middle interval)**. In chart coordinates, let the
angle-`θ₁` flow start at `W` and the angle-`θ₂` flow at `0` (`θ₁ < θ₂`), and let the data be constant `C` on an open
interval `(a, a')` between the seeds (`0 ≤ a`, `a' ≤ W`): right of the higher-angle flow, left of the lower-angle one.
Almost surely, if either flow visits `(a, a')` strictly before its lifetime, then `−λ − θ₂χ < C < λ − θ₁χ`. Proof (the
note's "equivalent exclusion"): if `C ≤ −λ − θ₂χ`, the right weight `r₂ = (C + θ₂χ)/λ − 1 ≤ −2` of the higher-angle
flow forbids its visit before its lifetime (`ThresholdVisitStatement`), and the left weight `ℓ₁ = −(C + θ₁χ)/λ − 1 ≥
d > 0
> κ/2 − 2` of the lower-angle flow forbids every visit (Lemma GB7a, `Supp8.gb7aFlowStatement`, proved); if
`C ≥ λ − θ₁χ`, the roles reverse. -/
theorem ae_admissible_of_visit (hTV : ThresholdVisitStatement.{u}) {κ θ₁ θ₂ W : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ₁ < θ₂) {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {a a' C : ℝ}
    (ha : 0 ≤ a) (ha' : a' ≤ W) (hcC : ∀ y ∈ Ioo a a', y ∉ J → c y = C)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData P H c J)
    (Γ₁ Γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) (h₁ : IsFlowLine κ c J W θ₁ P H Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ P H Γ₂ U₂) :
    ∀ᵐ ω ∂P, ((∃ t : ℝ≥0, (t : ℝ≥0∞) < U₁ ω ∧ ∃ y ∈ Ioo a a', Γ₁ ω t = y) ∨
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < U₂ ω ∧ ∃ y ∈ Ioo a a', Γ₂ ω t = y)) →
      -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
  have hlam := Sec4.sleLambda_pos hκ
  have hθχ : θ₁ * QuantumZipper.chiC κ < θ₂ * QuantumZipper.chiC κ :=
    mul_lt_mul_of_pos_right hθ (Sec4.chiC_pos hκ hκ4)
  have hc0 : κ / 2 - 2 < 0 := by linarith
  set χ := QuantumZipper.chiC κ with hχ
  have G₁ := Supp8.gb7aFlowStatement κ hκ hκ4 c J hc W θ₁ a a' C hcC P H hH Γ₁ U₁ h₁
  have G₂ := Supp8.gb7aFlowStatement κ hκ hκ4 c J hc 0 θ₂ a a' C hcC P H hH Γ₂ U₂ h₂
  have T₁ := hTV κ hκ hκ4 c J hc W θ₁ a a' C hcC P H hH Γ₁ U₁ h₁
  have T₂ := hTV κ hκ hκ4 c J hc 0 θ₂ a a' C hcC P H hH Γ₂ U₂ h₂
  by_cases hlo : -sleLambda κ - θ₂ * χ < C
  · by_cases hhi : C < sleLambda κ - θ₁ * χ
    · exact ae_of_all _ fun _ _ => ⟨hlo, hhi⟩
    -- `C ≥ λ − θ₁χ`: threshold for the first flow, GB7a for the second
    rw [not_lt] at hhi
    have hl₁ : Sec4.cumWeightLeft κ (C + θ₁ * χ) ≤ -2 := by
      unfold Sec4.cumWeightLeft
      have : 1 ≤ (C + θ₁ * χ) / sleLambda κ := (one_le_div hlam).2 (by linarith)
      rw [neg_div]; linarith
    have hr₂ : κ / 2 - 2 ≤ Sec4.cumWeightRight κ (C + θ₂ * χ) := by
      unfold Sec4.cumWeightRight
      have : 1 ≤ (C + θ₂ * χ) / sleLambda κ := (one_le_div hlam).2 (by linarith)
      linarith
    filter_upwards [T₁.2 ha' hl₁, G₂.1 ha hr₂] with ω e₁ e₂ hvis
    exfalso
    rcases hvis with ⟨t, ht, y, hy, he⟩ | ⟨t, ht, y, hy, he⟩
    · exact e₁ t ht y hy he
    · exact e₂ t ht.le y hy he
  · -- `C ≤ −λ − θ₂χ`: threshold for the second flow, GB7a for the first
    rw [not_lt] at hlo
    have hr₂ : Sec4.cumWeightRight κ (C + θ₂ * χ) ≤ -2 := by
      unfold Sec4.cumWeightRight
      have : (C + θ₂ * χ) / sleLambda κ ≤ -1 := by
        rw [div_le_iff₀ hlam]; linarith
      linarith
    have hl₁ : κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (C + θ₁ * χ) := by
      unfold Sec4.cumWeightLeft
      have : 1 ≤ -(C + θ₁ * χ) / sleLambda κ := (one_le_div hlam).2 (by linarith)
      linarith
    filter_upwards [T₂.1 ha hr₂, G₁.2 ha' hl₁] with ω e₂ e₁ hvis
    exfalso
    rcases hvis with ⟨t, ht, y, hy, he⟩ | ⟨t, ht, y, hy, he⟩
    · exact e₁ t ht.le y hy he
    · exact e₂ t ht y hy he

end RLC

end InteractingSLE
