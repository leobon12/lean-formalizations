/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCFG8

/-!
# The between-seeds real case per datum, with the seed collars in the buffer (Lemma G2a and G7a)

Packet PROVE-RLC-F. Source: W5's real local frame between the current seeds (`source/spec/p529-576.md` L167, p. 536:
"Choose the G2a middle word to equal `C` on `J` and to have the prescribed canonical germs in the two seed collars. All
these middle heights lie strictly in the displayed admissible interval. G2a supplies complete proper ordered reference
curves, and its opposite-seed avoidance follows from G12 […] The same G7a single-density comparison transfers the full
fresh stopped pair law"), with the explicit middle word of Astra's shortcut note §5.3 (R52).

PROVE-RLC-E's `RLC.ae_isChartCompletable_of_visit` uses a buffer whose closure meets `ℝ` only over the middle interval,
so it excludes the two seeds (its exit times vanish). Here the buffer may contain both seed collars, as W5 needs:

* `ae_isChartCompletable_of_g2aRef`: G2a (with its opposite-seed avoidance) makes every stopped pair of the reference
  completable, so it is a reference property for `RLC.ae_isChartCompletable_of_ref` with any `K`;
* **`ae_isChartCompletable_of_mid`**: per datum with the canonical seed germs and an admissible height `C` on a set
  `G ⊆ [a, b] ⊂ (0, w)`, there is a collar radius `ε₀ > 0` such that for every buffer whose closure meets `ℝ` only
  within `ε₀` of the seeds or in `G`, almost surely every stopped pair inside it is completable.

Conditional on the named G2a (`RLC.G2aReferenceStatement`, PROVE-RLC-C) and G3 (`RLC.G3ChartComparisonStatement`,
PROVE-RLC-A). They replace no source theorem.
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

/-- **The G2a reference pair is completable at every pair of times** (G2a with its opposite-seed avoidance): for the
GFF with a G2a word and its two flows, almost surely every pair of prefixes is completable — the complete curves are
their own ordered proper completions. -/
theorem ae_isChartCompletable_of_g2aRef (hG2a : G2aReferenceStatement.{u}) {κ θ₁ θ₂ w : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (hw : 0 < w) {m : ℝ → ℝ} {Jm : Finset ℝ} (hJm : ∀ j ∈ Jm, 0 < j ∧ j < w)
    (hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ 0 w m) (insert 0 (insert w Jm)))
    (hgL : ∃ ε > 0, ∀ x, 0 < x → x < 0 + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (hgR : ∃ ε > 0, ∀ x, w - ε < x → x < w → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    (hbd : ∀ x, 0 < x → x < w → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
      m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ)
    {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (hĤ : IsGFFWithBoundaryData Q Ĥ (g2aData κ θ₁ θ₂ 0 w m) ((insert 0 (insert w Jm) : Finset ℝ) : Set ℝ))
    (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞)
    (hα₁ : IsFlowLine κ (g2aData κ θ₁ θ₂ 0 w m) (insert 0 (insert w Jm)) w θ₁ Q Ĥ α₁ ζ₁)
    (hα₂ : IsFlowLine κ (g2aData κ θ₁ θ₂ 0 w m) (insert 0 (insert w Jm)) 0 θ₂ Q Ĥ α₂ ζ₂) :
    ∀ᵐ x ∂Q, ∀ s₁ s₂ : ℝ≥0, IsChartCompletable (α₁ x) s₁ (α₂ x) s₂ := by
  have hRef := hG2a κ hκ hκ4 θ₁ θ₂ 0 w hθ hw m Jm hJm hpc hgL hgR hbd Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂
  filter_upwards [hRef, Supp9.ae_apply_zero_of_isFlowLine hα₁, Supp9.ae_apply_zero_of_isFlowLine hα₂]
    with x hRx hz hz' s₁ s₂
  obtain ⟨-, -, hc₁, hc₂, hord, hv₁, hv₂⟩ := hRx
  refine ⟨α₁ x, α₂ x, ⟨hc₁.1, hc₁.2.1, hc₁.2.2.1, hc₁.2.2.2.1, fun t _ => rfl⟩,
    ⟨hc₂.1, hc₂.2.1, hc₂.2.2.1, hc₂.2.2.2.1, fun t _ => rfl⟩, hord, ?_, ?_⟩
  · rw [hz]; exact_mod_cast hv₂
  · rw [hz']; exact_mod_cast hv₁

/-- **Completability of the stopped chart pair between the seeds, at one datum, with the seed collars in the buffer**
(W5, p. 536; G2a with the explicit middle word `λ − θ₂χ | C | −λ − θ₁χ` of the shortcut note's §5.3, and G7a). Chart
datum with the canonical seed germs (`SeedGerm`) at `0` and `w`; an admissible height `−λ − θ₂χ < C < λ − θ₁χ` and a
compact interval `[a, b] ⊂ (0, w)`. There is a collar radius `ε₀ > 0` such that for every open `G ⊆ [a, b]` on which
`c = C` without jumps, and every bounded open buffer `V` whose closure meets `ℝ` only within `ε₀` of the seeds or in
`G`, almost surely every pair of prefixes strictly inside the exit times from `V` is completable. (The prefix and
common-point clauses are kept in the conclusion only to match `ae_isChartCompletable_of_frame`; they are not used.) -/
theorem ae_isChartCompletable_of_mid (hG2a : G2aReferenceStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    {κ θ₁ θ₂ q q₁ q₂ w a b C : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {c : BoundaryWord}
    (hS : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) (ha : 0 < a) (hab : a ≤ b) (hbw : b < w)
    (hC : -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ)
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
  have hlam := Sec4.sleLambda_pos hκ
  have hθχ : θ₁ * QuantumZipper.chiC κ < θ₂ * QuantumZipper.chiC κ :=
    mul_lt_mul_of_pos_right hθ (Sec4.chiC_pos hκ hκ4)
  -- the middle word: jumps strictly outside `[a, b]`
  set a₀ : ℝ := a / 2 with ha₀
  set b₀ : ℝ := (b + w) / 2 with hb₀
  have ha₀0 : 0 < a₀ := by positivity
  have ha₀a : a₀ < a := by linarith
  have hbb₀ : b < b₀ := by linarith
  have hb₀w : b₀ < w := by linarith
  set m : ℝ → ℝ := midWord κ θ₁ θ₂ a₀ b₀ C with hm
  set cR : ℝ → ℝ := g2aData κ θ₁ θ₂ 0 w m with hcRdef
  set Ĵ : Finset ℝ := insert 0 (insert w {a₀, b₀}) with hĴdef
  have hcR : IsPiecewiseConstantBoundaryData cR Ĵ := isPiecewiseConstant_g2aData_midWord κ θ₁ θ₂ w a₀ b₀ C
  set ε : ℝ := min a₀ (w - b₀) with hε
  have hεa : ε ≤ a₀ := min_le_left _ _
  have hεb : ε ≤ w - b₀ := min_le_right _ _
  have hε0 : 0 < ε := lt_min ha₀0 (by linarith)
  have gL₂ : ∀ x, 0 - ε < x → x < 0 → cR x = -sleLambda κ - θ₂ * QuantumZipper.chiC κ := fun x _ h2 => by
    simp only [hcRdef, g2aData, h2, ite_true]
  have gR₂ : ∀ x, 0 < x → x < 0 + ε → cR x = sleLambda κ - θ₂ * QuantumZipper.chiC κ := fun x h1 h2 => by
    have hx0 : ¬ x < 0 := not_lt.2 h1.le
    have hxw : x < w := by linarith
    have hxa : x < a₀ := by linarith
    simp only [hcRdef, g2aData, hm, midWord, hx0, hxw, hxa, ite_true, ite_false]
  have gL₁ : ∀ x, w - ε < x → x < w → cR x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ := fun x h1 h2 => by
    have hx0 : ¬ x < 0 := by intro h; linarith
    have hxa : ¬ x < a₀ := by intro h; linarith
    have hxb : ¬ x < b₀ := by intro h; linarith
    simp only [hcRdef, g2aData, hm, midWord, hx0, h2, hxa, hxb, ite_true, ite_false]
  have gR₁ : ∀ x, w < x → x < w + ε → cR x = sleLambda κ - θ₁ * QuantumZipper.chiC κ := fun x h1 _ => by
    have hx0 : ¬ x < 0 := by intro h; linarith
    have hxw : ¬ x < w := not_lt.2 h1.le
    simp only [hcRdef, g2aData, hx0, hxw, ite_false]
  have hĴ₂ : ∀ x ∈ Ĵ, |x - 0| < ε → x = 0 := fun x hx hxε => by
    rw [sub_zero, abs_lt] at hxε
    simp only [hĴdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h <;> first | exact h | (exfalso; rw [h] at hxε; linarith [hxε.1, hxε.2])
  have hĴ₁ : ∀ x ∈ Ĵ, |x - w| < ε → x = w := fun x hx hxε => by
    rw [abs_lt] at hxε
    simp only [hĴdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h <;> first | exact h | (exfalso; rw [h] at hxε; linarith [hxε.1, hxε.2])
  -- the reference property of the G2a pair
  have hRef : ∀ (Q : Measure S) [IsProbabilityMeasure Q] (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ cR Ĵ → ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ cR Ĵ w θ₁ Q Ĥ α₁ ζ₁ → IsFlowLine κ cR Ĵ 0 θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < ζ₁ x → (s₂ : ℝ≥0∞) < ζ₂ x →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → α₁ x t ∈ H ∨ ((α₁ x t).im = 0 ∧ (α₁ x t).re ∈ Icc a b)) →
        (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → α₂ x t ∈ H ∨ ((α₂ x t).im = 0 ∧ (α₂ x t).re ∈ Icc a b)) →
        (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ α₁ x t₁ = α₂ x t₂) →
        IsChartCompletable (α₁ x) s₁ (α₂ x) s₂ := by
    intro Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂
    have hJm : ∀ j ∈ ({a₀, b₀} : Finset ℝ), 0 < j ∧ j < w := fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact ⟨ha₀0, by linarith⟩
      · exact ⟨by linarith, hb₀w⟩
    have hgL : ∃ ε > 0, ∀ x, 0 < x → x < 0 + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ :=
      ⟨a₀, ha₀0, fun x _ hx => by simp only [hm, midWord, show x < a₀ by linarith, ite_true]⟩
    have hgR : ∃ ε > 0, ∀ x, w - ε < x → x < w → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ :=
      ⟨w - b₀, by linarith, fun x hx _ => by
        simp only [hm, midWord, show ¬ x < a₀ by intro h; linarith, show ¬ x < b₀ by intro h; linarith,
          ite_false]⟩
    have hbd : ∀ x, 0 < x → x < w → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
        m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
      intro x _ _
      simp only [hm, midWord]
      split_ifs
      · constructor <;> linarith
      · exact hC
      · constructor <;> linarith
    have hĤ' : IsGFFWithBoundaryData Q Ĥ (g2aData κ θ₁ θ₂ 0 w m)
        ((insert 0 (insert w ({a₀, b₀} : Finset ℝ)) : Finset ℝ) : Set ℝ) := hĤ
    filter_upwards [ae_isChartCompletable_of_g2aRef hG2a hκ hκ4 hθ hw hJm hcR hgL hgR hbd Q Ĥ hĤ' α₁ α₂ ζ₁ ζ₂
      hα₁ hα₂] with x hx s₁ s₂ _ _ _ _ _
    exact hx s₁ s₂
  obtain ⟨ε₀, hε₀, hmain⟩ := ae_isChartCompletable_of_ref hG3 hκ hκ4 hS hε0 hcR gL₂ gR₂ gL₁ gR₁ hĴ₂ hĴ₁
    (K := Icc a b) hRef Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  refine ⟨ε₀, hε₀, fun G V hGo hGab hGC hV hVb hVO => hmain G V hGo hGab (fun x hx => ?_) hV hVb hVO⟩
  have hxab := hGab hx
  have hx0 : ¬ x < 0 := by intro h; linarith [hxab.1]
  have hxw : x < w := by linarith [hxab.2]
  have hxa : ¬ x < a₀ := by intro h; linarith [hxab.1]
  have hxb : x < b₀ := by linarith [hxab.2]
  refine ⟨?_, (hGC x hx).2, ?_⟩
  · rw [(hGC x hx).1]
    simp only [hcRdef, g2aData, hm, midWord, hx0, hxw, hxa, hxb, ite_true, ite_false]
  · simp only [hĴdef, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨by linarith [hxab.1], by linarith [hxab.2], by linarith [hxab.1], by linarith [hxab.2]⟩

end RLC

end InteractingSLE
