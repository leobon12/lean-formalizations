/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCFG2a
import InteractingSLE.Spec.Supplement.RLCG3Shift

/-!
# Corollary G7a in the chart, and the real-contact transfers per datum

Packet PROVE-G3RESTART. Sources: Lemma G3 (supplement §7.3, `source/spec/p481-528.md` L301–L320, pp. 492–493) and
Corollary G7a (L424–L433, pp. 498–499: "In G3, allow the compact boundary of `U` to meet additional untouched
original-real intervals, on each of which the actual and reference canonical finite-piece means have the same height
and the same finite jump data. Stop each future at its first new retained-curve contact or at exit from `U₀`,
allowing genuine original-real contacts. […] Then the same single-density joint comparison holds"); W5's real local
frame (`source/spec/p529-576.md`, pp. 535–536: "G7a compares both entire fresh stopped laws under one density").

**Why the source-form G3 does not reach past a real contact.** In the real case of W5 the chart buffer meets `ℝ` in
the two seed collars and in an interval `G` of untouched original-real points, and a fresh prefix may touch `G`. The
source-form G3 (`RLC.G3SourceStatement`, ruling R60) asks the closure of each per-seed buffer to meet `ℝ` in ONE
interval `[aᵢ, cᵢ]` on which the actual and the reference data agree; that interval must contain the seed and `G`, so
it contains the chart interval between them. That interval is swallowed at the first contact with `G`, and there the
two data differ in general: for the G8 frame the reference junction `v_R` (source p. 501) and the chart junction (the
end of the image of the outer side of the retained prefix) are at independent positions, and for G2a the chart word
between the seeds may leave the admissible range on intervals that are swallowed without being visited. A restart at
the first contact outside the seed collar would need the domain Markov property at that boundary stopping time for
both laws and a re-application of G3 in the new chart (Aux. 53 in kernel form is itself a named input,
`Restart.KernelRestartCouplingStatement`). The source's route is Corollary G7a: one Cameron–Martin density whose
projection formula is applied "componentwise with every born pocket retained" (p. 499; Aux. 97's proof, p. 327: "the
full weighting changes the reference conditional mean to `M_A^ref + P_{ℍ∖A} f`, with all pockets retained").

* **`G7aChartStatement`** (**named input**, Corollary G7a in the chart, exactly the source's hypotheses): two seeds
  `y₂ < y₁` with angles `θ₁ < θ₂` and the canonical germs on disjoint collars of radius `ε` (G3, items 1–2), data `b`,
  `bR` and jump sets agreeing on an open `O` containing both collars (G7a's additional intervals), and one bounded
  buffer `V` whose closure meets `ℝ` only in `O`; one density carries the reference field and its two flow lines,
  which agree with the actual ones up to their exits from `V` (real contacts allowed).
* `g7aChartStatement_of_g3`: PROVE-RLC-A's `RLC.G3ChartComparisonStatement` implies it, so it is no stronger;
  `g7aChartStatement_of_shiftLocality`: it follows from flow-line locality for shift pairs with a general agreement set
  (`Restart.FlowStopIdentCM.FlowLocalityShiftStatement`) and Theorems 1.2 (param) / 1.3.
* `ae_isChartCompletable_of_ref_g7a`, `ae_isChartCompletable_of_frame_g7a`, `ae_isChartCompletable_of_frame_left_g7a`,
  `ae_isChartCompletable_of_mid_g7a`: PROVE-RLC-F's per-datum transfers (`RLC.ae_isChartCompletable_of_ref`,
  `…_of_frame`, `…_of_frame_left`, `…_of_mid`) with G7a in place of `RLC.G3ChartComparisonStatement`; the proofs are
  theirs, changed only in the comparison call.

Conditional helpers; they replace no source theorem. R43/R48: for Theorem 1.5 only.
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

/-! ### Corollary G7a in the chart -/

/-- **Named input: Corollary G7a in the chart** (supplement p. 498–499, with Lemma G3's items 1–4, pp. 492–493, and
its single-density proof). Fix `0 < κ < 4`, angles `θ₁ < θ₂` and chart seeds `y₂ < y₁` (G3, item 1: the higher-angle
tip on the left). The reference data `bR` (jumps `Ĵ`) have the canonical germs `−λ − θᵢχ` and `λ − θᵢχ` on the two
sides of `yᵢ` within disjoint collars of radius `ε`, with no other jump there (G3, item 2). The actual data `b` (jumps
`J`) agree with `bR`, together with the jump sets, on an open set `O ⊆ ℝ` containing both collars: the collars and
G7a's additional untouched original-real intervals with the same heights and jump data. `V` is a bounded open buffer
whose closure meets `ℝ` only in `O` (G3, item 4, with G7a's boundary buffers). Then for the GFF `H₀` with data `b`
under `Q₀` and its angle-`θᵢ` flow lines `Γᵢ` from `yᵢ` there is one density `Z > 0` with `E Z = 1` and, under
`Q = Z·Q₀`, a GFF `Ĥ` with data `bR` with flow lines `αᵢ` from the same seeds at the same angles, such that
`Q₀`-almost surely each `Γᵢ` agrees with `αᵢ` up to and including their common exit time from `V`
(`StoppedAgree`); genuine real contacts inside `O` are allowed before that exit. **Not proved in Lean.** Source proof:
the difference of the two means is harmonic across `O` with zero trace, the reflected cutoff gives one Cameron–Martin
shift, and the projection formula is applied with every born pocket retained (the retained-range kernel), so that on
the active component the tilted mean is the reference mean; G7 for both words and Lemma G1 conclude. -/
def G7aChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ y₂ y₁ ε : ℝ, θ₁ < θ₂ → y₂ < y₁ → 0 < ε → 2 * ε ≤ y₁ - y₂ →
    ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ →
    (∀ x, y₂ - ε < x → x < y₂ → bR x = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) →
    (∀ x, y₂ < x → x < y₂ + ε → bR x = sleLambda κ - θ₂ * QuantumZipper.chiC κ) →
    (∀ x, y₁ - ε < x → x < y₁ → bR x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
    (∀ x, y₁ < x → x < y₁ + ε → bR x = sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
    (∀ x ∈ Ĵ, |x - y₂| < ε → x = y₂) → (∀ x ∈ Ĵ, |x - y₁| < ε → x = y₁) →
    ∀ O : Set ℝ, IsOpen O → Ioo (y₂ - ε) (y₂ + ε) ⊆ O → Ioo (y₁ - ε) (y₁ + ε) ⊆ O →
    (∀ x ∈ O, b x = bR x) → (∀ x ∈ O, x ∈ J ↔ x ∈ Ĵ) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → (∀ z ∈ closure V, z.im = 0 → z.re ∈ O) →
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

/-- **PROVE-RLC-A's single-buffer G3 implies Corollary G7a** (G7a only adds hypotheses: ordered seeds and angles,
canonical germs on collars contained in the agreement set). -/
theorem g7aChartStatement_of_g3 (hG3 : G3ChartComparisonStatement.{u}) : G7aChartStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ y₂ y₁ ε _ _ _ _ b bR J Ĵ hb hbR _ _ _ _ _ _ O hO _ _ hbO hJO V hV hVb hVO S _ Q₀ _ H₀ hH
    Γ₁ Γ₂ U₁ U₂ h₁ h₂
  exact hG3 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO hJO V hV hVb hVO y₁ y₂ θ₁ θ₂ Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂

/-- **Corollary G7a from flow-line locality for shift pairs with a general agreement set** and Theorems 1.2 (param) /
1.3 (through `RLC.g3ChartComparisonStatement_of_shiftLocality`). -/
theorem g7aChartStatement_of_shiftLocality (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hloc : FlowStopIdentCM.FlowLocalityShiftStatement.{0}) :
    G7aChartStatement.{0} :=
  g7aChartStatement_of_g3 (g3ChartComparisonStatement_of_shiftLocality h12p h13 hloc)

/-! ### The single-density transfer from a reference frame, at one datum -/

/-- **Completability of the stopped chart pair from a reference word and G7a, at one datum**
(`RLC.ae_isChartCompletable_of_ref` with Corollary G7a in place of `RLC.G3ChartComparisonStatement`; W5's real local
frame, p. 535: "G7a compares both entire fresh stopped laws under one density"). -/
theorem ae_isChartCompletable_of_ref_g7a (hG7a : G7aChartStatement.{u})
    {κ θ₁ θ₂ q q₁ q₂ w ε : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {c : BoundaryWord}
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
  -- the two seed collars of radius `ε₀` lie in the agreement set
  have hcol₂ : Ioo (0 - ε₀) (0 + ε₀) ⊆ O := fun x hx =>
    Or.inl (abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hcol₁ : Ioo (w - ε₀) (w + ε₀) ⊆ O := fun x hx =>
    Or.inr (Or.inl (abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  -- Corollary G7a's single-density comparison with the reference
  obtain ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, hagree⟩ :=
    hG7a κ hκ hκ4 θ₁ θ₂ 0 w ε₀ hθ hw hε₀ (by linarith) c' cR J Ĵ hpc hcR
      (fun x h1 h2 => gL₂ x (by linarith) h2) (fun x h1 h2 => gR₂ x h1 (by linarith))
      (fun x h1 h2 => gL₁ x (by linarith) h2) (fun x h1 h2 => gR₁ x h1 (by linarith))
      (fun x hx hxε => hĴ₂ x hx (lt_of_lt_of_le hxε e1)) (fun x hx hxε => hĴ₁ x hx (lt_of_lt_of_le hxε e1))
      O hO hcol₂ hcol₁ hcO hJO V hV hVb hVO' Q₀ H₀ hH' Γ₁ Γ₂ U₁ U₂ h₁' h₂'
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

/-! ### The three regions at one datum -/

/-- **The exterior right real case at one datum, with G7a** (`RLC.ae_isChartCompletable_of_frame` with Corollary
G7a): the G8 frame (with G9) for a height `C` with `−2 < (C + θ₁χ)/λ − 1 < κ/2 − 2` on `[a, b]` right of `w`. -/
theorem ae_isChartCompletable_of_frame_g7a (hG8 : G8FrameStatement.{u}) (hG7a : G7aChartStatement.{u})
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
  obtain ⟨ε₀, hε₀, hmain⟩ := ae_isChartCompletable_of_ref_g7a hG7a hκ hκ4 hθ hS hε hcR gL₂ gR₂ gL₁ gR₁ hĴ₂ hĴ₁
    (K := Icc a b) (fun Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂ => hRef Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂) Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  refine ⟨ε₀, hε₀, fun G V hGo hGab hGC hV hVb hVO => hmain G V hGo hGab (fun x hx => ?_) hV hVb hVO⟩
  exact ⟨(hGC x hx).1.trans (hJab x (hGab hx)).1.symm, (hGC x hx).2, (hJab x (hGab hx)).2⟩

section Reflect

open Sec7.FlowReflect

/-- **The exterior left real case at one datum, with G7a** (`RLC.ae_isChartCompletable_of_frame_left` with
Corollary G7a): the reflected G8 frame for a height `C` on `[a, b]`, `b < 0`, with
`−2 < −(C + θ₂χ)/λ − 1 < κ/2 − 2`. -/
theorem ae_isChartCompletable_of_frame_left_g7a (hG8 : G8FrameStatement.{u}) (hG7a : G7aChartStatement.{u})
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
  obtain ⟨ε₀, hε₀, hmain⟩ := ae_isChartCompletable_of_ref_g7a hG7a hκ hκ4 hθ hS hε hcR gL₂ gR₂ gL₁ gR₁ hĴ₂ hĴ₁
    (K := Icc a b) hRef Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  refine ⟨ε₀, hε₀, fun G V hGo hGab hGC hV hVb hVO => hmain G V hGo hGab (fun x hx => ?_) hV hVb hVO⟩
  have hx' := hJab' (-x) ⟨by linarith [(hGab hx).2], by linarith [(hGab hx).1]⟩
  refine ⟨?_, (hGC x hx).2, fun h => hx'.2 (mem_reflJumps.1 h)⟩
  rw [(hGC x hx).1]
  simp only [hcRdef, reflData, hx'.1, neg_neg]

end Reflect

/-- **The between-seeds real case at one datum, with G7a** (`RLC.ae_isChartCompletable_of_mid` with Corollary G7a):
G2a with the explicit middle word `λ − θ₂χ | C | −λ − θ₁χ` for an admissible height `C` on `[a, b] ⊂ (0, w)`. -/
theorem ae_isChartCompletable_of_mid_g7a (hG2a : G2aReferenceStatement.{u}) (hG7a : G7aChartStatement.{u})
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
  obtain ⟨ε₀, hε₀, hmain⟩ := ae_isChartCompletable_of_ref_g7a hG7a hκ hκ4 hθ hS hε0 hcR gL₂ gR₂ gL₁ gR₁ hĴ₂ hĴ₁
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
