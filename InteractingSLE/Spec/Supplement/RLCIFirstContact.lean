/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux94
import InteractingSLE.Spec.Restart.R1GlueReduce
import InteractingSLE.Spec.Restart.ClockAssembly
import InteractingSLE.Spec.Restart.ChartMeasFlow
import InteractingSLE.Spec.Restart.Kernel
import InteractingSLE.Spec.Sec7.SideHeightBox
import InteractingSLE.Spec.Coupling.WholeField9Entr
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# Lemma 7.7's first-contact kernel in the form the proof of Lemma G2 uses

Packet PROVE-RLC-I. Source: the proof of Lemma G2 (supplement p. 491, `source/spec/p481-528.md#id-G2-proof`):
"Lemma 7.7 supplies their common first contact `q`, both stopped histories and their marked conditional kernel. […]
The finite original real marks strictly between `w₂` and `w₁` do not survive on the boundary of the joint unbounded
component at this contact. Indeed, apply the elementary filling fact […] In the active first-contact chart, the new
left side has height `−λ − θ₂χ` and the new right side has height `λ − θ₁χ`. The two surviving exterior real half-lines
have these same respective heights by construction. Aux. lemmas 57 and 79 give the inherited, exactly normalized
derivative branch and the absence of an additional singular harmonic term. Hence the entire conditional boundary mean
is the exact two-height mean of Aux. lemma 94, with no surviving intermediate mark."

In Lean the first-contact kernel is the named input `Restart.FirstContactWordKernelStatement` (Lemma 7.8's datum `β`
with the mean identification on every box, and the restart kernel (R2′)) on the canonical measurable pair data, with
the W8.1 clocks (`Restart.exists_canonClock`) and the first-contact chart (`PairData.IsMeasGood.chart_spec_of_agree`).
Lemma 7.8's explicit word `PairData.word` (PROVE-PRIMEEND2) also satisfies the mean identification, with the side
heights `−λ − θ₂χ`, `λ − θ₁χ` (`Sec7.SideHeightBox.isBoxSideLimit_of_flowLines`). This file proves:

* **the datum is the explicit word** (`ae_eqOn_mean_word`): the two mean identifications agree on every box, so the two
  word means agree on `ℍ` (Aux. lemma 57's inherited lift, `Sec7.SideHeightBox`, and the absence of an additional
  singular harmonic term, by bounded-harmonic uniqueness, are inside the landed identification of the explicit word);
* **the filling step in word form** (`word_mean_eq_twoHeightWordOf`): when every original mark lies between the two
  seeds (both of which are real points of the first-contact prefixes), the explicit word keeps no original mark — it is
  the exact two-height word when the exterior heights are the side heights (the elementary filling fact is
  `Supp7.filling_two_arcs`, already used by the explicit word's identification);
* **`exists_firstContactKernel_twoHeight`**: the first-contact kernel in G2's form — measurable restart coordinates, a
  disintegrating kernel under which the chart field is a GFF with the datum and the chart paths are its flow lines, and
  almost surely, at every first contact with two nonempty continuations, the datum has the (TH2) mean, with the
  first-contact chart (`IsFirstContactChart`) and the W8.1 clock data (`IsChartClockData`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real

open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace RLC

open Restart

/-! ### The explicit word at a first contact whose original marks all lie between the seeds -/

section Word

theorem index_eq_zero_of_le {c : BoundaryWord} {y : ℝ} (h : ∀ i < c.1, y ≤ c.2.1 i) : c.index y = 0 := by
  unfold BoundaryWord.index
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  exact not_lt.2 (h i (Finset.mem_range.1 hi))

theorem index_eq_of_lt {c : BoundaryWord} {y : ℝ} (h : ∀ i < c.1, c.2.1 i < y) : c.index y = c.1 := by
  unfold BoundaryWord.index
  rw [Finset.filter_true_of_mem fun i hi => h i (Finset.mem_range.1 hi), Finset.card_range]

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- **The filling step in word form** (proof of Lemma G2, "the finite original real marks strictly between `w₂` and
`w₁` do not survive"; "the two surviving exterior real half-lines have these same respective heights"): if both seeds
`x₂ < x₁` are real points of the first-contact prefixes and every original mark lies in `[x₂, x₁]`, Lemma 7.8's
explicit word keeps no original mark, and with exterior heights equal to the side heights its mean is the two-height
mean. -/
theorem word_mean_eq_twoHeightWordOf (hd : d.IsMeasGood) {ω : Ω} {c₀ : BoundaryWord} {x₁ x₂ hL hR : ℝ}
    (h₂K : (x₂ : ℂ) ∈ d.K ω) (h₁K : (x₁ : ℂ) ∈ d.K ω) (hpos : ∀ i < c₀.1, x₂ ≤ c₀.2.1 i ∧ c₀.2.1 i ≤ x₁)
    (hq0 : c₀.2.2 0 = hL) (hqN : c₀.2.2 c₀.1 = hR) :
    (d.word c₀ hL hR ω).mean = (twoHeightWordOf hL hR).mean := by
  have hk : d.wordK c₀ ω = 0 := by
    unfold PairData.wordK
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    exact not_lt.2 ((hd.baseL_le h₂K).trans (hpos i (Finset.mem_range.1 hi)).1)
  have hl : d.wordLe c₀ ω = c₀.1 := by
    unfold PairData.wordLe
    rw [Finset.filter_true_of_mem fun i hi => (hpos i (Finset.mem_range.1 hi)).2.trans (hd.le_baseR h₁K),
      Finset.card_range]
  funext z
  rw [twoHeightWordOf_mean]
  simp only [BoundaryWord.mean, PairData.word, hk, hl, Nat.sub_self, add_zero, zero_add]
  simp [Finset.sum_range_succ, hq0, hqN]

end Word

/-! ### The datum is Lemma 7.8's explicit word -/

section Ident

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The datum of the first-contact kernel is Lemma 7.8's explicit word**: any datum sorted on the meeting branch with
Lemma 7.8's mean identification on every box has, almost surely on the meeting branch, the mean of the explicit word
with side heights `−λ − θ₂χ`, `λ − θ₁χ`. -/
theorem ae_eqOn_mean_word (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁)
    (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    {β : Ω → BoundaryWord} (hsort : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hmean : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d → EqOn (β ω).mean
      (d.word c₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω).mean H := by
  have hA56 : RetainedRangeEntranceStatement.{u} := WholeField.retainedRangeEntranceStatement
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hu₀
  have hW := isBoxMeanIdentification_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b
    hside
  have hbox : ∀ m : ℕ, ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      ∫ z, (β ω).mean z * φ z =
        ∫ z, (d.word c₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω).mean z * φ z := by
    intro m
    obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, g, hg, -⟩ :=
      exists_fcUnion_marked_of_isFlowLine hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (m : ℝ≥0)
    filter_upwards [hmean m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg,
      hW m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg] with ω h1 h2 hbox φ
    rw [← h1 hbox φ, h2 hbox φ]
  filter_upwards [ae_all_iff.2 hbox, hsort] with ω hω hs hM
  obtain ⟨m, hm⟩ := mem_iUnion.1 hM
  have hE : ω ∈ d.E := (mem_meetBox_iff.1 hm).1
  exact Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl
    ((β ω).isBoundedHarmonicExtension_mean (hs hM)).1
    ((d.word c₀ _ _ ω).isBoundedHarmonicExtension_mean (hd.word_isSorted hE hc₀ _ _)).1 fun φ _ => hω m hm φ

end Ident

/-! ### The first-contact kernel in G2's form -/

section Kernel

/-- The end heights of a sorted word representing data constant outside `[x₂, x₁]`. -/
theorem word_end_heights {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps)
    (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y) {x₁ x₂ hL hR : ℝ} (hJ : ∀ y ∈ jumps, x₂ ≤ y ∧ y ≤ x₁)
    (hbL : ∀ y < x₂, b y = hL) (hbR : ∀ y, x₁ < y → b y = hR) :
    (∀ i < c₀.1, x₂ ≤ c₀.2.1 i ∧ c₀.2.1 i ≤ x₁) ∧ c₀.2.2 0 = hL ∧ c₀.2.2 c₀.1 = hR := by
  have hpos : ∀ i < c₀.1, x₂ ≤ c₀.2.1 i ∧ c₀.2.1 i ≤ x₁ := fun i hi =>
    hJ _ (hc₀J ▸ BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩)
  refine ⟨hpos, ?_, ?_⟩
  · have hy : x₂ - 1 ∉ jumps := fun hm => by linarith [(hJ _ hm).1]
    have := hc₀b _ hy
    rw [BoundaryWord.fn, index_eq_zero_of_le fun i hi => by linarith [(hpos i hi).1], hbL _ (by linarith)] at this
    exact this
  · have hy : x₁ + 1 ∉ jumps := fun hm => by linarith [(hJ _ hm).2]
    have := hc₀b _ hy
    rw [BoundaryWord.fn, index_eq_of_lt fun i hi => by linarith [(hpos i hi).2], hbR _ (by linarith)] at this
    exact this

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.7's first-contact kernel in the form the proof of Lemma G2 uses** (supplement p. 491). Two flow lines
from `x₂ < x₁` (angles `θ₂`, `θ₁`, `θ₁ < θ₂ + π`) of a GFF whose finite piecewise-constant datum has all its jump
candidates in `[x₂, x₁]`, the height `−λ − θ₂χ` left of `x₂` and `λ − θ₁χ` right of `x₁` (the exterior heights of
Lemma G2a). There are measurable restart coordinates `(Hc, γ₁, U₁, γ₂, U₂)` (chart field, chart continuations in
relative capacity time), a measurable meeting branch `M`, a datum `β` and a Markov kernel `K` disintegrating the restart
variable over `β` on `M`, such that:
* for almost every datum `c`, under `K c` the chart field is a GFF with boundary datum `c` and the two chart paths are
  its angle-`θ₁` and angle-`θ₂` flow lines from `0` (Lemma 7.8's kernel and (R2′));
* almost surely, at every first contact `(s₀, t₀)` with two nonempty continuations, `ω ∈ M`, the datum `β ω` has the
  exact two-height mean (TH2) ("the entire conditional boundary mean is the exact two-height mean of Aux. lemma 94"),
  and there is a first-contact chart `(φ, ψ, lift)` of the active domain whose inverse carries the chart continuations
  onto the physical continuations (`IsChartClockData`).
Named inputs: Lemmas 7.5 and 7.7 and `Restart.FirstContactWordKernelStatement`. -/
theorem exists_firstContactKernel_twoHeight (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hW : FirstContactWordKernelStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hJ : ∀ y ∈ jumps, x₂ ≤ y ∧ y ≤ x₁) (hbL : ∀ y < x₂, b y = -sleLambda κ - θ₂ * chiC κ)
    (hbR : ∀ y, x₁ < y → b y = sleLambda κ - θ₁ * chiC κ)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∃ (M : Set Ω) (β : Ω → BoundaryWord) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
      (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) (E : Type) (_ : MeasurableSpace E) (Y : Ω → E)
      (K : Kernel BoundaryWord (RestartSpace × E)),
      MeasurableSet M ∧ Measurable β ∧ Measurable Hc ∧ (∀ t, Measurable fun ω => γ₁ ω t) ∧
      (∀ t, Measurable fun ω => γ₂ ω t) ∧ Measurable U₁ ∧ Measurable U₂ ∧ Measurable Y ∧
      (∀ ω, ContinuousOn (γ₁ ω) {u | (u : ℝ≥0∞) ≤ U₁ ω}) ∧
      (∀ ω, ContinuousOn (γ₂ ω) {u | (u : ℝ≥0∞) ≤ U₂ ω}) ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω))) =
        (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β,
        IsGFFWithBoundaryData (K c) (fun s => s.1.field) c.fn c.jumps ∧
        IsFlowLine κ c.fn c.jumps 0 θ₁ (K c) (fun s => s.1.field) (fun s => s.1.path₁) (fun s => s.1.life₁) ∧
        IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) (fun s => s.1.field) (fun s => s.1.path₂) (fun s => s.1.life₂)) ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ω ∈ M ∧ β ω ∈ twoHeightSet κ θ₁ θ₂ ∧ ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ),
          IsFirstContactChart (η₁ ω) s₀ (η₂ ω) t₀ φ ψ lift ∧
          IsChartClockData ψ (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω) := by
  obtain ⟨d, hd, hζ₁, hζ₂, hae⟩ := exists_pairData_of_isFlowLine hL77 hκ hκ4 hb hx hθ hh hη₁ hη₂
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  obtain ⟨hpos, hq0, hqN⟩ := word_end_heights hc₀J hc₀b hJ hbL hbR
  obtain ⟨γ₁, γ₂, U₁, U₂, m₁, m₂, mU₁, mU₂, hcont₁, hcont₂, hcanon, hclock⟩ :=
    exists_canonClock Theorem15.aux25Statement hL77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
  obtain ⟨β, E, mE, Y, K, hβ, hsort, hmean, hY, hK, hlaw, hflow⟩ :=
    hW κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae _ rfl γ₁ γ₂ U₁ U₂ m₁ m₂
      mU₁ mU₂ hcanon u₀ hu₀
  have hM := hd.measurableSet_meetSet P
  have hMm : MeasurableSet (meetSet d) := retSigma_le P _ hM
  have hβm : Measurable β := hβ.mono (retSigma_le P) le_rfl
  have hHc : Measurable (hd.chartField κ h) := hd.measurable_chartField κ hh.1
  have hXm : Measurable fun ω => (RestartSpace.mk' (hd.chartField κ h ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω) :=
    (RestartSpace.measurable_mk' hHc m₁ m₂ mU₁ mU₂).prodMk hY
  have hR1 := fun φ => ae_condExp_cexp_chartField_eq_gaussCF_meetSet hL75 hL77
    WholeField.retainedRangeEntranceStatement hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hβ hmean φ
  have : IsMarkovKernel K := hK
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word (retSigma_le P) hM hβ (w := fun c => c) measurable_id hsort
    hXm (H := fun s : RestartSpace × E => s.1.field) (measurable_fst.comp measurable_fst) hlaw hR1
  have hword := ae_eqOn_mean_word hL75 hL77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b hsort hmean
  refine ⟨meetSet d, β, hd.chartField κ h, γ₁, γ₂, U₁, U₂, E, mE, Y, K, hMm, hβm, hHc, m₁, m₂, mU₁, mU₂, hY, hcont₁,
    hcont₂, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hgff, hflow] with c hc hc'
    exact ⟨hc.2, hc'.1, hc'.2⟩
  · filter_upwards [hae, hclock, ae_mem_meetSet hζ₁ hζ₂ hae, hword, hsort, Supp10.ae_apply_zero_of_isFlowLine hη₁,
      Supp10.ae_apply_zero_of_isFlowLine hη₂] with ω hω hclk hmeet hwd hs h0₁ h0₂ s₀ t₀ hfc hs₀ ht₀
    obtain ⟨hG, ha₁, ha₂⟩ := hω
    have hMω := hmeet s₀ t₀ hfc hs₀ ht₀
    have ha₁' : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s := fun s hs => ha₁ s (hζ₁ ▸ hs)
    have ha₂' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t := fun t ht => ha₂ t (hζ₂ ▸ ht)
    have hfc' : IsFirstContact (η₁ ω) (d.ζ₁ ω) (η₂ ω) (d.ζ₂ ω) s₀ t₀ := by rw [hζ₁, hζ₂]; exact hfc
    obtain ⟨hE, -, -, -, hC⟩ := hd.chart_spec_of_agree hG ha₁' ha₂' hfc'
    have hK2 : (x₂ : ℂ) ∈ d.K ω := by
      rw [PairData.K_of_mem hE]
      refine Or.inr ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
      rw [ha₂ 0 (by simp), h0₂]
    have hK1 : (x₁ : ℂ) ∈ d.K ω := by
      rw [PairData.K_of_mem hE]
      refine Or.inl ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
      rw [ha₁ 0 (by simp), h0₁]
    have hmean2 := word_mean_eq_twoHeightWordOf hd hK2 hK1 hpos hq0 hqN
    refine ⟨hMω, mem_twoHeightSet_of_eqOn (hs hMω) ?_, d.fwd ω, d.inv ω, d.lift ω, hC, hclk s₀ t₀ hfc hs₀ ht₀⟩
    intro z hz
    rw [hwd hMω hz, hmean2]
    rfl

end Kernel

end RLC

end InteractingSLE
