/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCGlue
import InteractingSLE.Spec.Supplement.RLCCFrame

/-!
# The localized real-contact case of W5's local comparison

Packet PROVE-RLC-C. Source: Theorem W5's proof, "The interior and real local frames" (`source/spec/p529-576.md`,
pp. 535–536): "Suppose `p` is real. […] Shrink the physical neighborhood to one on which the original height is one
constant `C`, and which avoids both original seeds. […] In each case choose a compact chart interval `J` containing all
real points of the fresh comparison buffer other than its canonical seed collars. […] G8 supplies the required
right-boundary frame […] G7a compares both entire fresh stopped laws under one density. G9–G10 again supply actual
ordered proper completions of the locally enlarged prefixes. […] For an interval `J` between the two current seeds
[…] G2a supplies complete proper ordered reference curves"; supplement §7.6–§7.8 (pp. 498–503: Corollary G7a, Lemmas
G8, G2a, G9, G10 and the planar gluing).

The probabilistic part (the comparison G7a with a G2a or G8 reference and G9, for almost every retained datum) is
isolated as the chart-level named input `RetainedChartRealCompletionStatement`: at an ordinary retained pair, almost
surely, the joint chart (`IsRealJointChart`, the pathwise content of G7 for both tips, with the chart's injectivity
over genuine original-real points) exists and every pair of available chart prefixes localized in a jump-free
physical ball around a real point, avoiding both seeds and with a fresh common point, is completable
(`ChartRealCompletion`). Everything else is proved here:

* `exists_chart_cut_open`: a chart cut strictly before the stop, staying in a prescribed open set;
* `exists_completion_of_realChart`: **the pathwise local completion at a localized real contact**, from the chart
  objects and `ChartRealCompletion`: the chart prefixes are localized, they share the chart point over `p`, G10
  (`Supp7.exists_interiorized_completions_of_seeds`) interiorizes, the set `E` of chart real points over genuine
  original-real points of the ball is open, and the planar gluing across real contacts
  (`hasOrderedProperCompletions_glue_real`) appends the completions;
* `retainedLocalCompletionRealLocStatement_of_chart`: `RLC.RetainedLocalCompletionRealLocStatement` from the named
  input; with PROVE-RLC-B's interior case and the late-cut consumer of `RLCCFrame.lean`, Theorem W5
  (`w5Statement_of_chartReal_param`).

`G2aReferenceStatement` records Lemma G2a exactly (the reference for an untouched interval between the current seeds).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9 Supp9B Supp9D Sec2.Assembly

/-! ### A chart cut inside an open set -/

/-- **A chart time strictly before the stop, just after a fresh time, inside an open set** (`RLC.exists_chart_cut`
with `ℍ` replaced by an arbitrary open set `N` containing the fresh arc). -/
theorem exists_chart_cut_open {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {A N : Set ℂ} {u a : ℝ≥0} {c : ℝ≥0 → ℝ≥0}
    {σ : ℝ≥0∞} (hA : IsClosed A) (hN : IsOpen N) (hc : ContinuousOn η {x | (x : ℝ≥0∞) ≤ ζ}) (hua : u < a)
    (haζ : (a : ℝ≥0∞) < ζ) (hf : ∀ x : ℝ≥0, u < x → x ≤ a → η x ∉ A)
    (hin : ∀ x : ℝ≥0, u < x → x ≤ a → η x ∈ N) (hmono : StrictMonoOn c {s | (s : ℝ≥0∞) ≤ σ})
    (himg : c '' {s | (s : ℝ≥0∞) ≤ σ} = {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η x' ∉ A}) :
    ∃ s' a₂ : ℝ≥0, (s' : ℝ≥0∞) < σ ∧ c s' = a₂ ∧ a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ ∧
      (∀ x : ℝ≥0, u < x → x ≤ a₂ → η x ∉ A ∧ η x ∈ N) ∧ c '' Icc 0 s' = Icc u a₂ ∧ c 0 = u := by
  have hnb : {x : ℝ≥0 | (x : ℝ≥0∞) < ζ} ∈ 𝓝 a :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds haζ
  have hca : ContinuousAt η a :=
    (hc.continuousWithinAt (show (a : ℝ≥0∞) ≤ ζ from le_of_lt haζ)).continuousAt
      (mem_of_superset hnb fun x (hx : (x : ℝ≥0∞) < ζ) => show (x : ℝ≥0∞) ≤ ζ from le_of_lt hx)
  have hgood : ∀ᶠ x in 𝓝 a, η x ∈ Aᶜ ∩ N ∧ (x : ℝ≥0∞) < ζ :=
    (hca.eventually ((hA.isOpen_compl.inter hN).mem_nhds ⟨hf a hua le_rfl, hin a hua le_rfl⟩)).and hnb
  obtain ⟨l, r', ⟨hla, har'⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨u, hua⟩ ⟨a + 1, lt_add_one a⟩).1 hgood
  obtain ⟨x₂, hax₂, hx₂r⟩ := exists_between har'
  obtain ⟨x₁, hax₁, hx₁x₂⟩ := exists_between hax₂
  have hfresh : ∀ x : ℝ≥0, u < x → x ≤ x₂ → η x ∉ A ∧ η x ∈ N := by
    intro x hux hxx
    by_cases hxa : x ≤ a
    · exact ⟨hf x hux hxa, hin x hux hxa⟩
    · have := (hsub ⟨hla.trans (not_le.1 hxa), lt_of_le_of_lt hxx hx₂r⟩).1
      exact ⟨this.1, this.2⟩
  have hmemImg : ∀ x : ℝ≥0, u ≤ x → x ≤ x₂ → x ∈ c '' {s | (s : ℝ≥0∞) ≤ σ} := by
    intro x hux hxx
    rw [himg]
    exact ⟨hux, (ENNReal.coe_le_coe.2 hxx).trans (le_of_lt (hsub ⟨hla.trans hax₂, hx₂r⟩).2),
      fun x' h1 h2 => (hfresh x' h1 (h2.le.trans hxx)).1⟩
  obtain ⟨s₂, hs₂, hcs₂⟩ := hmemImg x₂ (hua.trans hax₂).le le_rfl
  obtain ⟨s₁, hs₁, hcs₁⟩ := hmemImg x₁ (hua.trans hax₁).le hx₁x₂.le
  obtain ⟨s₀, hs₀, hcs₀⟩ := hmemImg u le_rfl (hua.trans hax₂).le
  have h0σ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ := by simp
  have hs₁s₂ : s₁ < s₂ := (hmono.lt_iff_lt hs₁ hs₂).1 (by rw [hcs₁, hcs₂]; exact hx₁x₂)
  have hc0 : c 0 = u := by
    have h1 : c 0 ∈ c '' {s | (s : ℝ≥0∞) ≤ σ} := mem_image_of_mem c h0σ
    rw [himg] at h1
    refine le_antisymm ?_ h1.1
    rw [← hcs₀]
    exact hmono.monotoneOn h0σ hs₀ zero_le
  refine ⟨s₁, x₁, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hs₁s₂) hs₂, hcs₁, hax₁,
    (hsub ⟨hla.trans hax₁, hx₁x₂.trans hx₂r⟩).2, fun x h1 h2 => hfresh x h1 (h2.trans hx₁x₂.le), ?_, hc0⟩
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsσ : (s : ℝ≥0∞) ≤ σ := (ENNReal.coe_le_coe.2 hs.2).trans hs₁
    refine ⟨?_, ?_⟩
    · rw [← hc0]; exact hmono.monotoneOn h0σ hsσ hs.1
    · rw [← hcs₁]; exact hmono.monotoneOn hsσ hs₁ hs.2
  · rintro ⟨hux, hxx⟩
    obtain ⟨s, hs, rfl⟩ := hmemImg x hux (hxx.trans hx₁x₂.le)
    refine ⟨s, ⟨zero_le, ?_⟩, rfl⟩
    exact (hmono.le_iff_le hs hs₁).1 (by rw [hcs₁]; exact hxx)

/-! ### The chart objects and the chart real completion property -/

/-- **The joint chart at a retained pair, with its inverse `ψ` named** (the pathwise content of Lemma G7 for both
tips, pp. 497–498, as in `RLC.IsJointRetainedChart`, without the chart field): `ψ` is a bijection of `ℍ` onto the
joint domain `D = activeDomain η₁ u η₂ r`, sends `ℝ` off `D`, is continuous on `ℍ̄` with bounded displacement, and
`ψ(0) = η₂(r)`; the clocks `cᵢ` read the physical continuations up to and including their first new contact with the
retained union `A` in the chart (`ηᵢ ∘ cᵢ = ψ ∘ Γᵢ`, `Γᵢ` in `ℍ̄`); and **`ψ` is injective over genuine original-real
points**: two real chart points with the same real image off `A` coincide (the fibre of the chart over an untouched
original-real point is a single prime end; Aux. 80 and the regular-point clause of `Restart.IsFirstContactChart`;
G7's proof, p. 497: "An untouched original-real point has a trace-free upper half-neighborhood […] The map `φ` extends
analytically by reflection across such an interval"). -/
def IsRealJointChart (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (r : ℝ≥0)
    (Γ₁ Γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) (ψ : ℂ → ℂ) : Prop :=
  BijOn ψ H (activeDomain η₁ u η₂ r) ∧ (∀ w ∉ H, ψ w ∉ activeDomain η₁ u η₂ r) ∧ ContinuousOn ψ Hbar ∧
    (∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) ∧ ψ 0 = η₂ r ∧
    (∃ (c₁ : ℝ≥0 → ℝ≥0) (σ₁ : ℝ≥0∞), σ₁ ≤ U₁ ∧ StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ₁} ∧
      c₁ '' {s | (s : ℝ≥0∞) ≤ σ₁} =
        {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ₁ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η₁ x' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ₁ → η₁ (c₁ s) = ψ (Γ₁ s) ∧ Γ₁ s ∈ Hbar) ∧
    (∃ (c₂ : ℝ≥0 → ℝ≥0) (σ₂ : ℝ≥0∞), σ₂ ≤ U₂ ∧ StrictMonoOn c₂ {s | (s : ℝ≥0∞) ≤ σ₂} ∧
      c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} =
        {y | r ≤ y ∧ (y : ℝ≥0∞) ≤ ζ₂ ∧ ∀ y' : ℝ≥0, r < y' → y' < y → η₂ y' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ₂ → η₂ (c₂ s) = ψ (Γ₂ s) ∧ Γ₂ s ∈ Hbar) ∧
    ∀ y y' : ℝ, ψ y = ψ y' → (ψ y).im = 0 → ψ y ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r → y = y'

/-- **The chart real completion property** (W5's real local frame, pp. 535–536, with Corollary G7a, Lemma G2a or G8,
and Lemma G9, pp. 491–502): every pair of available chart prefixes whose points after the seeds lie, through `ψ`, off
`A` in a physical ball `B(p, ρ)` around a real point `p` — a ball whose real trace has no boundary jump other than
possibly `p` and which avoids both physical seeds `x₁`, `x₂` — and which have a common point after their seeds (the
fresh contact of G9), is completable. -/
def ChartRealCompletion (J : Finset ℝ) (x₁ x₂ : ℝ) (A : Set ℂ) (ψ : ℂ → ℂ) (Γ₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞)
    (Γ₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) : Prop :=
  ∀ p ρ : ℝ, 0 < ρ → (∀ y : ℝ, |y - p| < ρ → y ≠ p → y ∉ J) → ρ ≤ |x₁ - p| → ρ ≤ |x₂ - p| →
    ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < U₁ → (s₂ : ℝ≥0∞) < U₂ →
      (∀ t : ℝ≥0, 0 < t → t ≤ s₁ → ψ (Γ₁ t) ∈ ball (p : ℂ) ρ ∧ ψ (Γ₁ t) ∉ A) →
      (∀ t : ℝ≥0, 0 < t → t ≤ s₂ → ψ (Γ₂ t) ∈ ball (p : ℂ) ρ ∧ ψ (Γ₂ t) ∉ A) →
      (∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ s₁ ∧ 0 < t₂ ∧ t₂ ≤ s₂ ∧ Γ₁ t₁ = Γ₂ t₂) →
      IsChartCompletable Γ₁ s₁ Γ₂ s₂

/-! ### The pathwise local completion at a localized real contact -/

/-- A real chart point whose image is off the retained union is sent to a real point (the chart sends `ℝ` into the
boundary of the joint domain, which in `ℍ` lies in the retained union). -/
theorem im_eq_zero_of_real {η₁ η₂ : ℝ≥0 → ℂ} {u r : ℝ≥0} {ψ : ℂ → ℂ}
    (hA : IsClosed (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)) (hbij : BijOn ψ H (activeDomain η₁ u η₂ r))
    (hoff : ∀ w ∉ H, ψ w ∉ activeDomain η₁ u η₂ r) (hψc : ContinuousOn ψ Hbar) (y : ℝ)
    (hyA : ψ y ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) : (ψ y).im = 0 := by
  have hy : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hcl : ψ y ∈ closure (activeDomain η₁ u η₂ r) := by
    rw [← hbij.image_eq]
    exact ((hψc _ hy).mono fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt (show (0 : ℝ) < w.im from hw))
      |>.mem_closure_image (mem_closure_H_of_mem_Hbar hy)
  have hge : (0 : ℝ) ≤ (ψ y).im :=
    closure_minimal (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz.1.1) QuantumZipper.isClosed_Hbar hcl
  rcases hge.lt_or_eq with hlt | heq
  · have := chart_mem_H hA hbij hoff hψc hy hlt hyA
    exact absurd (show (0 : ℝ) < (y : ℂ).im from this) (by simp)
  · exact heq.symm

/-- **The local completion at a retained pair, pathwise, localized real-contact case** (W5's proof, pp. 535–536,
with G7a, G2a/G8, G9, G10 and the planar gluing, pp. 491–503). Physical paths, continuous, injective and in `ℍ̄` on
their available intervals, from real seeds `η₂(0) ≤ η₁(0)`; an ordinary retained pair `(u, r)` with the joint chart
`IsRealJointChart` (chart seeds `w > 0` and `0`) and the chart real completion property; fresh arcs `η₁((u, a])`,
`η₂((r, τ])` (`a`, `τ` strictly available) ending at a common point, avoiding the retained union, localized
(`IsLocalContact`) and with a real point. Then for some `a₂ > a`, `b₂ > τ` (strictly available) the enlarged prefixes
have ordered proper completions. -/
theorem exists_completion_of_realChart {J : Finset ℝ} {η₁ η₂ Γ₁ Γ₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ U₁ U₂ : ℝ≥0∞}
    {u r a τ : ℝ≥0} {w : ℝ} {ψ : ℂ → ℂ}
    (hc₁ : ContinuousOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hm₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ ζ₁ → 0 ≤ (η₁ x).im) (hm₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ ζ₂ → 0 ≤ (η₂ y).im)
    (h01 : (η₁ 0).im = 0) (h02 : (η₂ 0).im = 0) (hseed : (η₂ 0).re ≤ (η₁ 0).re)
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) (hJ : IsRealJointChart η₁ ζ₁ u η₂ ζ₂ r Γ₁ Γ₂ U₁ U₂ ψ)
    (hw : 0 < w) (hΓ₁0 : Γ₁ 0 = w) (hΓ₂0 : Γ₂ 0 = 0)
    (hCR : ChartRealCompletion J (η₁ 0).re (η₂ 0).re (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) ψ Γ₁ U₁ Γ₂ U₂)
    (hua : u < a) (haζ : (a : ℝ≥0∞) < ζ₁) (hrτ : r < τ) (hτζ : (τ : ℝ≥0∞) < ζ₂) (hp : η₁ a = η₂ τ)
    (hf₁ : ∀ x : ℝ≥0, u < x → x ≤ a → η₁ x ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hf₂ : ∀ y : ℝ≥0, r < y → y ≤ τ → η₂ y ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hloc : IsLocalContact J η₁ u a η₂ r τ)
    (hreal : (∃ x : ℝ≥0, u < x ∧ x ≤ a ∧ η₁ x ∉ H) ∨ ∃ y : ℝ≥0, r < y ∧ y ≤ τ ∧ η₂ y ∉ H) :
    ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ∧
      HasOrderedProperCompletions η₁ a₂ η₂ b₂ := by
  obtain ⟨hbij, hoff, hψc, hψM, hψ0, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁⟩,
    ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂⟩, hinj⟩ := hJ
  set A := η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r with hAdef
  have hle₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ (u : ℝ≥0∞) → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => hx.trans (le_of_lt hord.1)
  have hle₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ (r : ℝ≥0∞) → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => hy.trans (le_of_lt hord.2.1)
  have hA : IsClosed A :=
    isClosed_prefixUnion (hc₁.mono fun x hx => hle₁ x (ENNReal.coe_le_coe.2 hx.2))
      (hc₂.mono fun y hy => hle₂ y (ENNReal.coe_le_coe.2 hy.2))
  have hpim : (η₁ a).im = 0 := hloc.im_eq_zero (hm₁ a haζ.le) hreal
  obtain ⟨ρ, hρ, hball₁, hball₂, -, hjump, hρ1, hρ2⟩ := hloc
  set P := (η₁ a).re with hPdef
  have hpP : η₁ a = (P : ℂ) := eq_ofReal_re_of_im_eq_zero hpim
  obtain ⟨s₁, a₂, hs₁σ, hcs₁, haa₂, ha₂ζ, hfr₁, hcimg₁, hc₁0⟩ :=
    exists_chart_cut_open hA isOpen_ball hc₁ hua haζ hf₁ hball₁ hmono₁ himg₁
  obtain ⟨s₂, b₂, hs₂σ, hcs₂, hτb₂, hb₂ζ, hfr₂, hcimg₂, hc₂0⟩ :=
    exists_chart_cut_open hA isOpen_ball hc₂ hrτ hτζ hf₂ hball₂ hmono₂ himg₂
  have h0σ₁ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have h0σ₂ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₂ := by simp
  have hψw : ψ w = η₁ u := by rw [← hΓ₁0, ← (hpth₁ 0 h0σ₁).1, hc₁0]
  -- the chart prefixes are localized and fresh
  have hpre₁ : ∀ t : ℝ≥0, 0 < t → t ≤ s₁ → ψ (Γ₁ t) ∈ ball (η₁ a) ρ ∧ ψ (Γ₁ t) ∉ A := by
    intro t ht hts
    have htσ : (t : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 hts).trans (le_of_lt hs₁σ)
    have hlo : u < c₁ t := by rw [← hc₁0]; exact hmono₁ h0σ₁ htσ ht
    have hhi : c₁ t ≤ a₂ := by rw [← hcs₁]; exact hmono₁.monotoneOn htσ (le_of_lt hs₁σ) hts
    obtain ⟨hA', hN'⟩ := hfr₁ (c₁ t) hlo hhi
    rw [(hpth₁ t htσ).1] at hA' hN'
    exact ⟨hN', hA'⟩
  have hpre₂ : ∀ t : ℝ≥0, 0 < t → t ≤ s₂ → ψ (Γ₂ t) ∈ ball (η₁ a) ρ ∧ ψ (Γ₂ t) ∉ A := by
    intro t ht hts
    have htσ : (t : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 hts).trans (le_of_lt hs₂σ)
    have hlo : r < c₂ t := by rw [← hc₂0]; exact hmono₂ h0σ₂ htσ ht
    have hhi : c₂ t ≤ b₂ := by rw [← hcs₂]; exact hmono₂.monotoneOn htσ (le_of_lt hs₂σ) hts
    obtain ⟨hA', hN'⟩ := hfr₂ (c₂ t) hlo hhi
    rw [(hpth₂ t htσ).1] at hA' hN'
    exact ⟨hN', hA'⟩
  have hs₁0 : 0 < s₁ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hc₁0] at hcs₁
    exact absurd (hcs₁ ▸ haa₂) (not_lt.2 hua.le)
  have hs₂0 : 0 < s₂ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hc₂0] at hcs₂
    exact absurd (hcs₂ ▸ hτb₂) (not_lt.2 hrτ.le)
  -- the chart points over the contact coincide
  have hDH : activeDomain η₁ u η₂ r ⊆ H := fun z hz => hz.1.1
  obtain ⟨t₁, ht₁, hct₁⟩ : a ∈ c₁ '' Icc 0 s₁ := by rw [hcimg₁]; exact ⟨hua.le, haa₂.le⟩
  obtain ⟨t₂, ht₂, hct₂⟩ : τ ∈ c₂ '' Icc 0 s₂ := by rw [hcimg₂]; exact ⟨hrτ.le, hτb₂.le⟩
  have ht₁σ : (t₁ : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 ht₁.2).trans (le_of_lt hs₁σ)
  have ht₂σ : (t₂ : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 ht₂.2).trans (le_of_lt hs₂σ)
  have ht₁0 : 0 < t₁ := pos_iff_ne_zero.2 fun h => by rw [h, hc₁0] at hct₁; exact (ne_of_lt hua) hct₁
  have ht₂0 : 0 < t₂ := pos_iff_ne_zero.2 fun h => by rw [h, hc₂0] at hct₂; exact (ne_of_lt hrτ) hct₂
  have hψt₁ : ψ (Γ₁ t₁) = η₁ a := by rw [← hct₁]; exact ((hpth₁ t₁ ht₁σ).1).symm
  have hψt₂ : ψ (Γ₂ t₂) = η₁ a := by rw [hp, ← hct₂]; exact ((hpth₂ t₂ ht₂σ).1).symm
  have hreal_of : ∀ z : ℂ, z ∈ Hbar → ψ z = η₁ a → z.im = 0 := by
    intro z hz he
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hlt | heq
    · have h1 : (0 : ℝ) < (ψ z).im := hDH (hbij.mapsTo hlt)
      rw [he, hpim] at h1
      exact absurd h1 (lt_irrefl 0)
    · exact heq.symm
  have hΓ₁r := hreal_of _ (hpth₁ t₁ ht₁σ).2 hψt₁
  have hΓ₂r := hreal_of _ (hpth₂ t₂ ht₂σ).2 hψt₂
  have hcommon : Γ₁ t₁ = Γ₂ t₂ := by
    have hpA : η₁ a ∉ A := hf₁ a hua le_rfl
    have h := hinj (Γ₁ t₁).re (Γ₂ t₂).re
      (by rw [← eq_ofReal_re_of_im_eq_zero hΓ₁r, ← eq_ofReal_re_of_im_eq_zero hΓ₂r, hψt₁, hψt₂])
      (by rw [← eq_ofReal_re_of_im_eq_zero hΓ₁r, hψt₁, hpim])
      (by rw [← eq_ofReal_re_of_im_eq_zero hΓ₁r, hψt₁]; exact hpA)
    rw [eq_ofReal_re_of_im_eq_zero hΓ₁r, eq_ofReal_re_of_im_eq_zero hΓ₂r, h]
  -- the chart real completion property, then G10
  have hnorm : ∀ x : ℝ, ‖(x : ℂ) - (P : ℂ)‖ = |x - P| := fun x => by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hρ1' : ρ ≤ |(η₁ 0).re - P| := by
    rw [← hnorm, ← eq_ofReal_re_of_im_eq_zero h01, ← hpP]; exact hρ1
  have hρ2' : ρ ≤ |(η₂ 0).re - P| := by
    rw [← hnorm, ← eq_ofReal_re_of_im_eq_zero h02, ← hpP]; exact hρ2
  have hCC := hCR P ρ hρ hjump hρ1' hρ2' s₁ s₂ (lt_of_lt_of_le hs₁σ hσ₁) (lt_of_lt_of_le hs₂σ hσ₂)
    (fun t ht hts => by rw [← hpP]; exact hpre₁ t ht hts) (fun t ht hts => by rw [← hpP]; exact hpre₂ t ht hts)
    ⟨t₁, t₂, ht₁0, ht₁.2, ht₂0, ht₂.2, hcommon⟩
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hγord, hav₁, hav₂⟩ := hCC
  obtain ⟨γ₁', γ₂', hγ₁', hγ₂', hord', hav₁', hav₂', hreal₁, hreal₂⟩ :=
    Supp7.exists_interiorized_completions_of_seeds hγ₁ hγ₂ (by rw [hΓ₁0]; simp) hγord hav₁ hav₂
  -- the chart real points over genuine original-real points of the ball
  set E : Set ℝ := {y | ψ y ∈ ball (η₁ a) ρ ∧ ψ y ∉ A} with hEdef
  have hψR : Continuous fun y : ℝ => ψ y :=
    hψc.comp_continuous continuous_ofReal fun y => show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hEo : IsOpen E := (isOpen_ball.inter hA.isOpen_compl).preimage hψR
  have hEr : ∀ y ∈ E, (ψ y).im = 0 := fun y hy => im_eq_zero_of_real hA hbij hoff hψc y hy.2
  have hEi : ∀ y ∈ E, ∀ y' ∈ E, ψ y = ψ y' → y = y' := fun y hy y' _ he => hinj y y' he (hEr y hy) hy.2
  have hEside : (∀ y ∈ E, (ψ y).re < (η₁ 0).re) ∨ ∀ y ∈ E, (η₂ 0).re < (ψ y).re := by
    have hre : ∀ y ∈ E, |(ψ y).re - P| < ρ := fun y hy => by
      have h1 := hy.1
      rw [mem_ball, hpP, Complex.dist_eq] at h1
      exact lt_of_le_of_lt (by simpa using abs_re_le_norm (ψ y - P)) h1
    rcases lt_or_gt_of_ne (show P ≠ (η₁ 0).re from fun h => by
      rw [h, sub_self, abs_zero] at hρ1'; exact absurd hρ1' (not_le.2 hρ)) with hlt | hgt
    · refine Or.inl fun y hy => ?_
      have h1 := hre y hy
      rw [abs_of_pos (sub_pos.2 hlt)] at hρ1'
      rw [abs_lt] at h1
      linarith
    · refine Or.inr fun y hy => ?_
      have h1 := hre y hy
      rw [abs_of_neg (sub_neg.2 (lt_of_le_of_lt hseed hgt))] at hρ2'
      rw [abs_lt] at h1
      linarith
  have hglue : ∀ (γ : ℝ≥0 → ℂ), (∀ t, 0 ≤ (γ t).im) →
      (∀ t, (γ t).im = 0 → γ t ∈ Γ₁ '' Iic s₁ ∪ Γ₂ '' Iic s₂) → (∀ t, 0 < t → γ t ≠ Γ₁ 0) →
      (∀ t, 0 < t → γ t ≠ Γ₂ 0) → ∀ t, 0 < t → IsGluePoint E (γ t) := by
    intro γ hγim hγre hγ1 hγ2 t ht
    rcases (hγim t).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq.symm, ?_⟩
      have hz : γ t = ((γ t).re : ℂ) := eq_ofReal_re_of_im_eq_zero heq.symm
      show ψ ((γ t).re : ℂ) ∈ ball (η₁ a) ρ ∧ ψ ((γ t).re : ℂ) ∉ A
      rw [← hz]
      rcases hγre t heq.symm with ⟨t'', ht'', he⟩ | ⟨t'', ht'', he⟩
      · have ht''0 : 0 < t'' := pos_iff_ne_zero.2 fun h0 => hγ1 t ht (by rw [← he, h0])
        rw [← he]; exact hpre₁ t'' ht''0 ht''
      · have ht''0 : 0 < t'' := pos_iff_ne_zero.2 fun h0 => hγ2 t ht (by rw [← he, h0])
        rw [← he]; exact hpre₂ t'' ht''0 ht''
  have hR₁ : ∀ t, 0 < t → IsGluePoint E (γ₁' t) :=
    hglue γ₁' hγ₁'.2.2.1 hreal₁
      (fun t ht he => (ne_of_gt ht) (hγ₁'.2.1 (he.trans (hγ₁'.2.2.2.2 0 zero_le).symm)))
      (fun t _ he => hav₂' ⟨t, he⟩)
  have hR₂ : ∀ t, 0 < t → IsGluePoint E (γ₂' t) :=
    hglue γ₂' hγ₂'.2.2.1 hreal₂ (fun t _ he => hav₁' ⟨t, he⟩)
      (fun t ht he => (ne_of_gt ht) (hγ₂'.2.1 (he.trans (hγ₂'.2.2.2.2 0 zero_le).symm)))
  -- the planar gluing
  have hsub₁ : ∀ x ∈ Icc (0 : ℝ≥0) a₂, (x : ℝ≥0∞) ≤ ζ₁ := fun x hx =>
    (ENNReal.coe_le_coe.2 hx.2).trans (le_of_lt ha₂ζ)
  have hsub₂ : ∀ y ∈ Icc (0 : ℝ≥0) b₂, (y : ℝ≥0∞) ≤ ζ₂ := fun y hy =>
    (ENNReal.coe_le_coe.2 hy.2).trans (le_of_lt hb₂ζ)
  have himg₁' : η₁ '' Icc u a₂ = (fun s => ψ (Γ₁ s)) '' Icc 0 s₁ := by
    rw [← hcimg₁, image_image]
    refine image_congr fun s hs => (hpth₁ s ((ENNReal.coe_le_coe.2 hs.2).trans (le_of_lt hs₁σ))).1
  have himg₂' : η₂ '' Icc r b₂ = (fun s => ψ (Γ₂ s)) '' Icc 0 s₂ := by
    rw [← hcimg₂, image_image]
    refine image_congr fun s hs => (hpth₂ s ((ENNReal.coe_le_coe.2 hs.2).trans (le_of_lt hs₂σ))).1
  have hend₁ : ψ (Γ₁ s₁) = η₁ a₂ := by rw [← hcs₁]; exact ((hpth₁ s₁ (le_of_lt hs₁σ)).1).symm
  have hend₂ : ψ (Γ₂ s₂) = η₂ b₂ := by rw [← hcs₂]; exact ((hpth₂ s₂ (le_of_lt hs₂σ)).1).symm
  refine ⟨a₂, b₂, haa₂, ha₂ζ, hτb₂, hb₂ζ, ?_⟩
  exact hasOrderedProperCompletions_glue_real hord.2.2.2.2.2.2.2.2 h01 h02 hseed (hua.trans haa₂).le
    (hrτ.trans hτb₂).le (hc₁.mono hsub₁) (hi₁.mono hsub₁) (fun x hx => hm₁ x (hsub₁ x ⟨zero_le, hx⟩))
    (hc₂.mono hsub₂) (hi₂.mono hsub₂) (fun y hy => hm₂ y (hsub₂ y ⟨zero_le, hy⟩)) hord.2.2.1 hord.2.2.2.1
    hord.2.2.2.2.1 hord.2.2.2.2.2.1 hDH (Set.disjoint_left.2 fun z hz hzA => hz.1.2 hzA) hbij.mapsTo
    hbij.injOn hψc hψM hψ0 hψw hEo hEi hEr (fun y hy => hy.2) hEside hw hΓ₁0 hΓ₂0 hs₁0 hs₂0 himg₁' hend₁
    himg₂' hend₂ hγ₁' hγ₂' hord' hR₁ hR₂

/-! ### The named chart-level input and the reduction -/

/-- **Named input: the joint chart and its real completion property at a retained pair** (W5's real local frame,
pp. 535–536: "G8 supplies the required right-boundary frame […] G7a compares both entire fresh stopped laws under one
density. G9–G10 again supply actual ordered proper completions of the locally enlarged prefixes. […] G2a supplies
complete proper ordered reference curves […] The same G7a single-density comparison transfers the full fresh stopped
pair law"; Corollary G7a, Lemmas G8, G2a, G9, pp. 498–502; Lemma G1 and the integration over the retained datum,
p. 490). Setting of `RLC.RetainedLocalCompletionRealLocStatement`. For all own cutoffs `(u, r)` there are random
chart paths `Γᵢ` with relative lifetimes `Uᵢ` and a chart tip position `W` such that almost surely, at an ordinary
retained pair: `W > 0`, `Γ₁(0) = W`, `Γ₂(0) = 0`, and for some inverse chart `ψ` the joint chart `IsRealJointChart`
holds and the chart pair has the real completion property `ChartRealCompletion` for the boundary jumps `J` and the
seeds `x₁`, `x₂`.

Proof route (not in Lean): `IsRealJointChart` is the joint chart of `RLC.JointRetainedChartStatement` (PROVE-RLC-A)
with the chart's injectivity over untouched original-real points (the regular-point clause of the retained chart
`Supp7.IsRetChart`). For `ChartRealCompletion`, per retained datum: the chart word near the chart preimage of the
ball is the original height `C` (G7's mean identification on untouched intervals with Aux. 57); both flows continue
at the contact, so the weights are admissible (W5, p. 535: `> −2` by continuation, `< c_κ` by GB7a, and no jump by
G12); the untouched interval is exterior (G8 frame with G9) or between the current seeds (G2a, with its opposite-seed
avoidance by G12); RLC-A's `G3ChartComparisonStatement` (whose open set `O` is arbitrary, i.e. G7a's buffers)
transfers the reference's completability under one density, as in `RLC.ae_isChartCompletable_of_buffer`; then
integration over the datum as in PROVE-RLC-B (`RLCBCode.lean`). **Not proved in Lean.** -/
def RetainedChartRealCompletionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (Γ₁ Γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) (W : Ω → ℝ),
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        0 < W ω ∧ Γ₁ ω 0 = W ω ∧ Γ₂ ω 0 = 0 ∧ ∃ ψ : ℂ → ℂ,
          IsRealJointChart (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r (Γ₁ ω) (Γ₂ ω) (U₁ ω) (U₂ ω) ψ ∧
          ChartRealCompletion jumps x₁ x₂ (η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) ψ (Γ₁ ω) (U₁ ω) (Γ₂ ω) (U₂ ω)

/-- **The localized real-contact case of the local completion** (`RLC.RetainedLocalCompletionRealLocStatement`,
PROVE-RLC-B's named input) from the chart-level named input. -/
theorem retainedLocalCompletionRealLocStatement_of_chart (hC : RetainedChartRealCompletionStatement.{u}) :
    RetainedLocalCompletionRealLocStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨Γ₁, Γ₂, U₁, U₂, W, hae⟩ := hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  filter_upwards [hae, Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Supp7.ae_im_nonneg_of_isFlowLine hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₂,
    Supp9.ae_apply_zero_of_isFlowLine hη₁, Supp9.ae_apply_zero_of_isFlowLine hη₂]
    with ω hω c₁ c₂ i₁ i₂ m₁ m₂ z₁ z₂ hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ hloc hreal
  obtain ⟨hW, hΓ₁0, hΓ₂0, ψ, hJ, hCR⟩ := hω hord
  exact exists_completion_of_realChart c₁ c₂ i₁ i₂ m₁ m₂ (by rw [z₁]; simp) (by rw [z₂]; simp)
    (by rw [z₁, z₂]; simpa using hx) hord hJ hW hΓ₁0 hΓ₂0 (by rw [z₁, z₂, ofReal_re, ofReal_re]; exact hCR)
    hua haζ hrτ hτζ hp hf₁ hf₂ hloc hreal

/-- **The localized local completion** from G2, G3, Theorems 1.2 (param), 1.3, PROVE-CONDDET's two-tip input and the
chart-level real-contact input. -/
theorem retainedLocalCompletionLocStatement_of_chartReal_param (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hC : RetainedChartRealCompletionStatement.{u}) : RetainedLocalCompletionLocStatement.{u} :=
  retainedLocalCompletionLocStatement_of_param hG2 hG3 h12p h13 hD (retainedLocalCompletionRealLocStatement_of_chart hC)

/-- **Theorem W5** (`Theorem15.W5Statement`) from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the
common-seed comparison, G2, G3, Theorems 1.2 (param), 1.3, PROVE-CONDDET's two-tip input and the chart-level
real-contact input `RetainedChartRealCompletionStatement`. -/
theorem w5Statement_of_chartReal_param (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hC : RetainedChartRealCompletionStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_realLoc_param h25 hW0a hW0b h77 hJ hCS hG2 hG3 h12p h13 hD
    (retainedLocalCompletionRealLocStatement_of_chart hC)

/-! ### Lemma G2a -/

/-- The boundary data of Lemma G2a: `−λ − θ₂χ` left of `w₂`, a middle word `m` on `[w₂, w₁)`, `λ − θ₁χ` from `w₁`. -/
def g2aData (κ θ₁ θ₂ w₂ w₁ : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < w₂ then -sleLambda κ - θ₂ * QuantumZipper.chiC κ
  else if x < w₁ then m x else sleLambda κ - θ₁ * QuantumZipper.chiC κ

/-- **Named statement: Lemma G2a with its opposite-seed avoidance** (supplement §7.2, pp. 491–492, exactly: "In
Lemma G2, the boundary mean on `(w₂, w₁)` may instead be any bounded finite piecewise constant word which agrees with
`λ − θ₂χ` just to the right of `w₂` and with `−λ − θ₁χ` just to the left of `w₁`, and whose every intermediate height
`C` satisfies `−λ − θ₂χ < C < λ − θ₁χ`. The same complete ordered-reference conclusion holds"; "Extension to G2a. The
same opposite-seed avoidance holds for the arbitrary middle word of G2a"). The middle word `m` has its jumps in a finite
set `Jm ⊆ (w₂, w₁)`. Conclusion as in `RLC.G2ReferenceStatement`. This is the reference W5 uses for an untouched real
interval between the two current seeds (p. 536). **Not proved in Lean** (G2a's proof: G2's, with the cumulative weights
`−(C + θ₁χ)/λ − 1 > −2`, `(C + θ₂χ)/λ − 1 > −2`; the extension: Lemma G12 at the other seed, weight `d > κ/2 − 4`). -/
def G2aReferenceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ w₂ w₁ : ℝ, θ₁ < θ₂ → w₂ < w₁ →
    ∀ (m : ℝ → ℝ) (Jm : Finset ℝ), (∀ j ∈ Jm, w₂ < j ∧ j < w₁) →
      IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) →
      (∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * QuantumZipper.chiC κ) →
      (∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
      (∀ x, w₂ < x → x < w₁ → -sleLambda κ - θ₂ * QuantumZipper.chiC κ < m x ∧
        m x < sleLambda κ - θ₁ * QuantumZipper.chiC κ) →
    ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
      (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData Q Ĥ (g2aData κ θ₁ θ₂ w₂ w₁ m) ((insert w₂ (insert w₁ Jm) : Finset ℝ) : Set ℝ) →
    ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ θ₁ Q Ĥ α₁ ζ₁ →
      IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ θ₂ Q Ĥ α₂ ζ₂ →
      ∀ᵐ x ∂Q, ζ₁ x = ⊤ ∧ ζ₂ x = ⊤ ∧ IsProperCompletion (α₁ x) 0 (α₁ x) ∧
        IsProperCompletion (α₂ x) 0 (α₂ x) ∧ range (α₂ x) ⊆ closedLeftSide (α₁ x) ∧
        (w₂ : ℂ) ∉ range (α₁ x) ∧ (w₁ : ℂ) ∉ range (α₂ x)

/-- **Lemma G2 (with G2b) is the special case of Lemma G2a** with the middle word `λ − θ₂χ` on `(w₂, m)` and
`−λ − θ₁χ` on `(m, w₁)`: `RLC.G2ReferenceStatement` follows from `G2aReferenceStatement`. -/
theorem g2ReferenceStatement_of_g2a (hG2a : G2aReferenceStatement.{u}) : G2ReferenceStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ w₂ m w₁ hθ hm1 hm2 S _ Q _ Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂
  set mid : ℝ → ℝ := fun x => if x < m then sleLambda κ - θ₂ * QuantumZipper.chiC κ
    else -sleLambda κ - θ₁ * QuantumZipper.chiC κ with hmid
  have hfun : g2Data κ θ₁ θ₂ w₂ m w₁ = g2aData κ θ₁ θ₂ w₂ w₁ mid := by
    funext x
    simp only [g2Data, g2aData, hmid]
    split_ifs <;> first | rfl | (exfalso; linarith)
  have hJ : ({w₂, m, w₁} : Finset ℝ) = insert w₂ (insert w₁ {m}) := by
    rw [Finset.pair_comm m w₁]
  have hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ mid) (insert w₂ (insert w₁ {m})) := by
    rw [← hfun, ← hJ]; exact isPiecewiseConstant_g2Data κ θ₁ θ₂ w₂ m w₁
  rw [hfun, hJ] at hĤ h₁ h₂
  have hlam := Sec4.sleLambda_pos hκ
  have hθχ : θ₁ * QuantumZipper.chiC κ < θ₂ * QuantumZipper.chiC κ :=
    mul_lt_mul_of_pos_right hθ (Sec4.chiC_pos hκ hκ4)
  exact hG2a κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ (hm1.trans hm2) mid {m} (by simp [hm1, hm2]) hpc
    ⟨m - w₂, sub_pos.2 hm1, fun x _ hx => by simp [hmid, show x < m by linarith]⟩
    ⟨w₁ - m, sub_pos.2 hm2, fun x hx _ => by simp [hmid, show ¬ x < m by linarith]⟩
    (fun x _ _ => by simp only [hmid]; split_ifs <;> constructor <;> linarith)
    Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ h₁ h₂

end RLC

end InteractingSLE
