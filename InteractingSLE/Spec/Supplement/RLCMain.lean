/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCChart
import InteractingSLE.Spec.Supplement.S9DFrame
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Spec.Sec7.InteractionProbLemma77
import InteractingSLE.Spec.Supplement.S9Propagation

/-!
# `Supp9D.RetainedLocalCompletionStatement`: the gluing at a retained pair (interior case) and the reduction

Packet PROVE-RLC-A, part (d). Source: W5's proof (`source/spec/p529-576.md` L140–L180, pp. 534–536) and supplement
§7.3–§7.8 (G1–G10 and the planar gluing, `source/spec/p481-528.md` L216–L535, pp. 490–503).

At an ordinary retained pair `(u, r)` the two fresh continuations are read in the joint chart (`IsJointRetainedChart`,
R47). In the **interior case** — the fresh arcs `η₁((u, a])`, `η₂((r, τ])` stay in `ℍ` — the conclusion of the local
comparison (G3 with the G2 reference, G2b, G1) is that the chart prefixes which stay in `ℍ` are completable
(`ChartInteriorCompletion`); G10 interiorizes the chart completions and the planar gluing (`RLCGlue`) maps them back.
The contact `η₁(a) = η₂(τ)` itself is not used in this case: the G2 reference curves are complete, ordered and proper,
so every interior stopped tangle of the reference is completable, not only the ones at a fresh contact.

## Main results

* `exists_chart_cut`: a chart time strictly before the stop, just after a fresh physical time (pathwise);
* `exists_completion_of_jointChart`: **the local completion at a retained pair, pathwise, interior case**;
* `RetainedChartCompletionStatement` (named input): the joint chart and its interior local completion property almost
  surely at every ordinary retained pair — G7 for both tips (R47) with G3 / G2 / G2b / G1 at the retained pair;
* `RetainedLocalCompletionRealStatement` (named input): the conclusion of `RetainedLocalCompletionStatement` when a
  fresh arc touches the real line (G7a with G2a / G8, G9, and the gluing across real contacts);
* **`retainedLocalCompletionInteriorStatement_of_chart`**, **`retainedLocalCompletionStatement_of_chart`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D

/-! ### Pathwise lemmas -/

/-- A point of `ℍ̄` is adherent to `ℍ`. -/
theorem mem_closure_H_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : z ∈ closure H := by
  have ht : Tendsto (fun s : ℝ => z + (s : ℂ) * I) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + (s : ℂ) * I) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  show (0 : ℝ) < (z + (s : ℂ) * I).im
  have h1 : (0 : ℝ) ≤ z.im := hz
  have h2 : (0 : ℝ) < s := hs
  simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  linarith

/-- A point of `ℍ` off a closed set `A` and adherent to the active domain lies in it. -/
theorem mem_activeDomain_of_mem_closure {η₁ η₂ : ℝ≥0 → ℂ} {u r : ℝ≥0} {z : ℂ}
    (hA : IsClosed (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)) (hz : z ∈ closure (activeDomain η₁ u η₂ r)) (hzH : z ∈ H)
    (hzA : z ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) : z ∈ activeDomain η₁ u η₂ r := by
  set O := H \ (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) with hO
  have hOo : IsOpen O := (isOpen_lt continuous_const continuous_im).sdiff hA
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hOo z ⟨hzH, hzA⟩
  obtain ⟨y, hyD, hyz⟩ := Metric.mem_closure_iff.1 hz ρ hρ
  have hyB : y ∈ ball z ρ := by rw [mem_ball, dist_comm]; exact hyz
  have hsub : ball z ρ ⊆ connectedComponentIn O y :=
    (convex_ball z ρ).isPreconnected.subset_connectedComponentIn hyB hball
  have hzc : z ∈ connectedComponentIn O y := hsub (mem_ball_self hρ)
  refine ⟨⟨hzH, hzA⟩, ?_⟩
  rw [← connectedComponentIn_eq hzc]
  exact hyD.2

/-- **A chart time strictly before the stop, just after a fresh time.** For a clock `c`, strictly increasing on the
chart times `[0, σ]` and mapping them onto the physical times up to and including the first new contact with a
closed set `A`, and a fresh physical time `a ∈ (u, ζ)` with `η((u, a]) ⊆ ℍ \ A`: some chart time `s' < σ` has
`c(s') = a₂ ∈ (a, ζ)`, `η((u, a₂]) ⊆ ℍ \ A`, `c([0, s']) = [u, a₂]` and `c(0) = u`. -/
theorem exists_chart_cut {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {A : Set ℂ} {u a : ℝ≥0} {c : ℝ≥0 → ℝ≥0} {σ : ℝ≥0∞}
    (hA : IsClosed A) (hc : ContinuousOn η {x | (x : ℝ≥0∞) ≤ ζ}) (hua : u < a) (haζ : (a : ℝ≥0∞) < ζ)
    (hf : ∀ x : ℝ≥0, u < x → x ≤ a → η x ∉ A) (hin : ∀ x : ℝ≥0, u < x → x ≤ a → η x ∈ H)
    (hmono : StrictMonoOn c {s | (s : ℝ≥0∞) ≤ σ})
    (himg : c '' {s | (s : ℝ≥0∞) ≤ σ} = {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η x' ∉ A}) :
    ∃ s' a₂ : ℝ≥0, (s' : ℝ≥0∞) < σ ∧ c s' = a₂ ∧ a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ ∧
      (∀ x : ℝ≥0, u < x → x ≤ a₂ → η x ∉ A ∧ η x ∈ H) ∧ c '' Icc 0 s' = Icc u a₂ ∧ c 0 = u := by
  -- a neighbourhood of `a` where `η` is fresh, interior and available
  have hnb : {x : ℝ≥0 | (x : ℝ≥0∞) < ζ} ∈ 𝓝 a :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds haζ
  have hca : ContinuousAt η a :=
    (hc.continuousWithinAt (show (a : ℝ≥0∞) ≤ ζ from le_of_lt haζ)).continuousAt
      (mem_of_superset hnb fun x (hx : (x : ℝ≥0∞) < ζ) => show (x : ℝ≥0∞) ≤ ζ from le_of_lt hx)
  have hgood : ∀ᶠ x in 𝓝 a, η x ∈ Aᶜ ∩ H ∧ (x : ℝ≥0∞) < ζ :=
    (hca.eventually ((hA.isOpen_compl.inter (isOpen_lt continuous_const continuous_im)).mem_nhds
      ⟨hf a hua le_rfl, hin a hua le_rfl⟩)).and hnb
  obtain ⟨l, r', ⟨hla, har'⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨u, hua⟩ ⟨a + 1, lt_add_one a⟩).1 hgood
  obtain ⟨x₂, hax₂, hx₂r⟩ := exists_between har'
  obtain ⟨x₁, hax₁, hx₁x₂⟩ := exists_between hax₂
  have hfresh : ∀ x : ℝ≥0, u < x → x ≤ x₂ → η x ∉ A ∧ η x ∈ H := by
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

/-- The union of two compact prefixes is closed. -/
theorem isClosed_prefixUnion {η₁ η₂ : ℝ≥0 → ℂ} {u r : ℝ≥0} (h₁ : ContinuousOn η₁ (Icc 0 u))
    (h₂ : ContinuousOn η₂ (Icc 0 r)) : IsClosed (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) :=
  ((isCompact_Icc.image_of_continuousOn h₁).union (isCompact_Icc.image_of_continuousOn h₂)).isClosed

/-- Chart points over fresh interior physical points are interior. -/
theorem chart_mem_H {η₁ η₂ : ℝ≥0 → ℂ} {u r : ℝ≥0} {ψ : ℂ → ℂ} {z : ℂ}
    (hA : IsClosed (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)) (hbij : BijOn ψ H (activeDomain η₁ u η₂ r))
    (hoff : ∀ w ∉ H, ψ w ∉ activeDomain η₁ u η₂ r) (hψc : ContinuousOn ψ Hbar) (hz : z ∈ Hbar)
    (hzH : ψ z ∈ H) (hzA : ψ z ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) : z ∈ H := by
  by_contra hzn
  have hcl : ψ z ∈ closure (activeDomain η₁ u η₂ r) := by
    rw [← hbij.image_eq]
    exact ((hψc z hz).mono fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt (show (0 : ℝ) < w.im from hw))
      |>.mem_closure_image (mem_closure_H_of_mem_Hbar hz)
  exact hoff z hzn (mem_activeDomain_of_mem_closure hA hcl hzH hzA)

/-- **The local completion at a retained pair, pathwise, interior case** (W5's proof, pp. 535–536, with G3, G10 and
the planar gluing, pp. 492–503). Physical paths, continuous, injective and in `ℍ̄` on their available intervals, from
real seeds `η₂(0) ≤ η₁(0)`; an ordinary retained pair `(u, r)` with the joint chart, chart seeds `w > 0` and `0`, and
the interior local completion property of the chart pair; fresh arcs `η₁((u, a])`, `η₂((r, τ])` (`a`, `τ` strictly
available) that avoid the retained union `A` and stay in `ℍ`. Then for some `a₂ > a`, `b₂ > τ` (strictly available)
the enlarged prefixes have ordered proper completions. -/
theorem exists_completion_of_jointChart {κ : ℝ} {h₀ H₀ : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ η₂ Γ₁ Γ₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ U₁ U₂ : ℝ≥0∞} {u r a τ : ℝ≥0} {w : ℝ}
    (hc₁ : ContinuousOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {x | (x : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {y | (y : ℝ≥0∞) ≤ ζ₂})
    (hm₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ ζ₁ → 0 ≤ (η₁ x).im) (hm₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ ζ₂ → 0 ≤ (η₂ y).im)
    (h01 : (η₁ 0).im = 0) (h02 : (η₂ 0).im = 0) (hseed : (η₂ 0).re ≤ (η₁ 0).re)
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r)
    (hJ : IsJointRetainedChart κ h₀ H₀ η₁ ζ₁ u η₂ ζ₂ r Γ₁ Γ₂ U₁ U₂)
    (hw : 0 < w) (hΓ₁0 : Γ₁ 0 = w) (hΓ₂0 : Γ₂ 0 = 0) (hCI : ChartInteriorCompletion Γ₁ U₁ Γ₂ U₂)
    (hua : u < a) (haζ : (a : ℝ≥0∞) < ζ₁) (hrτ : r < τ) (hτζ : (τ : ℝ≥0∞) < ζ₂)
    (hf₁ : ∀ x : ℝ≥0, u < x → x ≤ a → η₁ x ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hf₂ : ∀ y : ℝ≥0, r < y → y ≤ τ → η₂ y ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hin₁ : ∀ x : ℝ≥0, u < x → x ≤ a → η₁ x ∈ H) (hin₂ : ∀ y : ℝ≥0, r < y → y ≤ τ → η₂ y ∈ H) :
    ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ∧
      HasOrderedProperCompletions η₁ a₂ η₂ b₂ := by
  obtain ⟨φ, ψ, lift, c₁, c₂, σ₁, σ₂, -, hbij, -, hoff, -, -, -, hψc, hψM, hψ0, hσ₁, hmono₁, himg₁, hσ₂, hmono₂,
    himg₂, hpth₁, hpth₂, -⟩ := hJ
  have hle₁ : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ (u : ℝ≥0∞) → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => hx.trans (le_of_lt hord.1)
  have hle₂ : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ (r : ℝ≥0∞) → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => hy.trans (le_of_lt hord.2.1)
  have hA : IsClosed (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r) :=
    isClosed_prefixUnion (hc₁.mono fun x hx => hle₁ x (ENNReal.coe_le_coe.2 hx.2))
      (hc₂.mono fun y hy => hle₂ y (ENNReal.coe_le_coe.2 hy.2))
  obtain ⟨s₁, a₂, hs₁σ, hcs₁, haa₂, ha₂ζ, hfr₁, hcimg₁, hc₁0⟩ :=
    exists_chart_cut hA hc₁ hua haζ hf₁ hin₁ hmono₁ himg₁
  obtain ⟨s₂, b₂, hs₂σ, hcs₂, hτb₂, hb₂ζ, hfr₂, hcimg₂, hc₂0⟩ :=
    exists_chart_cut hA hc₂ hrτ hτζ hf₂ hin₂ hmono₂ himg₂
  have h0σ₁ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have h0σ₂ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₂ := by simp
  have hψw : ψ w = η₁ u := by rw [← hΓ₁0, ← (hpth₁ 0 h0σ₁).1, hc₁0]
  -- the chart prefixes stay in `ℍ`
  have hchart₁ : ∀ t : ℝ≥0, 0 < t → t ≤ s₁ → Γ₁ t ∈ H := by
    intro t ht hts
    have htσ : (t : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 hts).trans (le_of_lt hs₁σ)
    have hlo : u < c₁ t := by rw [← hc₁0]; exact hmono₁ h0σ₁ htσ ht
    have hhi : c₁ t ≤ a₂ := by rw [← hcs₁]; exact hmono₁.monotoneOn htσ (le_of_lt hs₁σ) hts
    obtain ⟨hA', hH'⟩ := hfr₁ (c₁ t) hlo hhi
    rw [(hpth₁ t htσ).1] at hA' hH'
    exact chart_mem_H hA hbij hoff hψc (hpth₁ t htσ).2 hH' hA'
  have hchart₂ : ∀ t : ℝ≥0, 0 < t → t ≤ s₂ → Γ₂ t ∈ H := by
    intro t ht hts
    have htσ : (t : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 hts).trans (le_of_lt hs₂σ)
    have hlo : r < c₂ t := by rw [← hc₂0]; exact hmono₂ h0σ₂ htσ ht
    have hhi : c₂ t ≤ b₂ := by rw [← hcs₂]; exact hmono₂.monotoneOn htσ (le_of_lt hs₂σ) hts
    obtain ⟨hA', hH'⟩ := hfr₂ (c₂ t) hlo hhi
    rw [(hpth₂ t htσ).1] at hA' hH'
    exact chart_mem_H hA hbij hoff hψc (hpth₂ t htσ).2 hH' hA'
  -- the chart completions
  have hCC := hCI s₁ s₂ (lt_of_lt_of_le hs₁σ hσ₁) (lt_of_lt_of_le hs₂σ hσ₂) hchart₁ hchart₂
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hγord, hH₁, hH₂⟩ :=
    exists_interior_completions hCC (by rw [hΓ₁0]; simp) hchart₁ hchart₂
  have hs₁0 : 0 < s₁ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hc₁0] at hcs₁
    exact absurd (hcs₁ ▸ haa₂) (not_lt.2 hua.le)
  have hs₂0 : 0 < s₂ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hc₂0] at hcs₂
    exact absurd (hcs₂ ▸ hτb₂) (not_lt.2 hrτ.le)
  have himg₁' : η₁ '' Icc u a₂ = (fun s => ψ (Γ₁ s)) '' Icc 0 s₁ := by
    rw [← hcimg₁, image_image]
    refine image_congr fun s hs => (hpth₁ s ((ENNReal.coe_le_coe.2 hs.2).trans (le_of_lt hs₁σ))).1
  have himg₂' : η₂ '' Icc r b₂ = (fun s => ψ (Γ₂ s)) '' Icc 0 s₂ := by
    rw [← hcimg₂, image_image]
    refine image_congr fun s hs => (hpth₂ s ((ENNReal.coe_le_coe.2 hs.2).trans (le_of_lt hs₂σ))).1
  have hend₁ : ψ (Γ₁ s₁) = η₁ a₂ := by rw [← hcs₁]; exact ((hpth₁ s₁ (le_of_lt hs₁σ)).1).symm
  have hend₂ : ψ (Γ₂ s₂) = η₂ b₂ := by rw [← hcs₂]; exact ((hpth₂ s₂ (le_of_lt hs₂σ)).1).symm
  have hsub₁ : ∀ x ∈ Icc (0 : ℝ≥0) a₂, (x : ℝ≥0∞) ≤ ζ₁ := fun x hx =>
    (ENNReal.coe_le_coe.2 hx.2).trans (le_of_lt ha₂ζ)
  have hsub₂ : ∀ y ∈ Icc (0 : ℝ≥0) b₂, (y : ℝ≥0∞) ≤ ζ₂ := fun y hy =>
    (ENNReal.coe_le_coe.2 hy.2).trans (le_of_lt hb₂ζ)
  refine ⟨a₂, b₂, haa₂, ha₂ζ, hτb₂, hb₂ζ, ?_⟩
  exact hasOrderedProperCompletions_glue hord.2.2.2.2.2.2.2.2 h01 h02 hseed (hua.trans haa₂).le
    (hrτ.trans hτb₂).le (hc₁.mono hsub₁) (hi₁.mono hsub₁) (fun x hx => hm₁ x (hsub₁ x ⟨zero_le, hx⟩))
    (hc₂.mono hsub₂) (hi₂.mono hsub₂) (fun y hy => hm₂ y (hsub₂ y ⟨zero_le, hy⟩)) hord.2.2.2.1
    hord.2.2.2.2.1 hord.2.2.2.2.2.1 hbij hψc hψM hψ0 hψw hw hΓ₁0 hΓ₂0 hs₁0 hs₂0 himg₁' hend₁ himg₂' hend₂
    hγ₁ hγ₂ hγord hH₁ hH₂

/-! ### The reduction -/

/-- **Named input: the joint chart and its interior local completion property at a retained pair** (Lemma G7 for both
tips, R47; Lemma G3 with the G2 reference, G2b and G1, supplement §7.1–§7.3, pp. 490–493; the comparison "is a
countable stopped-law comparison", p. 536). Setting of `Supp9D.RetainedLocalCompletionStatement`. For all own cutoffs
`(u, r)` there are random chart objects (chart field `H₀`, chart paths `Γᵢ` with relative lifetimes `Uᵢ`, chart tip
position `W`) such that almost surely, at an ordinary retained pair: the joint chart `IsJointRetainedChart` holds, the
chart seeds are `W > 0` and `0`, and every pair of available chart prefixes that stay in `ℍ` after their seeds is
completable (`ChartInteriorCompletion`).

Its proof: `JointRetainedChartStatement` (proved here from `Restart.RetainedCanonCondDetStatement` and Theorems 1.2
(param), 1.3) gives the chart objects with the canonical finite-word kernel; for almost every datum, Lemma G3 compares
the stopped chart pair in a buffer around the two prefixes with the complete ordered reference of Lemma G2, whose curves
avoid each other's seeds (G2b), and G1 transfers the probability-one completability of the reference. **Not proved in
Lean**; see `planning/handoffs/PROVE-RLC-A.md` for the exact missing steps. -/
def RetainedChartCompletionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (H₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) (W : Ω → ℝ),
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        IsJointRetainedChart κ (h ω) (H₀ ω) (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r (Γ₁ ω) (Γ₂ ω) (U₁ ω) (U₂ ω) ∧
        0 < W ω ∧ Γ₁ ω 0 = W ω ∧ Γ₂ ω 0 = 0 ∧ ChartInteriorCompletion (Γ₁ ω) (U₁ ω) (Γ₂ ω) (U₂ ω)

/-- `Supp9D.RetainedLocalCompletionStatement` restricted to fresh arcs which stay in `ℍ` (the interior case). -/
def RetainedLocalCompletionInteriorStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0, ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ ω → r < τ → (τ : ℝ≥0∞) < ζ₂ ω → η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∈ H) → (∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∈ H) →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂

/-- **Named input: the local completion when a fresh arc touches the real line** (W5's proof, p. 535: "G8 or G2a with
G7a for real `p`"; Corollary G7a, Lemmas G8, G2a, G9, and the planar gluing across genuine original-real contacts,
supplement §7.6–§7.8, pp. 498–503). `Supp9D.RetainedLocalCompletionStatement` restricted to fresh arcs with a point on
the real line. **Not proved in Lean.** -/
def RetainedLocalCompletionRealStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0, ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ ω → r < τ → (τ : ℝ≥0∞) < ζ₂ ω → η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        ((∃ x : ℝ≥0, u < x ∧ x ≤ a ∧ η₁ ω x ∉ H) ∨ ∃ y : ℝ≥0, r < y ∧ y ≤ τ ∧ η₂ ω y ∉ H) →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂

/-- **The interior case of the local completion from the joint chart and its interior local completion property**
(W5's proof with G3, G10 and the planar gluing). -/
theorem retainedLocalCompletionInteriorStatement_of_chart (hC : RetainedChartCompletionStatement.{u}) :
    RetainedLocalCompletionInteriorStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨H₀, Γ₁, Γ₂, U₁, U₂, W, hae⟩ := hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  filter_upwards [hae, Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Supp7.ae_im_nonneg_of_isFlowLine hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₂,
    Supp9.ae_apply_zero_of_isFlowLine hη₁, Supp9.ae_apply_zero_of_isFlowLine hη₂]
    with ω hω c₁ c₂ i₁ i₂ m₁ m₂ z₁ z₂ hord a τ hua haζ hrτ hτζ _hp hf₁ hf₂ hin₁ hin₂
  obtain ⟨hJ, hW, hΓ₁0, hΓ₂0, hCI⟩ := hω hord
  exact exists_completion_of_jointChart c₁ c₂ i₁ i₂ m₁ m₂ (by rw [z₁]; simp) (by rw [z₂]; simp)
    (by rw [z₁, z₂]; simpa using hx) hord hJ hW hΓ₁0 hΓ₂0 hCI hua haζ hrτ hτζ hf₁ hf₂ hin₁ hin₂

/-- The local completion splits into the interior case and the real-contact case. -/
theorem retainedLocalCompletionStatement_of_interior_of_real (hI : RetainedLocalCompletionInteriorStatement.{u})
    (hR : RetainedLocalCompletionRealStatement.{u}) : Supp9D.RetainedLocalCompletionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  filter_upwards [hI κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r,
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r]
    with ω hIω hRω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂
  by_cases hin : (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∈ H) ∧ ∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∈ H
  · exact hIω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ hin.1 hin.2
  · refine hRω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ ?_
    by_contra hno
    push Not at hno
    exact hin ⟨fun x h1 h2 => hno.1 x h1 h2, fun y h1 h2 => hno.2 y h1 h2⟩

/-- **`Supp9D.RetainedLocalCompletionStatement` from the joint chart with its interior local completion property and
the real-contact case.** -/
theorem retainedLocalCompletionStatement_of_chart (hC : RetainedChartCompletionStatement.{u})
    (hR : RetainedLocalCompletionRealStatement.{u}) : Supp9D.RetainedLocalCompletionStatement.{u} :=
  retainedLocalCompletionStatement_of_interior_of_real (retainedLocalCompletionInteriorStatement_of_chart hC) hR

end RLC

end InteractingSLE
