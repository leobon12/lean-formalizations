/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Spec.Supplement.S7Weights
import Mathlib.Analysis.Complex.Convex

/-!
# Supplement §9: the completion predicate of Convention W0

Packet PROVE-SUPP9 (specification supplement §9, `source/spec/p481-528.md` L1121–L1158 and
`source/spec/p529-576.md` L1–L180, pp. 528–536). The predicate `𝓔(A, B)` of Convention W0 is the frozen
`HasOrderedProperCompletions α a β c` (`β([0, c])` on the closed left side of `α([0, a])`).

* **Heredity** (W0, p. 528: "The predicate is hereditary under restriction of either prefix"):
  `IsProperCompletion.mono`, `HasOrderedProperCompletions.mono` (and `mono_left`, `mono_right`).
* The prefix inherits continuity, injectivity and the closed half-plane from a completion
  (`IsProperCompletion.continuousOn`, `.injOn`, `.im_nonneg`, `.image_subset_range`).
* **Singleton prefixes** (W0, p. 528: "For a singleton prefix the code is instead required only to begin at
  that point"; W4's proof, p. 532: "If both are singletons, use a common vertical ray"): two seeds `x₂ ≤ x₁`
  have ordered proper completions by the vertical rays `t ↦ xᵢ + it` (`hasOrderedProperCompletions_zero`).
  This is the base case from which W4 (via G13a) gives the initial order of W5 for distinct seeds.
* **Corollary W0a, the weight computation** (p. 528): with `d = (θ₂ − θ₁)χ/λ > 0` and `d_κ = κ/2 − 4 < −2`, the
  outward cumulative weight of one flow at the other flow's seed is that flow's seed group plus `d`, hence
  `> −2 + d > d_κ` (`w0a_right_weight`, `w0a_left_weight`). The conclusion of W0a (no visit) is G12's, a
  probabilistic §7 statement: `S9Propagation.lean` derives `W0aStatement` from `G12FlowStatement`
  (`w0aStatement_of_g12`).

W0's measurability remarks (the predicate is analytic, hence universally measurable) are not needed: the
almost-sure statements of §9 are stated with `∀ᵐ`, which requires no measurability of the event.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Filter
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp9

/-! ### Heredity and the prefix carried by a completion -/

section Completion

variable {γ γ' : ℝ≥0 → ℂ} {a a' : ℝ≥0}

/-- A completion of a prefix is a completion of every shorter prefix. -/
theorem IsProperCompletion.mono (h : IsProperCompletion γ a γ') (ha : a' ≤ a) :
    IsProperCompletion γ a' γ' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun t ht => h.2.2.2.2 t (ht.trans ha)⟩

/-- The prefix agrees with its completion on `[0, a]`. -/
theorem IsProperCompletion.eqOn (h : IsProperCompletion γ a γ') : EqOn γ γ' (Icc 0 a) :=
  fun t ht => (h.2.2.2.2 t ht.2).symm

/-- A prefix with a completion is continuous on `[0, a]`. -/
theorem IsProperCompletion.continuousOn (h : IsProperCompletion γ a γ') :
    ContinuousOn γ (Icc 0 a) :=
  h.1.continuousOn.congr (IsProperCompletion.eqOn h)

/-- A prefix with a completion is injective on `[0, a]`. -/
theorem IsProperCompletion.injOn (h : IsProperCompletion γ a γ') : InjOn γ (Icc 0 a) :=
  fun s hs t ht hst => h.2.1 (by rw [← IsProperCompletion.eqOn h hs, ← IsProperCompletion.eqOn h ht, hst])

/-- A prefix with a completion lies in the closed upper half-plane. -/
theorem IsProperCompletion.im_nonneg (h : IsProperCompletion γ a γ') {t : ℝ≥0} (ht : t ≤ a) :
    0 ≤ (γ t).im := by
  rw [← h.2.2.2.2 t ht]
  exact h.2.2.1 t

/-- The prefix is part of the completed curve. -/
theorem IsProperCompletion.image_subset_range (h : IsProperCompletion γ a γ') :
    γ '' Icc 0 a ⊆ range γ' := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, h.2.2.2.2 t ht.2⟩

end Completion

section Ordered

variable {α β : ℝ≥0 → ℂ} {a a' c c' : ℝ≥0}

/-- **Heredity** (Convention W0, p. 528): "The predicate is hereditary under restriction of either prefix." -/
theorem HasOrderedProperCompletions.mono (h : HasOrderedProperCompletions α a β c) (ha : a' ≤ a)
    (hc : c' ≤ c) : HasOrderedProperCompletions α a' β c' := by
  obtain ⟨α', β', hα, hβ, hs⟩ := h
  exact ⟨α', β', IsProperCompletion.mono hα ha, IsProperCompletion.mono hβ hc, hs⟩

/-- Heredity in the first prefix. -/
theorem HasOrderedProperCompletions.mono_left (h : HasOrderedProperCompletions α a β c) (ha : a' ≤ a) :
    HasOrderedProperCompletions α a' β c :=
  HasOrderedProperCompletions.mono h ha le_rfl

/-- Heredity in the second prefix. -/
theorem HasOrderedProperCompletions.mono_right (h : HasOrderedProperCompletions α a β c) (hc : c' ≤ c) :
    HasOrderedProperCompletions α a β c' :=
  HasOrderedProperCompletions.mono h le_rfl hc

/-- The first prefix of an ordered pair is continuous on `[0, a]`. -/
theorem HasOrderedProperCompletions.continuousOn_left (h : HasOrderedProperCompletions α a β c) :
    ContinuousOn α (Icc 0 a) := by
  obtain ⟨_, _, hα, -, -⟩ := h
  exact IsProperCompletion.continuousOn hα

/-- The second prefix of an ordered pair is continuous on `[0, c]`. -/
theorem HasOrderedProperCompletions.continuousOn_right (h : HasOrderedProperCompletions α a β c) :
    ContinuousOn β (Icc 0 c) := by
  obtain ⟨_, _, -, hβ, -⟩ := h
  exact IsProperCompletion.continuousOn hβ

/-- The first prefix of an ordered pair is injective on `[0, a]`. -/
theorem HasOrderedProperCompletions.injOn_left (h : HasOrderedProperCompletions α a β c) :
    InjOn α (Icc 0 a) := by
  obtain ⟨_, _, hα, -, -⟩ := h
  exact IsProperCompletion.injOn hα

/-- The second prefix of an ordered pair is injective on `[0, c]`. -/
theorem HasOrderedProperCompletions.injOn_right (h : HasOrderedProperCompletions α a β c) :
    InjOn β (Icc 0 c) := by
  obtain ⟨_, _, -, hβ, -⟩ := h
  exact IsProperCompletion.injOn hβ

end Ordered

/-! ### Singleton prefixes: the vertical rays -/

section VerticalRay

/-- The upward vertical ray `t ↦ x + it` from a real point `x`. -/
def verticalRay (x : ℝ) (t : ℝ≥0) : ℂ := (x : ℂ) + ((t : ℝ) : ℂ) * Complex.I

variable {x x₁ x₂ : ℝ}

@[simp]
theorem verticalRay_re (x : ℝ) (t : ℝ≥0) : (verticalRay x t).re = x := by
  simp [verticalRay]

@[simp]
theorem verticalRay_im (x : ℝ) (t : ℝ≥0) : (verticalRay x t).im = t := by
  simp [verticalRay]

theorem verticalRay_zero (x : ℝ) : verticalRay x 0 = x := by
  simp [verticalRay]

theorem continuous_verticalRay (x : ℝ) : Continuous (verticalRay x) := by
  unfold verticalRay
  fun_prop

theorem verticalRay_injective (x : ℝ) : Function.Injective (verticalRay x) := by
  intro s t hst
  have := congrArg Complex.im hst
  simp only [verticalRay_im] at this
  exact NNReal.coe_injective this

theorem tendsto_norm_verticalRay (x : ℝ) :
    Tendsto (fun t => ‖verticalRay x t‖) atTop atTop := by
  refine tendsto_atTop_mono (fun t => ?_) (NNReal.tendsto_coe_atTop.2 tendsto_id)
  calc ((id t : ℝ≥0) : ℝ) = |(verticalRay x t).im| := by simp
    _ ≤ ‖verticalRay x t‖ := Complex.abs_im_le_norm _

/-- The vertical ray from the seed completes the singleton prefix `γ([0, 0])`. -/
theorem isProperCompletion_verticalRay {γ : ℝ≥0 → ℂ} (h : γ 0 = x) :
    IsProperCompletion γ 0 (verticalRay x) := by
  refine ⟨continuous_verticalRay x, verticalRay_injective x, fun t => ?_, tendsto_norm_verticalRay x,
    fun t ht => ?_⟩
  · simp
  · rw [le_antisymm ht zero_le, verticalRay_zero, h]

/-- The vertical ray closed along its lower vertical ray is the whole vertical line. -/
theorem seedRayClosure_verticalRay (x : ℝ) : seedRayClosure (verticalRay x) = {z | z.re = x} := by
  ext z
  simp only [seedRayClosure, mem_union, mem_range, mem_ofPred_eq, verticalRay_zero, Complex.ofReal_re,
    Complex.ofReal_im]
  constructor
  · rintro (⟨t, rfl⟩ | ⟨h, -⟩)
    · exact verticalRay_re x t
    · exact h
  · intro h
    rcases le_or_gt 0 z.im with h0 | h0
    · refine Or.inl ⟨z.im.toNNReal, Complex.ext ?_ ?_⟩
      · rw [verticalRay_re, h]
      · rw [verticalRay_im, Real.coe_toNNReal _ h0]
    · exact Or.inr ⟨h, h0.le⟩

/-- A vertical ray from `x₂ ≤ x₁` lies on the closed left side of the vertical ray from `x₁`. -/
theorem range_verticalRay_subset_closedLeftSide (h : x₂ ≤ x₁) :
    range (verticalRay x₂) ⊆ closedLeftSide (verticalRay x₁) := by
  rintro _ ⟨t, rfl⟩
  rcases h.lt_or_eq with h | h
  · refine Or.inl ?_
    have hsub : {z : ℂ | z.re < x₁} ⊆ (seedRayClosure (verticalRay x₁))ᶜ := by
      intro z hz hz'
      rw [seedRayClosure_verticalRay] at hz'
      exact (ne_of_lt hz) hz'
    have hbase : verticalRay x₁ 0 - 1 - Complex.I ∈ {z : ℂ | z.re < x₁} := by
      simp [verticalRay_zero]
    refine (convex_halfSpace_re_lt x₁).isPreconnected.subset_connectedComponentIn hbase hsub ?_
    simpa using h
  · refine Or.inr ?_
    rw [seedRayClosure_verticalRay]
    simp [h]

/-- **Two singleton prefixes from ordered seeds** (W0, p. 528; W4's proof, p. 532): seeds `β 0 = x₂ ≤ x₁ = α 0`
have ordered proper completions by vertical rays. -/
theorem hasOrderedProperCompletions_zero {α β : ℝ≥0 → ℂ} (hα : α 0 = x₁) (hβ : β 0 = x₂) (h : x₂ ≤ x₁) :
    HasOrderedProperCompletions α 0 β 0 :=
  ⟨verticalRay x₁, verticalRay x₂, isProperCompletion_verticalRay hα, isProperCompletion_verticalRay hβ,
    range_verticalRay_subset_closedLeftSide h⟩

end VerticalRay

/-! ### Corollary W0a: the cumulative weights at the opposite seed -/

section W0a

open Sec4 Supp7
open QuantumZipper (chiC)

variable {κ θ₁ θ₂ : ℝ}

/-- **Corollary W0a, at `x_α`** (p. 528): `S_{β,R}(x_α) = (h_right(x_α) + θ₂χ)/λ − 1 = ρ_{α,seed,R} + d`, and
`ρ_{α,seed,R} > −2` (positive lifetime) gives `S_{β,R}(x_α) > −2 + d > d_κ = κ/2 − 4`. Here `C = h_right(x_α)`. -/
theorem w0a_right_weight (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {C : ℝ}
    (hρ : -2 < cumWeightRight κ (C + θ₁ * chiC κ)) :
    cumWeightRight κ (C + θ₂ * chiC κ) = cumWeightRight κ (C + θ₁ * chiC κ) + angleGap κ θ₁ θ₂ ∧
      -2 + angleGap κ θ₁ θ₂ < cumWeightRight κ (C + θ₂ * chiC κ) ∧
      κ / 2 - 4 < -2 + angleGap κ θ₁ θ₂ := by
  have hd := angleGap_pos hκ hκ4 hθ
  have hS := cumWeightRight_add_angle hκ C θ₁ θ₂
  refine ⟨hS, ?_, ?_⟩
  · rw [hS]
    linarith
  · linarith

/-- **Corollary W0a, at `x_β`** (p. 528): `S_{α,L}(x_β) = −(h_left(x_β) + θ₁χ)/λ − 1 = ρ_{β,seed,L} + d`, and
`ρ_{β,seed,L} > −2` gives `S_{α,L}(x_β) > −2 + d > d_κ`. Here `C = h_left(x_β)`. -/
theorem w0a_left_weight (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {C : ℝ}
    (hρ : -2 < cumWeightLeft κ (C + θ₂ * chiC κ)) :
    cumWeightLeft κ (C + θ₁ * chiC κ) = cumWeightLeft κ (C + θ₂ * chiC κ) + angleGap κ θ₁ θ₂ ∧
      -2 + angleGap κ θ₁ θ₂ < cumWeightLeft κ (C + θ₁ * chiC κ) ∧
      κ / 2 - 4 < -2 + angleGap κ θ₁ θ₂ := by
  have hd := angleGap_pos hκ hκ4 hθ
  have hS := cumWeightLeft_add_angle hκ C θ₁ θ₂
  have hS' : cumWeightLeft κ (C + θ₁ * chiC κ) = cumWeightLeft κ (C + θ₂ * chiC κ) + angleGap κ θ₁ θ₂ := by
    linarith
  refine ⟨hS', ?_, ?_⟩
  · rw [hS']
    linarith
  · linarith

end W0a

end Supp9

end InteractingSLE
