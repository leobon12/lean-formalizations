/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCLPositivity
import InteractingSLE.Spec.Supplement.RLCJSwallowFlow
import InteractingSLE.Spec.Supplement.W0b
import InteractingSLE.Spec.Supplement.RLCKG8Main

/-!
# Lemma G8's positivity: the probabilistic part of the pathwise core

Packet PROVE-RLC-L. Source: proof of Lemma G8 (supplement pp. 500–501): "the probability of a positive real contact is
positive. Exact scaling implies a positive probability of reaching `(x, ∞)` for every fixed `x > 0`. Let `τ_x` be the
first swallowing of `x` […] Continuity at the common seed and strict capacity growth give rational interior times of
`β` arbitrarily near zero, with the entire retained prefix in `B(0, x/4)`. […] A countable union now supplies one
deterministic rational `s` […] On that event, let `t ↑ τ_x` through the final interior approach."

`G8PathFrameStatement` (`RLCLPositivity.lean`) is reduced to a **deterministic** statement about one sample:

* `G8DetFrameStatement` (**named input**, deterministic): for a complete ordered pair `(α, β)` from `0`, with `α` the
  Loewner trace of a continuous driver which swallows `1` at a finite time `σ` with a real landing point `q > 1`, and a
  cut `r` of `β` whose tip is interior and off `α([0, σ])` and whose prefix lies in `B(0, 1/2)`: at every own time `u`
  of `α` in a final interval before `σ` the first tip is interior, off the second prefix, both tips are active, and
  the gap at `1` is small (`IsFrameGap ε`). This is the GB1 part of the source proof (the relative Loewner chain after
  a late cut, the passive characteristics of the `β` tip, of the junction and of `1`, Aux. lemmas 85 and 90);
* `exists_notMem_image_of_not_subarc`: two simple paths with no common open subarc (Lemma W0b) — every open time
  interval of `β` contains a point off the compact `α`-prefix;
* `exists_dyad_cut`: a dyadic interior `β`-cut near the seed, off `α([0, σ])`;
* **`g8PathFrameStatement_of_det`**: `G8PathFrameStatement` from `G8DetFrameStatement` and Lemma W0b (almost surely:
  the swallow and landing of `1`, `RLCJ.ae_swallow_landing`; the cut; a dyadic `u` in the final interval);
* **`g8PositivityStatement_of_det`**: hence `G8PositivityStatement`;
* **`g8FrameStatement_of_inputs`**: Lemma G8 (`G8FrameStatement`, with G9) from Lemma 7.5, Proposition 7.4's complete
  ordered reference, Theorems 1.2 (param) and 1.3, and the two remaining named inputs
  `RetainedCanonCondDetHistStatement` (G7's conditional law given the retained histories) and `G8DetFrameStatement`.

Lemma W0b is `Supp9.w0bStatement_of_lemma75` (from Lemma 7.5, an input on Theorem 1.5's route).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart

/-- **Named input: the deterministic core of Lemma G8's positivity** (supplement p. 500: "On that event, let
`t ↑ τ_x` through the final interior approach. […] Aux. lemma 90 gives joint activity, and Aux. lemma 85 gives ordered
current coordinates `w_β(t) < w_α(t) < v_R(t)` […] The deterministic passive-gap estimate GB1 […] gives
`liminf (v_R − w_α)/(w_α − w_β) = 0`"; here in the limit form `GB1.tendsto_ratio`, read at the untouched point `1`).
For a complete ordered pair `(α, β)` from `0` with `α` the generating trace of a continuous driver `w` (`w 0 = 0`)
which swallows `1` at time `σ` (`RealSwallowAt`) with landing point `α σ = q > 1`, and a cut `r` of `β` with interior
tip off `α([0, σ])` and prefix in `B(0, 1/2)`: for every `ε > 0` there is `t₀ < σ` such that at every `u ∈ (t₀, σ)`
the first tip is interior and off the second prefix, both tips are adherent to the joint domain, and the gap at `1`
is `ε`-small. **Not proved in Lean.** -/
def G8DetFrameStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q ε : ℝ), 0 < ε →
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    ∃ t₀ : ℝ≥0, t₀ < σ ∧ ∀ u : ℝ≥0, t₀ < u → u < σ →
      α u ∈ H ∧ α u ∉ β '' Icc 0 r ∧ α u ∈ closure (activeDomain α u β r) ∧
        β r ∈ closure (activeDomain α u β r) ∧ IsFrameGap ε α u β r

/-! ### A cut of the second path off the first prefix -/

/-- **No common open subarc gives points off the prefix**: if no open subarc of `α([0, σ])` lies in `β([0, c])`,
every open time interval `(ρ₁, ρ₂)`, `ρ₂ ≤ c`, of `β` contains a time at which `β` is off `α([0, σ])` (otherwise the
inverse of the compact embedding `α|[0, σ]` would carry the arc `β(ρ₁, ρ₂)` onto a time interval of `α`). -/
theorem exists_notMem_image_of_not_subarc {α β : ℝ≥0 → ℂ} {σ c ρ₁ ρ₂ : ℝ≥0} (hα : Continuous α)
    (hαi : Function.Injective α) (hβ : Continuous β) (hβi : Function.Injective β) (hρ : ρ₁ < ρ₂) (hρc : ρ₂ ≤ c)
    (hno : ¬ Supp9.HasCommonOpenSubarc α σ β c) : ∃ s ∈ Ioo ρ₁ ρ₂, β s ∉ α '' Icc 0 σ := by
  by_contra hall
  push Not at hall
  apply hno
  set e : Icc (0 : ℝ≥0) σ → ℂ := fun t => α t with hedef
  have he : Topology.IsClosedEmbedding e :=
    (hα.comp continuous_subtype_val).isClosedEmbedding (hαi.comp Subtype.val_injective)
  set S : Set (Icc (0 : ℝ≥0) σ) := e ⁻¹' (β '' Ioo ρ₁ ρ₂) with hSdef
  have himg : e '' S = β '' Ioo ρ₁ ρ₂ := by
    refine image_preimage_eq_of_subset ?_
    rintro z ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hte⟩ := hall s hs
    exact ⟨⟨t, ht⟩, hte⟩
  have hSc : IsPreconnected S :=
    he.isInducing.isPreconnected_image.1 (himg ▸ isPreconnected_Ioo.image β hβ.continuousOn)
  have hV : IsPreconnected (Subtype.val '' S) := hSc.image _ continuous_subtype_val.continuousOn
  obtain ⟨s₁, hs₁, hs₁₂⟩ := exists_between hρ
  obtain ⟨s₂, hs₂, hs₂₂⟩ := exists_between hs₁₂
  have hs₁I : s₁ ∈ Ioo ρ₁ ρ₂ := ⟨hs₁, hs₁₂⟩
  have hs₂I : s₂ ∈ Ioo ρ₁ ρ₂ := ⟨hs₁.trans hs₂, hs₂₂⟩
  obtain ⟨t₁, ht₁, he₁⟩ := hall s₁ hs₁I
  obtain ⟨t₂, ht₂, he₂⟩ := hall s₂ hs₂I
  have hS₁ : (t₁ : ℝ≥0) ∈ Subtype.val '' S := ⟨⟨t₁, ht₁⟩, ⟨s₁, hs₁I, he₁.symm⟩, rfl⟩
  have hS₂ : (t₂ : ℝ≥0) ∈ Subtype.val '' S := ⟨⟨t₂, ht₂⟩, ⟨s₂, hs₂I, he₂.symm⟩, rfl⟩
  have hne : t₁ ≠ t₂ := by
    intro h
    rw [h] at he₁
    exact hs₂.ne (hβi (he₁.symm.trans he₂))
  have hsub : ∀ {a b : ℝ≥0}, a ∈ Subtype.val '' S → b ∈ Subtype.val '' S → α '' Ioo a b ⊆ β '' Icc 0 c := by
    intro a b ha hb z ⟨t, ht, hz⟩
    obtain ⟨⟨t', ht'⟩, ⟨s, hs, hst⟩, rfl⟩ := hV.Icc_subset ha hb (Ioo_subset_Icc_self ht)
    exact ⟨s, ⟨zero_le, hs.2.le.trans hρc⟩, hst.trans hz⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨t₁, t₂, h, ht₂.2, hsub hS₁ hS₂⟩
  · exact ⟨t₂, t₁, h, ht₁.2, hsub hS₂ hS₁⟩

/-- **A dyadic interior cut of `β` near the seed, off `α([0, σ])`.** -/
theorem exists_dyad_cut {α β : ℝ≥0 → ℂ} {σ : ℝ≥0} (hα : Continuous α) (hαi : Function.Injective α)
    (hβ : Continuous β) (hβi : Function.Injective β) (hβ0 : β 0 = 0)
    (hno : ∀ c : ℝ≥0, ¬ Supp9.HasCommonOpenSubarc α σ β c)
    (hH : ∀ x y : ℝ≥0, x < y → ∃ z ∈ Ioo x y, β z ∈ H) :
    ∃ r ∈ dyadSet, β r ∈ H ∧ β r ∉ α '' Icc 0 σ ∧ ∀ t ≤ r, ‖β t‖ < 1 / 2 := by
  -- a prefix inside `B(0, 1/2)`
  obtain ⟨δ, hδ, hδβ⟩ := Metric.continuousAt_iff.1 (hβ.continuousAt (x := 0)) (1 / 2) (by norm_num)
  set ρ : ℝ≥0 := ⟨δ / 2, by positivity⟩ with hρdef
  have hρ0 : 0 < ρ := by rw [← NNReal.coe_pos]; show 0 < δ / 2; positivity
  have hsmall : ∀ t ≤ ρ, ‖β t‖ < 1 / 2 := by
    intro t ht
    have h := hδβ (x := t) (by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
      have : (t : ℝ) ≤ δ / 2 := ht
      linarith)
    rwa [dist_eq_norm, hβ0, sub_zero] at h
  -- a time off the first prefix, then an interior one nearby
  obtain ⟨s, hs, hsα⟩ := exists_notMem_image_of_not_subarc hα hαi hβ hβi hρ0 le_rfl (hno ρ)
  have hO : IsOpen {t : ℝ≥0 | β t ∉ α '' Icc 0 σ} :=
    ((isCompact_Icc.image hα).isClosed.isOpen_compl).preimage hβ
  have hO' : IsOpen ({t : ℝ≥0 | β t ∉ α '' Icc 0 σ} ∩ Ioo 0 ρ) := hO.inter isOpen_Ioo
  obtain ⟨a, b, hab, hsub⟩ : ∃ a b : ℝ≥0, a < b ∧ Ioo a b ⊆ {t : ℝ≥0 | β t ∉ α '' Icc 0 σ} ∩ Ioo 0 ρ := by
    obtain ⟨l, u', hlu, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨0, hs.1⟩ ⟨ρ, hs.2⟩).1
      (hO'.mem_nhds ⟨hsα, hs⟩)
    exact ⟨l, u', hlu.1.trans hlu.2, hsub⟩
  obtain ⟨z, hz, hzH⟩ := hH a b hab
  have hU : IsOpen ({t : ℝ≥0 | β t ∈ H} ∩ Ioo a b) :=
    (QuantumZipper.isOpen_H.preimage hβ).inter isOpen_Ioo
  obtain ⟨l, u', hlu, hsub'⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨a, hz.1⟩ ⟨b, hz.2⟩).1
    (hU.mem_nhds ⟨hzH, hz⟩)
  obtain ⟨r, hr, hlr, hru⟩ := exists_dyadSet_btwn (hlu.1.trans hlu.2)
  have hrm := hsub' ⟨hlr, hru⟩
  have hrm' := hsub hrm.2
  exact ⟨r, hr, hrm.1, hrm'.1, fun t ht => hsmall t (ht.trans hrm'.2.2.le)⟩


/-! ### The pathwise core from its deterministic part -/

/-- **The pathwise core of G8's positivity from its deterministic part and Lemma W0b.** Almost surely: the point `1`
is swallowed by `α` at a finite time `σ` with a real landing point `q > 1` (`RLCJ.ae_swallow_landing`); Lemma W0b and
the absence of real subarcs of `β` give a dyadic interior cut `r` of `β` near the seed, off `α([0, σ])`
(`exists_dyad_cut`); the deterministic part gives a final interval `(t₀, σ)`, and a dyadic `u` in it is an ordinary
retained pair `(u, r)` (the completions are the complete ordered pair itself) with a small gap at `1`. -/
theorem g8PathFrameStatement_of_det (hW0b : Supp9.W0bStatement.{u}) (hD : G8DetFrameStatement) :
    G8PathFrameStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ C hθ hr₁ hr₂ Ω mΩ P hP h hh α β ζα ζβ hα hβ hord ε hε
  have hlam := Sec4.sleLambda_pos hκ
  have hchi := Sec4.chiC_pos hκ hκ4
  -- the driver of `α`, its generating trace, and the swallow of `1`
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hc, htrace⟩ := Sec7.isFlowLine_prop74Data_iff.1 hα
  have hL : -2 < (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ - θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
    have h0 : 0 ≤ (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ - θ₁ * QuantumZipper.chiC κ) / sleLambda κ := by
      apply div_nonneg _ hlam.le
      nlinarith
    linarith
  have hR : -2 < (C + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 := hr₁
  have hRc : (C + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 < κ / 2 - 2 := hr₂
  have hηα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζα ω) (α ω) := by
    filter_upwards [htrace] with ω hω
    simpa using hω
  have hland := RLCJ.ae_swallow_landing hκ hκ4 hL hR hRc hc.1 hηα one_pos
  have hgα := LP.ae_good hκ hL hR hc.1
  have hpα := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hα
  have hpβ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hβ
  have hw0b := hW0b κ hκ hκ4 _ _ (Sec7.isPiecewiseConstant_prop74Data
    (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) 0 0 θ₁ θ₂ le_rfl hθ P h hh α β ζα ζβ hα hβ
  refine Filter.Eventually.frequently ?_
  filter_upwards [hland, hgα, hpα, hpβ, hw0b, hord, hηα] with ω ⟨σ, _, hsw, q, hq1, hασ, _⟩ ⟨_, hw, hw0⟩ hpαω
    hpβω hw0bω ⟨hζα, hζβ, hcop⟩ hηω
  have hα0 : α ω 0 = 0 := by simpa using Sec7.IsPathGood.zero hpαω
  have hβ0 : β ω 0 = 0 := by simpa using Sec7.IsPathGood.zero hpβω
  rw [hζα] at hηω
  obtain ⟨-, wβ, hwβ, hwβ0, hgβ⟩ := hpβω
  have hH : ∀ x y : ℝ≥0, x < y → ∃ z ∈ Ioo x y, β ω z ∈ H := by
    intro x y hxy
    obtain ⟨z, hz, hzH⟩ := exists_mem_H_of_isGeneratingTrace hgβ hwβ hwβ0 hxy
      (by rw [hζβ]; exact ENNReal.coe_lt_top)
    exact ⟨z, hz, by simpa using hzH⟩
  have hno : ∀ c : ℝ≥0, ¬ Supp9.HasCommonOpenSubarc (α ω) σ (β ω) c := fun c =>
    hw0bω σ c (by rw [hζα]; exact ENNReal.coe_lt_top) (by rw [hζβ]; exact ENNReal.coe_lt_top)
      (hcop.hasOrderedProperCompletions σ c)
  obtain ⟨r, hr, hβrH, hβrα, hβsmall⟩ :=
    exists_dyad_cut hcop.1 hcop.2.1 hcop.2.2.2.2.1 hcop.2.2.2.2.2.1 hβ0 hno hH
  obtain ⟨t₀, ht₀σ, hfr⟩ := hD (α ω) (β ω) (fun t => W t ω) σ r q ε hε hcop hα0 hβ0 hw hw0 hηω hsw hq1
    hασ hβrH hβrα hβsmall
  obtain ⟨u, hu, ht₀u, huσ⟩ := exists_dyadSet_btwn ht₀σ
  obtain ⟨h1, h2, h3, h4, hgap⟩ := hfr u ht₀u huσ
  refine ⟨u, hu, r, hr, ⟨by rw [hζα]; exact ENNReal.coe_lt_top, by rw [hζβ]; exact ENNReal.coe_lt_top, h1,
    hβrH, fun h => hβrα (image_mono (Icc_subset_Icc_right huσ.le) h), h2, h3, h4,
    hcop.hasOrderedProperCompletions _ _⟩, hgap⟩

/-- **Lemma G8's positivity from the deterministic frame statement and Lemma W0b.** -/
theorem g8PositivityStatement_of_det (hW0b : Supp9.W0bStatement.{u}) (hD : G8DetFrameStatement) :
    G8PositivityStatement.{u} :=
  g8PositivityStatement_of_pathFrame (g8PathFrameStatement_of_det hW0b hD)


/-- **Lemma G8 (with G9) from its remaining inputs**: PROVE-RLC-K's assembly `g8FrameStatement_of_cond_pos` with the
conditional restart from Theorems 1.2 (param), 1.3 and `RetainedCanonCondDetHistStatement`
(`retainedPairRestartCondStatement_of_param`), and the positivity from `G8DetFrameStatement` and Lemma W0b, which
follows from Lemma 7.5 (`Supp9.w0bStatement_of_lemma75`). R43/R48: for Theorem 1.5 only. -/
theorem g8FrameStatement_of_inputs (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetHistStatement.{0})
    (hDet : G8DetFrameStatement) : G8FrameStatement.{0} :=
  g8FrameStatement_of_cond_pos h75 href (retainedPairRestartCondStatement_of_param h12p h13 hD)
    (g8PositivityStatement_of_det (Supp9.w0bStatement_of_lemma75 h75) hDet)

end RLC

end InteractingSLE
