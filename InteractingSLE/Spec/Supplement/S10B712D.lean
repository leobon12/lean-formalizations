/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S10Theorem15
import InteractingSLE.Spec.Supplement.S10Weights

/-!
# Theorem 7.12D (critical-angle exclusion of interior contacts), reduced to its local step

Packet PROVE-SUPP10-B (specification supplement §10.1, `source/spec/p529-576.md` L343–L363, pp. 543–544).

The proof of Theorem 7.12D has a deterministic frame and one local probabilistic step. The frame is proved here
(`thm712DStatement_of_inputs`):

1. *Strictness.* "A nonempty interior path has positive initial lifetime, and a genuine finite continuation endpoint
   is original-real. Thus every proposed interior contact `q = α(a) = β(t)` is strict for both maximal lifetimes."
   The fact used is the named input `FiniteEndpointRealStatement`; the seeds are real (`ae_apply_zero_of_isFlowLine`).
2. *Order.* "W5 gives all the earlier ordered proper completions and, by their contact-order theorem, increasing
   coordinates of the contacts." This is PROVE-SUPP10's `ae_contactsIncreasing_of_lt` (`x₂ < x₁`) and `w6_of_lt`
   (`x₁ = x₂`), from W5, W2a, Aux. 84 / G5 and Aux. 25; the angles are ordered because `D_θ ≥ κ/2 > 0`.
3. *The retained pair and the first new hit* (`notMem_H_of_firstHit`). "Choose a rational own cutoff `u > a`, still
   strictly available […]. Since there is no common open arc, choose a rational own time `r < t` on that portion with
   `β(r)` off `A` [= `α([0, u])`]. Choose it sufficiently late that its segment through `q` stays inside the buffered
   collar." W0b is the named input `W0bSecondArcStatement`, which follows from PROVE-SUPP9's form of W0b by the
   deterministic arc symmetry `exists_firstArc_of_secondArc` (`w0bSecondArcStatement_of_firstArc`). Then the first time `t* ∈ (r, t]` at which `β` meets `A`
   is attained (compactness), `β(t*) = α(x*)` lies in `ℍ` (the late segment stays in `ℍ`), and `x* < u` by increasing
   contact order: "It cannot belong to the first prefix before its last old common point, by increasing contact
   order" (`x*` follows every old contact), and `x* ≤ a < u` (the collar "avoids the current first tip").
4. *The local step* is the named input `Thm712DFirstHitStatement`: at a retained pair `(u, r)`, the left path's future
   does not first meet the retained right prefix `α([0, u])` at an interior point `α(x)`, `x < u`. This is the part of
   the proof that runs under the conditional law: "G7 identifies this entire conditional stopped field–path law with
   the canonical finite-word flow […] this first hit belongs to an open interval of the exposed first left side in
   (7.12D.1) […] GB7a excludes every point of this interval for the canonical conditional law". The weight
   computation (7.12D.1) itself is `thm712D_one` (PROVE-SUPP10).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp10

open Sec7 Theorem15

/-! ### Named inputs -/

/-- **Named input: a genuine finite continuation endpoint is original-real** (supplement §10.1, proof of
Theorem 7.12D, p. 543: "A nonempty interior path has positive initial lifetime, and a genuine finite continuation
endpoint is original-real"; the continuation threshold is reached only at a collision of the driver with a force
group of cumulative weight at most `−2`, p. 20, whose geometric force endpoints lie on the real boundary, p. 39). For
a flow line, almost surely the value at a finite available lifetime is not in `ℍ`. -/
def FiniteEndpointRealStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω → η ω T ∉ QuantumZipper.H

/-- **Named input: Lemma W0b** (no common open arc on an ordered earlier prefix; supplement §9, p. 529): "For
`θ₁ ≠ θ₂`, almost surely no pair of original finite prefixes which admits the ordered proper completions of W0
contains a common nontrivial open subarc", for the flow lines of W5 (`x₂ ≤ x₁`, `θ₁ < θ₂`), with the common arc
parametrized by the second path: no open subarc `η₂((y₁, y₂))`, `y₂ ≤ c`, of the second prefix lies in the first
prefix `η₁([0, a])`. PROVE-SUPP9 states W0b with the arc parametrized by the first path (`Supp9.W0bStatement`);
that form implies this one (`w0bSecondArcStatement_of_firstArc`, with Aux. lemma 25), so this is not an additional
source obligation. -/
def W0bSecondArcStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c →
        ¬ ∃ y₁ y₂ : ℝ≥0, y₁ < y₂ ∧ y₂ ≤ c ∧ η₂ ω '' Ioo y₁ y₂ ⊆ η₁ ω '' Icc 0 a

/-- **Named input: the local step of Theorem 7.12D** (supplement §10.1, p. 543–544: the retained ordinary pair, G7
and GB7a). In the setting of `Theorem15.Thm712DStatement` (`η₁` the lower-angle path from `x₁`, `η₂` the higher-angle
path from `x₂ ≤ x₁`, `D_θ ≥ κ/2`), almost surely, given the ordered proper completions of W5 and increasing contact
order: for a retained pair of strictly available own cutoffs `u` (first path) and `r` (second path) with `η₂(r)` off
the retained first prefix `A = η₁([0, u])`, the second future does not make its first new contact with `A` at an
interior point `η₁(x) ∈ ℍ` before the first tip (`x < u`). Source: "Stop the actual second future at its first new
contact with the retained old union […]. G7 identifies this entire conditional stopped field–path law with the
canonical finite-word flow. […] On the proposed witness, there is a first new old-range hit […]. Consequently this
first hit belongs to an open interval of the exposed first left side in (7.12D.1). […] GB7a excludes every point of
this interval for the canonical conditional law, including its continuous terminal stop." The source takes rational
cutoffs; real cutoffs are equivalent (a first hit for real `u`, `r` is one for rational `u' ∈ (x, u)`,
`r' ∈ (r, t)`). -/
def Thm712DFirstHitStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → κ / 2 ≤ (θ₂ - θ₁) * QuantumZipper.chiC κ / sleLambda κ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) →
        ∀ u r : ℝ≥0, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → η₂ ω r ∉ η₁ ω '' Icc 0 u →
          ∀ t x : ℝ≥0, r < t → (t : ℝ≥0∞) < ζ₂ ω → x < u → η₂ ω t = η₁ ω x →
            η₁ ω x ∈ QuantumZipper.H → (∀ t' : ℝ≥0, r < t' → t' < t → η₂ ω t' ∉ η₁ ω '' Icc 0 u) →
            False

/-! ### The deterministic frame -/

/-- A real point is not in `ℍ`. -/
theorem ofReal_notMem_H (x : ℝ) : (x : ℂ) ∉ QuantumZipper.H := fun h => by
  have h' : (0 : ℝ) < (x : ℂ).im := h
  rw [Complex.ofReal_im] at h'
  exact lt_irrefl 0 h'

/-- **The retained pair and the first new hit** (Theorem 7.12D's proof, p. 543): for continuous injective curves `α`,
`β` with increasing contacts, a non-interior seed of `β`, no common open subarc (W0b) and the local first-hit
exclusion at retained pairs, no strict contact `α(a) = β(t)` lies in `ℍ`. The cutoff `u ∈ (a, ζ₁)`; a left
neighbourhood `(l, t]` on which `β` stays in `ℍ`; by W0b a time `r ∈ (l, t)` with `β(r) ∉ α([0, u])`; the least time
`t* ∈ [r, t]` with `β(t*) ∈ α([0, u])` (compactness), `t* > r`, `β(t*) = α(x*)`; then `x* ≤ a < u` by increasing
contact order (or injectivity when `t* = t`) and `β(t*) ∈ ℍ`, so the first-hit exclusion applies. -/
theorem notMem_H_of_firstHit {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hcα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hcβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hiα : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hiβ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hβ0 : β 0 ∉ QuantumZipper.H) (hCI : ContactsIncreasing α ζ₁ β ζ₂)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ →
      ¬ ∃ y₁ y₂ : ℝ≥0, y₁ < y₂ ∧ y₂ ≤ c ∧ β '' Ioo y₁ y₂ ⊆ α '' Icc 0 a)
    (hFH : ∀ u r : ℝ≥0, (u : ℝ≥0∞) < ζ₁ → (r : ℝ≥0∞) < ζ₂ → β r ∉ α '' Icc 0 u →
      ∀ t x : ℝ≥0, r < t → (t : ℝ≥0∞) < ζ₂ → x < u → β t = α x → α x ∈ QuantumZipper.H →
        (∀ t' : ℝ≥0, r < t' → t' < t → β t' ∉ α '' Icc 0 u) → False)
    {a t : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ₁) (ht : (t : ℝ≥0∞) < ζ₂) (hat : α a = β t) :
    α a ∉ QuantumZipper.H := by
  intro hH
  have hβt : β t ∈ QuantumZipper.H := by rw [← hat]; exact hH
  -- the cutoff `u`
  obtain ⟨u, hau, hu⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
  have hau' : a < u := ENNReal.coe_lt_coe.mp hau
  -- `t > 0`, since the seed of `β` is not interior
  have ht0 : 0 < t := pos_iff_ne_zero.mpr fun h0 => by
    rw [h0] at hβt
    exact hβ0 hβt
  -- a left neighbourhood `(l, t]` on which `β` stays in `ℍ`
  have hcont : ContinuousWithinAt β (Iic t) t :=
    (hcβ.mono fun t' (ht' : t' ≤ t) => (ENNReal.coe_le_coe.mpr ht').trans ht.le) t (mem_Iic.mpr le_rfl)
  have hnhds : β ⁻¹' QuantumZipper.H ∈ 𝓝[≤] t :=
    hcont.preimage_mem_nhdsWithin (QuantumZipper.isOpen_H.mem_nhds hβt)
  obtain ⟨l, hlt, hIoc⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' ht0).mp hnhds
  -- W0b: a time `r ∈ (l, t)` with `β r` off the first prefix
  obtain ⟨r, hrI, hr⟩ : ∃ r ∈ Ioo l t, β r ∉ α '' Icc 0 u := by
    by_contra hcon
    push Not at hcon
    refine hW0b u t hu ht ⟨l, t, hlt, le_rfl, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hcon r hr
  have hrζ : (r : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.mpr hrI.2).trans ht
  -- the first hit of the first prefix after `r`
  have hAc : IsClosed (α '' Icc 0 u) :=
    (isCompact_Icc.image_of_continuousOn
      (hcα.mono fun s (hs : s ∈ Icc 0 u) => (ENNReal.coe_le_coe.mpr hs.2).trans hu.le)).isClosed
  have hβIcc : ContinuousOn β (Icc r t) :=
    hcβ.mono fun t' (ht' : t' ∈ Icc r t) => (ENNReal.coe_le_coe.mpr ht'.2).trans ht.le
  have hSc : IsCompact (Icc r t ∩ β ⁻¹' (α '' Icc 0 u)) :=
    isCompact_Icc.of_isClosed_subset (hβIcc.preimage_isClosed_of_isClosed isClosed_Icc hAc)
      inter_subset_left
  have hSne : (Icc r t ∩ β ⁻¹' (α '' Icc 0 u)).Nonempty :=
    ⟨t, ⟨hrI.2.le, le_rfl⟩, ⟨a, ⟨zero_le, hau'.le⟩, hat⟩⟩
  obtain ⟨ts, ⟨⟨hrts, htst⟩, x, hx, hβx⟩, hleast⟩ := hSc.exists_isLeast hSne
  have hrts' : r < ts := lt_of_le_of_ne hrts fun h => by
    subst h
    exact hr ⟨x, hx, hβx⟩
  have htsζ : (ts : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.mpr htst).trans_lt ht
  have hxζ : (x : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.mpr hx.2).trans hu.le
  -- `x ≤ a`: increasing contact order (or injectivity at `ts = t`)
  have hxa : x ≤ a := by
    rcases eq_or_lt_of_le htst with heq | hlt'
    · rw [heq] at hβx
      exact (hiα hxζ ha.le (hβx.trans hat.symm)).le
    · have hp : ((x, ts) : ℝ≥0 × ℝ≥0) ∈ stoppedContactSet α 0 ζ₁ β 0 ζ₂ :=
        ⟨zero_le, hxζ, zero_le, htsζ.le, hβx⟩
      have hq : ((a, t) : ℝ≥0 × ℝ≥0) ∈ stoppedContactSet α 0 ζ₁ β 0 ζ₂ :=
        ⟨zero_le, ha.le, zero_le, ht.le, hat⟩
      exact (hCI.fst_lt_of_snd_lt hiβ hp hq hlt').le
  have hgap : ∀ t' : ℝ≥0, r < t' → t' < ts → β t' ∉ α '' Icc 0 u := fun t' h1 h2 hmem =>
    not_le.mpr h2 (hleast ⟨⟨h1.le, h2.le.trans htst⟩, hmem⟩)
  have hHx : α x ∈ QuantumZipper.H := by
    rw [hβx]
    exact hIoc ⟨hrI.1.trans hrts', htst⟩
  exact hFH u r hu hrζ hr ts x hrts' htsζ (hxa.trans_lt hau') hβx.symm hHx hgap

/-! ### The two forms of W0b -/

/-- **A common open subarc is symmetric** (for the two forms of Lemma W0b): if an open subarc `β((y₁, y₂))`,
`y₂ ≤ c`, of an injective continuous curve lies in `α([0, a])` for an injective continuous `α`, then an open subarc
`α((x₁, x₂))`, `x₂ ≤ a`, lies in `β([0, c])`. Choose `y₁ < p < q < y₂`. As `α` is a closed embedding of the compact
interval `[0, a]`, `g = α⁻¹ ∘ β` is continuous on `[p, q]`, with `g p ≠ g q`; by the intermediate value theorem
`α` maps the interval between `g p` and `g q` into `β([p, q])`. -/
theorem exists_firstArc_of_secondArc {α β : ℝ≥0 → ℂ} {a c : ℝ≥0}
    (hcα : ContinuousOn α (Icc 0 a)) (hiα : InjOn α (Icc 0 a)) (hcβ : ContinuousOn β (Icc 0 c))
    (hiβ : InjOn β (Icc 0 c)) {y₁ y₂ : ℝ≥0} (hy : y₁ < y₂) (hy₂ : y₂ ≤ c)
    (hsub : β '' Ioo y₁ y₂ ⊆ α '' Icc 0 a) :
    ∃ x₁ x₂ : ℝ≥0, x₁ < x₂ ∧ x₂ ≤ a ∧ α '' Ioo x₁ x₂ ⊆ β '' Icc 0 c := by
  -- two interior parameters `p < q` of the arc
  obtain ⟨p, hy₁p, hpy₂⟩ := exists_between hy
  obtain ⟨q, hpq, hqy₂⟩ := exists_between hpy₂
  have hIcc : Icc p q ⊆ Ioo y₁ y₂ := fun y hy => ⟨hy₁p.trans_le hy.1, hy.2.trans_lt hqy₂⟩
  have hIcc' : Icc p q ⊆ Icc 0 c := fun y hy => ⟨zero_le, hy.2.trans (hqy₂.le.trans hy₂)⟩
  -- `α` on `[0, a]` is a closed embedding
  have : CompactSpace (Icc 0 a) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hF : Topology.IsClosedEmbedding ((Icc 0 a).domRestrict α) :=
    (continuousOn_iff_continuous_domRestrict.mp hcα).isClosedEmbedding hiα.injective
  -- the inverse chart `G : [p, q] → [0, a]`, `α ∘ G = β`
  have hmem : ∀ y : Icc p q, ∃ x : Icc 0 a, (Icc 0 a).domRestrict α x = β y := fun y => by
    obtain ⟨x, hx, hxy⟩ := hsub (mem_image_of_mem β (hIcc y.2))
    exact ⟨⟨x, hx⟩, hxy⟩
  choose G hG using hmem
  have hGc : Continuous G := by
    rw [hF.isInducing.continuous_iff]
    have hcomp : ((Icc 0 a).domRestrict α ∘ G) = (Icc p q).domRestrict β := funext hG
    rw [hcomp]
    exact continuousOn_iff_continuous_domRestrict.mp (hcβ.mono hIcc')
  set g : ℝ≥0 → ℝ≥0 := fun y => if hy : y ∈ Icc p q then (G ⟨y, hy⟩ : ℝ≥0) else 0 with hg
  have hgG : ∀ y (hy : y ∈ Icc p q), g y = G ⟨y, hy⟩ := fun y hy => by
    simp only [hg]
    exact dite_eq_left hy
  have hgc : ContinuousOn g (Icc p q) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : (Icc p q).domRestrict g = fun y => (G y : ℝ≥0) := funext fun y => hgG y y.2
    rw [hres]
    exact continuous_subtype_val.comp hGc
  have hαg : ∀ y (hy : y ∈ Icc p q), α (g y) = β y := fun y hy => by
    rw [hgG y hy]
    exact hG ⟨y, hy⟩
  have hga : ∀ y (hy : y ∈ Icc p q), g y ≤ a := fun y hy => by
    rw [hgG y hy]
    exact (G ⟨y, hy⟩).2.2
  have hp : p ∈ Icc p q := left_mem_Icc.mpr hpq.le
  have hq : q ∈ Icc p q := right_mem_Icc.mpr hpq.le
  have hne : g p ≠ g q := fun h =>
    hpq.ne (hiβ (hIcc' hp) (hIcc' hq) (by rw [← hαg p hp, ← hαg q hq, h]))
  refine ⟨min (g p) (g q), max (g p) (g q), min_lt_max.mpr hne, max_le (hga p hp) (hga q hq), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzu : z ∈ uIcc (g p) (g q) := Ioo_subset_Icc_self hz
  have hivt := intermediate_value_uIcc (a := p) (b := q) (f := g)
    (by rw [uIcc_of_le hpq.le]; exact hgc)
  obtain ⟨y, hy, rfl⟩ := hivt hzu
  rw [uIcc_of_le hpq.le] at hy
  exact ⟨y, hIcc' hy, (hαg y hy).symm⟩

/-- **The second-arc form of W0b from the first-arc form.** The hypothesis is Lemma W0b with the common open arc
parametrized by the first path (`α((x₁, x₂)) ⊆ β([0, c])`, `x₂ ≤ a`), the form in which PROVE-SUPP9 states it
(`Supp9.W0bStatement`, with `Supp9.HasCommonOpenSubarc` unfolded); with Aux. lemma 25 (simplicity) and continuity
of flow lines it gives `W0bSecondArcStatement` (`exists_firstArc_of_secondArc`). -/
theorem w0bSecondArcStatement_of_firstArc
    (hW0b : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
      IsPiecewiseConstantBoundaryData b jumps → ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
      ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
        IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
        ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c →
          ¬ ∃ x₁ x₂ : ℝ≥0, x₁ < x₂ ∧ x₂ ≤ a ∧ η₁ ω '' Ioo x₁ x₂ ⊆ η₂ ω '' Icc 0 c)
    (hA25 : Aux25Statement.{u}) : W0bSecondArcStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hW0b κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂] with ω hω hi₁ hi₂ hc₁ hc₂
  rintro a c ha hc hord ⟨y₁, y₂, hy, hy₂, hsub⟩
  have hsa : Icc 0 a ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ ζ₁ ω} := fun s hs =>
    (ENNReal.coe_le_coe.mpr hs.2).trans ha.le
  have hsc : Icc 0 c ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₂ ω} := fun t ht =>
    (ENNReal.coe_le_coe.mpr ht.2).trans hc.le
  exact hω a c ha hc hord (exists_firstArc_of_secondArc (hc₁.mono hsa) (hi₁.mono hsa) (hc₂.mono hsc)
    (hi₂.mono hsc) hy hy₂ hsub)

/-! ### Theorem 7.12D -/

/-- **Theorem 7.12D** (critical-angle exclusion of interior contacts; supplement §10.1, p. 543), the Theorem 1.5
input `Theorem15.Thm712DStatement`, from its local step (`Thm712DFirstHitStatement`: G7 and GB7a at a retained
pair), the reality of finite continuation endpoints (`FiniteEndpointRealStatement`), Lemma W0b, Theorem W5, Lemma W2a,
the boundary-order theorems Aux. 84 and G5, and Aux. lemma 25. -/
theorem thm712DStatement_of_inputs (hFH : Thm712DFirstHitStatement.{u})
    (hE : FiniteEndpointRealStatement.{u}) (hW0b : W0bSecondArcStatement.{u}) (hW5 : W5Statement.{u})
    (hW2a : W2aStatement.{u}) (h84 : Aux84Statement) (hG5 : G5Statement) (hA25 : Aux25Statement.{u}) :
    Thm712DStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have hθ : θ₁ < θ₂ := lt_of_half_le_angleGap hκ hκ4 hD
  have hCI : ∀ᵐ ω ∂P, ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) := by
    rcases hx.lt_or_eq with hlt | heq
    · exact ae_contactsIncreasing_of_lt hW5 hW2a h84 hA25 hκ hκ4 hb hlt hθ hh h₁ h₂
    · subst heq
      exact w6_of_lt hW5 hW2a hG5 hA25 hκ hκ4 hb hθ hh h₁ h₂
  filter_upwards [hFH κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    hE κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ h₁, hE κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ h₂,
    hW0b κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂, hCI,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂,
    ae_apply_zero_of_isFlowLine h₂] with ω hFHω hE₁ hE₂ hW0bω hord hCIω hi₁ hi₂ hc₁ hc₂ h0₂
  intro s t hs ht hst
  rcases hs.lt_or_eq with hs' | hs'
  · rcases ht.lt_or_eq with ht' | ht'
    · exact notMem_H_of_firstHit hc₁ hc₂ hi₁ hi₂ (by rw [h0₂]; exact ofReal_notMem_H x₂) hCIω
        (fun a c ha hc => hW0bω a c ha hc (hord a c ha hc)) (hFHω hord hCIω) hs' ht' hst
    · rw [hst]
      exact hE₂ t ht'
  · exact hE₁ s hs'

end Supp10

end InteractingSLE
