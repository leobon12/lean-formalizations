/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Inputs
import InteractingSLE.Spec.Supplement.S9Propagation

/-!
# Theorem 1.5 by D.5: the critical-angle exclusion (Theorem 7.12D) from the D.5 interfaces

Packet PROVE-T15-D5. Follow-up note D.5, "Critical-angle exclusion": "Put `D = (θ₊ − θ₋)χ/λ`. In the exposed-side
chart of interface 5, the higher-angle path sees the left side of the lower-angle path at height
`−λ + (θ₊ − θ₋)χ`. Its right outward cumulative force weight is therefore `D − 2`. If `D ≥ κ/2`, this is at least
`c`, and GB7a excludes the first new contact with that open side before collar exit. The rational-cut construction
ensures any proposed interior contact supplies such a witness".

* `notMem_H_of_firstHit_strict` — **interface 5, the rational-cut collar** (supplement p. 543): every strict
  interior contact supplies a retained pair `(u, r)` and a first new hit `η₁(x*) ∈ ℍ`, `x* < u`, of the retained
  prefix. It is PROVE-SUPP10-B's frame `Supp10.notMem_H_of_firstHit` with the order hypothesis weakened to the
  increasing order of the **strict** contacts, which is all the source uses.
* `ae_strictContactsIncreasing` — the strict contacts of W5's ordered pair increase, by the contact-order theorem
  of the completions (G5 for one seed, Aux. 84 for ordered distinct seeds); no W2a/W6 terminal-contact step.
* `thm712DStatement_of_d5` — **Theorem 7.12D** (`Theorem15.Thm712DStatement`) from the D.5 interfaces only:
  `G7GB7aFirstHitStatement` (with (7.12D.1): `D ≥ κ/2 ⟹` exposed-side weight `D − 2 ≥ c`), W0b, W5 with its
  contact-order theorems, Aux. 25 and the reality of finite endpoints.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem15D5

open Sec7 Theorem15 Supp10

/-- **Interface 5: the rational-cut collar of Theorem 7.12D** (supplement p. 543), with the increasing order of
the strict contacts. For continuous injective available curves `α`, `β` with a non-interior seed of `β`, no common
open subarc (W0b) and the local first-hit exclusion at retained pairs (G7 + GB7a), no strict contact
`α(a) = β(t)` lies in `ℍ`. The cutoff `u ∈ (a, ζ₁)`; a left neighbourhood `(l, t]` on which `β` stays in `ℍ`; by
W0b a time `r ∈ (l, t)` with `β(r) ∉ α([0, u])`; the least time `t* ∈ [r, t]` with `β(t*) ∈ α([0, u])`
(compactness), `t* > r`, `β(t*) = α(x*)`; then `x* ≤ a < u` (injectivity when `t* = t`, otherwise the strict
contact order: `a < x*` would force `t < t*`), and `β(t*) ∈ ℍ`, so the first-hit exclusion applies. -/
theorem notMem_H_of_firstHit_strict {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hcα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hcβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hiα : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hβ0 : β 0 ∉ QuantumZipper.H) (hCI : StrictContactsIncreasing α ζ₁ β ζ₂)
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
  have hxζ' : (x : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.mpr hx.2).trans_lt hu
  -- `x ≤ a`: injectivity at `ts = t`, the strict contact order otherwise
  have hxa : x ≤ a := by
    rcases eq_or_lt_of_le htst with heq | hlt'
    · rw [heq] at hβx
      exact (hiα hxζ'.le ha.le (hβx.trans hat.symm)).le
    · by_contra hax
      exact absurd (hCI a x t ts ha hxζ' ht htsζ hat hβx (not_le.mp hax)) (not_lt.mpr hlt'.le)
  have hgap : ∀ t' : ℝ≥0, r < t' → t' < ts → β t' ∉ α '' Icc 0 u := fun t' h1 h2 hmem =>
    not_le.mpr h2 (hleast ⟨⟨h1.le, h2.le.trans htst⟩, hmem⟩)
  have hHx : α x ∈ QuantumZipper.H := by
    rw [hβx]
    exact hIoc ⟨hrI.1.trans hrts', htst⟩
  exact hFH u r hu hrζ hr ts x hrts' htsζ (hxa.trans_lt hau') hβx.symm hHx hgap

/-- **Interface 3's contact-order theorem**: for W5's ordered pair (lower-angle `η₁` from `x₁`, higher-angle `η₂`
from `x₂ ≤ x₁`), almost surely the strict contacts increase (Aux. 84 for `x₂ < x₁`, G5 for `x₁ = x₂`). -/
theorem ae_strictContactsIncreasing (hW5 : W5Statement.{u}) (h84 : Aux84Statement) (hG5 : G5Statement)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (h₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (h₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, StrictContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) := by
  filter_upwards [hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    ae_apply_zero_of_isFlowLine h₁, ae_apply_zero_of_isFlowLine h₂] with ω hord h0₁ h0₂
  intro s s' t t' hs hs' ht ht' hst hst' hlt
  rcases hx.lt_or_eq with hlt₁₂ | heq
  · exact contacts_strict_increasing_of_completions_of_lt h84 hlt₁₂ h0₁ h0₂ hord hs hs' ht ht' hst hst' hlt
  · rw [heq] at h0₂
    exact (contacts_strict_increasing_of_completions hG5 h0₁ h0₂ hord hs hs' ht ht' hst hst').mp hlt

/-- **Theorem 7.12D** (critical-angle exclusion of interior contacts; supplement §10.1, p. 543) from the D.5
interfaces: G7 + GB7a at a retained pair (`G7GB7aFirstHitStatement`, whose weight hypothesis is supplied by (7.12D.1)
from `D_θ ≥ κ/2`), W0b, W5 with its contact-order theorems (Aux. 84, G5), Aux. 25 and the reality of finite
continuation endpoints; the rational-cut collar is `notMem_H_of_firstHit_strict`. -/
theorem thm712DStatement_of_d5 (hFH : G7GB7aFirstHitStatement.{u}) (hE : FiniteEndpointRealStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (hW5 : W5Statement.{u}) (h84 : Aux84Statement) (hG5 : G5Statement)
    (hA25 : Aux25Statement.{u}) : Thm712DStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have hθ : θ₁ < θ₂ := lt_of_half_le_angleGap hκ hκ4 hD
  have hW0b' := w0bSecondArcStatement_of_firstArc hW0b hA25
  filter_upwards [hFH κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx (cumWeightRight_exposed_ge_of_half_le hκ hD)
      P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    hE κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ h₁, hE κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ h₂,
    hW0b' κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    ae_strictContactsIncreasing hW5 h84 hG5 hκ hκ4 hb hx hθ hh h₁ h₂,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂,
    ae_apply_zero_of_isFlowLine h₂] with ω hFHω hE₁ hE₂ hW0bω hord hCIω hi₁ hc₁ hc₂ h0₂
  intro s t hs ht hst
  rcases hs.lt_or_eq with hs' | hs'
  · rcases ht.lt_or_eq with ht' | ht'
    · exact notMem_H_of_firstHit_strict hc₁ hc₂ hi₁ (by rw [h0₂]; exact ofReal_notMem_H x₂) hCIω
        (fun a c ha hc => hW0bω a c ha hc (hord a c ha hc)) (hFHω hord hCIω) hs' ht' hst
    · rw [hst]
      exact hE₂ t ht'
  · exact hE₁ s hs'

end Theorem15D5

end InteractingSLE
