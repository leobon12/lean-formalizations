/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9CTip
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Spec.Supplement.G7Carrier

/-!
# Theorem 1.5's leaf 3: when a later line of a continuation is an ordinary pair

Packet PROVE-T15-ORDDET4. The later-line facts of both continuations (PROVE-T15-ORDDET2/3:
`OrdDet.ae_retLine_facts_snd_of_ordinary`, `OrdDet.ae_retLine_facts_fst_canon`) are proved at lines whose later pair is
ordinary (`Supp7.IsOrdinaryRetainedPair`). This file reduces the ordinariness of the later pair, before the
continuation's first new contact with the retained range `A = η₁[0,u] ∪ η₂[0,r]`, to exactly two conditions:

* **the moving tip is interior** at the line (`η₂(r + t) ∈ ℍ`, resp. `η₁(u + t) ∈ ℍ`; fails only at the times the
  continuation sits on an untouched real interval);
* **the fixed tip stays active** (`η₁(u)`, resp. `η₂(r)`, adherent to the later joint unbounded component; fails exactly
  when the continuation has closed a real pocket around the other prefix, G7 p. 498: "Any portion of the fixed
  retained hull it surrounds is swallowed with that same pocket").

The moving tip's activity is PROVE-T15-ORDDET2/3's `OrdDet.later_tip_mem_closure_activeDomain(_fst)`. **The ordered
proper completions at the later pair are proved here** from the earlier ones by Lemma W4 (`Supp9.W4Statement`,
proved from Aux. lemma 25: `Supp9B.w4Statement_of_aux25`): a continuation without a new contact keeps them.

* `isOrdinaryRetainedPair_later_snd`, `isOrdinaryRetainedPair_later_fst`: the deterministic reduction, given W4's
  pathwise conclusion `Supp9.ExtendsWithoutNewContact`;
* **`ae_hasOrderedProperCompletions_later`**: almost surely, simultaneously for all cutoffs, the ordered completions
  propagate along both continuations without new contact;
* **`ae_isOrdinaryRetainedPair_later_snd`**, **`ae_isOrdinaryRetainedPair_later_fst`**: almost surely, simultaneously
  for all cutoffs, an ordinary pair continued without new contact is ordinary at the later line once the moving tip is
  interior and the fixed tip active.

No result of Theorems 1.2–1.3 is used (W4 rests on Aux. lemma 25 only).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RLC.OrdLate

open Supp7

/-! ### The deterministic reduction -/

/-- **The later pair of the second continuation is ordinary** if the moving tip is interior and both tips are active:
an ordinary pair `(u, r)` continued along the second path to `r + t` (before its lifetime) without a new contact with
the first prefix, with W4's extension property for the two paths. -/
theorem isOrdinaryRetainedPair_later_snd {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {u r t : ℝ≥0}
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) (hW4 : Supp9.ExtendsWithoutNewContact η₁ ζ₁ η₂ ζ₂)
    (hlt : ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂) (hnc : ∀ s, r < s → s ≤ r + t → η₂ s ∉ η₁ '' Icc 0 u)
    (hH : η₂ (r + t) ∈ QuantumZipper.H) (hact₁ : η₁ u ∈ closure (activeDomain η₁ u η₂ (r + t)))
    (hact₂ : η₂ (r + t) ∈ closure (activeDomain η₁ u η₂ (r + t))) :
    IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ (r + t) := by
  obtain ⟨hu, -, hH₁, -, h5, h6, -, -, hE⟩ := hord
  have h5' : η₂ (r + t) ∉ η₁ '' Icc 0 u := by
    rcases eq_or_lt_of_le (le_add_right (le_refl r) : r ≤ r + t) with h | h
    · rw [← h]; exact h5
    · exact hnc _ h le_rfl
  have hc : ∀ x ∈ Icc 0 u, ∀ y ∈ Icc 0 (r + t), η₁ x = η₂ y → x ≤ u ∧ y ≤ r := by
    intro x hx y hy hxy
    refine ⟨hx.2, not_lt.1 fun hry => hnc y hry hy.2 ⟨x, hx, hxy⟩⟩
  refine ⟨hu, hlt, hH₁, hH, h5', ?_, hact₁, hact₂, ?_⟩
  · rintro ⟨y, hy, hye⟩
    rcases le_or_gt y r with hyr | hyr
    · exact h6 ⟨y, ⟨hy.1, hyr⟩, hye⟩
    · exact hnc y hyr hy.2 ⟨u, ⟨zero_le, le_rfl⟩, hye.symm⟩
  · exact hW4 u u r (r + t) le_rfl hu (le_add_right le_rfl) hlt hE hc (fun h => absurd h (lt_irrefl u))
      fun _ => h5

/-- **The later pair of the first continuation is ordinary** if the moving tip is interior and both tips are active
(the mirror of `isOrdinaryRetainedPair_later_snd`, continuing the first path to `u + t`). -/
theorem isOrdinaryRetainedPair_later_fst {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {u r t : ℝ≥0}
    (hord : IsOrdinaryRetainedPair η₁ ζ₁ u η₂ ζ₂ r) (hW4 : Supp9.ExtendsWithoutNewContact η₁ ζ₁ η₂ ζ₂)
    (hlt : ((u + t : ℝ≥0) : ℝ≥0∞) < ζ₁) (hnc : ∀ s, u < s → s ≤ u + t → η₁ s ∉ η₂ '' Icc 0 r)
    (hH : η₁ (u + t) ∈ QuantumZipper.H) (hact₁ : η₁ (u + t) ∈ closure (activeDomain η₁ (u + t) η₂ r))
    (hact₂ : η₂ r ∈ closure (activeDomain η₁ (u + t) η₂ r)) :
    IsOrdinaryRetainedPair η₁ ζ₁ (u + t) η₂ ζ₂ r := by
  obtain ⟨-, hr, -, hH₂, h5, h6, -, -, hE⟩ := hord
  have h6' : η₁ (u + t) ∉ η₂ '' Icc 0 r := by
    rcases eq_or_lt_of_le (le_add_right (le_refl u) : u ≤ u + t) with h | h
    · rw [← h]; exact h6
    · exact hnc _ h le_rfl
  have hc : ∀ x ∈ Icc 0 (u + t), ∀ y ∈ Icc 0 r, η₁ x = η₂ y → x ≤ u ∧ y ≤ r := by
    intro x hx y hy hxy
    exact ⟨not_lt.1 fun hux => hnc x hux hx.2 ⟨y, hy, hxy.symm⟩, hy.2⟩
  refine ⟨hlt, hr, hH, hH₂, ?_, h6', hact₁, hact₂, ?_⟩
  · rintro ⟨x, hx, hxe⟩
    rcases le_or_gt x u with hxu | hxu
    · exact h5 ⟨x, ⟨hx.1, hxu⟩, hxe⟩
    · exact hnc x hxu hx.2 ⟨r, ⟨zero_le, le_rfl⟩, hxe.symm⟩
  · exact hW4 u (u + t) r r (le_add_right le_rfl) hlt le_rfl hr hE hc (fun _ => h6)
      fun h => absurd h (lt_irrefl r)

/-! ### Almost surely, for all cutoffs -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma W4 for two flow lines** (`Supp9B.w4Statement_of_aux25` with Aux. lemma 25 proved). -/
theorem ae_extendsWithoutNewContact (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, Supp9.ExtendsWithoutNewContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) :=
  Supp9B.w4Statement_of_aux25 Theorem15.aux25Statement κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂
    hη₁ hη₂

/-- **The ordered proper completions propagate along both continuations** (Lemma W4): almost surely, for all cutoffs
`u, r` and extensions `t`, if the prefixes at `(u, r)` have ordered proper completions and the tip that is not
continued is off the other prefix, then a continuation of either path, strictly before its lifetime and without a new
contact with the other prefix, keeps them. -/
theorem ae_hasOrderedProperCompletions_later (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ u r t : ℝ≥0, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω →
      HasOrderedProperCompletions (η₁ ω) u (η₂ ω) r →
      ((((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → η₂ ω r ∉ η₁ ω '' Icc 0 u →
          (∀ s, r < s → s ≤ r + t → η₂ ω s ∉ η₁ ω '' Icc 0 u) →
          HasOrderedProperCompletions (η₁ ω) u (η₂ ω) (r + t)) ∧
        (((u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → η₁ ω u ∉ η₂ ω '' Icc 0 r →
          (∀ s, u < s → s ≤ u + t → η₁ ω s ∉ η₂ ω '' Icc 0 r) →
          HasOrderedProperCompletions (η₁ ω) (u + t) (η₂ ω) r)) := by
  filter_upwards [ae_extendsWithoutNewContact hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hW4 u r t hu hr hE
  refine ⟨fun hlt h5 hnc => ?_, fun hlt h6 hnc => ?_⟩
  · refine hW4 u u r (r + t) le_rfl hu (le_add_right le_rfl) hlt hE
      (fun x hx y hy hxy => ⟨hx.2, not_lt.1 fun hry => hnc y hry hy.2 ⟨x, hx, hxy⟩⟩)
      (fun h => absurd h (lt_irrefl u)) fun _ => h5
  · refine hW4 u (u + t) r r (le_add_right le_rfl) hlt le_rfl hr hE
      (fun x hx y hy hxy => ⟨not_lt.1 fun hux => hnc x hux hx.2 ⟨y, hy, hxy.symm⟩, hy.2⟩)
      (fun _ => h6) fun h => absurd h (lt_irrefl r)

/-- **Ordinary later lines of the second continuation**, almost surely and simultaneously for all cutoffs: an
ordinary pair `(u, r)` continued along the second path to `r + t < ζ₂` without a new contact with `η₁[0,u]` is an
ordinary pair at `(u, r + t)` as soon as the moving tip `η₂(r + t)` is interior and both tips are active there. -/
theorem ae_isOrdinaryRetainedPair_later_snd (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ u r t : ℝ≥0, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → (∀ s, r < s → s ≤ r + t → η₂ ω s ∉ η₁ ω '' Icc 0 u) →
      η₂ ω (r + t) ∈ QuantumZipper.H → η₁ ω u ∈ closure (activeDomain (η₁ ω) u (η₂ ω) (r + t)) →
      η₂ ω (r + t) ∈ closure (activeDomain (η₁ ω) u (η₂ ω) (r + t)) →
      IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) (r + t) := by
  filter_upwards [ae_extendsWithoutNewContact hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hW4 u r t hord hlt hnc hH h1 h2
  exact isOrdinaryRetainedPair_later_snd hord hW4 hlt hnc hH h1 h2

/-- **Ordinary later lines of the first continuation**, almost surely and simultaneously for all cutoffs (the mirror
of `ae_isOrdinaryRetainedPair_later_snd`). -/
theorem ae_isOrdinaryRetainedPair_later_fst (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ u r t : ℝ≥0, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ((u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → (∀ s, u < s → s ≤ u + t → η₁ ω s ∉ η₂ ω '' Icc 0 r) →
      η₁ ω (u + t) ∈ QuantumZipper.H → η₁ ω (u + t) ∈ closure (activeDomain (η₁ ω) (u + t) (η₂ ω) r) →
      η₂ ω r ∈ closure (activeDomain (η₁ ω) (u + t) (η₂ ω) r) →
      IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) (u + t) (η₂ ω) (ζ₂ ω) r := by
  filter_upwards [ae_extendsWithoutNewContact hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hW4 u r t hord hlt hnc hH h1 h2
  exact isOrdinaryRetainedPair_later_fst hord hW4 hlt hnc hH h1 h2

/-! ### The moving tip at a fixed time -/

/-- **Fixed-time nonzero force gaps** (named, not proved here): for every integrated `SLE_κ(ρ)` evolution and every
fixed time `t > 0`, almost surely on `{t < ζ}` the driver differs from every force point at time `t`. (Each gap is,
up to an absolutely continuous change of measure, a Bessel-type process of positive dimension, whose law at a fixed
positive time has no atom at `0`; the project has the pathwise Lebesgue-null collision sets of the frozen
`IsIntegratedSLEPath`, which give this only for almost every `t`.) -/
def FixedTimeGapStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ t : ℝ≥0, 0 < t → ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω → (∀ i, W t ω ≠ VL i t ω) ∧ ∀ j, W t ω ≠ VR j t ω

/-- **The tip of a flow line at a fixed positive time is interior** (`κ ≤ 4`), from fixed-time nonzero force gaps and
Aux. lemma 24 (`IsIntegratedSLEEvolution.ae_mem_H_of_forall_ne`). This is the "moving tip interior" condition of
`ae_isOrdinaryRetainedPair_later_snd`/`_fst` at a deterministic line. -/
theorem ae_mem_H_at_of_fixedTimeGap {x θ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hgap : FixedTimeGapStatement.{u} κ) (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hfl : IsFlowLine κ b jumps x θ P h η ζ)
    (t : ℝ≥0) (ht : 0 < t) : ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω → η ω t ∈ QuantumZipper.H := by
  obtain ⟨_, 𝓕, W, VL, VR, B, -, hcpl, htrace⟩ := hfl
  have hE := hcpl.1
  filter_upwards [hE.ae_mem_H_of_forall_ne hκ hκ4,
    hgap _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b jumps x) P 𝓕 W VL VR B ζ hE t ht, htrace]
    with ω hH hg htr htζ
  obtain ⟨hgL, hgR⟩ := hg htζ
  have hm := hH (ζ ω) le_rfl _ htr t ht htζ.le htζ hgL hgR
  change 0 < (η ω t - (x : ℂ)).im at hm
  change 0 < (η ω t).im
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hm

end InteractingSLE.RLC.OrdLate
