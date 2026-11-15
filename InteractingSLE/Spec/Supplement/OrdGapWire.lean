/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdGapWord
import InteractingSLE.Spec.Supplement.OrdGapFixed
import InteractingSLE.Spec.Supplement.OrdFstWire

/-!
# Theorem 1.5's leaf 3: the second continuation's line facts at every later line before its stop

Packet PROVE-T15-ORDDET5. PROVE-T15-ORDDET2/3 proved the later-line facts of the second continuation (the `hline` input
of `RetAux79.hasSafeLaw_of_retLines`) at lines whose later pair is ordinary (`OrdDet.ae_retLine_facts_snd_of_ordinary`).
This file removes that restriction:

* **`ae_ord_or_encl_snd`** (the cover): at a deterministic line, almost surely, an ordinary pair `(u, r)` continued
  along the second path to `r + t` (before its lifetime, without a new contact with the first prefix, along a chart
  path) is at the later line either an ordinary pair again or an **enclosed** pair (`enclSet`: the first prefix lies
  in the filling of the later second prefix). The moving tip is interior by fixed-time nonzero force gaps
  (`OrdLate.ae_mem_H_at`, PROVE-ABSMERGE); if the first tip is active the later pair is ordinary
  (`OrdLate.ae_isOrdinaryRetainedPair_later_snd`, W4), otherwise it is enclosed (`subset_fillH_of_inactive_snd`).
* `isRetMeanIdentOn_union`, **`exists_ordEnclWord`**: one word with the mean identification and the outer word on the
  union of the ordinary and the enclosed events (the sided ordinary word of PROVE-T15-ORDDET3 and `exists_enclWord`);
* **`ae_retLine_facts_snd_ordEncl`**: the later-line facts (III-a) and (III-b) at every line whose later pair is
  ordinary or enclosed (`OrdDet.ae_retLine_facts_of_retainedWord_dense`, which needs neither ordinariness nor the
  absence of new contacts);
* **`ae_retLine_facts_snd_late`**: the composition — almost surely, at an ordinary pair, for a deterministic line
  before the second continuation's first new contact with the first prefix, along a chart path, the line facts hold
  with the word of `exists_ordEnclWord` at the later pair.

Uses Lemma 7.5 only (no Theorem 1.2/1.3); for Theorem 1.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RLC.OrdGap

open Supp7 Restart
open MartChar.RealFlow (rightImg)

/-! ### One word on the union of the ordinary and the enclosed events -/

section Union

variable {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u₀ : ℂ → ℝ} {d : RetData Ω} {hd : d.IsMeasGood}

open scoped Classical in
/-- **The mean identification on a union of events, with the word chosen piecewise.** -/
theorem isRetMeanIdentOn_union {O₁ O₂ : Set Ω} {β₁ β₂ : Ω → BoundaryWord}
    (h₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₁ β₁) (h₂ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₂ β₂) :
    IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd (O₁ ∪ O₂) (fun ω => if ω ∈ O₁ then β₁ ω else β₂ ω) := by
  intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  filter_upwards [h₁ ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, h₂ ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg]
    with ω e₁ e₂ hω φ
  by_cases hO : ω ∈ O₁
  · simp only [hO, ↓reduceIte]; exact e₁ hO φ
  · simp only [hO, ↓reduceIte]; exact e₂ (hω.resolve_left hO) φ

end Union

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- The event of ordinary or enclosed retained pairs of data `d`. -/
def ordEnclSet (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (d : RetData Ω) : Set Ω :=
  {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} ∪ enclSet η₁ η₂ ζ₁ ζ₂ d

/-- **One word on the ordinary and the enclosed pairs**: the sided ordinary word
(`retOrdMeanWordFstStatement_of_lemma75`) at ordinary pairs, the second path's own word (`exists_enclWord`) at
enclosed pairs. -/
theorem exists_ordEnclWord (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ β : Ω → BoundaryWord, IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd (ordEnclSet η₁ η₂ ζ₁ ζ₂ d) β ∧
      ∀ᵐ ω ∂P, ω ∈ ordEnclSet η₁ η₂ ζ₁ ζ₂ d → (β ω).IsSorted ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω) := by
  classical
  obtain ⟨βo, -, hmo, hwo⟩ := retOrdMeanWordFstStatement_of_lemma75 hL75 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P
    h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  obtain ⟨βe, hme, hwe⟩ := exists_enclWord (θ₁ := θ₁) hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd hag
  refine ⟨_, isRetMeanIdentOn_union hmo hme, ?_⟩
  filter_upwards [hwo, hwe] with ω h1 h2 hω
  by_cases hO : ω ∈ {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r}
  · have hO' : IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := hO
    simp only [hO', ↓reduceIte]
    obtain ⟨hs, -, -, hrw, -⟩ := h1 hO
    exact ⟨hs, hrw⟩
  · have hO' : ¬ IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := hO
    simp only [hO', ↓reduceIte]
    exact h2 (hω.resolve_left hO)

/-- **The second continuation's line facts at every ordinary or enclosed later line** (the `hline` facts (III-a),
(III-b) of `RetAux79.hasSafeLaw_of_retLines`): `OrdDet.ae_retLine_facts_snd_of_ordinary` with the later word given on
the ordinary and the enclosed pairs. -/
theorem ae_retLine_facts_snd_ordEncl (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) (hu : d'.u = d.u) {t : ℝ≥0} (hr : d'.r = d.r + t)
    {O₀ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (ordEnclSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ ordEnclSet η₁ η₂ ζ₁ ζ₂ d' →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → ω ∈ ordEnclSet η₁ η₂ ζ₁ ζ₂ d' → ω ∈ d.E → (β₀ ω).IsSorted →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t) →
        d.inv ω (γ Q) = d.η₂ ω (d.r + t) →
        (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ (flowLineRhoL κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (flowLineRhoR κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL (β₀ ω).fn (β₀ ω).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR (β₀ ω).fn (β₀ ω).jumps 0 j) Q - W Q) y =
            (β₁ ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  have hl := OrdDet.ae_retLine_facts_of_retainedWord_dense (θ₁ := θ₁) (θ₂ := θ₂) hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd
    hd' hag hag' h₁ h₂ hu hr hm₀ hm₁
  filter_upwards [hl, hag', hw₁] with ω hlω hag'ω hw₁ω
  intro hO₀ hO₁ hE hs₀ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  have hlt : (d'.u : ℝ≥0∞) < ζ₁ ω ∧ (d'.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d'.E := by
    rcases hO₁ with hord | henc
    · obtain ⟨hG', a₁', a₂'⟩ := hag'ω hord.1 hord.2.1
      exact ⟨hord.1, hord.2.1, hd'.mem_E_of_ordinary hG' a₁' a₂' hord⟩
    · exact ⟨henc.1, henc.2.1, henc.2.2.1⟩
  obtain ⟨-, a₁', a₂'⟩ := hag'ω hlt.1 hlt.2.1
  obtain ⟨hs₁, hrw⟩ := hw₁ω hO₁
  have hrw' : IsRetainedWord κ θ₁ θ₂ (d.η₁ ω) d.u (d.η₂ ω) (d.r + t) (d'.inv ω) (β₁ ω) := by
    have := isRetainedWord_congr (α' := d'.η₁ ω) (β' := d'.η₂ ω) (fun s hs => (a₁' s hs.2).symm)
      (fun s hs => (a₂' s hs.2).symm) hrw
    rwa [h₁, h₂, hu, hr] at this
  exact hlω hO₀ hO₁ hlt.1 hlt.2.1 hE hlt.2.2 hs₀ hs₁ hrw' W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip

/-- **The cover: every later line of the second continuation before its first new contact is ordinary or enclosed**
(almost surely, at a deterministic line `t`, along a chart path of the continuation as in
`OrdDet.later_tip_mem_closure_activeDomain`). -/
theorem ae_ord_or_encl_snd (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) (hu : d'.u = d.u) {t : ℝ≥0} (hr : d'.r = d.r + t) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → (∀ s, d.r < s → s ≤ d.r + t → η₂ ω s ∉ η₁ ω '' Icc 0 d.u) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → (Q : ℝ≥0∞) < ζc →
        (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t) →
        d.inv ω (γ Q) = d.η₂ ω (d.r + t) →
        ω ∈ ordEnclSet η₁ η₂ ζ₁ ζ₂ d' := by
  have hHae : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → η₂ ω (d.r + t) ∈ H := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ d.r + t) with h0 | hpos
    · refine Eventually.of_forall fun ω hord _ => ?_
      have hr0 : d.r = 0 := le_antisymm (by rw [h0]; exact le_add_right le_rfl) zero_le
      have hrt : d.r + t = d.r := by rw [← h0, hr0]
      rw [hrt]
      exact hord.2.2.2.1
    · filter_upwards [OrdLate.ae_mem_H_at hκ hκ4.le hη₂ (d.r + t) hpos] with ω hH _ hlt
      exact hH hlt
  filter_upwards [OrdLate.ae_isOrdinaryRetainedPair_later_snd_at hκ hκ4 hb hx hθ hh hη₁ hη₂ d.u d.r t,
    ae_isZoneInterval hκ hκ4 hx hη₁ hη₂ hd hag, hag, hag', hHae] with ω hlate hzone hagω hag'ω hHω
  intro hord hlt hnc W γ ζc Q hg hWc hW0 hQ himg htip
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  obtain ⟨hE, ⟨L, R, τ, hZ⟩, -⟩ := hzone hord
  have hu' : (d'.u : ℝ≥0∞) < ζ₁ ω := by rw [hu]; exact hord.1
  have hr' : (d'.r : ℝ≥0∞) < ζ₂ ω := by rw [hr]; exact hlt
  obtain ⟨hG', -, a₂'⟩ := hag'ω hu' hr'
  -- the data paths are the flow lines up to the later cutoffs
  have e₂ : ∀ s ≤ d.r + t, d.η₂ ω s = η₂ ω s := fun s hs => by
    have := a₂' s (by rw [hr]; exact hs)
    rwa [h₂] at this
  have i₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => a₁ s hs.2
  have i₂ : d.η₂ ω '' Icc 0 (d.r + t) = η₂ ω '' Icc 0 (d.r + t) := image_congr fun s hs => e₂ s hs.2
  have hDcongr : activeDomain (d.η₁ ω) d.u (d.η₂ ω) (d.r + t) = activeDomain (η₁ ω) d.u (η₂ ω) (d.r + t) :=
    activeDomain_congr_Icc (fun s hs => a₁ s hs.2) fun s hs => e₂ s hs.2
  -- no new contact of the continuation with the first prefix, including its start
  have hnc' : ∀ s ∈ Icc d.r (d.r + t), d.η₂ ω s ∉ d.η₁ ω '' Icc 0 d.u := by
    intro s hs
    rw [i₁, e₂ s hs.2]
    rcases eq_or_lt_of_le hs.1 with hrs | hrs
    · rw [← hrs]; exact hord.2.2.2.2.1
    · exact hnc s hrs hs.2
  by_cases hact : η₁ ω d.u ∈ closure (activeDomain (η₁ ω) d.u (η₂ ω) (d.r + t))
  · -- an active first tip: the later pair is ordinary
    have hact₂ := (OrdDet.later_tip_mem_closure_activeDomain hd hE hg hWc hW0 hQ himg htip).2
    rw [hDcongr, e₂ _ le_rfl] at hact₂
    left
    show IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r
    rw [hu, hr]
    exact hlate hord hlt hnc hact hact₂
  · -- an inactive first tip: the first prefix is enclosed
    have hin : d.η₁ ω d.u ∉ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) (d.r + t)) := by
      rw [hDcongr, a₁ d.u le_rfl]; exact hact
    have hencl := subset_fillH_of_inactive_snd hd hE hZ hg hWc hW0 hQ himg htip hnc' hin
    rw [i₁, i₂] at hencl
    have hH : d.η₂ ω (d.r + t) ∈ H := by rw [e₂ _ le_rfl]; exact hHω hord hlt
    have hE' : ω ∈ d'.E := OrdDet.mem_E_of_later hd hd' h₁ h₂ hu hr hE hG' hH
      (hnc' _ ⟨le_add_right le_rfl, le_rfl⟩) hg hWc hW0 hQ himg htip
    right
    refine ⟨hu', hr', hE', ?_⟩
    rw [hu, hr]
    exact hencl

/-- **The second continuation's line facts at every deterministic line before its first new contact** (the
composition of `ae_ord_or_encl_snd` and `ae_retLine_facts_snd_ordEncl`): almost surely, at an ordinary pair `(u, r)`
with a stop-line word `β₀` (mean identification on `O₀ ∋ ω`, sorted), for a line `t` with `r + t < ζ₂` and no new
contact of `η₂(r, r + t]` with `η₁[0, u]`, along every chart path of the continuation reaching the later tip at a
positive capacity time, the facts (III-a) and (III-b) hold with any later word `β₁` given on the ordinary and enclosed
later pairs (`exists_ordEnclWord`). -/
theorem ae_retLine_facts_snd_late (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) (hu : d'.u = d.u) {t : ℝ≥0} (hr : d'.r = d.r + t)
    {O₀ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (ordEnclSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ ordEnclSet η₁ η₂ ζ₁ ζ₂ d' →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted →
      ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → (∀ s, d.r < s → s ≤ d.r + t → η₂ ω s ∉ η₁ ω '' Icc 0 d.u) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t) →
        d.inv ω (γ Q) = d.η₂ ω (d.r + t) →
        (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ (flowLineRhoL κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (flowLineRhoR κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL (β₀ ω).fn (β₀ ω).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR (β₀ ω).fn (β₀ ω).jumps 0 j) Q - W Q) y =
            (β₁ ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  filter_upwards [ae_retLine_facts_snd_ordEncl (θ₁ := θ₁) hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd hd' hag hag' h₁ h₂ hu hr
      hm₀ hm₁ hw₁, ae_ord_or_encl_snd hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hd' hag hag' h₁ h₂ hu hr, hag]
    with ω hf hc hagω
  intro hO₀ hord hs₀ hlt hnc W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hord
  exact hf hO₀ (hc hord hlt hnc W γ ζc Q hg hWc hW0 hQ himg htip) hE hs₀ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip

end Main

end InteractingSLE.RLC.OrdGap
