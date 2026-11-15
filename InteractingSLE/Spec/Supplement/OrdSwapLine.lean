/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdSwapChart
import InteractingSLE.Spec.Supplement.OrdGapFst

/-!
# Theorem 1.5's leaf 3: the first continuation's line facts at every later line before its stop

Packet PROVE-T15-ORDDET6. The first continuation (the path `η₁` continued from `u` to `u + t`) is read in the stop
chart of the retained data `d` recentred at the first tip's chart point `τ₀ = tipPos d η₁` (PROVE-T15-ORDDET3). By
PROVE-T15-ORDDET5's cover `OrdGap.ae_ord_or_encl_fst`, a later line `(u + t, r)` before the stop is almost surely
ordinary, or the second prefix is enclosed — and then the later chart of `d'` (data at `(u + t, r)`, chart at the
second tip) does not exist. Here every later line is read in the chart of the **exchanged** later data `d''` (paths
exchanged, cutoffs `(r, u + t)`, chart at the moving tip `η₁(u + t)`):

* **`ae_retLine_facts_fst_encl`** (enclosed lines): PROVE-T15-ORDDET2's `OrdDet.ae_retLine_facts_of_retainedWord_dense`
  for the exchanged flow lines `(η₂, η₁)`, stop data `e` (exchanged stop data at `(r, u)`, `OrdSwap.IsSwap d e`) and
  later data `d''`, with the stop word `shiftW τ₀ β₀` (`isRetMeanIdentOn_swap`) and the exchanged enclosed word
  (`OrdGap.exists_enclWord` for the exchanged flow lines), read back in the recentred stop chart
  (`IsSwap.chart_inv`, `IsSwap.chart_lift`);
* **`ae_retLine_facts_fst_ordSwap`** (ordinary lines): PROVE-T15-ORDDET3's `OrdDet.ae_retLine_facts_fst_of_ordinary`
  with the later chart `(d'.chart).recenter (tipPos d' η₁)` replaced by `d''.chart` (`IsSwap d' d''`);
* `fstOrdSet`, `fstOrdEnclSet`, **`fstLateWord`** (the later word: `shiftW (tipPos d' η₁) β₁` at ordinary lines, the
  enclosed word `β₂` otherwise), **`isRetMeanIdentOn_fstLateWord`** (its mean identification in the chart of `d''`, for
  the exchanged flow lines, on the ordinary-or-enclosed event), `ae_isSorted_fstLateWord`;
* **`ae_retLine_facts_fst_late`** (the composition with the cover): almost surely, at an ordinary pair `(u, r)` with
  a stop word `β₀`, for a line `t` before the first continuation's first new contact with the second prefix, along
  every chart path through `τ₀` reaching the later tip at a positive capacity time, the later pair is ordinary or
  enclosed and the `hline` facts (III-a), lift chain rule and (III-b) of `RetAux79.hasSafeLaw_of_retLines` hold with
  the stop chart `(d.chart).recenter τ₀`, the later chart `d''.chart` and the word `fstLateWord`.

Uses Lemma 7.5 only (no Theorem 1.2/1.3, R48); for Theorem 1.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RLC.OrdSwap

open Supp7 Restart OrdGap
open Exist.StagedLaw.BoundaryWord (shiftW isSorted_shiftW)
open MartChar.RealFlow (rightImg)

/-! ### The later word of the first continuation -/

section Word

variable {Ω : Type*}

/-- The ordinary later pairs `(u + t, r)` of the first continuation (data `d'`). -/
def fstOrdSet (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (d' : RetData Ω) : Set Ω :=
  {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r}

/-- The ordinary later pairs of the first continuation, and the enclosed ones of the exchanged data `d''`. -/
def fstOrdEnclSet (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (d' d'' : RetData Ω) : Set Ω :=
  fstOrdSet η₁ η₂ ζ₁ ζ₂ d' ∪ enclSet η₂ η₁ ζ₂ ζ₁ d''

open scoped Classical in
/-- **The first continuation's later word in the exchanged chart**: the ordinary later word recentred at the moving
tip's chart point at an ordinary later pair, the exchanged enclosed word otherwise. -/
def fstLateWord (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (d' : RetData Ω) (β₁ β₂ : Ω → BoundaryWord) (ω : Ω) :
    BoundaryWord :=
  if ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' then shiftW (tipPos d' η₁ ω) (β₁ ω) else β₂ ω

theorem fstLateWord_of_mem {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d' : RetData Ω} {β₁ β₂ : Ω → BoundaryWord}
    {ω : Ω} (hω : ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d') :
    fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω = shiftW (tipPos d' η₁ ω) (β₁ ω) := by
  classical
  simp only [fstLateWord, hω, ↓reduceIte]

theorem fstLateWord_of_notMem {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d' : RetData Ω}
    {β₁ β₂ : Ω → BoundaryWord} {ω : Ω} (hω : ω ∉ fstOrdSet η₁ η₂ ζ₁ ζ₂ d') :
    fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω = β₂ ω := by
  classical
  simp only [fstLateWord, hω, ↓reduceIte]

end Word

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

omit [IsProbabilityMeasure P] in
/-- Almost surely at an ordinary pair both chart events hold and the first tip's chart point is read off the data
paths (the premise `hO` of `isRetMeanIdentOn_swap` on the ordinary pairs). -/
theorem ae_mem_E_swap_of_ordinary {d e : RetData Ω} (hd : d.IsMeasGood) (he : e.IsMeasGood) (hs : IsSwap d e)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hage : ∀ᵐ ω ∂P, (e.u : ℝ≥0∞) < ζ₂ ω → (e.r : ℝ≥0∞) < ζ₁ ω → ω ∈ e.G ∧
      (∀ s ≤ e.u, e.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ e.r, e.η₂ ω t = η₁ ω t) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ω ∈ d.E ∧ ω ∈ e.E ∧ tipPos d η₁ ω = tipPos d d.η₁ ω := by
  filter_upwards [hag, hage] with ω hagω hageω hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  obtain ⟨hGe, -, -⟩ := hageω (by rw [hs.u_eq]; exact hord.2.1) (by rw [hs.r_eq]; exact hord.1)
  refine ⟨hd.mem_E_of_ordinary hG a₁ a₂ hord, hs.mem_E_of_ordinary he hGe a₁ a₂ hord, ?_⟩
  simp only [tipPos, a₁ d.u le_rfl]

/-- **The first continuation's line facts at an enclosed later line** (the second prefix enclosed by the later first
prefix, `enclSet` of the exchanged later data `d''`): the facts (III-a), lift chain rule and (III-b) with the stop chart
`(d.chart).recenter τ₀` (`τ₀ = tipPos d η₁`), the later chart `d''.chart` and the exchanged enclosed word `β₂`. -/
theorem ae_retLine_facts_fst_encl (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d e d'' : RetData Ω} (hd : d.IsMeasGood) (he : e.IsMeasGood) (hd'' : d''.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hage : ∀ᵐ ω ∂P, (e.u : ℝ≥0∞) < ζ₂ ω → (e.r : ℝ≥0∞) < ζ₁ ω → ω ∈ e.G ∧
      (∀ s ≤ e.u, e.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ e.r, e.η₂ ω t = η₁ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t)
    (hs : IsSwap d e) {t : ℝ≥0} (s₁ : d''.η₁ = d.η₂) (s₂ : d''.η₂ = d.η₁) (su : d''.u = d.r)
    (sr : d''.r = d.u + t) {O₀ : Set Ω} {β₀ β₂ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₂ : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ hd'' (enclSet η₂ η₁ ζ₂ ζ₁ d'') β₂)
    (hw₂ : ∀ᵐ ω ∂P, ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' →
      (β₂ ω).IsSorted ∧ IsRetainedWord κ θ₂ θ₁ (η₂ ω) d''.u (η₁ ω) d''.r (d''.inv ω) (β₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted →
      ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s + tipPos d η₁ ω)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t) →
        d.inv ω (γ Q + tipPos d η₁ ω) = d.η₁ ω (d.u + t) →
        (∀ w ∈ H, (d''.chart ω).2.1 w =
          ((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d''.chart ω).2.2 ((d''.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter (tipPos d η₁ ω)).2.2
              (((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 j) Q - W Q)
              y =
            (β₂ ω).fn y + θ₁ * QuantumZipper.chiC κ := by
  -- the stop word in the exchanged chart
  have hm₀' : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ he
      (O₀ ∩ {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r})
      (fun ω => shiftW (tipPos d η₁ ω) (β₀ ω)) := by
    refine isRetMeanIdentOn_swap hd he hs (isRetMeanIdentOn_mono hm₀ inter_subset_left) _ ?_
    filter_upwards [ae_mem_E_swap_of_ordinary hd he hs hag hage] with ω hω hωO using hω hωO.2
  have hl := OrdDet.ae_retLine_facts_of_retainedWord_dense (θ₁ := θ₂) (θ₂ := θ₁) hL75 hκ hκ4 hb hh hη₂ hη₁ hu₀
    he hd'' hage hag'' (s₁.trans hs.η₁_eq.symm) (s₂.trans hs.η₂_eq.symm) (su.trans hs.u_eq.symm)
    (by rw [sr, hs.r_eq]) hm₀' hm₂
  filter_upwards [hl, ae_mem_E_swap_of_ordinary hd he hs hag hage, hag'', hw₂] with ω hlω hEω hag''ω hw₂ω
  intro hO₀ hord hs₀ hencl W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hE, hE', htp⟩ := hEω hord
  obtain ⟨-, b₁, b₂⟩ := hag''ω hencl.1 hencl.2.1
  -- the exchanged stop chart is the recentred one
  have hinv : ∀ w ∈ Hbar, e.inv ω w = d.inv ω (w + tipPos d η₁ ω) := by
    rw [htp]; exact hs.inv_eq hd he hE hE'
  have hci : ∀ w ∈ Hbar, (e.chart ω).2.1 w = ((d.chart ω).recenter (tipPos d η₁ ω)).2.1 w := by
    rw [htp]; exact fun w hw => hs.chart_inv hd he hE hE' hw
  have hcl := hs.chart_lift hE hE' (tipPos d η₁ ω)
  have hγH : ∀ s ∈ Icc 0 Q, γ s ∈ Hbar := fun s hs' =>
    RetAux79.mem_Hbar_of_isGeneratingTrace hg hWc hW0 ((ENNReal.coe_le_coe.2 hs'.2).trans_lt hQ)
  have himg' : (fun s => e.inv ω (γ s)) '' Icc 0 Q = e.η₂ ω '' Icc e.r (e.r + t) := by
    rw [hs.η₂_eq, hs.r_eq, ← himg]
    exact image_congr fun s hs' => hinv _ (hγH s hs')
  have htip' : e.inv ω (γ Q) = e.η₂ ω (e.r + t) := by
    rw [hs.η₂_eq, hs.r_eq, hinv _ (hγH Q ⟨zero_le, le_rfl⟩), htip]
  -- the exchanged enclosed word on the data paths
  obtain ⟨hs₂, hrw⟩ := hw₂ω hencl
  have hu'' : d''.u = e.u := su.trans hs.u_eq.symm
  have hr'' : d''.r = e.r + t := by rw [sr, hs.r_eq]
  have hrw' : IsRetainedWord κ θ₂ θ₁ (e.η₁ ω) e.u (e.η₂ ω) (e.r + t) (d''.inv ω) (β₂ ω) := by
    have h1 : EqOn (η₂ ω) (e.η₁ ω) (Icc 0 d''.u) := fun s hs' => by
      rw [← b₁ s hs'.2, s₁, hs.η₁_eq]
    have h2 : EqOn (η₁ ω) (e.η₂ ω) (Icc 0 d''.r) := fun s hs' => by
      rw [← b₂ s hs'.2, s₂, hs.η₂_eq]
    have := isRetainedWord_congr h1 h2 hrw
    rwa [hu'', hr''] at this
  have hw'c : Continuous fun r : ℝ => W r.toNNReal := hWc.comp continuous_real_toNNReal
  have hw'0 : (fun r : ℝ => W r.toNNReal) 0 = 0 := by simp [hW0]
  have hF : ∀ w ∈ H, fwdMapInv (fun s : ℝ => W s.toNNReal) Q w ∈ Hbar := fun w hw =>
    QuantumZipper.H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw'c hw'0 Q.coe_nonneg hw).1
  obtain ⟨hA, hL, hB⟩ := hlω ⟨hO₀, hord⟩ hencl hencl.1 hencl.2.1 hE' hencl.2.2.1 (isSorted_shiftW hs₀ _) hs₂ hrw'
    W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg' htip'
  refine ⟨fun w hw => ?_, fun w hw => ?_, hB⟩
  · rw [hA w hw, hci _ (hF w hw)]
  · rw [hL w hw, hcl, hci _ (hF w hw)]

/-- **The first continuation's line facts at an ordinary later line, in the exchanged later chart**:
PROVE-T15-ORDDET3's `OrdDet.ae_retLine_facts_fst_of_ordinary` with the later chart `(d'.chart).recenter (tipPos d' η₁)`
replaced by the chart of the exchanged later data `d''` (`IsSwap d' d''`; they agree on `ℍ̄`, `IsSwap.chart_inv`). -/
theorem ae_retLine_facts_fst_ordSwap (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' d'' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood) (hd'' : d''.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) {t : ℝ≥0} (hu : d'.u = d.u + t) (hr : d'.r = d.r)
    (hs' : IsSwap d' d'') {O₀ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (fstOrdSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' → ω ∈ d.E → (β₀ ω).IsSorted →
      ∀ (τ₀ : ℝ) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ →
        Continuous W → W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t) →
        d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t) →
        (∀ w ∈ H, (d''.chart ω).2.1 w =
          ((d.chart ω).recenter τ₀).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d''.chart ω).2.2 ((d''.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter τ₀).2.2
              (((d.chart ω).recenter τ₀).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (shiftW τ₀ (β₀ ω)).fn (shiftW τ₀ (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (shiftW τ₀ (β₀ ω)).fn (shiftW τ₀ (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (shiftW τ₀ (β₀ ω)).fn (shiftW τ₀ (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (shiftW τ₀ (β₀ ω)).fn (shiftW τ₀ (β₀ ω)).jumps 0 j) Q - W Q) y =
            (shiftW (tipPos d' η₁ ω) (β₁ ω)).fn y + θ₁ * QuantumZipper.chiC κ := by
  have hl := OrdDet.ae_retLine_facts_fst_of_ordinary hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hd hd' hag hag' h₁ h₂
    hu hr hm₀ hm₁ hw₁
  filter_upwards [hl, ae_mem_E_swap_of_ordinary hd' hd'' hs' hag' hag''] with ω hlω hEω
  intro hO₀ hord hE hs₀ τ₀ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hE', hE'', htp⟩ := hEω hord
  have hci : ∀ w ∈ Hbar, (d''.chart ω).2.1 w = ((d'.chart ω).recenter (tipPos d' η₁ ω)).2.1 w := by
    rw [htp]; exact fun w hw => hs'.chart_inv hd' hd'' hE' hE'' hw
  have hcl := hs'.chart_lift hE' hE'' (tipPos d' η₁ ω)
  obtain ⟨hA, hL, hB⟩ := hlω hO₀ hord hE hs₀ τ₀ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  refine ⟨fun w hw => ?_, fun w hw => ?_, hB⟩
  · rw [hci w (QuantumZipper.H_subset_Hbar hw), hA w hw]
  · rw [hcl, hci w (QuantumZipper.H_subset_Hbar hw), hL w hw]

omit [IsProbabilityMeasure P] in
/-- **The mean identification of the first continuation's later word in the exchanged chart**, on the ordinary or
enclosed later pairs: the ordinary later word recentred (`isRetMeanIdentOn_swap`) and the exchanged enclosed word
(`OrdGap.isRetMeanIdentOn_union`). -/
theorem isRetMeanIdentOn_fstLateWord {d' d'' : RetData Ω} (hd' : d'.IsMeasGood) (hd'' : d''.IsMeasGood)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t)
    (hs' : IsSwap d' d'') {u₀ : ℂ → ℝ} {β₁ β₂ : Ω → BoundaryWord}
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (fstOrdSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hm₂ : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ hd'' (enclSet η₂ η₁ ζ₂ ζ₁ d'') β₂) :
    IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ hd'' (fstOrdEnclSet η₁ η₂ ζ₁ ζ₂ d' d'')
      (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂) := by
  have h1 := isRetMeanIdentOn_swap hd' hd'' hs' hm₁ (fun ω => tipPos d' η₁ ω) (by
    filter_upwards [ae_mem_E_swap_of_ordinary hd' hd'' hs' hag' hag''] with ω hω hωO using hω hωO)
  exact isRetMeanIdentOn_union h1 hm₂

omit [IsProbabilityMeasure P] in
/-- The first continuation's later word is sorted on the ordinary or enclosed later pairs. -/
theorem ae_isSorted_fstLateWord {d' d'' : RetData Ω} {β₁ β₂ : Ω → BoundaryWord}
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' → (β₁ ω).IsSorted)
    (hw₂ : ∀ᵐ ω ∂P, ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' → (β₂ ω).IsSorted) :
    ∀ᵐ ω ∂P, ω ∈ fstOrdEnclSet η₁ η₂ ζ₁ ζ₂ d' d'' → (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω).IsSorted := by
  filter_upwards [hw₁, hw₂] with ω h1 h2 hω
  by_cases ho : ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d'
  · rw [fstLateWord_of_mem ho]; exact isSorted_shiftW (h1 ho) _
  · rw [fstLateWord_of_notMem ho]
    exact h2 ((show ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' ∨ ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' from hω).resolve_left ho)

/-- **The two later words from Lemma 7.5**: at the ordinary later pairs `(u + t, r)` the ordinary word
(`retOrdMeanWordFstStatement_of_lemma75` for the data `d'`), at the enclosed ones the exchanged enclosed word
(`OrdGap.exists_enclWord` for the exchanged flow lines and data `d''`), with the hypotheses `hm₁ hw₁ hm₂ hw₂` of
`ae_retLine_facts_fst_late`. -/
theorem exists_fstLateWords (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d' d'' : RetData Ω} (hd' : d'.IsMeasGood) (hd'' : d''.IsMeasGood)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t) :
    ∃ β₁ β₂ : Ω → BoundaryWord,
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (fstOrdSet η₁ η₂ ζ₁ ζ₂ d') β₁ ∧
      (∀ᵐ ω ∂P, ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' →
        (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) ∧
      IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ hd'' (enclSet η₂ η₁ ζ₂ ζ₁ d'') β₂ ∧
      ∀ᵐ ω ∂P, ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' →
        (β₂ ω).IsSorted ∧ IsRetainedWord κ θ₂ θ₁ (η₂ ω) d''.u (η₁ ω) d''.r (d''.inv ω) (β₂ ω) := by
  obtain ⟨βo, -, hmo, hwo⟩ := retOrdMeanWordFstStatement_of_lemma75 hL75 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P
    h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d' hd' hag' u₀ hu₀
  obtain ⟨βe, hme, hwe⟩ := exists_enclWord (θ₁ := θ₂) (θ₂ := θ₁) hL75 hκ hκ4 hb hh hη₂ hη₁ hu₀ hd'' hag''
  refine ⟨fun ω => (βo ω).1, βe, hmo, ?_, hme, hwe⟩
  filter_upwards [hwo] with ω hω hO
  obtain ⟨hs, -, -, hrw, -⟩ := hω hO
  exact ⟨hs, hrw⟩

/-- **The first continuation's line facts at every deterministic line before its first new contact** (the
composition of PROVE-T15-ORDDET5's cover `OrdGap.ae_ord_or_encl_fst` with `ae_retLine_facts_fst_ordSwap` and
`ae_retLine_facts_fst_encl`): almost surely, at an ordinary pair `(u, r)` with a stop-line word `β₀` (mean
identification on `O₀ ∋ ω`, sorted), for a line `t` with `u + t < ζ₁` and no new contact of `η₁(u, u + t]` with
`η₂[0, r]`, along every chart path of the continuation through `τ₀ = tipPos d η₁` reaching the later tip at a positive
capacity time, the later pair is ordinary or enclosed (`fstOrdEnclSet`) and the facts (III-a), lift chain rule and
(III-b) hold with the stop chart `(d.chart).recenter τ₀`, the exchanged later chart `d''.chart` and the later word
`fstLateWord` (its mean identification: `isRetMeanIdentOn_fstLateWord`). -/
theorem ae_retLine_facts_fst_late (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d e d' d'' : RetData Ω} (hd : d.IsMeasGood) (he : e.IsMeasGood) (hd' : d'.IsMeasGood)
    (hd'' : d''.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hage : ∀ᵐ ω ∂P, (e.u : ℝ≥0∞) < ζ₂ ω → (e.r : ℝ≥0∞) < ζ₁ ω → ω ∈ e.G ∧
      (∀ s ≤ e.u, e.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ e.r, e.η₂ ω t = η₁ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t)
    (hs : IsSwap d e) (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) {t : ℝ≥0} (hu : d'.u = d.u + t) (hr : d'.r = d.r)
    (hs' : IsSwap d' d'') {O₀ : Set Ω} {β₀ β₁ β₂ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (fstOrdSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω))
    (hm₂ : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ hd'' (enclSet η₂ η₁ ζ₂ ζ₁ d'') β₂)
    (hw₂ : ∀ᵐ ω ∂P, ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' →
      (β₂ ω).IsSorted ∧ IsRetainedWord κ θ₂ θ₁ (η₂ ω) d''.u (η₁ ω) d''.r (d''.inv ω) (β₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted →
      ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → (∀ s, d.u < s → s ≤ d.u + t → η₁ ω s ∉ η₂ ω '' Icc 0 d.r) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s + tipPos d η₁ ω)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t) →
        d.inv ω (γ Q + tipPos d η₁ ω) = d.η₁ ω (d.u + t) →
        ω ∈ fstOrdEnclSet η₁ η₂ ζ₁ ζ₂ d' d'' ∧
        (∀ w ∈ H, (d''.chart ω).2.1 w =
          ((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d''.chart ω).2.2 ((d''.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter (tipPos d η₁ ω)).2.2
              (((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 j) Q - W Q)
              y =
            (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω).fn y + θ₁ * QuantumZipper.chiC κ := by
  have s₁ : d''.η₁ = d.η₂ := hs'.η₁_eq.trans h₂
  have s₂ : d''.η₂ = d.η₁ := hs'.η₂_eq.trans h₁
  have su : d''.u = d.r := hs'.u_eq.trans hr
  have sr : d''.r = d.u + t := hs'.r_eq.trans hu
  filter_upwards [ae_retLine_facts_fst_ordSwap hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hd hd' hd'' hag hag' hag''
      h₁ h₂ hu hr hs' hm₀ hm₁ hw₁,
    ae_retLine_facts_fst_encl (θ₂ := θ₂) hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd he hd'' hag hage hag'' hs s₁ s₂ su sr
      hm₀ hm₂ hw₂,
    ae_ord_or_encl_fst hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hd'' hag hag'' s₁ s₂ su sr, hag] with ω hoω heω hcω hagω
  intro hO₀ hord hs₀ hlt hnc W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  have hcov := hcω hord hlt hnc (tipPos d η₁ ω) W γ ζc Q hg hWc hW0 hQ himg htip
  by_cases ho : ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d'
  · obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
    have hE := hd.mem_E_of_ordinary hG a₁ a₂ hord
    rw [fstLateWord_of_mem ho]
    exact ⟨Or.inl ho, hoω hO₀ ho hE hs₀ (tipPos d η₁ ω) W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip⟩
  · have hencl : ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' := by
      refine hcov.resolve_left fun h' => ho ?_
      show IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r
      rw [hu, hr]
      exact h'
    rw [fstLateWord_of_notMem ho]
    exact ⟨Or.inr hencl, heω hO₀ hord hs₀ hencl W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip⟩

/-- **The first continuation's line facts along its canonical clock, at every line before its stop** (the `hline`
facts of `RetAux79.hasSafeLaw_of_retLines` at a line `t > 0`; PROVE-T15-ORDDET3's `OrdDet.ae_retLine_facts_fst_canon`
without its premise that the later pair be ordinary). Almost surely, at an ordinary pair `(u, r)` with a sorted stop
word `β₀` (mean identification on `O₀ ∋ ω`) and `t` before the continuation's stop (first new contact with
`η₁[0, u] ∪ η₂[0, r]`, or its lifetime): the canonical chart path of the first continuation (chart shifted by
`tipPos d η₁`) reaches the line at a capacity time `0 < Q <` its lifetime, and for EVERY continuous driver `W` from `0`
generating it, the later pair is ordinary or enclosed and the facts (III-a), lift chain rule and (III-b) hold at `Q`
with the stop chart `(d.chart).recenter (tipPos d η₁)`, the exchanged later chart `d''.chart` and `fstLateWord`. -/
theorem ae_retLine_facts_fst_late_canon (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d e d' d'' : RetData Ω} (hd : d.IsMeasGood) (he : e.IsMeasGood) (hd' : d'.IsMeasGood)
    (hd'' : d''.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hage : ∀ᵐ ω ∂P, (e.u : ℝ≥0∞) < ζ₂ ω → (e.r : ℝ≥0∞) < ζ₁ ω → ω ∈ e.G ∧
      (∀ s ≤ e.u, e.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ e.r, e.η₂ ω t = η₁ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t)
    (hs : IsSwap d e) (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) {t : ℝ≥0} (ht0 : 0 < t) (hu : d'.u = d.u + t)
    (hr : d'.r = d.r) (hs' : IsSwap d' d'') {O₀ : Set Ω} {β₀ β₁ β₂ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (fstOrdSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω))
    (hm₂ : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ hd'' (enclSet η₂ η₁ ζ₂ ζ₁ d'') β₂)
    (hw₂ : ∀ᵐ ω ∂P, ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' →
      (β₂ ω).IsSorted ∧ IsRetainedWord κ θ₂ θ₁ (η₂ ω) d''.u (η₁ ω) d''.r (d''.inv ω) (β₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted →
      (t : ℝ≥0∞) < contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) →
      0 < (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal ∧
      (((chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal : ℝ≥0) : ℝ≥0∞) <
        canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
      ∀ W : ℝ≥0 → ℝ, Continuous W → W 0 = 0 →
        IsGeneratingTrace W (canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
          (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
            (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0) →
        let Q := (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal
        ω ∈ fstOrdEnclSet η₁ η₂ ζ₁ ζ₂ d' d'' ∧
        (∀ w ∈ H, (d''.chart ω).2.1 w =
          ((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d''.chart ω).2.2 ((d''.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter (tipPos d η₁ ω)).2.2
              (((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (shiftW (tipPos d η₁ ω) (β₀ ω)).fn (shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 j) Q - W Q)
              y =
            (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω).fn y + θ₁ * QuantumZipper.chiC κ := by
  have hl := ae_retLine_facts_fst_late hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hd he hd' hd'' hag hage hag' hag'' hs
    h₁ h₂ hu hr hs' hm₀ hm₁ hw₁ hm₂ hw₂
  have hpg := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  filter_upwards [hl, hag, hag', hpg] with ω hlω hagω hag'ω hpgω
  intro hO₀ hord hs₀ htV
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hord
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun s hs => a₂ s hs.2
  -- the line is before the lifetime and before any new contact with the second prefix
  have hstop : (((d.u + t : ℝ≥0)) : ℝ≥0∞) < contStop (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) :=
    Supp7.coe_add_lt_iff.1 htV
  have hlt : ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω := hstop.trans_le contStop_le
  have hnc : ∀ s, d.u < s → s ≤ d.u + t → η₁ ω s ∉ η₂ ω '' Icc 0 d.r := fun s hs1 hs2 hmem =>
    notMem_of_lt_contStop hs1 ((ENNReal.coe_le_coe.2 hs2).trans_lt hstop) (Or.inr hmem)
  obtain ⟨-, a₁', -⟩ := hag'ω (by rw [hu]; exact hlt) (by rw [hr]; exact hord.2.1)
  have e₁' : ∀ s ≤ d.u + t, d.η₁ ω s = η₁ ω s := fun s hs => by
    rw [← h₁]; exact a₁' s (hu ▸ hs)
  -- the pathwise premises of the canonical clock at the stop line (as in `OrdDet.ae_retLine_facts_fst_canon`)
  have hinj₁ : InjOn (η₁ ω) (Icc 0 d.u) := Sec7.IsPathGood.injOn_Icc hpgω hord.1.le
  have hpH : d.η₁ ω d.u ∈ H := by rw [a₁ d.u le_rfl]; exact hord.2.2.1
  have hpO : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r := by
    rw [a₁ d.u le_rfl, e₂.image_eq]; exact hord.2.2.2.2.2.1
  have hcl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r) := by
    rw [a₁ d.u le_rfl, activeDomain_congr_Icc (fun s hs => a₁ s hs.2) e₂]; exact hord.2.2.2.2.2.2.1
  have hne₁ : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u := fun s hs he' => by
    rw [a₁ s hs.le, a₁ d.u le_rfl] at he'
    exact hs.ne (hinj₁ ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he')
  obtain ⟨-, -, -, -, hinj, hfacts⟩ :=
    OrdDet.exists_ordContFst_facts hd hE hpgω (fun s hs => a₁ s hs) hord.1 hpH hpO hcl hne₁
  have hK : η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
    rw [e₂.image_eq]
  have htp : tipPos d d.η₁ ω = tipPos d η₁ ω := by simp only [tipPos, a₁ d.u le_rfl]
  rw [hK, htp] at hinj hfacts
  obtain ⟨hQpos, hQlt, himg, htip⟩ := hfacts t ht0 htV
  refine ⟨hQpos, hQlt, fun W hWc hW0 hgen => ?_⟩
  have himg' : (fun s => d.inv ω (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
      (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s + tipPos d η₁ ω)) ''
        Icc 0 (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal =
      d.η₁ ω '' Icc d.u (d.u + t) := by
    rw [himg]
    exact (image_congr fun s hs => e₁' s hs.2).symm
  have htip' : d.inv ω (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
      (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 (chartClock (contPath (d.D ω)
        (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal +
        tipPos d η₁ ω) = d.η₁ ω (d.u + t) := by
    rw [htip, e₁' (d.u + t) le_rfl]
  exact hlω hO₀ hord hs₀ hlt hnc W _ _ _ hgen hWc hW0 hinj hQlt hQpos himg' htip'

end Line

end InteractingSLE.RLC.OrdSwap
