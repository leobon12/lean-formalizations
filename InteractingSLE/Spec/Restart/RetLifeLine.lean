/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetLines
import InteractingSLE.Spec.Restart.RetLife

/-!
# The later-line facts of the retained continuation with the boundary stop (ruling R55)

Packet PROVE-RETAUX79C. PROVE-RETAUX79B proved the later-line facts of `hline` (chart composition (III-a) and the
boundary-data identity (III-b′)) for the canonical retained continuation at every later line `(u, r + t)` that is again
a disjoint pair (`exists_retLine_facts_canon`), but with the old lifetime the later pairs need not be disjoint pairs.
With the source's lifetime (first contact with `η₁[0, u] ∪ η₂[0, r] ∪ ℝ`) they are (`isDisjointPair_of_lt_contStop`),
so the facts hold at **every** later line before the lifetime.

* `retFam`: retained data with common paths and cutoffs `(u, r')` for every `r'` (the later lines share the paths);
* `lt_contStop_of_eventually`, **`lt_contStop_of_isDisjointPair`**: the boundary stop is after `r` at a disjoint pair;
* `isSetting_shorten`, `isSetting_of_retData`: LEMMA76G's setting for the shortened lifetime and for retained data;
* `IsRetLineFacts`: the three later-line facts of `hline` (chart inverse, lift, force data) at a capacity time;
* **`exists_retLine_facts_R`**: at a disjoint pair `(u, r)`, one continuous driver `W` (`W 0 = 0`) generating the
  canonical retained path with the boundary stop, such that at every continuation time `0 < t` before the boundary
  stop, `(u, r + t)` is a disjoint pair, `ω` is in the later chart event (if it is in the later good event), and the
  later-line facts hold at the capacity time `Q = C(t)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv logDerivFwd)

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Sec7 Sec7.Lemma76G MartChar.RealFlow

/-! ### The boundary stop at a disjoint pair -/

section Stop

/-- If, just after `a`, the path is before its lifetime and off `K`, the first contact with `K` is after `a`. -/
theorem lt_contStop_of_eventually {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K : Set ℂ}
    (h : ∀ᶠ t : ℝ≥0 in 𝓝[>] a, (t : ℝ≥0∞) ≤ ζ ∧ η t ∉ K) : (a : ℝ≥0∞) < contStop η ζ a K := by
  obtain ⟨u, hau, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 h
  obtain ⟨t₀, ht₀a, ht₀u⟩ := exists_between (show a < u from hau)
  exact (ENNReal.coe_lt_coe.2 ht₀a).trans_le (le_contStop ⟨ht₀a.le, (hu ⟨ht₀a, ht₀u⟩).1,
    fun t' h1 h2 => (hu ⟨h1, h2.trans ht₀u⟩).2⟩)

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a r : ℝ≥0}

/-- **At a disjoint pair the boundary stop of the second path is after `r`.** -/
theorem lt_contStop_of_isDisjointPair (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ r) :
    (r : ℝ≥0∞) < contStop β ζ₂ r (α '' Icc 0 a ∪ β '' Icc 0 r ∪ realLine) := by
  apply lt_contStop_of_eventually
  have hc := isPathGood_continuousAt hp₂ hpair.2.1
  have hα : IsClosed (α '' Icc 0 a) := (Sec7.IsPathGood.isCompact_image_Icc hp₁ hpair.1.le).isClosed
  have hβα : β r ∉ α '' Icc 0 a := fun h => Set.disjoint_left.1 hpair.2.2.2.1 h ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩
  have h1 : ∀ᶠ t in 𝓝 r, β t ∈ (α '' Icc 0 a)ᶜ := hc.eventually (hα.isOpen_compl.mem_nhds hβα)
  have h2 : ∀ᶠ t in 𝓝 r, β t ∈ H := hc.eventually (QuantumZipper.isOpen_H.mem_nhds hpair.2.2.1)
  have h3 : ∀ᶠ t : ℝ≥0 in 𝓝 r, (t : ℝ≥0∞) ∈ Iio ζ₂ :=
    (ENNReal.continuous_coe.tendsto r).eventually (Iio_mem_nhds hpair.2.1)
  filter_upwards [nhdsWithin_le_nhds (h1.and (h2.and h3)), self_mem_nhdsWithin] with t ht htr
  obtain ⟨ht1, ht2, ht3⟩ := ht
  refine ⟨le_of_lt ht3, ?_⟩
  rintro ((hA | ⟨s, hs, hst⟩) | hR)
  · exact ht1 hA
  · have hs' : (s : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hs.2).trans hpair.2.1.le
    have h := hp₂.1 hs' (show (t : ℝ≥0∞) ≤ ζ₂ from le_of_lt ht3) hst
    rw [h] at hs
    exact absurd hs.2 (not_le.2 htr)
  · exact (ne_of_gt (show (0 : ℝ) < (β t).im from ht2)) hR

/-- **LEMMA76G's setting with the lifetime shortened to the boundary stop.** -/
theorem isSetting_shorten {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ r φ ψ lift) :
    IsSetting α ζ₁ x₁ a β (contStop β ζ₂ r (α '' Icc 0 a ∪ β '' Icc 0 r ∪ realLine)) x₂ r φ ψ lift :=
  ⟨hs.hp₁, isPathGood_mono hs.hp₂ contStop_le, hs.hx,
    ⟨hs.hpair.1, lt_contStop_of_isDisjointPair hs.hp₁ hs.hp₂ hs.hpair, hs.hpair.2.2⟩, hs.hC⟩

/-- **LEMMA76G's setting for retained data** at a good disjoint pair whose prefixes agree with the paths. -/
theorem isSetting_of_retData {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω}
    (hG : ω ∈ d.G) (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    (ha₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (ha₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ d.u β ζ₂ d.r) :
    ω ∈ d.E ∧ IsSetting α ζ₁ x₁ d.u β ζ₂ x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) := by
  have hE := mem_E_of_isDisjointPair hd hG ha₁ ha₂ hpair
  exact ⟨hE, hp₁, hp₂, hx, hpair, (Lemma76F.isRetChart_congr ha₁ ha₂).1 (hd.isRetChart hE).2⟩

end Stop

/-! ### Retained data along the later lines -/

/-- **Retained data with common paths** `η₁'`, `η₂'`, first cutoff `u`, second cutoff `r` and good event `G r`. -/
def retFam {Ω : Type*} (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (u r : ℝ≥0) : RetData Ω :=
  ⟨G r, η₁', η₂', u, r⟩

/-- **The later-line facts** of `hline` at capacity time `Q` for the driver `W`, the stop-line data `d` and the
later-line data `d'`: (III-a) for the chart inverses and the lifts, and (III-b′) for the force data of the flow-line
word of `B₀` (angle `θ`) against the later word `Bt`. -/
def IsRetLineFacts {Ω : Type*} [MeasurableSpace Ω] (d d' : RetData Ω) (ω : Ω) (W : ℝ≥0 → ℝ) (Q : ℝ≥0)
    (κ θ : ℝ) (B₀ Bt : BoundaryWord) : Prop :=
  (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
  (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
    (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
      (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
  ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
    forceBoundaryData κ (flowLineRhoL κ B₀.fn B₀.jumps 0 θ) (flowLineRhoR κ B₀.fn B₀.jumps 0 θ)
        (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL B₀.fn B₀.jumps 0 i) Q - W Q)
        (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR B₀.fn B₀.jumps 0 j) Q - W Q) y =
      Bt.fn y + θ * QuantumZipper.chiC κ

/-- **The later-line facts of the canonical retained continuation with the boundary stop** (ruling R55). At a
disjoint pair `(u, r)` of good paths, for retained data with common paths agreeing with the two paths: one continuous
driver `W`, `W 0 = 0`, generates the canonical retained path stopped at its first contact with
`η₁[0, u] ∪ η₂[0, r] ∪ ℝ`, and at every continuation time `0 < t` before that stop (with `ω` in the later good event)
`(u, r + t)` is a disjoint pair, `ω` is in the later chart event, and the later-line facts hold at the capacity time
reached at `t`. -/
theorem exists_retLine_facts_R {Ω : Type*} [MeasurableSpace Ω] {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {u r : ℝ≥0} (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood) {ω : Ω} {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {x₁ x₂ : ℝ} (hp₁ : IsPathGood η₁ ζ₁ x₁) (hp₂ : IsPathGood η₂ ζ₂ x₂) (hx : x₂ < x₁)
    (hpair : Lemma76Exit.IsDisjointPair η₁ ζ₁ u η₂ ζ₂ r) (hG : ω ∈ G r) (ha₁ : ∀ s ≤ u, η₁' ω s = η₁ s)
    (ha₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ → η₂' ω s = η₂ s) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {κ : ℝ} (hκ : 0 < κ) (θ g₃ g₄ : ℝ) :
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      IsGeneratingTrace W
        (canonRetLife ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).fwd ω) η₂ ζ₂ r
          (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine) 0)
        (canonRetPath ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).fwd ω) η₂ ζ₂ r
          (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine) 0) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < contLife η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine) →
        ω ∈ G (r + t) →
        Lemma76Exit.IsDisjointPair η₁ ζ₁ u η₂ ζ₂ (r + t) ∧ ω ∈ (retFam G η₁' η₂' u (r + t)).E ∧
        IsRetLineFacts (retFam G η₁' η₂' u r) (retFam G η₁' η₂' u (r + t)) ω W
          (chartClock (contPath ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).fwd ω) η₂ r
            (contLife η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine))) t).toNNReal κ θ
          (wordM (retFam G η₁' η₂' u r) c₀ (-sleLambda κ - θ * QuantumZipper.chiC κ)
            (sleLambda κ - θ * QuantumZipper.chiC κ) g₃ g₄ ω)
          (wordM (retFam G η₁' η₂' u (r + t)) c₀ (-sleLambda κ - θ * QuantumZipper.chiC κ)
            (sleLambda κ - θ * QuantumZipper.chiC κ) g₃ g₄ ω) := by
  set d := retFam G η₁' η₂' u r with hddef
  have hdu : d.u = u := rfl
  have hdr : d.r = r := rfl
  have hrζ : (r : ℝ≥0∞) ≤ ζ₂ := hpair.2.1.le
  obtain ⟨hE, hs⟩ := isSetting_of_retData (hd r) hG hp₁ hp₂ hx ha₁
    (fun t ht => ha₂ t ((ENNReal.coe_le_coe.2 ht).trans hrζ)) hpair
  replace hs : IsSetting η₁ ζ₁ x₁ u η₂ ζ₂ x₂ r (d.fwd ω) (d.inv ω) (d.lift ω) := hs
  have hs' := isSetting_shorten hs
  have hi₁ : d.η₁ ω '' Icc 0 u = η₁ '' Icc 0 u := image_congr fun s hs => ha₁ s hs.2
  obtain ⟨W, hWc, hW0, hgen, hfacts⟩ := exists_retLine_facts_canon (hd r) hE hs' ha₁
    (fun t ht => ha₂ t ((ENNReal.coe_le_coe.2 ht).trans hrζ)) hc₀ hκ θ g₃ g₄ rfl
  rw [hdu, hdr, hi₁, canonRetLife_shorten, canonRetPath_shorten] at hgen
  rw [hdu, hdr, hi₁, contLife_shorten] at hfacts
  refine ⟨W, hWc, hW0, hgen, fun t ht0 htV hGt => ?_⟩
  have hstop : (r : ℝ≥0∞) ≤ contStop η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine) :=
    (lt_contStop_of_isDisjointPair hp₁ hp₂ hpair).le
  have hlt : ((r + t : ℝ≥0) : ℝ≥0∞) < contStop η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine) :=
    coe_add_lt_iff.1 htV
  have hpair' := isDisjointPair_of_lt_contStop hp₁ hp₂ hpair (lt_add_of_pos_right r ht0) hlt
  have hrtζ : ((r + t : ℝ≥0) : ℝ≥0∞) ≤ ζ₂ := hpair'.2.1.le
  obtain ⟨hE', hs₁⟩ := isSetting_of_retData (hd (r + t)) hGt hp₁ hp₂ hx ha₁
    (fun s hs => ha₂ s ((ENNReal.coe_le_coe.2 hs).trans hrtζ)) hpair'
  have hs₁' : IsSetting η₁ ζ₁ x₁ u η₂ (contStop η₂ ζ₂ r (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r ∪ realLine)) x₂ (r + t)
      ((retFam G η₁' η₂' u (r + t)).fwd ω) ((retFam G η₁' η₂' u (r + t)).inv ω)
      ((retFam G η₁' η₂' u (r + t)).lift ω) :=
    ⟨hs₁.hp₁, isPathGood_mono hs₁.hp₂ contStop_le, hx, ⟨hpair'.1, hlt, hpair'.2.2⟩, hs₁.hC⟩
  exact ⟨hpair', hE', hfacts t ht0 htV (hd (r + t)) rfl rfl rfl rfl hE' hs₁'
    (fun s hs => ha₂ s ((ENNReal.coe_le_coe.2 hs).trans hrtζ)) rfl⟩

end Restart.RetAux79

end InteractingSLE
