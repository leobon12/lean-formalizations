/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetAux79ZoneLine
import InteractingSLE.Spec.Restart.RetAux79Path

/-!
# The later-line facts of the canonical retained continuation (pathwise)

Packet PROVE-RETAUX79B. Composition of the chart-path facts of the canonical retained clock
(`RetAux79.canonRetPath_facts`) with the later-line facts for retained data (`RetAux79.retLine_facts`): at a
point `ω` of the chart event of the stop-line retained data `d` where `(u, r)` is a disjoint-pair setting of the two
paths `η₁`, `η₂`, the second continuation's canonical retained clock `γ` (translation `0`) has one continuous driver
`W`, `W 0 = 0`, generating it up to `canonRetLife`; and at every later continuation time `0 < t < V` at which
`(u, r + t)` is again a disjoint-pair setting (later retained data `d'`), the later chart is the stop-line chart
followed by `f_Q`, `Q = C(t)` the capacity time, and the boundary-data identity (III-b′) holds for the measurable words
`wordM d …` and `wordM d' …`. These are the last three conjuncts of `hline` in `RetAux79.hasSafeLaw_of_retLines`, with
`W` independent of `t`.

Also `image_inv_eq_of_trans`: under (III-a) the later active domain is the stop-line chart image of `ℍ \ K_Q`, the
hull identity `hBK` of `DomainMarkov.Aux79.hasSafeMembers_of_lineLocal` (with `B t` the complement of the later
active domain).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv logDerivFwd)

namespace InteractingSLE

namespace Restart.RetAux79

open Sec7 Sec7.Lemma76G Supp7 MartChar.RealFlow


/-- **The later active domain is the stop-line image of `ℍ \ K_Q`** under (III-a): if `ψ₁` maps `ℍ` onto `D₁` and
`ψ₁ = ψ₀ ∘ f_Q⁻¹` on `ℍ`, then `D₁ = ψ₀(ℍ \ K_Q)`. -/
theorem image_inv_eq_of_trans {ψ₀ ψ₁ : ℂ → ℂ} {D₁ : Set ℂ} (hbij : BijOn ψ₁ H D₁) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {Q : ℝ} (hQ : 0 ≤ Q) (hinv : ∀ w ∈ H, ψ₁ w = ψ₀ (fwdMapInv W Q w)) :
    D₁ = ψ₀ '' (H \ QuantumZipper.fwdHull W Q) := by
  rw [← hbij.image_eq, ← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hQ, image_image]
  exact image_congr hinv

/-- **The later-line facts of the canonical retained continuation** (see the module docstring). -/
theorem exists_retLine_facts_canon {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω}
    (hω : ω ∈ d.E) {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}
    (hs₀ : IsSetting η₁ ζ₁ x₁ d.u η₂ ζ₂ x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω))
    (hα : ∀ s ≤ d.u, d.η₁ ω s = η₁ s) (hβ₀ : ∀ s ≤ d.r, d.η₂ ω s = η₂ s) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {κ : ℝ} (hκ : 0 < κ) (θ g₃ g₄ : ℝ) {B₀ : BoundaryWord}
    (hB₀ : B₀ = Lemma76G.wordM d c₀ (-sleLambda κ - θ * QuantumZipper.chiC κ)
      (sleLambda κ - θ * QuantumZipper.chiC κ) g₃ g₄ ω) :
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      IsGeneratingTrace W (canonRetLife (d.D ω) (d.fwd ω) η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r) 0)
        (canonRetPath (d.D ω) (d.fwd ω) η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r) 0) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r) →
      ∀ {d' : RetData Ω}, d'.IsMeasGood → d'.η₁ = d.η₁ → d'.η₂ = d.η₂ → d'.u = d.u → d'.r = d.r + t →
      ω ∈ d'.E → IsSetting η₁ ζ₁ x₁ d.u η₂ ζ₂ x₂ (d.r + t) (d'.fwd ω) (d'.inv ω) (d'.lift ω) →
      (∀ s ≤ d.r + t, d.η₂ ω s = η₂ s) → ∀ {Bt : BoundaryWord},
      Bt = Lemma76G.wordM d' c₀ (-sleLambda κ - θ * QuantumZipper.chiC κ)
        (sleLambda κ - θ * QuantumZipper.chiC κ) g₃ g₄ ω →
      (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal)
        (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
          (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal w)) ∧
      (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal)
          (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
            (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal
          (fwdMapInv (fun s : ℝ => W s.toNNReal) (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
            (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal w)).im +
        (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal)
          (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
            (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ (flowLineRhoL κ B₀.fn B₀.jumps 0 θ) (flowLineRhoR κ B₀.fn B₀.jumps 0 θ)
          (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL B₀.fn B₀.jumps 0 i)
            (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
              (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal -
            W (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
              (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal)
          (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR B₀.fn B₀.jumps 0 j)
            (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
              (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal -
            W (chartClock (contPath (d.D ω) (d.fwd ω) η₂ d.r
              (contLife η₂ ζ₂ d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r))) t).toNNReal) y =
          Bt.fn y + θ * QuantumZipper.chiC κ := by
  have hg := hd.good ω (RetData.E_subset_G hω)
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hω
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hω]⟩
  have hωE₀ := RetData.E_subset_E₀ hω
  have hcl : d.η₂ ω d.r ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r) := by
    rw [← hd.DOf_of_mem RetData.E₀_subset_G hωE₀]
    exact hω.2
  have hR := isRetCont_snd hg hC hφ hs₀.hp₂ hβ₀ hs₀.hpair.2.1 hωE₀.1.2 hωE₀.2 hcl
  have hD : d.D ω = H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r) := by
    rw [hd.D_of_mem hω, activeDomain_eq (isCompact_prefixSet' hg.1 hg.2.1).isClosed, prefixSet,
      image_congr fun t ht => hβ₀ t ht.2]
  rw [hD]
  obtain ⟨W, hWc, hW0, hgen, hinj, hfacts⟩ := canonRetPath_facts hR
  refine ⟨W, hWc, hW0, hgen, fun t ht0 htV d' hd' h₁ h₂ hu hr hω' hs₁ hβ Bt hBt => ?_⟩
  obtain ⟨-, hQlt, hQpos, himg, htip⟩ := hfacts t htV.le
  refine retLine_facts hd hd' h₁ h₂ hu hr hω hω' hs₀ hs₁ hα hβ hgen hWc hW0 hinj (hQlt htV) (hQpos ht0) ?_ ?_ hc₀
    hκ θ g₃ g₄ hB₀ hBt
  · rw [himg]
    exact (image_congr fun s hs => hβ s hs.2).symm
  · rw [htip, hβ _ le_rfl]

end Restart.RetAux79

end InteractingSLE
