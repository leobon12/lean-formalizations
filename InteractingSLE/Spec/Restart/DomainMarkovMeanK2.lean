/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovMeanLoc

/-!
# K2 for a field read through a retained chart

Packet PROVE-DOMAINMARKOV6. The consumers of PROVE-DOMAINMARKOV5's K2 (`K2.ae_isOptionalHullCoupling_k`) all read the
field through a retained chart `c` fixed by the conditioning σ-algebra `𝒢`: `X = chartTransport c 1 a k h` (G7's and
Lemma 7.6's retained chart, the first-contact chart of Lemma 7.8, GB6's counterflow chart). This file assembles K2 for
such a field from

* (E) the continuation's random word evolution (`IsRandomWordEvolution`, PROVE-DOMAINMARKOV7);
* (S) at every capacity time `q`: the physical later-line Gaussian kernel on `inv(ℍ ∖ K̃_q)` given marks `𝓜_q ⊇ 𝓗'_q`
  (Aux. lemma 77) and the later-line mean identification `chartTransport c 1 a k M_q = 𝔥_q` (Aux. lemma 79), through
  `Mean.hasSafeLaw_chartTransport`;
* (L) at every capacity time `s`: the history-marked locality of the physical later-line union `A_s` for marks
  `ℋ_s ⊇ 𝓗'_s` with `ℍ ∖ A_s = inv(ℍ ∖ K̃_s)` (Aux. lemma 77), through `Mean.hasSafeMembers_chartTransport`.

The driver regularity used by (S) and (L) comes from (E) (`IsIntegratedSLEPath.isWeakPath`).

* **`ae_isOptionalHullCoupling_chartTransport`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.Mean

open Coupling K2 LocalSets WholeField Sec7 Sec7.Aux122Disint

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- (E) gives the driver regularity used by (S) and (L) on the live event. -/
theorem ae_isDrvReg_of_isRandomWordEvolution (hE : IsRandomWordEvolution κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ω ∈ F → IsDrvReg W ζ ω := by
  filter_upwards [hE.2.2.2.2.2.2.2.2] with ω h hωF
  have hw := IsIntegratedSLEPath.isWeakPath (h hωF)
  exact ⟨hw.2.1, hw.1⟩

/-- **K2 for a field read through a retained chart** (`K2.ae_isOptionalHullCoupling_k` with
`Mean.hasSafeLaw_chartTransport` and `Mean.hasSafeMembers_chartTransport`). Let the conformal chart `c` with continuous
harmonic lifts be measurable for the conditioning σ-algebra `𝒢`, let `h` be a measurable field whose centring `h − u₀`
is a zero-boundary GFF, and let `(W, VL, VR, B, ζ)` be the continuation, a random word evolution (E) on the live event
`F ∈ 𝒢`, adapted to a filtration `𝓗'` with `𝒢 ≤ 𝓗'_0`. Suppose that at every capacity time

* (S) there are marks `𝓜_q ⊇ 𝓗'_q` given which, almost surely on `F ∩ {q < ζ}`, `h` paired with test functions
  supported in `inv(ℍ ∖ K̃_q)` is Gaussian with mean `M_q` and the zero-boundary covariance of `inv(ℍ ∖ K̃_q)`, and
  the chart transport of `M_q` is the canonical finite-force mean `𝔥_q` of the continuation off `K̃_q`;
* (L) there are marks `ℋ_s ⊇ 𝓗'_s` for which a hitting-measurable relatively closed random set `A_s` is a
  history-marked local set of `h − u₀`, with `ℍ ∖ A_s = inv(ℍ ∖ K̃_s)` almost surely on `F ∩ {s < ζ}`.

Then for almost every `ω₀ ∈ F`, under `condExpKernel P 𝒢 ω₀`, processes equal to the continuation at every time and
the transported field `chartTransport c 1 a k h` form an optional hull coupling of the word `(ΘL ω₀, ΘR ω₀)`. -/
theorem ae_isOptionalHullCoupling_chartTransport
    (hE : IsRandomWordEvolution κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ) (hζ0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω)
    {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' ζ W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗' q ≤ 𝓜 q) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) :
            ℂ)))
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ DomainMarkov.avoidSet W ζ ψ q → Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (bheProc κ ρL ρR W VL VR ω q) z * ψ z)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓗ℋ : ∀ s, 𝓗' s ≤ ℋ s) (hℋ : ∀ s, ℋ s ≤ mΩ)
    (A : ℝ≥0 → Ω → Set ℂ) (hAm : ∀ s, Measurable[mΩ, hittingSigma] (A s))
    (hAc : ∀ s ω, A s ω ⊆ H ∧ IsOpen (H \ A s ω))
    (hloc : ∀ s, IsHistoryAvoidanceLocal (ℋ s) (A s) (centredField h u₀) P)
    (hAK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (s : ℝ≥0∞) < ζ ω →
      H \ A s ω = (c ω).2.1 '' (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) s)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' ζ
          (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
          ∀ j, VR' j t ω = VR j t ω := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢'.trans (𝓗'.le 0)
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢m _ (hdom z))
      (fun z => (hfwd z).mono h𝒢m le_rfl) (fun z => (hliftm z).mono h𝒢m le_rfl) hliftc hhm 1 a k
  have hreg := ae_isDrvReg_of_isRandomWordEvolution hE
  have hlaw := hasSafeLaw_chartTransport (ρL := ρL) (ρR := ρR) (VL := VL) (VR := VR) h𝒢' hc hdom hfwd hliftm
    hliftc hhm a k 𝓜 h𝓗𝓜 h𝓜 M hcond hmean hreg
  have hmem := hasSafeMembers_chartTransport h𝒢' hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift a k ℋ h𝓗ℋ hℋ A
    hAm hAc hloc hAK hreg
  exact ae_isOptionalHullCoupling_k hE hX hζ0 h𝒢' hW' hVL' hVR' hlaw hmem

end InteractingSLE.Restart.DomainMarkov.Mean
