/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2Loc

/-!
# K2: the kernel coupling of a general continuation, from `P`-side inputs

Packet PROVE-DOMAINMARKOV5, item (K2). **The kernel assembly of every restart, single- or two-curve, done once.**

Setting: a standard Borel space `(Ω, P)`, a sub-σ-algebra `𝒢` (the information conditioned on: the stopped history
`𝓓_T` of one path for the single-curve restart; the joint stopped σ-algebra of two prefixes for Lemma G7, the
first-contact restart, GB6 and Lemma 7.6), a live event `F ∈ 𝒢`, a `P`-side filtration `𝓗` with `𝒢 ≤ 𝓗 0`, a
continuation `(W, VL, VR, B, ζ)` with `𝒢`-measurable word `(ΘL, ΘR)`, and a field `X` (the field read in the
continuation's chart). (S) and (L) may use any filtration `𝓗'` with `𝒢 ≤ 𝓗' 0` in which the continuation is adapted
(e.g. the smallest one), not necessarily the filtration `𝓗` of (E). The `P`-side inputs are

* **(E)** `IsRandomWordEvolution κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ`: the continuation is an integrated
  `SLE_κ(ρ)` evolution of the random initial word on `F` (Aux. lemma 122's form);
* **(S)** `HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR X`: the conditional law of `X` off the continuation hull at every
  deterministic time, on `𝓗`-events (`DomainMarkovK2Law.lean`);
* **(L)** `HasSafeMembers P 𝓗' F ζ W X`: the member identities of the continuation hulls at deterministic times
  (`DomainMarkovK2Loc.lean`);
* `0 < ζ` almost surely on `F` (admissible seed groups).

**`ae_isOptionalHullCoupling_k`**: for `P`-almost every `ω₀ ∈ F`, under `ν = condExpKernel P 𝒢 ω₀`, processes equal
to the continuation `ν`-almost surely at every time form, with `X`, an optional hull coupling (the frozen
`IsOptionalHullCoupling`) of the deterministic word `(ΘL ω₀, ΘR ω₀)`.

The proof is PROVE-DOMAINMARKOV2's `kernelRestartCouplingStatement_of_locality` with the restart objects replaced:
(E) through `exists_ae_condExpKernel_agree`; the dyadic protected-kernel law from (S) (`ae_isDyadicSampled_k`); the
coupling characteristic functional at every stopping time and the Gaussian law at time `0` from it
(`condExp_cexp_eq_frozenRHS_of_dyadic`, `Lemma71J.isZBGFFProcess_of_isCouplingCharFun`); locality from (L)
(`ae_isLocalSet_k`).

For the two-curve consumers, (E), (S) and (L) are the `P`-side content still to be supplied in each setting: (S) and
(L) are the union local-set Markov property at the later stopping lines read in the retained chart (PROVE-
DOMAINMARKOV4's S2 with chart transport and the mean identification), (E) is the driver of the continuation in the
retained chart (item E2). See `planning/handoffs/PROVE-DOMAINMARKOV5.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped ENNReal NNReal

namespace InteractingSLE.Restart.DomainMarkov.K2

open Coupling Ito Sec7 Sec7.Aux122Disint

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **K2: the kernel coupling of a general continuation from its `P`-side inputs.** For `P`-almost every `ω₀ ∈ F`,
under the regular conditional law `condExpKernel P 𝒢 ω₀`, processes equal to the continuation (almost surely, at
every time) and the field `X` form an optional hull coupling of the word `(ΘL ω₀, ΘR ω₀)`, with lifetime `ζ`. -/
theorem ae_isOptionalHullCoupling_k
    (hE : IsRandomWordEvolution κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ) (hX : Measurable X)
    (hζ0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' ζ W) (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR X) (hmem : HasSafeMembers P 𝓗' F ζ W X) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' ζ X ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
          ∀ j, VR' j t ω = VR j t ω := by
  obtain ⟨NE, 𝓖, W', VL', VR', B', -, hNE0, hagE, hev⟩ := exists_ae_condExpKernel_agree hE
  obtain ⟨h0, hF, -, -, -, -, -, -, hpath⟩ := hE
  have h𝒢m : 𝒢 ≤ mΩ := h0.trans (𝓗.le 0)
  have hweakP : ∀ᵐ ω ∂P, ω ∈ F →
      IsWeakPath (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) :=
    hpath.mono fun ω h hωF => IsIntegratedSLEPath.isWeakPath (h hωF)
  obtain ⟨N, hNm, hN0, hN, -⟩ := exists_isKGood hweakP (p := fun _ => True) (ae_of_all _ fun _ => trivial)
  have hS := ae_isDyadicSampled_k h𝒢' hF hW' hVL' hVR' hX hNm hN0 hN hlaw
  have hL := ae_isLocalSet_k h𝒢' hF hW' hVL' hVR' hX hNm hN0 hN hmem
  filter_upwards [hev, hS, hL, ae_ae_condExpKernel h𝒢m (measure_eq_zero_iff_ae_notMem.1 hN0),
    ae_ae_condExpKernel h𝒢m (measure_eq_zero_iff_ae_notMem.1 hNE0), ae_ae_condExpKernel_mem (P := P) h𝒢m hF,
    ae_ae_condExpKernel h𝒢m hζ0] with ω₀ hev0 hS0 hL0 hNν hNEν hmemF hζν hω₀F
  have hE' := hev0 hω₀F
  have hFν := hmemF hω₀F
  have hagW : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
      ∀ j, VR' j t ω = VR j t ω := by
    filter_upwards [hNEν, hFν] with ω hωNE hωF t
    obtain ⟨e1, e2, e3, -⟩ := hagE ω hωNE hωF t
    exact ⟨e1, e2, e3⟩
  have hagree : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = kW N F W VL VR t ω ∧
      (∀ i, VL' i t ω = kVL N F W VL VR i t ω) ∧ ∀ j, VR' j t ω = kVR N F W VL VR j t ω := by
    filter_upwards [hagW, hNν, hFν] with ω hω hωN hωF t
    obtain ⟨e1, e2, e3⟩ := hω t
    exact ⟨by rw [e1, kW_eq hωN hωF], fun i => by rw [e2 i, kVL_eq hωN hωF],
      fun j => by rw [e3 j, kVR_eq hωN hωF]⟩
  have hX' := IsIntegratedSLEEvolution.isMeasurableKilledDriving hE'
  have hdy : ∀ hX'' : IsMeasurableKilledDriving W' VL' VR' ζ,
      IsDyadicSampled κ W' (bheProc κ ρL ρR W' VL' VR') (condExpKernel P 𝒢 ω₀) hX'' X :=
    fun hX'' => hS0 hω₀F W' VL' VR' hX'' hagree
  have hcf : MartMeans.IsCouplingCharFun κ ρL ρR (condExpKernel P 𝒢 ω₀)
      (drivingFiltration (condExpKernel P 𝒢 ω₀) hX') W' VL' VR' ζ X := fun τ hτ hτζ uτ huτ φ =>
    condExp_cexp_eq_frozenRHS_of_dyadic hE' (bheProc κ ρL ρR W' VL' VR')
      (fun ω s => isBoundedHarmonicExtension_bheProc ω s) _
      (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hX) hX' (hdy hX') hτ hτζ uτ huτ φ
  have hζν' : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), 0 < ζ ω := by
    filter_upwards [hζν, hFν] with ω h1 h2 using h1 h2
  have h0' : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), 0 < ζ ω ∧
      ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W' 0 ω = 0 ∧
      (∀ i, VL' i 0 ω = ΘL ω₀ i) ∧ ∀ j, VR' j 0 ω = ΘR ω₀ j := by
    filter_upwards [hE'.2.2.2.2, hζν'] with ω hp hω
    exact ⟨hω, hp.2.2.2.1, hp.1, hp.2.1, hp.2.2.1⟩
  have hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (ΘL ω₀) (ΘR ω₀))
      (forceJumpSet (ΘL ω₀) (ΘR ω₀)) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z)
        (condExpKernel P 𝒢 ω₀) :=
    fun u₀ hu₀ => Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcf hX h0' hu₀
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR (ΘL ω₀) (ΘR ω₀)
  refine ⟨𝓖, W', VL', VR', B', ?_, hagW⟩
  exact isOptionalHullCoupling_of_dyadic hE' hX hgff (bheProc κ ρL ρR W' VL' VR')
    (fun ω s => isBoundedHarmonicExtension_bheProc ω s) hdy
    (fun hX'' τ hτ hτζ => hL0 hω₀F _ hu₀.1 (hgff _ hu₀) W' VL' VR' hX''
      (hagree.mono fun ω h t _ => h t) hζν' τ hτ hτζ)

end InteractingSLE.Restart.DomainMarkov.K2
