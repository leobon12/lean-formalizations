/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCDetAnnounce
import InteractingSLE.Spec.Restart.FlowCodeMain
import InteractingSLE.Spec.Supplement.StagedRegularize

/-!
# (Det) for drivers from (S) and (L)

Packet PROVE-FCDET. `FCDet.ae_codeMatch_of_hasSafeLaw'` concludes the code match of a *path* and therefore needs the
path to be the generating trace of the continuation's driver almost surely. That pathwise property is not a Borel
property of a coded path, so it cannot be carried along a push-forward to a canonical space. The driver form needs no
path: K2's coupling is a flow-line driver (`IsFlowLineDriver`), and canonical driver codes (`IsCanonicalDriverCode`)
certify determination of drivers. This file gives that form:

* `ae_driverCodeMatch_of_ae_condExpKernel`, `ae_driverCodeMatch_prod`: the driver analogues of
  `DomainMarkov.K2.ae_codeMatch_of_ae_condExpKernel_isFlowLine` and `ConverseBefore.ae_codeMatch_prod`;
* `isFlowLineDriver_of_isOptionalHullCoupling`: step (N) for drivers;
* **`ae_driverCodeMatch_of_hasSafeLaw`**: on a standard Borel space in `Type`, (S), (L), the flow-line type, an
  admissible seed and integrable pairings give the driver code match with the threshold as lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCDet

open DomainMarkov.K2 Sec7.PocketTraversal

/-! ### The driver form of (Det) -/

section Lift

/-- **(Det) for drivers from flow-line drivers under the regular conditional law** (the driver analogue of
`DomainMarkov.K2.ae_codeMatch_of_ae_condExpKernel_isFlowLine`, same proof): if for `P`-almost every `ω₀` in a `𝒢`-event
`M` the driver `W` with lifetime `L` is, under `condExpKernel P 𝒢 ω₀`, a flow-line driver of the field `Hc` with the
`𝒢`-measurable word `c ω₀`, then `P`-almost surely on `M` it matches the canonical driver code of `(c, Hc)`. -/
theorem ae_driverCodeMatch_of_ae_condExpKernel {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c) {Hc : Ω → DistOn upperHalfPlaneOpens}
    (hH : Measurable Hc) {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) {L : Ω → ℝ≥0∞} (hL : Measurable L)
    {κ θ : ℝ} {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F)
    (hfl : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → IsFlowLineDriver κ (c ω₀).fn (c ω₀).jumps θ (condExpKernel P 𝒢 ω₀) Hc W L) :
    ∀ᵐ ω ∂P, ω ∈ M → IsDriverCodeMatch (F (c ω, Hc ω)) (fun t => W t ω) (L ω) := by
  set G : BoundaryWord × Ω → Sec2.Assembly.PCode × ℝ≥0∞ := fun p => F (p.1, Hc p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (measurable_fst.prodMk (hH.comp measurable_snd))
  have hA : MeasurableSet {p : BoundaryWord × Ω | IsDriverCodeMatch (G p) (fun t => W t p.2) (L p.2)} :=
    measurableSet_driverCodeMatch hGm hW hL
  have h : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      (c ω₀, ω) ∈ {p : BoundaryWord × Ω | IsDriverCodeMatch (G p) (fun t => W t p.2) (L p.2)} := by
    filter_upwards [hfl] with ω₀ hfl₀ hω₀
    exact hF.2.2 (c ω₀) (condExpKernel P 𝒢 ω₀) Hc W L (hfl₀ hω₀)
  filter_upwards [Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param h𝒢 hc hA hM h] with ω hω hωM
  exact hω hωM

/-- **(Det) for drivers through the enlargement** (`ConverseBefore.ae_codeMatch_prod` for drivers). -/
theorem ae_driverCodeMatch_prod {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {Ω₀ : Type} [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω}
    [IsProbabilityMeasure P] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c) {Hc : Ω → DistOn upperHalfPlaneOpens}
    (hH : Measurable Hc) {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) {L : Ω → ℝ≥0∞} (hL : Measurable L)
    {κ θ : ℝ} {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F)
    (hfl : ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ M →
      IsFlowLineDriver κ (c p₀.1).fn (c p₀.1).jumps θ (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀)
        (fun p => Hc p.1) (fun t p => W t p.1) (fun p => L p.1)) :
    ∀ᵐ ω ∂P, ω ∈ M → IsDriverCodeMatch (F (c ω, Hc ω)) (fun t => W t ω) (L ω) := by
  have hfst : Measurable[𝒢.comap Prod.fst, 𝒢] (Prod.fst : Ω × Ω₀ → Ω) := Measurable.of_comap_le le_rfl
  have h := ae_driverCodeMatch_of_ae_condExpKernel (Ω := Ω × Ω₀) (𝒢 := 𝒢.comap Prod.fst)
    (P := P.prod P₀) ((MeasurableSpace.comap_mono h𝒢).trans measurable_fst.comap_le) ⟨M, hM, rfl⟩
    (hc.comp hfst) (hH.comp measurable_fst) (fun t => (hW t).comp measurable_fst) (hL.comp measurable_fst) hF hfl
  exact ConverseBefore.ae_of_ae_fst (P₀ := P₀)
    (q := fun ω => ω ∈ M → IsDriverCodeMatch (F (c ω, Hc ω)) (fun t => W t ω) (L ω)) h

end Lift

section Det

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **An optional hull coupling of the flow-line type is a flow-line driver** (step (N) without the trace). -/
theorem isFlowLineDriver_of_isOptionalHullCoupling {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'}
    {κ θ : ℝ} {c : BoundaryWord} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (htype : IsFlowType κ θ c xL xR ρL ρR)
    {𝓕 : Filtration ℝ≥0 m'} {W : ℝ≥0 → Ω' → ℝ} {VL : Fin nL → ℝ≥0 → Ω' → ℝ} {VR : Fin nR → ℝ≥0 → Ω' → ℝ}
    {B : ℝ≥0 → Ω' → ℝ} {ζ : Ω' → ℝ≥0∞} {Hc X : Ω' → DistOn upperHalfPlaneOpens}
    (hX : ∀ p, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc p) (X p))
    (hc : IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 W VL VR B ζ X) :
    IsFlowLineDriver κ c.fn c.jumps θ Q Hc W ζ := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  have h' := isOptionalHullCoupling_cast eL eR hc
  rw [hxL, hxR, hρL, hρR] at h'
  exact ⟨X, 𝓕, fun i => VL (Fin.cast eL i), fun j => VR (Fin.cast eR j), B, hX, h'⟩

/-- **(Det) for drivers from (S) and (L)**, on a standard Borel space in `Type`: the setting of
`ae_codeMatch_of_hasSafeLaw'` without any path. Almost surely the driver, with the threshold as lifetime, matches the
canonical driver code of `(c, Hc)`. No generating trace is used, so this form transfers along laws. -/
theorem ae_driverCodeMatch_of_hasSafeLaw {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) (htype : ∀ᵐ ω ∂P, IsFlowType κ θ (c ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {Hc X : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hX : Measurable X) (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hseed : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ (thr ρL ρR W xL xR) W X)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) :
    ∀ᵐ ω ∂P, IsDriverCodeMatch (F (c ω, Hc ω)) (fun t => W t ω) (thr ρL ρR W xL xR ω) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have h0U : 𝒢 ≤ usualAugmentation 𝓗 P 0 := h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t =>
    (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have hpos : ∀ᵐ ω ∂P, 0 < thr ρL ρR W xL xR ω := hseed.mono fun ω h => thr_pos hW0 hWc hxL0 hxR0 h
  obtain ⟨T, hT, -⟩ := exists_isAnnouncingSeq_thr (ρL := ρL) (ρR := ρR) (𝓖 := usualAugmentation 𝓗 P)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) hWc hWaU (hxL.mono h0U le_rfl)
    (hxR.mono h0U le_rfl) hxLa hxRm hpos
  obtain ⟨P₀, hP₀, hK⟩ := exists_ae_isOptionalHullCoupling hκ h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa hX
    hint hpos hT hlaw hmem
  have hthrm : Measurable (thr ρL ρR W xL xR) :=
    measurable_thr hWc hWa (hxL.mono h𝒢 le_rfl) (hxR.mono h𝒢 le_rfl)
  have htype' : ∀ᵐ p₀ ∂(P.prod P₀), IsFlowType κ θ (c p₀.1) (xL p₀.1) (xR p₀.1) ρL ρR :=
    ConverseBefore.ae_fst_of_ae htype
  have h := ae_driverCodeMatch_prod (P₀ := P₀) (M := univ) h𝒢m MeasurableSet.univ hc hHc
    (fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl) hthrm hF (by
      filter_upwards [hK, htype'] with p₀ hp₀ hty₀ _
      obtain ⟨𝓕', W', VL', VR', B', hcpl, hag⟩ := hp₀
      have hW' : IsFlowLineDriver κ (c p₀.1).fn (c p₀.1).jumps θ
          (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀) (fun p => Hc p.1) W'
          (fun p => thr ρL ρR W xL xR p.1) :=
        isFlowLineDriver_of_isOptionalHullCoupling hty₀ (fun p : Ω × (ℕ → ℝ) => hXH p.1) hcpl
      refine Theorem14.StagedReg.isFlowLineDriver_congr_ae hW'
        (fun t => ((hWa t).measurable.mono (𝓗.le t) le_rfl).comp measurable_fst) ?_
      filter_upwards [hag] with p hp
      exact ⟨(hp 0).1.symm, fun t _ => (hp t).1.symm⟩)
  filter_upwards [h] with ω hω using hω (mem_univ ω)

end Det

end InteractingSLE.Restart.FCDet
