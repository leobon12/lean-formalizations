/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMean

/-!
# The pocket chart law at the ambient times from the union law and the boundary values

Packet PROVE-STRIPSYS33. Specification §7.4, Aux. lemmas 124–125 (`source/spec/p385-432.md` L171–L250) and Aux.
lemmas 35–36 (`source/spec/p145-192.md` L908–L940, `source/spec/p193-240.md` L1–L78).

PROVE-STRIPSYS32's `PocketUnionPt.PocketStopChartLaw` (the input of `pocketUnionPtChartLaw_of_stop`, hence of
`PocketStopInput`/`…Inf` and of Theorem 1.3's pocket word) asks for a pocket chart and, at every relative capacity
time `q`, a set `K_q` with the marked union law (`PocketStopLaw`) and the central pocket mean (`PocketStopMeanAt`) at
the ambient time `T(q)`. With the canonical `K_q = ℍ ∖ activeDom` both reduce to two named field-level inputs:

* `PocketStopUnionLaw` (`PocketStopActive.lean`): the marked union law of `B ∪ R_{T(q)}` for the relative history;
* `PocketStopSideLimit` (`PocketStopMean.lean`): the boundary values of the mean in the relative chart.

## Main results

* **`pocketStopChartLaw_of_sideLimit`**: `PocketStopChartLaw` for any pocket data (open pocket, injective coordinate,
  ambient-domain identity, relatively closed hulls, driven curves, a conformal pocket chart with a derivative logarithm)
  from the two named inputs at every `q`;
* **`pocketStopChartLaw_cfPocket`**, **`pocketStopChartLaw_cfPocketInf`**: the same for the change pocket of the strip
  system (bounded, and opening at the flow seed), with every geometric hypothesis discharged from the counterflow pocket
  configuration (`IsCfPocketConfig`, `IsCfPocketConfigInf`) as in PROVE-STRIPSYS32.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStop

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt

section Generic

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The pocket chart law at the ambient times from the two named inputs.** For pocket data on `A` (open pockets `C`,
injective coordinates `ψ`, the ambient-domain identity `ψ(C ∩ (ℍ ∖ F_q)) = ℍ ∖ K^{rel}_q`, relatively closed hulls
`F_q`, driven traversals `γ`, prefix σ-algebras inside `mΩ`), a conformal pocket chart `c` with a derivative logarithm
`ℓ` whose imaginary part is the lift, and the deterministic mean `𝔥 = u` (bounded harmonic): if at every `q` the marked
union law of `B ∪ R_{T(q)}` and the boundary values of the mean in the relative chart hold, then `PocketStopChartLaw`
holds with the canonical sets `K_q = ℍ ∖ activeDom` and `k = χ(κ)`. -/
theorem pocketStopChartLaw_of_sideLimit [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ} (hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C : Ω → Set ℂ}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) {ψ : Ω → ℂ → ℂ} (hinj : ∀ ω ∈ A, InjOn (ψ ω) (C ω)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {𝔥 : DistOn upperHalfPlaneOpens} (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    {c : Ω → Chart} (hc : IsPocketChartOn 𝓦 A C ψ c) {ℓ : Ω → ℂ → ℂ}
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im) {a : ℝ}
    (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) q) :
    PocketStopChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ F h₀ 𝔥 := by
  have hact : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F q ω) :=
    fun q ω hω hq => activeDom_eq_inter hω hq (hc.1 ω hω).1 (hc.1 ω hω).2.1 (hc.1 ω hω).2.2.1 (hinj ω hω)
      (hgeo q ω hω hq)
  refine ⟨c, a, chiC κ, hc, fun q => ⟨activeCompl A γ c q, ?_⟩⟩
  have hlaw := pocketStopLaw_activeCompl (hpre q) (hact q) hCo (hFo q) (hU q)
  refine ⟨hlaw, ?_⟩
  have hloc : IsLocalSet (activeCompl A γ c q) h₀ P :=
    ((isLocalSet_tfae hh₀ hlaw.1 hlaw.2.1).out 1 4).1 (IsHistoryAvoidanceLocal.isAvoidanceLocal hlaw.2.2.1)
  refine pocketStopMeanAt_of_sideLimit hh₀ hlaw.1 hloc (fun ω hω hq => ?_)
    (fun ω hω hq => (hact q ω hω hq).symm) hγ (fun ω hω => ⟨(hc.1 ω hω).1, (hℓ ω hω).1, (hℓ ω hω).2⟩) hu hub h𝔥
    (hside q)
  rw [activeCompl, sdiff_sdiff_cancel_left]
  rw [hact q ω hω hq]
  exact inter_subset_right.trans sdiff_subset

end Generic

/-! ### The change pocket of the strip system -/

section Pocket

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The pocket chart law for the bounded change pocket** (`0 ∉ closure` of the pocket, `x₀ ≠ x`): on a
walls-measurable event `A` of configurations, for a walls-point-measurable Jordan coordinate `ψ`, the chart law at the
ambient times of the erased traversal `travAll R L r η ψ` with the hulls `stopHull … q` follows from the two named
inputs; every geometric hypothesis of `pocketStopChartLaw_of_sideLimit` comes from the counterflow pocket
configuration. -/
theorem pocketStopChartLaw_cfPocket [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {𝔥 : DistOn upperHalfPlaneOpens}
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z) {c : Ω → Chart}
    (hc : IsPocketChartOn 𝓦 A (fun ω => cfPocket (R ω) (L ω) r) ψ c) {ℓ : Ω → ℂ → ℂ}
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im) {a : ℝ}
    (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHull R L r W η ψ q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A (travAll R L r η ψ) xL xR c a h₀ u
      (activeCompl A (travAll R L r η ψ) c q) q) :
    PocketStopChartLaw κ ρL ρR 𝓦 P A (travAll R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (stopHull R L r W η ψ) h₀ 𝔥 := by
  have hP : ∀ ω ∈ A, Sec6.IsReversePocket (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r)
      (cfArcL (R ω) (L ω) r) (cfBeta (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG hω)).conf (hcfg ω (hAG hω)).bounded)
      (hcfg ω (hAG hω)).trace (hcfg ω (hAG hω)).continuous_W (hcfg ω (hAG hω)).W_zero (hcfg ω (hAG hω)).revR
      (hcfg ω (hAG hω)).revL (hcfg ω (hAG hω)).visR
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (ψ ω) := fun ω hω => by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ ω hω
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA hγ
      (PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
        hψm)
  refine pocketStopChartLaw_of_sideLimit hpre hγ (fun ω hω => (hP ω hω).isOpen)
    (fun ω hω => (hψ ω hω).2.2.2.1.2.injOn) (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTime (hP ω hω) (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub h𝔥 hc hℓ hU hside

/-- **The pocket chart law for the change pocket opening at the flow seed** (`x₀ = x`): as
`pocketStopChartLaw_cfPocket`, for the configuration `IsCfPocketConfigInf`, the traversal `travAllInf` and the hulls
`stopHullInf … q`. -/
theorem pocketStopChartLaw_cfPocketInf [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {𝔥 : DistOn upperHalfPlaneOpens}
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z) {c : Ω → Chart}
    (hc : IsPocketChartOn 𝓦 A (fun ω => cfPocket (R ω) (L ω) r) ψ c) {ℓ : Ω → ℂ → ℂ}
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im) {a : ℝ}
    (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHullInf R L r W η ψ q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a h₀ u
      (activeCompl A (travAllInf R L r η ψ) c q) q) :
    PocketStopChartLaw κ ρL ρR 𝓦 P A (travAllInf R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (stopHullInf R L r W η ψ) h₀ 𝔥 := by
  have hP : ∀ ω ∈ A, Sec6.IsReversePocketInf (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r)
      (cfArcLInf (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).isReversePocketInf
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) :=
    fun ω hω => by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA hγ fun u hu => measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  refine pocketStopChartLaw_of_sideLimit hpre hγ (fun ω hω => (hP ω hω).isOpen)
    (fun ω hω => (hψ ω hω).2.2.2.1.2.injOn)
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub h𝔥 hc hℓ hU hside

end Pocket

/-! ### The ambient-time pocket inputs from the named field-level inputs -/

section FieldDefs

variable {Ω : Type*}

/-- **The field-level pocket data for one word** (the two named inputs, with their chart): a conformal pocket chart
`c` (walls-measurable lift) with a derivative logarithm `ℓ` whose imaginary part is the lift, and a constant `a`, such
that at every relative capacity time `q` the marked union law of `B ∪ R_{T(q)}` (`PocketStopUnionLaw`) and the boundary
values of the mean in the relative chart (`PocketStopSideLimit`, for the canonical set `ℍ ∖ activeDom`) hold; `u` is the
deterministic harmonic mean of the field (`h = h₀ + u`). -/
def PocketStopField (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓦 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (F : ℝ≥0 → Ω → Set ℂ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∃ (c : Ω → Chart) (ℓ : Ω → ℂ → ℂ) (a : ℝ), IsPocketChartOn 𝓦 A C ψ c ∧
    (∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im) ∧
    ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q ∧
      PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) q

/-- **The field-level pocket inputs on every word-shape event** (bounded change pocket): `PocketStopInput` with the
pocket chart law replaced by the named field-level data `PocketStopField`. -/
def PocketStopFieldInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopField (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHull R L r W η ψ) h₀ u) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopField (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHull R L r W η ψ) h₀ u)

/-- **The field-level pocket inputs on every word-shape event** (change pocket opening at the flow seed). -/
def PocketStopFieldInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopField (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHullInf R L r W η ψ) h₀ u) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopField (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHullInf R L r W η ψ) h₀ u)

end FieldDefs

section FieldThms

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketStopInput` from the named field-level inputs** (bounded change pocket): on a walls-measurable event of
counterflow pocket configurations, the ambient-time pocket inputs follow from `PocketStopFieldInput` and the
representation of the deterministic mean `𝔥` by the bounded harmonic function `u`. -/
theorem pocketStopInput_of_field [IsProbabilityMeasure P] {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {𝔥 : DistOn upperHalfPlaneOpens}
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hin : PocketStopFieldInput κ rL rR 𝓦 P R L r W η G h₀ u) :
    PocketStopInput κ rL rR 𝓦 P R L r W η G h₀ 𝔥 := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨c, ℓ, a, hc, hℓ, hq⟩ := h1 hs
    exact pocketStopChartLaw_cfPocket h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm hh₀ hu hub h𝔥 hc hℓ
      (fun q => (hq q).1) fun q => (hq q).2
  · obtain ⟨c, ℓ, a, hc, hℓ, hq⟩ := h2 hs
    exact pocketStopChartLaw_cfPocket h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm hh₀ hu hub h𝔥 hc hℓ
      (fun q => (hq q).1) fun q => (hq q).2

/-- **`PocketStopInputInf` from the named field-level inputs** (change pocket opening at the flow seed). -/
theorem pocketStopInputInf_of_field [IsProbabilityMeasure P] {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {𝔥 : DistOn upperHalfPlaneOpens}
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hin : PocketStopFieldInputInf κ rL rR 𝓦 P R L r W η G h₀ u) :
    PocketStopInputInf κ rL rR 𝓦 P R L r W η G h₀ 𝔥 := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨c, ℓ, a, hc, hℓ, hq⟩ := h1 hs
    exact pocketStopChartLaw_cfPocketInf h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm hh₀ hu hub h𝔥 hc hℓ
      (fun q => (hq q).1) fun q => (hq q).2
  · obtain ⟨c, ℓ, a, hc, hℓ, hq⟩ := h2 hs
    exact pocketStopChartLaw_cfPocketInf h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm hh₀ hu hub h𝔥 hc hℓ
      (fun q => (hq q).1) fun q => (hq q).2

end FieldThms

end InteractingSLE.Sec7.PocketStop
