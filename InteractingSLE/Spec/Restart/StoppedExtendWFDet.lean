/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedExtendWFLaw
import InteractingSLE.Spec.Restart.StoppedExtendProofFlow

/-!
# The stopped (Det) and flow locality from Aux. lemma 54 for Galmarino stops

Packet PROVE-DOMAINMARKOV10. PROVE-DOMAINMARKOV9 derived the stopped (Det) of Lemma G7, Lemma 7.6 and GB6 and
`RLC.FlowLocalityStatement` from Aux. lemma 54 for arbitrary stops (`StoppedExtend.StoppedHullExtendKStatement`). Its
§4.2: the proof route needs the stop to be a path functional (Galmarino). This file repeats the consumer side for
Galmarino stops (`StoppedExtendWF.StoppedHullExtendGKStatement`, which follows from the stopped whole-field
identification, `stoppedHullExtendGKStatement_of_jointLaw`):

* `IsStoppedFlowLineG`: PROVE-DOMAINMARKOV9's `IsStoppedFlowLine` with the stop `e = R(history killed at e)` for a
  measurable Galmarino rule `R`;
* `IsStoppedFlowLineG.ae_stopMatch_of_extendGK`: the stopped flow line matches a determination code on `[0, e]`;
* `IsStoppedFlowLineG.ae_codeMatch_le`, `ae_stoppedCodeMatch_of_ae_condExpKernelG`: the stopped (Det) clause with a
  canonical flow code, directly and under the regular conditional law (the clause of `RetainedCanonCondDetStatement`,
  `Lemma76DetStatement`, `GB6CondDetStatement`);
* `FlowLineStopIdentGStatement` (**named input**, (L1) with the exit time given as a Galmarino rule) and
  `flowLocalityStatement_of_stopIdentG`, `flowLocalityStatement_of_stopIdentG_jointLaw`: `RLC.FlowLocalityStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace StoppedExtendWF

open LawUnique StoppedExtend Sec2.Assembly Exist.Staged

/-! ### Stopped flow lines with a Galmarino stop -/

/-- **A flow line through a Galmarino stop `e`**: PROVE-DOMAINMARKOV9's `IsStoppedFlowLine`, with the stop almost
surely `R(history killed at e)` for a measurable Galmarino rule `R` of the flow-line word's killed histories. -/
def IsStoppedFlowLineG (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (e : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (R : HistorySpace (flowLineNL b jumps x) (flowLineNR b jumps x) → ℝ≥0∞),
    (∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsStoppedHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
      (flowLineRhoR κ b jumps x θ) P 𝓕 W VL VR B e h' ∧
    Measurable R ∧ IsHistGalmarino R ∧ (∀ᵐ ω ∂P, e ω = R (killedHistory W VL VR e ω)) ∧
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (e ω) (fun t => η ω t - x)

/-- Forgetting the rule. -/
theorem IsStoppedFlowLineG.isStoppedFlowLine {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {e : Ω → ℝ≥0∞} (hfl : IsStoppedFlowLineG κ b jumps x θ P h η e) : IsStoppedFlowLine κ b jumps x θ P h η e := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, htr, hSC, -, -, -, hgen⟩ := hfl
  exact ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen⟩

/-- **A stopped flow line through a Galmarino stop matches a determination code on `[0, e]`**, from Aux. lemma 54 for
Galmarino stops in kernel form and Theorem 1.3 (PROVE-DOMAINMARKOV9's `IsStoppedFlowLine.ae_stopMatch_of_extendK`). -/
theorem IsStoppedFlowLineG.ae_stopMatch_of_extendGK {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    (hext : StoppedHullExtendGKStatement.{u} κ) (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    {G : DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hdet : IsFlowDet.{u} κ b jumps x θ G)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {e : Ω → ℝ≥0∞}
    (hfl : IsStoppedFlowLineG κ b jumps x θ P h η e) :
    ∀ᵐ ω ∂P, IsStopMatch (G (h ω)) (η ω) (e ω) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, R, htr, hSC, hRm, hRg, hR, hgen⟩ := hfl
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    hext _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b jumps x) R hRm hRg P 𝓕 W VL VR B e h' hSC hR
  exact ae_of_ae_compProd_fst
    (ae_stopMatch_on_extension h13 hκ hdet htr hSC.1.ae_path hgen (Measure.fst_compProd P K) hC hag)

/-- **A stopped flow line through a Galmarino stop is the decoded canonical flow code on `[0, e]`** (Aux. lemma 54 for
Galmarino stops, Theorem 1.3, and a canonical flow code `F`, i.e. Theorem 1.2). No measurability is needed. -/
theorem IsStoppedFlowLineG.ae_codeMatch_le {κ θ : ℝ} (hext : StoppedHullExtendGKStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) (c : BoundaryWord) (x : ℝ) {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {e : Ω → ℝ≥0∞} (hfl : IsStoppedFlowLineG κ c.fn c.jumps x θ P h η e) :
    ∀ᵐ ω ∂P, e ω ≤ (F ((c, x), h ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → η ω t = decPath (F ((c, x), h ω)) t :=
  hfl.ae_stopMatch_of_extendGK (G := fun f => F ((c, x), f)) hext h13 hκ (IsCanonicalFlowCode.isFlowDet hF c x)

/-- **(Det) through a Galmarino stop, from stopped flow lines under the regular conditional law**
(PROVE-DOMAINMARKOV9's `ae_stoppedCodeMatch_of_ae_condExpKernel` with Galmarino stops): the stopped (Det) clause of
`RetainedCanonCondDetStatement`, `Lemma76DetStatement` and `GB6CondDetStatement`. -/
theorem ae_stoppedCodeMatch_of_ae_condExpKernelG {κ θ : ℝ} (hext : StoppedHullExtendGKStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord × ℝ} (hβ : Measurable[𝒢] β)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hH : Measurable Hc) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ t, Measurable fun ω => γ ω t) {e : Ω → ℝ≥0∞} (he : Measurable e)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ e ω})
    (hfl : ∀ᵐ ω₀ ∂P, ω₀ ∈ M →
      IsStoppedFlowLineG κ (β ω₀).1.fn (β ω₀).1.jumps (β ω₀).2 θ (condExpKernel P 𝒢 ω₀) Hc γ e) :
    ∀ᵐ ω ∂P, ω ∈ M → e ω ≤ (F (β ω, Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → γ ω t = decPath (F (β ω, Hc ω)) t := by
  set G : (BoundaryWord × ℝ) × Ω → (PCode × PCode) × ℝ≥0∞ := fun p => F (p.1, Hc p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (measurable_fst.prodMk (hH.comp measurable_snd))
  have hA : MeasurableSet (stopMatchSet G γ e) := measurableSet_stopMatchSet hGm hγ he
  have h : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (β ω₀, ω) ∈ stopMatchSet G γ e := by
    filter_upwards [hfl] with ω₀ hfl₀ hω₀
    have hd := (hfl₀ hω₀).ae_codeMatch_le hext h13 hκ hF (β ω₀).1 (β ω₀).2
    filter_upwards [hd] with ω hω
    exact ⟨hω.1, fun n k hnk => hω.2 _ hnk⟩
  filter_upwards [Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param h𝒢 hβ hA hM h] with ω hω hωM
  exact stopMatch_of_mem (G := G) (p := (β ω, ω)) (hγc ω) (hω hωM)

/-! ### Flow locality -/

/-- **Named input (L1) with a Galmarino stop**: PROVE-DOMAINMARKOV9's `FlowLineStopIdentStatement`, with the flow line
stopped at its exit time from `V` a stopped flow line of `Ĥ` through a Galmarino stop (`IsStoppedFlowLineG`): the exit
time is a measurable Galmarino rule of the killed driving history of the flow-line word of `(bR, Ĵ)`. -/
def FlowLineStopIdentGStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N → ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ →
      (∀ (x : S) (φ : TestOn upperHalfPlaneOpens), tsupport φ ⊆ N → Ĥ x φ = H₀ x φ) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      IsStoppedFlowLineG κ bR Ĵ y θ Q Ĥ Γ fun x => RLC.exitTime V (Γ x) (U x)

/-- The Galmarino form of (L1) gives PROVE-DOMAINMARKOV9's form. -/
theorem flowLineStopIdentStatement_of_G (hL1 : FlowLineStopIdentGStatement.{u}) :
    FlowLineStopIdentStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U hΓ
  exact (hL1 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U
    hΓ).isStoppedFlowLine

/-- **`RLC.FlowLocalityStatement` from (L1) with Galmarino stops and Aux. lemma 54 for Galmarino stops** (with
Theorems 1.2–1.3): PROVE-DOMAINMARKOV9's assembly `flowLocalityStatement_of_stopIdent`. -/
theorem flowLocalityStatement_of_stopIdentG (hL1 : FlowLineStopIdentGStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : RLC.FlowLocalityStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr
    Γ α U ζ hΓ hα
  have hs1 := hL1 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U hΓ
  have hs2 := hL1 κ hκ hκ4 bR b Ĵ J hbR hb O hO (fun z hz => (hbO z hz).symm) N hN hNO V hV hVb hVN y θ Q Q₀
    hQQ₀ hQ₀Q Ĥ H₀ hĤ hH₀ (fun z φ hφ => (hagr z φ hφ).symm) α ζ hα
  have m1 := hs1.ae_stopMatch_of_extendGK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ bR Ĵ y θ)
  have c1 := isFlowDet_flowDetCode h12p hκ bR Ĵ y θ Q Ĥ α ζ hα
  have m2 := hs2.ae_stopMatch_of_extendGK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ b J y θ)
  have c2 := isFlowDet_flowDetCode h12p hκ b J y θ Q₀ H₀ Γ U hΓ
  filter_upwards [hQ₀Q.ae_le m1, hQ₀Q.ae_le c1, m2, c2] with z e1 e2 e3 e4
  exact stoppedAgree_of_matches e1 e2 e3 e4

/-- **`RLC.FlowLocalityStatement` from (L1) with Galmarino stops and the stopped whole-field identification** for
`0 < κ < 4` (with Theorems 1.2–1.3). -/
theorem flowLocalityStatement_of_stopIdentG_jointLaw (hL1 : FlowLineStopIdentGStatement.{u})
    (hJL : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedJointLawStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : RLC.FlowLocalityStatement.{u} :=
  flowLocalityStatement_of_stopIdentG hL1
    (fun κ hκ hκ4 => stoppedHullExtendGKStatement_of_jointLaw hκ (hJL κ hκ hκ4)) h12p h13

/-! ### From the two remaining inputs of the whole-field route -/

/-- **Aux. lemma 54 for Galmarino stops (kernel form) from the continuation (U) and the stopped kernel (K)** (every
`κ > 0`). -/
theorem stoppedHullExtendGKStatement_of_inputs {κ : ℝ} (hκ : 0 < κ) (hC : StoppedContinuationStatement.{u} κ)
    (hK : StoppedKernelStatement.{u, u} κ) : StoppedHullExtendGKStatement.{u} κ :=
  stoppedHullExtendGKStatement_of_jointLaw hκ
    (stoppedJointLawStatement_of_histLaw_kernel (stoppedHistLawStatement_of_continuation hκ hC) hK)

/-- **`RLC.FlowLocalityStatement` from (L1) with Galmarino stops, the continuation and the stopped kernel** for
`0 < κ < 4` (with Theorems 1.2–1.3). -/
theorem flowLocalityStatement_of_inputs (hL1 : FlowLineStopIdentGStatement.{u})
    (hC : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedContinuationStatement.{u} κ)
    (hK : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedKernelStatement.{u, u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : RLC.FlowLocalityStatement.{u} :=
  flowLocalityStatement_of_stopIdentG hL1
    (fun κ hκ hκ4 => stoppedHullExtendGKStatement_of_inputs hκ (hC κ hκ hκ4) (hK κ hκ hκ4)) h12p h13

end StoppedExtendWF

end Restart

end InteractingSLE
