/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Supplement.OrdAStopK2

/-!
# The stopped (Det) with announcing stops that see a `𝒢`-measurable code

Packet PROVE-T15-ASTOP. The chain of `Restart.StoppedK2` (`StoppedK2Wire.lean`, PROVE-STOPPEDK2) from the stopped K2
to the stopped (Det) clause, with announcing stops `σₙ` of the killed driving filtration **enlarged at time `0` by a
`𝒢`-measurable real code `e`** (`OrdAStop.drivingSupCode`) instead of the killed driving filtration itself:

* `isCondStopSeq_fst`: such stops, read on the enlargement `Ω × Ω₀`, are announcing stops in transferred form there
  (the enlarged filtration pulls back: `supConst_fst`);
* `ae_isStoppedHullCoupling_k_prod_sup`, `ae_isStoppedFlowLine_k_prod_sup`, `ae_stoppedCodeMatch_of_k_sup`,
  **`ae_stoppedCodeMatch_of_hasSafeLaw_sup`**.

The A-stop of Theorem 1.5's leaf 3 is announced by a process reading the chart image of the retained union, which is
not a force coordinate in general; with this chain it may be read through a `𝒢`-measurable code.

Provenance: the four theorems are `Restart.StoppedK2.{ae_isStoppedHullCoupling_k_prod, ae_isStoppedFlowLine_k_prod,
ae_stoppedCodeMatch_of_k, ae_stoppedCodeMatch_of_hasSafeLaw}` verbatim, with the stopping-time hypothesis `hσ`
replaced by stopping times of `drivingSupCode` (and the code `e`, `he`, `hem`), and the inner call
`ae_isStoppedHullCoupling_k … (isStoppingTime_drivingFiltration_fst …)` replaced by
`ae_isStoppedHullCoupling_k_cond … (isCondStopSeq_fst …)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdAStop

open Restart Restart.StoppedK2 Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.ConverseBefore

/-! ### The enlarged filtration through the first projection -/

section Fst

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Ω₀ : Type*}
  [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

omit [StandardBorelSpace Ω] [StandardBorelSpace Ω₀] in
/-- The killed driving filtration of coordinates read through `fst`, enlarged by a code read through `fst`, is the
pulled-back enlarged filtration. -/
theorem supConst_fst (hXP : IsMeasurableKilledDriving W VL VR V)
    (hXf : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) (fun p => V p.1)) {e : Ω → ℝ} (hem : Measurable e)
    (hemf : Measurable fun p : Ω × Ω₀ => e p.1) :
    supConst (killedDrivingFiltration hXf) (MeasurableSpace.comap (fun p : Ω × Ω₀ => e p.1) inferInstance)
        hemf.comap_le =
      Coupling.filtrationFst (supConst (killedDrivingFiltration hXP) (MeasurableSpace.comap e inferInstance)
        hem.comap_le) Ω₀ := by
  ext t : 2
  show killedDrivingSigma _ _ _ _ t ⊔ _ = (killedDrivingSigma W VL VR V t ⊔ _).comap Prod.fst
  rw [killedDrivingSigma_fst, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  rfl

/-- **Announcing stops of the enlarged filtration, read on `Ω × Ω₀`, are announcing stops in transferred form for
the regular conditional law given `𝒢` read through `fst`.** -/
theorem isCondStopSeq_fst {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    (h𝒢 : 𝒢 ≤ mΩ) {e : Ω → ℝ} (he : Measurable[𝒢] e) (hem : Measurable e)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    (hXf : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) (fun p => V p.1))
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingSupCode P hXP hem) (σ n)) :
    IsCondStopSeq (𝒢.comap Prod.fst) (P.prod P₀) (fun t p => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) (fun p => V p.1) (fun n p => σ n p.1) := by
  have h𝒢f : 𝒢.comap Prod.fst ≤ (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
    (MeasurableSpace.comap_mono h𝒢).trans measurable_fst.comap_le
  have hef : Measurable[𝒢.comap Prod.fst] fun p : Ω × Ω₀ => e p.1 :=
    he.comp (Measurable.of_comap_le le_rfl)
  have hemf : Measurable fun p : Ω × Ω₀ => e p.1 := hem.comp measurable_fst
  refine isCondStopSeq_of_sup h𝒢f hef hXf fun n => ?_
  have hμ : (P.prod P₀).map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  intro t
  have h := Coupling.measurableSet_usualAugmentation_fst (X := Ω₀) hμ (hσ n t)
  rw [← supConst_fst hXP hXf hem hemf] at h
  exact h

end Fst

/-! ### The stopped K2 on the enlargement -/

section K2

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Ω₀ : Type*}
  [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω}
  {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}

/-- **The stopped K2 on the enlargement `Ω × Ω₀`** (`ae_isStoppedHullCoupling_k` on the product, as
`ConverseBefore.ae_isOptionalHullCoupling_k_prod` for K2): (E-stop) on the enlargement (as produced by
`isRandomWordEvolutionUpTo_prod`), the other inputs on `Ω`, read through the first projection. -/
theorem ae_isStoppedHullCoupling_k_prod_sup
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))} {B : ℝ≥0 → Ω × Ω₀ → ℝ}
    (hE : IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR 𝓕 (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B
      (fun p => V p.1))
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' V W) (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X) (hmem : HasSafeMembers P 𝓗' F V W X)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    {σ : ℕ → Ω → WithTop ℝ≥0} {e : Ω → ℝ} (he : Measurable[𝒢] e) (hem : Measurable e)
    (hσ : ∀ n, IsStoppingTime (drivingSupCode P hXP hem) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ F → Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω))) :
    ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))) (W' : ℝ≥0 → Ω × Ω₀ → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × Ω₀ → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × Ω₀ → ℝ) (B' : ℝ≥0 → Ω × Ω₀ → ℝ),
        StoppedExtend.IsStoppedHullCoupling κ (ΘL p₀.1) (ΘR p₀.1) ρL ρR
          (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀) 𝓕' W' VL' VR' B' (fun p => V p.1) (fun p => X p.1) ∧
        ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1 := by
  have hXf : IsMeasurableKilledDriving (fun t (p : Ω × Ω₀) => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) (fun p => V p.1) :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore
      (adaptedBefore_fst (Ω₀ := Ω₀) (Coupling.adaptedBefore_killedDriving_W hXP))
      (fun i => adaptedBefore_fst (Ω₀ := Ω₀) (Coupling.adaptedBefore_killedDriving_VL hXP i))
      (fun j => adaptedBefore_fst (Ω₀ := Ω₀) (Coupling.adaptedBefore_killedDriving_VR hXP j))
  exact ae_isStoppedHullCoupling_k_cond (𝒢 := 𝒢.comap Prod.fst) hE (ae_fst_of_ae (P₀ := P₀) hcont)
    (hX.comp measurable_fst) (ae_fst_of_ae (P₀ := P₀) hV0) (𝓗' := Coupling.filtrationComap 𝓗' measurable_fst)
    (MeasurableSpace.comap_mono h𝒢') (adaptedBefore_fst hW') (fun i => adaptedBefore_fst (hVL' i))
    (fun j => adaptedBefore_fst (hVR' j)) (hasSafeLaw_fst hlaw) (hasSafeMembers_fst hmem)
    (isCondStopSeq_fst (P₀ := P₀) (h𝒢'.trans (𝓗'.le 0)) he hem hXP hXf hσ)
    (fun p => hσm p.1)
    (ae_fst_of_ae (P₀ := P₀) hσV) (ae_fst_of_ae (P₀ := P₀) hσlim)


end K2

/-! ### The stopped (Det) -/

section Det

open StoppedExtend FCDet Sec2.Assembly Sec7.PocketTraversal

variable {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Ω₀ : Type}
  [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀] {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω}
  {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {X Hc : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord}
  {γ : Ω → ℝ≥0 → ℂ}

/-- **The stopped flow line under the regular conditional law** (the input `hfl` of DOMAINMARKOV9's lift
`StoppedExtend.ae_stoppedCodeMatch_of_ae_condExpKernel`, on the enlargement). In the setting of
`ae_isStoppedHullCoupling_k_prod`, if on `F` the word `(ΘL, ΘR, ρL, ρR)` is almost surely of the flow-line type of
`c` (`FCDet.IsFlowType`, path from `0`), the field is `X = Hc + θχ`, and the path `γ` is almost surely on `F` a
generating trace of `W` through `V`, then for almost every `p₀` with `p₀.1 ∈ F`, under the regular conditional law
given `𝒢` read through `fst`, `γ` read through `fst` is a stopped flow line of `Hc` read through `fst` through `V`. -/
theorem ae_isStoppedFlowLine_k_prod_sup
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))} {B : ℝ≥0 → Ω × Ω₀ → ℝ}
    (hE : IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR 𝓕 (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B
      (fun p => V p.1))
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' V W) (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X) (hmem : HasSafeMembers P 𝓗' F V W X)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    {σ : ℕ → Ω → WithTop ℝ≥0} {e : Ω → ℝ} (he : Measurable[𝒢] e) (hem : Measurable e)
    (hσ : ∀ n, IsStoppingTime (drivingSupCode P hXP hem) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ F → Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (htype : ∀ᵐ ω ∂P, ω ∈ F → IsFlowType κ θ (c ω) (ΘL ω) (ΘR ω) ρL ρR)
    (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (htr : ∀ᵐ ω ∂P, ω ∈ F → IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) (h𝒢m : 𝒢 ≤ mΩ) :
    ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ F →
      IsStoppedFlowLine κ (c p₀.1).fn (c p₀.1).jumps 0 θ (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀)
        (fun p => Hc p.1) (fun p => γ p.1) (fun p => V p.1) := by
  have h𝒢f : 𝒢.comap Prod.fst ≤ (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
    (MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le
  have htr' : ∀ᵐ p₀ ∂(P.prod P₀), ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀),
      p.1 ∈ F → IsGeneratingTrace (fun t => W t p.1) (V p.1) (γ p.1) :=
    Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢f (ae_fst_of_ae (P₀ := P₀) htr)
  have hFν := Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P.prod P₀) h𝒢f hE.2.1
  have hK := ae_isStoppedHullCoupling_k_prod_sup (P₀ := P₀) hE hcont hX hV0 h𝒢' hW' hVL' hVR' hlaw hmem hXP he hem
    hσ hσm
    hσV hσlim
  have htype' : ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ F → IsFlowType κ θ (c p₀.1) (ΘL p₀.1) (ΘR p₀.1) ρL ρR :=
    ae_fst_of_ae (P₀ := P₀) htype
  filter_upwards [hK, htr', htype', hFν] with p₀ hp₀ htr₀ hty₀ hF₀ hp₀F
  obtain ⟨𝓕', W', VL', VR', B', hcpl, hag⟩ := hp₀ hp₀F
  refine isStoppedFlowLine_of_isStoppedHullCoupling (hty₀ hp₀F) (fun p : Ω × Ω₀ => hXH p.1) hcpl ?_
  filter_upwards [hag, htr₀, hF₀ hp₀F] with p hp hgt hpF
  exact isGeneratingTrace_congr (fun t ht => ((hp t ht.le).1).symm) (hgt hpF)

/-- **The stopped (Det) clause from the stopped K2** (`ae_isStoppedFlowLine_k_prod` fed to DOMAINMARKOV9's lift
`StoppedExtend.ae_stoppedCodeMatch_of_ae_condExpKernel` on the enlargement, brought back to `Ω` by
`ConverseBefore.ae_of_ae_fst`): almost surely on `F`, the stop `V` comes before the lifetime of the canonical flow code
of `(c, Hc)` and `γ` is the decoded code on `[0, V]`. Aux. lemma 54 enters through DOMAINMARKOV9's lift, in the form
`StoppedExtend.StoppedHullExtendStatement` (see `planning/handoffs/PROVE-DOMAINMARKOV9.md` §4.2 on its form). -/
theorem ae_stoppedCodeMatch_of_k_sup (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0})
    (hκ : 0 < κ) {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc)
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))} {B : ℝ≥0 → Ω × Ω₀ → ℝ}
    (hE : IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR 𝓕 (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B
      (fun p => V p.1))
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' V W) (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X) (hmem : HasSafeMembers P 𝓗' F V W X)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    {σ : ℕ → Ω → WithTop ℝ≥0} {e : Ω → ℝ} (he : Measurable[𝒢] e) (hem : Measurable e)
    (hσ : ∀ n, IsStoppingTime (drivingSupCode P hXP hem) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ F → Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (htype : ∀ᵐ ω ∂P, ω ∈ F → IsFlowType κ θ (c ω) (ΘL ω) (ΘR ω) ρL ρR)
    (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (htr : ∀ᵐ ω ∂P, ω ∈ F → IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) (h𝒢m : 𝒢 ≤ mΩ)
    (hF : MeasurableSet[𝒢] F) (hc : Measurable[𝒢] c) (hH : Measurable Hc) (hγ : ∀ t, Measurable fun ω => γ ω t)
    (hVm : Measurable V) (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω}) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hfst : Measurable[𝒢.comap Prod.fst, 𝒢] (Prod.fst : Ω × Ω₀ → Ω) := Measurable.of_comap_le le_rfl
  have hfl := ae_isStoppedFlowLine_k_prod_sup (P₀ := P₀) hE hcont hX hV0 h𝒢' hW' hVL' hVR' hlaw hmem hXP he hem
    hσ hσm hσV
    hσlim htype hXH htr h𝒢m
  have h := ae_stoppedCodeMatch_of_ae_condExpKernel (Ω := Ω × Ω₀) (𝒢 := 𝒢.comap Prod.fst) (P := P.prod P₀)
    hext h13 hκ hFc ((MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le) (M := Prod.fst ⁻¹' F)
    ⟨F, hF, rfl⟩ (β := fun p => (c p.1, (0 : ℝ))) ((hc.comp hfst).prodMk measurable_const)
    (hH.comp measurable_fst) (fun t => (hγ t).comp measurable_fst) (hVm.comp measurable_fst) (fun p => hγc p.1) hfl
  exact ae_of_ae_fst (P₀ := P₀) (q := fun ω => ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t) h

end Det

section Generic

open StoppedExtend FCDet Sec2.Assembly Sec7.PocketTraversal

variable {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}


/-- **The stopped (Det) from (S) and (L), for a continuation read in a chart** (the stopped analogue of
`FCDet.ae_codeMatch_of_hasSafeLaw`). The continuation is a globally continuous adapted driver `W` from `0` with the
geometric images `geomLW W xL`, `geomRW W xR` of a sorted random word `(xL, xR)` of the flow-line type of
`c`, stopped at a stopping time `V` of `𝓗` with `0 < V ≤ thr` (the continuation threshold). The inputs:

* (S), (L) with lifetime `V` (`HasSafeLaw`, `HasSafeMembers`, live event `univ`) for `𝓗`;
* an announcing sequence `T` of `V` in the usual augmentation of `𝓗` (for (E-stop), through
  `isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun`), and nondecreasing stopping times `σₙ < V`, `σₙ → V`, of the
  driving filtration of the continuation killed at `V` (for the clauses at `τ ≤ V`);
* integrable pairings of the field `X = Hc + θχ`, a generating trace `γ` of `W` through `V`;
* Aux. lemma 54 (`StoppedHullExtendStatement`), Theorem 1.3 and a canonical flow code (through DOMAINMARKOV9's lift).

Then almost surely `V ≤ (Fc ((c, 0), Hc)).2` and `γ` is the decoded canonical code on `[0, V]`. -/
theorem ae_stoppedCodeMatch_of_hasSafeLaw_sup (hext : StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hFc : IsCanonicalFlowCode κ θ Fc)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) (htype : ∀ᵐ ω ∂P, IsFlowType κ θ (c ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {Hc X : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hX : Measurable X) (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    {V : Ω → ℝ≥0∞} (hVst : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) (hV0 : ∀ᵐ ω ∂P, 0 < V ω)
    (hVthr : ∀ᵐ ω ∂P, V ω ≤ thr ρL ρR W xL xR ω)
    {T : ℕ → Ω → ℝ≥0} (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P V T)
    (hXP : IsMeasurableKilledDriving W (geomLW W xL) (geomRW W xR) V)
    {σ : ℕ → Ω → WithTop ℝ≥0} {e : Ω → ℝ} (he : Measurable[𝒢] e) (hem : Measurable e)
    (hσ : ∀ n, IsStoppingTime (drivingSupCode P hXP hem) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ V W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ V W X) {γ : Ω → ℝ≥0 → ℂ} (hγ : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω})
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) :
    ∀ᵐ ω ∂P, V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hxL₀ : Measurable[𝓗 0] xL := hxL.mono h𝒢 le_rfl
  have hxR₀ : Measurable[𝓗 0] xR := hxR.mono h𝒢 le_rfl
  have hWa₀ : AdaptedBefore 𝓗 V W := MartChar.adaptedBefore_of_stronglyAdapted hVst hWa
  have hVLa₀ : ∀ i, AdaptedBefore 𝓗 V (geomLW W xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst (stronglyAdapted_geomLW hWa hWc hxL₀ i)
  have hVRa₀ : ∀ j, AdaptedBefore 𝓗 V (geomRW W xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst (stronglyAdapted_geomRW hWa hWc hxR₀ j)
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp hX
  have hcf := DomainMarkov.Aux79.isCouplingCharFun_of_hasSafeLaw X hXψ hlaw
    (ae_of_all _ (isForceReg_thr hW0 hWc xL xR V)) (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa₀ hVLa₀
    hVRa₀
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t =>
    (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have hVU : IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (V ω : WithTop ℝ≥0) := fun t =>
    Ito.le_usualAugmentation 𝓗 P t _ (hVst t)
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
    (𝒢 := 𝒢) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)) MeasurableSet.univ hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWaU
    hVU hT hint hcf (hVthr.mono fun ω h _ => h)
  have hVm : Measurable V := by
    refine measurable_of_Iic fun t => ?_
    induction t using ENNReal.recTopCoe with
    | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
    | coe t => exact 𝓗.le t _ (hVst t)
  have hcont : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (geomLW W xL i · ω) (Iic (V ω).toNNReal)) ∧
        ∀ j, ContinuousOn (geomRW W xR j · ω) (Iic (V ω).toNNReal) :=
    ae_of_all _ fun ω _ _ => ⟨(hWc ω).continuousOn, fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
      fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn⟩
  have h := ae_stoppedCodeMatch_of_k_sup (P₀ := P₀) (F := univ) (ΘL := xL) (ΘR := xR) hext h13 hκ hFc hE hcont hX
    (hV0.mono fun ω h _ => h) h𝒢 hWa₀ hVLa₀ hVRa₀ hlaw hmem hXP he hem hσ hσm (hσV.mono fun ω h _ => h)
    (hσlim.mono fun ω h _ => h) (htype.mono fun ω h _ => h) hXH (htr.mono fun ω h _ => h) h𝒢m MeasurableSet.univ
    hc hHc hγ hVm hγc
  filter_upwards [h] with ω hω using hω (mem_univ ω)

end Generic

end InteractingSLE.RLC.OrdAStop
