/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofAssembly
import InteractingSLE.Spec.Supplement.OrdAStopWire

/-!
# Stopped models whose announcing stops read an initial code

Packet PROVE-T15-ASTOP. PROVE-RETPLUMB's typed stopped models (`RetAux79.StoppedTypeData`, `StoppedTypeModel`,
`StoppedModelTransfer`) ask for driving stops in the killed driving filtration. For the A-stop of Theorem 1.5's leaf 3
(first new contact with the retained union only, Lemma G7) they must be allowed to read the chart image of the
retained union, which is an initial datum but not a force coordinate in general. Here:

* `StoppedTypeDataJ`: `StoppedTypeData` with an initial real code `code` (`filt 0`-measurable) and driving stops of
  the killed driving filtration enlarged by `code` (`OrdAStop.drivingSupCode`);
* `StoppedTypeData.toJ`: every landed model is one (constant code);
* `StoppedTypeModelJ.ae_codeMatch`: the stopped (Det) on the model (`ae_stoppedCodeMatch_of_hasSafeLaw_sup`);
* `StoppedModelTransferJ`, `ae_codeMatch_of_stoppedModelTransferJ`, **`ae_codeMatch_of_finite_stoppedModelsJ`**:
  pull-back from the conditional law of a type event and finite gluing (as PROVE-RETPLUMB's
  `ae_codeMatch_of_stoppedModelTransfer`, `ae_codeMatch_of_finite_stoppedModels`, whose proofs are repeated).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdAStop

open LQGMetric (DistOn TestOn)
open Sec2.Assembly Sec7.PocketTraversal
open Restart Restart.RetAux79 Supp7 Sec7.Lemma76F
open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 Restart.FCDet Restart.StoppedExtend

/-- **Typed stopped-K2 inputs with an initial code**: `RetAux79.StoppedTypeData` whose driving stops are stopping
times of the killed driving filtration enlarged at time `0` by the `filt 0`-measurable code `code`. -/
structure StoppedTypeDataJ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (κ θ : ℝ) where
  nL : ℕ
  nR : ℕ
  rhoL : Fin nL → ℝ
  rhoR : Fin nR → ℝ
  filt : Filtration ℝ≥0 mΩ
  word : Ω → BoundaryWord
  wordMeas : Measurable[filt 0] word
  xL : Ω → Fin nL → ℝ
  xR : Ω → Fin nR → ℝ
  xLMeas : Measurable[filt 0] xL
  xRMeas : Measurable[filt 0] xR
  xLNonpos : ∀ ω i, xL ω i ≤ 0
  xRNonneg : ∀ ω j, 0 ≤ xR ω j
  xLAnti : ∀ ω, Antitone (xL ω)
  xRMono : ∀ ω, Monotone (xR ω)
  typed : ∀ᵐ ω ∂P, IsFlowType κ θ (word ω) (xL ω) (xR ω) rhoL rhoR
  driver : ℝ≥0 → Ω → ℝ
  driverZero : ∀ ω, driver 0 ω = 0
  driverCont : ∀ ω, Continuous fun t => driver t ω
  driverAdapted : StronglyAdapted filt driver
  field : Ω → DistOn upperHalfPlaneOpens
  shiftedField : Ω → DistOn upperHalfPlaneOpens
  fieldMeas : Measurable field
  shiftedMeas : Measurable shiftedField
  shifted : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (field ω) (shiftedField ω)
  integrable : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => shiftedField ω φ) P
  life : Ω → ℝ≥0∞
  lifeStop : ∀ t : ℝ≥0, MeasurableSet[filt t] {ω | life ω ≤ t}
  lifePos : ∀ᵐ ω ∂P, 0 < life ω
  lifeThreshold : ∀ᵐ ω ∂P, life ω ≤ thr rhoL rhoR driver xL xR ω
  announce : ℕ → Ω → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq (usualAugmentation filt P) P life announce
  killedMeas : IsMeasurableKilledDriving driver (geomLW driver xL) (geomRW driver xR) life
  driveStops : ℕ → Ω → WithTop ℝ≥0
  code : Ω → ℝ
  codeMeas : Measurable[filt 0] code
  driveStopping : ∀ n, IsStoppingTime (drivingSupCode P killedMeas (codeMeas.mono (filt.le 0) le_rfl))
    (driveStops n)
  driveMono : ∀ ω, Monotone fun n => driveStops n ω
  driveLt : ∀ᵐ ω ∂P, ∀ n, (driveStops n ω : ℝ≥0∞) < life ω
  driveLimit : ∀ᵐ ω ∂P, Tendsto (fun n => (driveStops n ω : ℝ≥0∞)) atTop (𝓝 (life ω))
  safeLaw : HasSafeLaw κ rhoL rhoR P filt univ life driver
    (geomLW driver xL) (geomRW driver xR) shiftedField
  safeMembers : HasSafeMembers P filt univ life driver shiftedField
  trace : Ω → ℝ≥0 → ℂ
  traceMeas : ∀ t, Measurable fun ω => trace ω t
  traceCont : ∀ ω, ContinuousOn (trace ω) {t | (t : ℝ≥0∞) ≤ life ω}
  generates : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => driver t ω) (life ω) (trace ω)

/-- A standard Borel probability model with the typed stopped-K2 inputs and an initial code. -/
structure StoppedTypeModelJ (κ θ : ℝ) where
  space : Type
  sigma : MeasurableSpace space
  borel : @StandardBorelSpace space sigma
  law : @Measure space sigma
  probability : @IsProbabilityMeasure space sigma law
  data : @StoppedTypeDataJ space sigma law κ θ

instance StoppedTypeModelJ.measurableSpace {κ θ : ℝ} (M : StoppedTypeModelJ κ θ) :
    MeasurableSpace M.space := M.sigma

/-- **The stopped K2 on a model with an initial code.** -/
theorem StoppedTypeModelJ.ae_codeMatch {κ θ : ℝ} (M : StoppedTypeModelJ κ θ)
    (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t := by
  let _ := M.sigma
  let _ := M.borel
  let _ := M.probability
  exact ae_stoppedCodeMatch_of_hasSafeLaw_sup hext h13 hκ hFc le_rfl
    M.data.wordMeas M.data.xLMeas M.data.xRMeas M.data.xLNonpos M.data.xRNonneg
    M.data.xLAnti M.data.xRMono M.data.typed M.data.driverZero M.data.driverCont
    M.data.driverAdapted M.data.fieldMeas M.data.shiftedMeas M.data.shifted M.data.integrable
    M.data.lifeStop M.data.lifePos M.data.lifeThreshold M.data.announcing M.data.killedMeas
    M.data.codeMeas (M.data.codeMeas.mono (M.data.filt.le 0) le_rfl)
    M.data.driveStopping M.data.driveMono M.data.driveLt M.data.driveLimit
    M.data.safeLaw M.data.safeMembers M.data.traceMeas M.data.traceCont M.data.generates

/-- **Every landed typed model is a model with an initial code** (the constant code `0`). -/
def StoppedTypeData.toJ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ}
    (D : StoppedTypeData Ω P κ θ) : StoppedTypeDataJ Ω P κ θ :=
  { D with
    code := fun _ => 0
    codeMeas := measurable_const
    driveStopping := fun n t => drivingFiltration_le_drivingSupCode P D.killedMeas measurable_const t _
      (D.driveStopping n t) }

/-- The landed typed models embed. -/
def StoppedTypeModel.toJ {κ θ : ℝ} (M : StoppedTypeModel κ θ) : StoppedTypeModelJ κ θ :=
  { space := M.space, sigma := M.sigma, borel := M.borel, law := M.law, probability := M.probability,
    data := @StoppedTypeData.toJ M.space M.sigma M.law κ θ M.data }

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Law transport of a type event to a model with an initial code** (`RetAux79.StoppedModelTransfer` with a
`StoppedTypeModelJ`). -/
structure StoppedModelTransferJ (κ θ : ℝ) (P : Measure Ω) (F : Set Ω)
    (c : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (V : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) where
  model : StoppedTypeModelJ κ θ
  read : Ω → model.space
  readMeas : @Measurable Ω model.space mΩ model.sigma read
  mapLaw : (P[|F]).map read = model.law
  agrees : ∀ᵐ ω ∂P, ω ∈ F →
    model.data.word (read ω) = c ω ∧ model.data.field (read ω) = Hc ω ∧
      model.data.life (read ω) = V ω ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → model.data.trace (read ω) t = γ ω t

/-- The landed law transports embed. -/
def StoppedModelTransfer.toJ {κ θ : ℝ} {F : Set Ω} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (T : StoppedModelTransfer κ θ P F c Hc V γ) :
    StoppedModelTransferJ κ θ P F c Hc V γ :=
  { model := StoppedTypeModel.toJ T.model, read := T.read, readMeas := T.readMeas, mapLaw := T.mapLaw,
    agrees := T.agrees }

/-- **Pull the stopped-K2 match back from the conditional law of a type event** (models with an initial code). -/
theorem ae_codeMatch_of_stoppedModelTransferJ [IsProbabilityMeasure P]
    {κ θ : ℝ} {F : Set Ω} {c : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransferJ κ θ P F c Hc V γ) (hF : MeasurableSet F)
    (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hm := T.model.ae_codeMatch hext h13 hκ hFc
  have hm' : ∀ᵐ ω ∂(P[|F]).map T.read,
      T.model.data.life ω ≤ (Fc ((T.model.data.word ω, 0), T.model.data.field ω)).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T.model.data.life ω →
          T.model.data.trace ω t = decPath (Fc ((T.model.data.word ω, 0), T.model.data.field ω)) t :=
    (congrArg (fun μ : Measure T.model.space => ae μ) T.mapLaw).symm ▸ hm
  have hp := FCDet.ae_imp_of_ae_cond hF (ae_of_ae_map T.readMeas.aemeasurable hm')
  filter_upwards [hp, T.agrees] with ω hω he hωF
  obtain ⟨ec, eH, eV, eγ⟩ := he hωF
  obtain ⟨hV, hγ⟩ := hω hωF
  rw [ec, eH, eV] at hV hγ
  exact ⟨hV, fun t ht => (eγ t ht).symm.trans (hγ t ht)⟩

/-- **Finitely many conditional models with initial codes suffice.** Null type events need no model. -/
theorem ae_codeMatch_of_finite_stoppedModelsJ [IsProbabilityMeasure P]
    {κ θ : ℝ} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {F : Set Ω} {n : ℕ} {M : Fin n → Set Ω}
    (hM : ∀ i, MeasurableSet (M i))
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ i, ω ∈ M i)
    (hmodels : ∀ i, P (M i) ≠ 0 → Nonempty (StoppedModelTransferJ κ θ P (M i) c Hc V γ))
    (hext : StoppedHullExtendStatement.{0} κ) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hi : ∀ i : Fin n, ∀ᵐ ω ∂P, ω ∈ M i → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
    intro i
    by_cases hz : P (M i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω hωM
      exact (hω hωM).elim
    · obtain ⟨T⟩ := hmodels i hz
      exact ae_codeMatch_of_stoppedModelTransferJ T (hM i) hext h13 hκ hFc
  filter_upwards [ae_all_iff.2 hi, hcover] with ω hω hc hωF
  obtain ⟨i, hi⟩ := hc hωF
  exact hω i hi

end InteractingSLE.RLC.OrdAStop
