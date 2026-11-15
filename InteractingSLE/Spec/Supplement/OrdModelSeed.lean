/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelWire
import InteractingSLE.Spec.Supplement.OrdLateSeed

/-!
# Leaf 3's first continuation: seeded A-stopped models with codes (R79-safe), and leaf 3 from source inputs

Packet PROVE-T15-ASTOP2. The first continuation starts at the random seed `τ = tipPos` of the retained chart.
PROVE-T15-ORDDET4 showed that (Det) in the recentred chart does not give (Det) at the seed by itself (canonical codes
are pinned down only for fixed seeds), and put the seed into the model (`OrdLate.SeedModelTransfer`, a coordinate
measurable at time `0`) with the R79-safe consumer `OrdLate.ae_codeMatch_of_model_historyRule_seed`. This file does
the same for models with an initial code (the A-stop reads the A-set):

* `SeedModelTransferJ` and **`ae_codeMatch_of_codeRule_seed`** (PROVE-T15-ORDDET4's seeded consumer with the code:
  kernel stops through PROVE-T15-ASTOP's `isCondStopSeq_fst`, the code frozen under the conditional law),
  `ae_codeMatch_of_seedModelTransferJ`, `ae_codeMatch_of_finite_seedModelsJ`;
* `exists_seedModelTransferJ_rule_of_sourceInputs`: A-stopped source inputs of the recentred continuation with the seed
  as initial coordinate give a seeded model with its code rule;
* `RLC.RetOrdAStopSourceFstSeedStatement` (named source statement, **not proved**),
  `RLC.RetOrdStoppedModelsFstRStatement`,
  **`RLC.retOrdDetFstStatement_of_source`**;
* **`RLC.retOrdDetStatement_of_source`**: Theorem 1.5's leaf 3 (`RLC.RetOrdDetStatement`) from the two A-stopped source
  statements and Theorem 1.3 (no arbitrary-stop extension).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace RLC.OrdModel

open Restart Restart.RetAux79 Restart.StoppedExtend Restart.StoppedExtendWF
open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79
open Restart.FCDet Restart.ConverseBefore LawUnique Sec2.Assembly Sec7.PocketTraversal OrdAStop OrdLate

/-- **(Det) at a seed on a model with an initial code and a code rule** (PROVE-T15-ORDDET4's
`OrdLate.ae_codeMatch_of_model_historyRule_seed` for models with codes). -/
theorem ae_codeMatch_of_codeRule_seed {κ θ : ℝ} (M : StoppedTypeModelJ κ θ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) (hrule : HasCodeHistoryRule M)
    {s : M.space → ℝ} (hs : Measurable[M.data.filt 0] s) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s ω) (M.data.word ω), s ω),
        Exist.flowField (-s ω) 0 (M.data.field ω))).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t + s ω = decPath (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s ω) (M.data.word ω), s ω),
          Exist.flowField (-s ω) 0 (M.data.field ω))) t := by
  let _ := M.sigma
  let _ := M.borel
  let _ := M.probability
  let D := M.data
  obtain ⟨R, hRm, hRg, hR⟩ := hrule
  have h𝒢m : D.filt 0 ≤ M.sigma := D.filt.le 0
  have hWa : AdaptedBefore D.filt D.life D.driver :=
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop D.driverAdapted
  have hVLa : ∀ i, AdaptedBefore D.filt D.life (geomLW D.driver D.xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop
      (stronglyAdapted_geomLW D.driverAdapted D.driverCont D.xLMeas i)
  have hVRa : ∀ j, AdaptedBefore D.filt D.life (geomRW D.driver D.xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop
      (stronglyAdapted_geomRW D.driverAdapted D.driverCont D.xRMeas j)
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => D.shiftedField ω ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp D.shiftedMeas
  have hcf := isCouplingCharFun_of_hasSafeLaw D.shiftedField hXψ D.safeLaw
    (ae_of_all _ (isForceReg_thr D.driverZero D.driverCont D.xL D.xR D.life))
    (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa hVLa hVRa
  have hWaU : StronglyAdapted (usualAugmentation D.filt M.law) D.driver := fun t =>
    (D.driverAdapted t).mono (Ito.le_usualAugmentation D.filt M.law t)
  have hVU : IsStoppingTime (usualAugmentation D.filt M.law)
      fun ω => (D.life ω : WithTop ℝ≥0) := fun t =>
    Ito.le_usualAugmentation D.filt M.law t _ (D.lifeStop t)
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ :=
    StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
      (𝒢 := D.filt 0) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.le_usualAugmentation D.filt M.law 0) MeasurableSet.univ D.xLMeas D.xRMeas
      D.xLNonpos D.xRNonneg D.xLAnti D.xRMono D.driverZero D.driverCont hWaU
      hVU D.announcing D.integrable hcf (D.lifeThreshold.mono fun _ h _ => h)
  have hXf : IsMeasurableKilledDriving
      (fun t (p : M.space × (ℕ → ℝ)) => D.driver t p.1)
      (fun i t p => geomLW D.driver D.xL i t p.1)
      (fun j t p => geomRW D.driver D.xR j t p.1) (fun p => D.life p.1) :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore
      (adaptedBefore_fst (Ω₀ := ℕ → ℝ) (Coupling.adaptedBefore_killedDriving_W D.killedMeas))
      (fun i => adaptedBefore_fst (Coupling.adaptedBefore_killedDriving_VL D.killedMeas i))
      (fun j => adaptedBefore_fst (Coupling.adaptedBefore_killedDriving_VR D.killedMeas j))
  have h𝒢f : (D.filt 0).comap (Prod.fst : M.space × (ℕ → ℝ) → M.space) ≤
      (inferInstance : MeasurableSpace (M.space × (ℕ → ℝ))) :=
    (MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le
  have hcs := isCondStopSeq_fst (P := M.law) (P₀ := P₀) (Ω₀ := ℕ → ℝ) h𝒢m D.codeMeas
    (D.codeMeas.mono (D.filt.le 0) le_rfl) D.killedMeas hXf D.driveStopping
  have hT : ∀ n, Supp8.Q3Stop.IsKernelStop ((D.filt 0).comap Prod.fst)
      (M.law.prod P₀) (Prod.fst ⁻¹' (univ : Set M.space))
      (fun t p => D.driver t p.1) (fun i t p => geomLW D.driver D.xL i t p.1)
      (fun j t p => geomRW D.driver D.xR j t p.1) (fun p => D.life p.1)
      (fun p => D.driveStops n p.1) := fun n => by
    filter_upwards [hcs n] with p₀ h _ using h
  have hcont : ∀ᵐ ω ∂M.law, ω ∈ (univ : Set M.space) → D.life ω ≠ ⊤ →
      ContinuousOn (D.driver · ω) (Iic (D.life ω).toNNReal) ∧
        (∀ i, ContinuousOn (geomLW D.driver D.xL i · ω) (Iic (D.life ω).toNNReal)) ∧
        ∀ j, ContinuousOn (geomRW D.driver D.xR j · ω) (Iic (D.life ω).toNNReal) :=
    ae_of_all _ fun ω _ _ => ⟨(D.driverCont ω).continuousOn,
      fun i => (isForcePath_geomLW D.driverCont D.xL ω i).1.continuousOn,
      fun j => (isForcePath_geomRW D.driverCont D.xR ω j).1.continuousOn⟩
  have hK := Supp8.Q3Stop.ae_isStoppedHullCoupling_kk_prod (P₀ := P₀)
    (F := univ) (ΘL := D.xL) (ΘR := D.xR) hE hcont D.shiftedMeas
    (D.lifePos.mono fun _ h _ => h) le_rfl hWa hVLa hVRa D.safeLaw D.safeMembers
    hT (fun p => D.driveMono p.1)
    ((ae_fst_of_ae (P₀ := P₀) D.driveLt).mono fun _ h _ => h)
    ((ae_fst_of_ae (P₀ := P₀) D.driveLimit).mono fun _ h _ => h)
  have hRν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) hR)
  have htrν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) D.generates)
  have hcodef : Measurable[(D.filt 0).comap Prod.fst] fun p : M.space × (ℕ → ℝ) => D.code p.1 :=
    D.codeMeas.comp (Measurable.of_comap_le le_rfl)
  have hdirac := ae_map_condExpKernel_eq_dirac (P := M.law.prod P₀) h𝒢f hcodef
  let η : M.space × (ℕ → ℝ) → ℝ≥0 → ℂ := fun p => D.trace p.1
  let V : M.space × (ℕ → ℝ) → ℝ≥0∞ := fun p => D.life p.1
  let β : M.space × (ℕ → ℝ) → BoundaryWord × ℝ := fun p =>
    (Exist.StagedLaw.BoundaryWord.shiftW (-s p.1) (D.word p.1), s p.1)
  let G : (BoundaryWord × ℝ) × (M.space × (ℕ → ℝ)) → (PCode × PCode) × ℝ≥0∞ :=
    fun q => Fc (q.1, Exist.flowField (-q.1.2) 0 (D.field q.2.1))
  have hGm : Measurable G := measurable_seedCode (D.fieldMeas.comp measurable_fst) hFc.1
  have hηm : ∀ t, Measurable fun p => η p t := fun t => (D.traceMeas t).comp measurable_fst
  have hVm : Measurable V := (measurable_lifetime D.killedMeas).comp measurable_fst
  have hsf : Measurable[(D.filt 0).comap Prod.fst] fun p : M.space × (ℕ → ℝ) => s p.1 :=
    hs.comp (comap_measurable Prod.fst)
  have hβm : Measurable[(D.filt 0).comap Prod.fst] β :=
    (Exist.StagedLaw.BoundaryWord.measurable_shiftW.comp
      (hsf.neg.prodMk (D.wordMeas.comp (comap_measurable Prod.fst)))).prodMk hsf
  have hcond : ∀ᵐ p₀ ∂(M.law.prod P₀), p₀.1 ∈ (univ : Set M.space) →
      ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        (β p₀, p) ∈ seedMatchSet G η V := by
    filter_upwards [hK, hRν, htrν, hdirac, ae_fst_of_ae (P₀ := P₀) D.typed]
      with p₀ hK₀ hR₀ htr₀ hdir₀ htype₀ _
    obtain ⟨𝓕', W', VL', VR', B', hSC, hag, hfrz⟩ := hK₀ (mem_univ _)
    have htypeX : IsFlowTypeAt κ θ (Exist.StagedLaw.BoundaryWord.shiftW (-s p₀.1) (D.word p₀.1)) (s p₀.1)
        (D.xL p₀.1) (D.xR p₀.1) D.rhoL D.rhoR := by
      refine isFlowTypeAt_of_shiftW ?_
      rw [shiftW_shiftW_neg]
      exact htype₀
    have hcode₀ : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        D.code p.1 = D.code p₀.1 := by
      have hm : Measurable fun p : M.space × (ℕ → ℝ) => D.code p.1 := hcodef.mono h𝒢f le_rfl
      have h1 : ∀ᵐ x ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀).map
          (fun p : M.space × (ℕ → ℝ) => D.code p.1), x = D.code p₀.1 := by
        rw [hdir₀]
        exact (ae_dirac_iff (measurableSet_singleton _)).2 rfl
      exact (ae_map_iff hm.aemeasurable (measurableSet_singleton _)).1 h1
    have hRe : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        V p = R (D.code p₀.1) (killedHistory W' VL' VR' V p) := by
      filter_upwards [hag, hR₀, hcode₀] with p hp hRp hcp
      have he : Exist.AgreeBefore
          (fun t (p : M.space × (ℕ → ℝ)) => D.driver t p.1) W'
          (fun i t p => geomLW D.driver D.xL i t p.1) VL'
          (fun j t p => geomRW D.driver D.xR j t p.1) VR' V V p :=
        ⟨rfl, fun t ht => ⟨(hp t ht.le).1,
          fun i => (hp t ht.le).2.1 i, fun j => (hp t ht.le).2.2 j⟩⟩
      rw [Exist.killedHistory_eq_of_agreeBefore he, ← hcp]
      exact hRp
    have hgen : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        IsGeneratingTrace (fun t => W' t p) (V p) (fun t => (η p t + s p₀.1) - s p₀.1) := by
      filter_upwards [hag, htr₀] with p hp hgp
      simp only [add_sub_cancel_right]
      exact StoppedK2.isGeneratingTrace_congr (fun t ht => ((hp t ht.le).1).symm) hgp
    have hd := ae_codeMatch_of_regular_coupling_seed h13 hκ hFc
      ⟨D.xLAnti p₀.1, D.xLNonpos p₀.1, D.xRMono p₀.1, D.xRNonneg p₀.1⟩
      htypeX (Hc := fun p => Exist.flowField (-s p₀.1) 0 (D.field p.1))
      (fun p => isTranslateAddConst_flowField_neg (D.shifted p.1)) hSC (hRm (D.code p₀.1)) (hRg (D.code p₀.1))
      hRe (Aux54.isRegularStop_of_frozen hSC hfrz) (γ := fun p t => η p t + s p₀.1) hgen
    filter_upwards [hd] with p hp
    exact ⟨hp.1, fun n k hnk => hp.2 _ hnk⟩
  have hback := Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param
    h𝒢f hβm (measurableSet_seedMatchSet hGm hηm hVm)
    (F := Prod.fst ⁻¹' (univ : Set M.space)) ⟨univ, MeasurableSet.univ, rfl⟩ hcond
  have hall : ∀ᵐ p ∂(M.law.prod P₀),
      D.life p.1 ≤ (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s p.1) (D.word p.1), s p.1),
        Exist.flowField (-s p.1) 0 (D.field p.1))).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.life p.1 →
        D.trace p.1 t + s p.1 = decPath (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s p.1) (D.word p.1), s p.1),
          Exist.flowField (-s p.1) 0 (D.field p.1))) t := by
    filter_upwards [hback] with p hp
    exact seedMatch_of_mem (G := G) (p := (β p, p)) (D.traceCont p.1) (hp (mem_univ _))
  exact ae_of_ae_fst (P₀ := P₀) hall

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A seeded stopped model with an initial code** (PROVE-T15-ORDDET4's `OrdLate.SeedModelTransfer` with a
`StoppedTypeModelJ`): on `F` the model reads `shiftW τ c`, `flowField τ 0 Hc`, the seed `τ` (a coordinate measurable
at time `0`), the stop `V` and the path `γ − τ` on `[0, V]`. -/
structure SeedModelTransferJ (κ θ : ℝ) (P : Measure Ω) (F : Set Ω) (c : Ω → BoundaryWord) (τ : Ω → ℝ)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (V : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) where
  model : StoppedTypeModelJ κ θ
  seed : model.space → ℝ
  seedMeas : Measurable[model.data.filt 0] seed
  read : Ω → model.space
  readMeas : @Measurable Ω model.space mΩ model.sigma read
  mapLaw : (P[|F]).map read = model.law
  agrees : ∀ᵐ ω ∂P, ω ∈ F →
    model.data.word (read ω) = Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (c ω) ∧
      model.data.field (read ω) = Exist.flowField (τ ω) 0 (Hc ω) ∧ seed (read ω) = τ ω ∧
      model.data.life (read ω) = V ω ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → model.data.trace (read ω) t + τ ω = γ ω t

/-- **(Det) at a random seed from a seeded model with a code rule.** -/
theorem ae_codeMatch_of_seedModelTransferJ [IsProbabilityMeasure P] {κ θ : ℝ} {F : Set Ω}
    {c : Ω → BoundaryWord} {τ : Ω → ℝ} {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞}
    {γ : Ω → ℝ≥0 → ℂ} (T : SeedModelTransferJ κ θ P F c τ Hc V γ) (hF : MeasurableSet F)
    (hrule : HasCodeHistoryRule T.model) (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, τ ω), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, τ ω), Hc ω)) t := by
  let _ := T.model.sigma
  have hm := ae_codeMatch_of_codeRule_seed T.model h13 hκ hFc hrule T.seedMeas
  have hm' := (congrArg (fun μ : Measure T.model.space => ae μ) T.mapLaw).symm ▸ hm
  have hp := FCDet.ae_imp_of_ae_cond hF (ae_of_ae_map T.readMeas.aemeasurable hm')
  filter_upwards [hp, T.agrees] with ω hω he hωF
  obtain ⟨ec, eH, es, eV, eγ⟩ := he hωF
  obtain ⟨hV, hγ⟩ := hω hωF
  rw [ec, eH, es, eV, shiftW_neg_shiftW, flowField_neg_flowField] at hV hγ
  refine ⟨hV, fun t ht => ?_⟩
  rw [← eγ t ht, ← hγ t ht]

/-- Finitely many seeded models with codes and code rules suffice; null type events need no model. -/
theorem ae_codeMatch_of_finite_seedModelsJ [IsProbabilityMeasure P] {κ θ : ℝ}
    {c : Ω → BoundaryWord} {τ : Ω → ℝ} {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞}
    {γ : Ω → ℝ≥0 → ℂ} {F : Set Ω} {n : ℕ} {M : Fin n → Set Ω} (hM : ∀ i, MeasurableSet (M i))
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ i, ω ∈ M i)
    (hmodels : ∀ i, P (M i) ≠ 0 → ∃ T : SeedModelTransferJ κ θ P (M i) c τ Hc V γ, HasCodeHistoryRule T.model)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, τ ω), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, τ ω), Hc ω)) t := by
  have hi : ∀ i : Fin n, ∀ᵐ ω ∂P, ω ∈ M i → V ω ≤ (Fc ((c ω, τ ω), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, τ ω), Hc ω)) t := by
    intro i
    by_cases hz : P (M i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω hωM
      exact (hω hωM).elim
    · obtain ⟨T, hT⟩ := hmodels i hz
      exact ae_codeMatch_of_seedModelTransferJ T (hM i) hT h13 hκ hFc
  filter_upwards [ae_all_iff.2 hi, hcover] with ω hω hc hωF
  obtain ⟨i, hi⟩ := hc hωF
  exact hω i hi

/-- **A seeded model with its code rule from source inputs of the recentred continuation** (the seed is the source's
initial coordinate `Sd = τ`). -/
theorem exists_seedModelTransferJ_rule_of_sourceInputs [IsProbabilityMeasure P] {κ θ : ℝ} {M : Set Ω}
    {c : Ω → BoundaryWord} {τ : Ω → ℝ} {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞}
    {γ : Ω → ℝ≥0 → ℂ}
    (h : AStopSourceInputs κ θ P M τ (fun ω => Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (c ω))
      (fun ω => Exist.flowField (τ ω) 0 (Hc ω)) V (fun ω t => γ ω t - τ ω)) (hPM : P M ≠ 0) :
    ∃ T : SeedModelTransferJ κ θ P M c τ Hc V γ, HasCodeHistoryRule T.model := by
  obtain ⟨T, hT, seed, hseed, hread⟩ := exists_stoppedModelTransferJ_rule_of_sourceInputs h hPM
  refine ⟨{
    model := T.model
    seed := seed
    seedMeas := hseed
    read := T.read
    readMeas := T.readMeas
    mapLaw := T.mapLaw
    agrees := ?_ }, hT⟩
  filter_upwards [T.agrees] with ω hω hωM
  obtain ⟨ec, eH, eV, eγ⟩ := hω hωM
  refine ⟨ec, eH, hread ω, eV, fun t ht => ?_⟩
  rw [eγ t ht, sub_add_cancel]

end RLC.OrdModel

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F OrdAStop OrdModel

universe u

/-- **Source inputs of the A-stopped first continuation at its seed** (the remaining construction for the first
continuation, R79-safe): with the binders of `RetOrdStoppedModelsSndStatement`, finitely many measurable events cover
the ordinary pairs almost surely, and on each with positive probability the first continuation recentred at the seed
`(β ω).2` has A-stopped source inputs with the seed as initial coordinate: word `shiftW (β ω).2 (β ω).1`, field
`flowField (β ω).2 0` of the chart field, the canonical retained lifetime of `η₁` read from `tipPos` and the path
`canonRetPath … (tipPos) − (β ω).2`. **Not proved in Lean.** -/
def RetOrdAStopSourceFstSeedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → AStopSourceInputs κ θ₁ P (M i) (fun ω => (β ω).2)
        (fun ω => Exist.StagedLaw.BoundaryWord.shiftW (β ω).2 (β ω).1)
        (fun ω => Exist.flowField (β ω).2 0 (hd.chartField κ h ω))
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω))
        (fun ω t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) t - (β ω).2)

/-- **Seeded A-stopped models of the first continuation with their code rules** (R79-safe). -/
def RetOrdStoppedModelsFstRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → ∃ T : SeedModelTransferJ κ θ₁ P (M i) (fun ω => (β ω).1) (fun ω => (β ω).2)
        (hd.chartField κ h)
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω))
        (fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω)),
        HasCodeHistoryRule T.model

/-- The seeded R79-safe model statement from source inputs. -/
theorem retOrdStoppedModelsFstRStatement_of_source (hsrc : RetOrdAStopSourceFstSeedStatement.{u}) :
    RetOrdStoppedModelsFstRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hsource⟩ := hsrc κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ⟨n, M, hM, hcover, fun i hi => exists_seedModelTransferJ_rule_of_sourceInputs (hsource i hi) hi⟩

/-- **(Det) for the first continuation from seeded A-stopped models with code rules and Theorem 1.3.** -/
theorem retOrdDetFstStatement_of_stoppedModelsR (h13 : Exist.Theorem13Statement.{0})
    (hmodels : RetOrdStoppedModelsFstRStatement.{u}) : RetOrdDetFstStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₁ hF₁ u₀ hu₀
    β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hmodel⟩ := hmodels κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ae_codeMatch_of_finite_seedModelsJ
    (F := {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r}) hM hcover hmodel h13 hκ hF₁

/-- **(Det) for the first continuation from its seeded A-stopped source inputs and Theorem 1.3.** -/
theorem retOrdDetFstStatement_of_source (h13 : Exist.Theorem13Statement.{0})
    (hsrc : RetOrdAStopSourceFstSeedStatement.{u}) : RetOrdDetFstStatement.{u} :=
  retOrdDetFstStatement_of_stoppedModelsR h13 (retOrdStoppedModelsFstRStatement_of_source hsrc)

/-- **Theorem 1.5's leaf 3 from the two A-stopped source statements and Theorem 1.3** (R79-safe: no arbitrary-stop
extension). -/
theorem retOrdDetStatement_of_source (h13 : Exist.Theorem13Statement.{0})
    (hfst : RetOrdAStopSourceFstSeedStatement.{u}) (hsnd : RetOrdAStopSourceSndStatement.{u}) :
    RetOrdDetStatement.{u} :=
  retOrdDetStatement_of_fst_snd (retOrdDetFstStatement_of_source h13 hfst) (retOrdDetSndStatement_of_source h13 hsnd)

end RLC

end InteractingSLE
