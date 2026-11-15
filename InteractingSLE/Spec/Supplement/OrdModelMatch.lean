/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelRule
import InteractingSLE.Spec.Supplement.OrdAStopWire
import InteractingSLE.Spec.Wire.RetMatchModel

/-!
# (Det) on models with an initial code and a code-dependent history rule (R79-safe)

Packet PROVE-T15-ASTOP2. PROVE-T15-ASTOP's consumer of models with an initial code
(`OrdAStop.StoppedTypeModelJ.ae_codeMatch`) takes the arbitrary-stop extension
`StoppedExtend.StoppedHullExtendStatement`,
which ruling R79 declares defective. This file gives the R79-safe consumer: PROVE-T15-MATCH's
`RetMatch.ae_codeMatch_of_model_historyRule` (stopped K2 on the product with the auxiliary Gaussian space, regular
conditional law given `filt 0`, then R79's `Aux54.stoppedHullExtendRStatement` through
`RetMatch.ae_codeMatch_of_regular_coupling`) for models whose driving stops read the code (PROVE-T15-ASTOP's
`isCondStopSeq_fst` replaces the kernel stops of the plain driving filtration) and whose lifetime is `R (code)` of the
killed history (`HasCodeHistoryRule`): under the conditional law given `filt 0` the code is almost surely its value at
the frozen sample (`OrdAStop.ae_map_condExpKernel_eq_dirac`), so the stop is the fixed rule `R (code ω₀)` there.

* **`ae_codeMatch_of_codeRule`** (on a model), `ae_codeMatch_of_stoppedModelTransferJ_rule`,
  **`ae_codeMatch_of_finite_stoppedModelsJ_rule`** (pull-back and finite gluing, as PROVE-T15-ASTOP's);
* `RLC.RetOrdStoppedModelsSndRStatement` (the second continuation's A-stopped models with their code rules) and
  **`RLC.retOrdDetSndStatement_of_stoppedModelsR`**: `RetOrdDetSndStatement` from it and Theorem 1.3 alone (no
  arbitrary-stop extension).

The proof of `ae_codeMatch_of_codeRule` repeats `RetMatch.ae_codeMatch_of_model_historyRule`'s (PROVE-T15-MATCH)
with the two changes above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.OrdModel

open Restart Restart.RetAux79 Restart.StoppedExtend Restart.StoppedExtendWF
open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79
open Restart.FCDet Restart.ConverseBefore LawUnique Sec2.Assembly Sec7.PocketTraversal OrdAStop

/-- **(Det) on a model with an initial code whose lifetime is a code-dependent Galmarino rule of its killed history.**
No arbitrary-stop extension hypothesis occurs. -/
theorem ae_codeMatch_of_codeRule {κ θ : ℝ} (M : StoppedTypeModelJ κ θ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) (hrule : HasCodeHistoryRule M) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t := by
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
  -- The driving stops read the code: kernel stops through the enlarged filtration (PROVE-T15-ASTOP).
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
  -- The rule identity, the generating trace and the frozen code pass under the conditional law.
  have hRν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) hR)
  have htrν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) D.generates)
  have hcodef : Measurable[(D.filt 0).comap Prod.fst] fun p : M.space × (ℕ → ℝ) => D.code p.1 :=
    D.codeMeas.comp (Measurable.of_comap_le le_rfl)
  have hdirac := ae_map_condExpKernel_eq_dirac (P := M.law.prod P₀) h𝒢f hcodef
  let γ : M.space × (ℕ → ℝ) → ℝ≥0 → ℂ := fun p => D.trace p.1
  let V : M.space × (ℕ → ℝ) → ℝ≥0∞ := fun p => D.life p.1
  let β : M.space × (ℕ → ℝ) → BoundaryWord × ℝ := fun p => (D.word p.1, 0)
  let G : (BoundaryWord × ℝ) × (M.space × (ℕ → ℝ)) → (PCode × PCode) × ℝ≥0∞ :=
    fun q => Fc (q.1, D.field q.2.1)
  have hGm : Measurable G := hFc.1.comp
    (measurable_fst.prodMk (D.fieldMeas.comp (measurable_fst.comp measurable_snd)))
  have hγm : ∀ t, Measurable fun p => γ p t := fun t => (D.traceMeas t).comp measurable_fst
  have hVm : Measurable V := (measurable_lifetime D.killedMeas).comp measurable_fst
  have hβm : Measurable[(D.filt 0).comap Prod.fst] β :=
    (D.wordMeas.comp (comap_measurable Prod.fst)).prodMk measurable_const
  have hcond : ∀ᵐ p₀ ∂(M.law.prod P₀), p₀.1 ∈ (univ : Set M.space) →
      ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        (β p₀, p) ∈ stopMatchSet G γ V := by
    filter_upwards [hK, hRν, htrν, hdirac, ae_fst_of_ae (P₀ := P₀) D.typed]
      with p₀ hK₀ hR₀ htr₀ hdir₀ htype₀ _
    obtain ⟨𝓕', W', VL', VR', B', hSC, hag, hfrz⟩ := hK₀ (mem_univ _)
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
        IsGeneratingTrace (fun t => W' t p) (V p) (γ p) := by
      filter_upwards [hag, htr₀] with p hp hgp
      exact StoppedK2.isGeneratingTrace_congr (fun t ht => ((hp t ht.le).1).symm) hgp
    have hd := Wire.RetMatch.ae_codeMatch_of_regular_coupling h13 hκ hFc
      ⟨D.xLAnti p₀.1, D.xLNonpos p₀.1, D.xRMono p₀.1, D.xRNonneg p₀.1⟩
      htype₀ (fun p => D.shifted p.1) hSC (hRm (D.code p₀.1)) (hRg (D.code p₀.1)) hRe
      (Aux54.isRegularStop_of_frozen hSC hfrz) hgen
    filter_upwards [hd] with p hp
    exact ⟨hp.1, fun n k hnk => hp.2 _ hnk⟩
  have hback := Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param
    h𝒢f hβm (measurableSet_stopMatchSet hGm hγm hVm)
    (F := Prod.fst ⁻¹' (univ : Set M.space)) ⟨univ, MeasurableSet.univ, rfl⟩ hcond
  have hall : ∀ᵐ p ∂(M.law.prod P₀), D.life p.1 ≤ (Fc ((D.word p.1, 0), D.field p.1)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.life p.1 →
        D.trace p.1 t = decPath (Fc ((D.word p.1, 0), D.field p.1)) t := by
    filter_upwards [hback] with p hp
    exact stopMatch_of_mem (G := G) (p := (β p, p)) (D.traceCont p.1) (hp (mem_univ _))
  exact ae_of_ae_fst (P₀ := P₀) hall

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Pull the match back from the conditional law of a type event** (models with codes and code rules). -/
theorem ae_codeMatch_of_stoppedModelTransferJ_rule [IsProbabilityMeasure P]
    {κ θ : ℝ} {F : Set Ω} {c : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransferJ κ θ P F c Hc V γ) (hF : MeasurableSet F) (hrule : HasCodeHistoryRule T.model)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hm := ae_codeMatch_of_codeRule T.model h13 hκ hFc hrule
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

/-- **Finitely many conditional models with codes and code rules suffice.** Null type events need no model. -/
theorem ae_codeMatch_of_finite_stoppedModelsJ_rule [IsProbabilityMeasure P]
    {κ θ : ℝ} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {F : Set Ω} {n : ℕ} {M : Fin n → Set Ω}
    (hM : ∀ i, MeasurableSet (M i))
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ i, ω ∈ M i)
    (hmodels : ∀ i, P (M i) ≠ 0 → ∃ T : StoppedModelTransferJ κ θ P (M i) c Hc V γ, HasCodeHistoryRule T.model)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
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
    · obtain ⟨T, hT⟩ := hmodels i hz
      exact ae_codeMatch_of_stoppedModelTransferJ_rule T (hM i) hT h13 hκ hFc
  filter_upwards [ae_all_iff.2 hi, hcover] with ω hω hc hωF
  obtain ⟨i, hi⟩ := hc hωF
  exact hω i hi

end InteractingSLE.RLC.OrdModel
