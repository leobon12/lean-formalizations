/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchRegular
import InteractingSLE.Spec.Restart.RetPlumbProofAssembly
import InteractingSLE.Spec.Supplement.Q3StopK2

/-!
# The stopped model consumer with an explicit history rule

The model's two announcing sequences supply stopped K2. Its frozen conditional
driver supplies R79 regularity. A measurable Galmarino rule identifying the
model's lifetime is an additional, explicit hypothesis of this helper; this
file does not assert that every `StoppedTypeModel` supplies one.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Wire.RetMatch

open Restart Restart.RetAux79 Restart.StoppedExtend Restart.StoppedExtendWF
open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79
open Restart.FCDet Restart.ConverseBefore LawUnique Sec2.Assembly Sec7.PocketTraversal

/-- The stopped model has the canonical trace through its closed lifetime if
its stop is given by a measurable Galmarino history rule. No arbitrary-stop
extension hypothesis occurs. -/
theorem ae_codeMatch_of_model_historyRule {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc)
    {R : HistorySpace M.data.nL M.data.nR → ℝ≥0∞}
    (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hR : ∀ᵐ ω ∂M.law, M.data.life ω = R (killedHistory M.data.driver
      (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR) M.data.life ω)) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t := by
  let _ := M.sigma
  let _ := M.borel
  let _ := M.probability
  let D := M.data
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
  -- The existing driving-filtration announcements give kernel stops on the product.
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
  have hT : ∀ n, Supp8.Q3Stop.IsKernelStop ((D.filt 0).comap Prod.fst)
      (M.law.prod P₀) (Prod.fst ⁻¹' (univ : Set M.space))
      (fun t p => D.driver t p.1) (fun i t p => geomLW D.driver D.xL i t p.1)
      (fun j t p => geomRW D.driver D.xR j t p.1) (fun p => D.life p.1)
      (fun p => D.driveStops n p.1) := fun n =>
    Supp8.Q3Stop.isKernelStop_of_isStoppingTime h𝒢f hXf
      (StoppedK2.isStoppingTime_drivingFiltration_fst D.killedMeas hXf (D.driveStopping n)) _
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
  -- Both the rule identity and the generating trace pass under the conditional law.
  have hRν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) hR)
  have htrν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) D.generates)
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
    filter_upwards [hK, hRν, htrν, ae_fst_of_ae (P₀ := P₀) D.typed]
      with p₀ hK₀ hR₀ htr₀ htype₀ _
    obtain ⟨𝓕', W', VL', VR', B', hSC, hag, hfrz⟩ := hK₀ (mem_univ _)
    have hRe : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        V p = R (killedHistory W' VL' VR' V p) := by
      filter_upwards [hag, hR₀] with p hp hRp
      have he : Exist.AgreeBefore
          (fun t (p : M.space × (ℕ → ℝ)) => D.driver t p.1) W'
          (fun i t p => geomLW D.driver D.xL i t p.1) VL'
          (fun j t p => geomRW D.driver D.xR j t p.1) VR' V V p :=
        ⟨rfl, fun t ht => ⟨(hp t ht.le).1,
          fun i => (hp t ht.le).2.1 i, fun j => (hp t ht.le).2.2 j⟩⟩
      rw [Exist.killedHistory_eq_of_agreeBefore he]
      exact hRp
    have hgen : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        IsGeneratingTrace (fun t => W' t p) (V p) (γ p) := by
      filter_upwards [hag, htr₀] with p hp hgp
      exact StoppedK2.isGeneratingTrace_congr (fun t ht => ((hp t ht.le).1).symm) hgp
    have hd := ae_codeMatch_of_regular_coupling h13 hκ hFc
      ⟨D.xLAnti p₀.1, D.xLNonpos p₀.1, D.xRMono p₀.1, D.xRNonneg p₀.1⟩
      htype₀ (fun p => D.shifted p.1) hSC hRm hRg hRe
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

end InteractingSLE.Wire.RetMatch
