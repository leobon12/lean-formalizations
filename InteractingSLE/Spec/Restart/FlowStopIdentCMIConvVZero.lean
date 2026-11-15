/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVField
import InteractingSLE.Spec.Sec7.Lemma71PinNull
import InteractingSLE.WangWu.Adapted

/-! # The zero-exit coupling, using only an independent Brownian motion -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open LQGMetric (TestOn DistOn)
open QuantumZipper (H fwdHull)
open StoppedExtend
open Coupling

/-- Killing at zero leaves only null information in the driving filtration. -/
theorem drivingFiltration_zero_le_nullSets {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hX : IsMeasurableKilledDriving W VL VR (fun _ => 0)) (t : ℝ≥0) :
    drivingFiltration P hX t ≤ Ito.nullSets P := by
  have hraw : killedDrivingFiltration hX = ⊥ := by
    apply bot_unique
    intro r
    change killedDrivingSigma W VL VR (fun _ => 0) r ≤ ⊥
    unfold killedDrivingSigma
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨s, -, A, -, rfl⟩
    simpa only [ENNReal.not_lt_zero, false_and, Set.ofPred_false] using
      (@MeasurableSet.empty Ω ⊥)
  change usualAugmentation (killedDrivingFiltration hX) P t ≤ _
  rw [hraw, Ito.usualAugmentation_apply]
  refine (iInf₂_le (t + 1) (lt_add_one t)).trans ?_
  rw [Ito.nullAugmented_apply]
  exact le_of_eq (bot_sup_eq _)

/-- Any GFF with the word's initial mean has a coupling through time zero
with the constant initial coordinates and any available filtered Brownian motion. -/
theorem isStoppedHullCoupling_zero {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}
    (hH : IsGFFWithBoundaryData P X (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR))
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) :
    IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 (fun _ _ => 0)
      (fun i _ _ => xL i) (fun j _ _ => xR j) B (fun _ => 0) X := by
  classical
  have had : ∀ Y : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓕 (fun _ => 0) Y := by
    intro Y t A _
    simpa only [ENNReal.not_lt_zero, false_and, Set.ofPred_false] using
      (@MeasurableSet.empty Ω (𝓕 t))
  have hpath : ∀ ω, Sec2.IsSLEPathUpTo κ xL xR ρL ρR (fun _ => 0)
      (fun i _ => xL i) (fun j _ => xR j) (B · ω) 0 := by
    intro ω
    constructor <;> simp
  have hX : IsMeasurableKilledDriving (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ))
      (fun i _ _ => xL i) (fun j _ _ => xR j) (fun _ => 0) := by
    intro t A _
    simpa only [ENNReal.not_lt_zero, false_and, Set.ofPred_false] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  refine ⟨⟨hB, had _, fun i => had _, fun j => had _, ae_of_all _ hpath⟩,
    ae_of_all _ (fun ω T _ => continuousOn_const), hH.1, hH.2, hX, fun τ hτ hτ0 => ?_⟩
  have heq : ∀ᵐ ω ∂P, τ ω = 0 := hτ0.mono fun ω h => le_antisymm h.1 bot_le
  have htime : ∀ᵐ ω ∂P, (τ ω).untopD 0 = 0 := heq.mono fun ω h => by rw [h]; rfl
  have hK : ∀ᵐ ω ∂P, fwdHull (fun _ : ℝ => (0 : ℝ)) ((τ ω).untopD 0 : ℝ≥0) = ∅ := by
    filter_upwards [htime] with ω hω
    rw [hω, NNReal.coe_zero]
    exact QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const
  let u₀ := LocalExt.bheAt κ ρL ρR xL xR
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  have huc : ContinuousOn u₀ H := hu₀.1.continuousOn
  have hgff := isZeroBoundaryGFF_sub_smoothDist hH.1 huc (hH.2 u₀ hu₀)
  have hempty := Coupling.IsLocalSet.add_dist (WangWu.isLocalSet_empty hgff)
    (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  have hempty' : IsLocalSet (fun _ : Ω => (∅ : Set ℂ)) X P := by
    convert hempty using 1
    funext ω
    exact (sub_add_cancel _ _).symm
  refine ⟨Coupling.IsLocalSet.congr_set hempty' hK, fun u hu φ => ?_⟩
  let f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))
  have hfi : Integrable f P := Integrable.of_bound
    (GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hH.1)).aestronglyMeasurable
    1 (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hsig : hτ.measurableSpace ≤ Ito.nullSets P := fun A hA =>
    (iSup_le fun t => drivingFiltration_zero_le_nullSets hX t) A hA.1
  have hce := Sec7.Lemma71S.condExp_ae_eq_of_le_sup_nullSets bot_le
    (by simpa only [bot_sup_eq] using hsig) hτ.measurableSpace_le hfi
  rw [condExp_bot] at hce
  have hfin : (forceJumpSet xL xR).Finite :=
    ((Set.finite_range xL).union (Set.finite_range xR)).insert 0
  have hH₀ : IsGFFWithBoundaryData P X (forceBoundaryData κ ρL ρR xL xR) hfin.toFinset := by
    simpa only [Set.Finite.coe_toFinset] using hH
  have hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (hfin.toFinset : Set ℝ) u₀ := by simpa only [Set.Finite.coe_toFinset] using hu₀
  have hchar := integral_cexp_of_isGFF hH₀ hu₀' φ
  filter_upwards [hce, htime] with ω hceω htω _
  have huω := hu ω
  simp only [htω, NNReal.coe_zero, sub_zero] at huω ⊢
  rw [hceω, hchar]
  change LocalExt.cfVal _ _ = LocalExt.cfVal _ _
  congr 1
  have hmean := StoppedK2.integral_couplingMean_bhe_eq (κ := κ)
    (w := fun _ : ℝ≥0 => 0) (a := 0) (φ := φ) continuous_const
    (by rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const]; exact disjoint_empty _)
    hu₀ huω
  simp only [NNReal.coe_zero] at hmean
  rw [← hmean]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  · have hzH : 0 < z.im := φ.tsupport_subset (subset_tsupport _ hz)
    have hz0 : z ≠ 0 := fun h => by
      rw [h, Complex.zero_im] at hzH
      exact (lt_irrefl 0) hzH
    exact congrArg (fun v : ℝ => v * φ z)
      (Coupling.MartMeans2.couplingMean_zero κ (w := fun _ => 0) rfl u₀ hz0).symm

namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- The physical shifted GFF, expressed in the reference chart. -/
theorem isGFFWithBoundaryData_chartField : IsGFFWithBoundaryData D.tilt D.chartField
    (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
      (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y))
    (forceJumpSet (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y)) := by
  let _ := D.Q₀_prob
  have hH := isGFFWithBoundaryData_shift D.b_pc D.F D.q_extension D.H₀_gff D.s_bound D.s_limit
    D.Λ_measurable D.pairing_limit
    (integrable_exp_neg_of_prob D.Λ_measurable D.k_pos D.tilt_prob) D.k_pos D.tilt_prob
  have hG := Exist.isGFFWithBoundaryData_flowField D.κ_pos D.bR_pc D.y D.θ hH
  have heq : (fun ω => Exist.flowField D.y (D.θ * QuantumZipper.chiC D.κ) (D.shiftedField ω)) =
      D.chartField := funext fun ω => (Lemma75Bridge.eq_flowField_of_isTranslateAddConst
        (D.translate_shift ω)).symm
  change IsGFFWithBoundaryData D.tilt
    (fun ω => Exist.flowField D.y (D.θ * QuantumZipper.chiC D.κ) (D.shiftedField ω)) _ _ at hG
  rwa [heq] at hG

/-- The degenerate seed condition gives a measurable version equal to zero. -/
theorem ae_exit_zero (hs : FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V) :
    ∀ᵐ ω ∂D.Q₀, RLC.exitTime D.V (D.Γ ω) (D.U ω) = 0 := by
  filter_upwards [D.coupling.1.ae_isIntegratedSLEPath, D.trace] with ω hp hg
  exact (FlowStopIdentG.exitTime_seed D.V_open hp hg).1 hs

/-- A zero-exit reference coupling needs no clock or tilt-locality input. -/
theorem exists_isStoppedFlowLine_zero :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      IsStoppedFlowLine D.κ D.bR D.JR D.y D.θ (D.tilt.prod ν)
        (fun p => D.shiftedField p.1) (fun p => D.Γ p.1) (fun _ => 0) := by
  let _ : IsProbabilityMeasure D.tilt := D.tilt_prob
  obtain ⟨ν, hν, 𝓦, β, hβ, -, -⟩ := ConverseBefore.exists_noiseBM
  have hμ : (D.tilt.prod ν).map Prod.fst = D.tilt := Measure.map_fst_prod.trans (by simp)
  have hH := D.isGFFWithBoundaryData_chartField
  have hHP : IsGFFWithBoundaryData (D.tilt.prod ν) (fun p => D.chartField p.1)
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
        (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y))
      (forceJumpSet (flowLineXL D.bR D.JR D.y) (flowLineXR D.bR D.JR D.y)) := by
    refine ⟨hH.1.comp measurable_fst, fun u hu => ?_⟩
    have h := hH.2 u hu
    rw [← hμ] at h
    exact isZBGFFProcess_comp measurable_fst h
  refine ⟨ν, hν, fun p => D.chartField p.1, WholeField.prodFiltration ⊥ 𝓦,
    fun _ _ => 0, fun i _ _ => flowLineXL D.bR D.JR D.y i,
    fun j _ _ => flowLineXR D.bR D.JR D.y j, fun t p => β t p.2,
    fun p => D.translate_shift p.1,
    isStoppedHullCoupling_zero hHP (StoppedCont.isFilteredBrownianReal_prod_snd ⊥ hβ), ?_⟩
  have hg0 : ∀ᵐ ω ∂D.tilt,
      IsGeneratingTrace (fun _ => 0) 0 (fun t => D.Γ ω t - D.y) := by
    filter_upwards [D.tilt_equivalent.1.ae_le D.trace] with ω hg
    exact StoppedK2.isGeneratingTrace_congr (fun t ht => (not_lt_zero ht).elim)
      (LP.isGeneratingTrace_mono hg bot_le)
  exact ConverseBefore.ae_fst_of_ae (P₀ := ν) hg0

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
