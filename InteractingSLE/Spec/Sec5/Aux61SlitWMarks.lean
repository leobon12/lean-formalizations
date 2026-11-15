/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWNull
import InteractingSLE.Spec.Sec5.Aux61SlitWMean
import InteractingSLE.Spec.Sec5.Aux61AsmSlit

/-! # Concrete comparison unions and marked slit wiring -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61Asm Aux61ULoc Aux61ChLoc LocalSets WholeField LawUnique
open WangWu GlueCond Cond44Ref CfRegQ CrossCond.Theta Coupling
open Sec7.PocketStopWallsFin (regHull regHull_mono ae_regHull_eq)
universe u

section Physical
variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {Bm : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k]
  {u₀ : ℂ → ℝ} {μ : Measure (Ω × HistorySpace 0 0)} [IsProbabilityMeasure μ]

/-- The null-completed physical marks and current live sets of MARKS admit
SLIT's comparison wiring, constructed from the actual capacity rules. -/
theorem exists_slitWiring_of_null_capacityRules
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hμ : μ = glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
    (D : MarksData μ) (hF : MarksFacts μ D)
    (c : D.ι → HistorySpace 0 0 × HistorySpace nL nR → Chart)
    (hc : ∀ i, Aux61FibData.IsMeasChart (c i)) (r : D.ι → ℝ≥0) (s : ℝ≥0)
    (q : D.index → ℝ≥0) (uph : D.index → Ω → ℂ → ℝ)
    (huph : ∀ j ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i (q j) ω - W (q j) ω)
        (fun i => VR i (q j) ω - W (q j) ω))
      (forceJumpSet (fun i => VL i (q j) ω - W (q j) ω)
        (fun i => VR i (q j) ω - W (q j) ω)) (uph j ω))
    (hfield : D.field = fun p => h p.1) (hmean₀ : D.originalMean = u₀)
    (hscale : D.scale = 0) (hconstant : D.constant = chiC κ) (hdata : ∀ i, (D.data i).κ = κ)
    (hmarks : ∀ i t, D.baseMarks i t = nullMarks
      (ruleMarks stopRec (capacityRule (c i) (r i) t)
        (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ)
    (hcontains : ∀ i t, ∀ᵐ p ∂μ,
      unionAt (fun p => cfHullQ s p.2) (fun v p => regHull W ζ v p.1)
        (fun p => capacityRule (c i) (r i) t (stopRec s p.2, killedHistory W VL VR ζ p.1)) p ⊆ D.liveSets i t p)
    (hpatch : ∀ j i t, D.patches j i t = fun p => hullAt (q j) (killedHistory W VL VR ζ p.1))
    (hmean : ∀ j i t, D.mean j i t = fun p => couplingMean κ (fun v : ℝ => W v.toNNReal p.1)
      (q j) (uph j p.1))
    (hevent : ∀ j i t, D.comparisonEvent j i t =
      liveEv (D.Z i) (D.B i) (D.code i) 0 ∩
        {p | (q j : ℝ≥0∞) ≤ capacityRule (c i) (r i) t
          (stopRec s p.2, killedHistory W VL VR ζ p.1)}) :
    ∃ G : SlitWiringData (D.toAsmData hF), SlitWiring μ (D.toAsmData hF) G := by
  subst μ
  classical
  obtain ⟨hX, -⟩ := hC.2.2.2
  let Y₀ := fun p : Ω × HistorySpace 0 0 => stopRec s p.2
  let R₀ := fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1
  let rule := fun i t => capacityRule (c i) (r i) t
  let N := fun i t => nullMarks (ruleMarks stopRec (rule i t) Y₀ R₀)
    (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
  let M := fun j i t => nullMarks
    (ruleMarks stopRec (fun p => max (rule i t p) (q j : ℝ≥0∞)) Y₀ R₀)
    (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
  have hY : Measurable Y₀ := isRecordStop_stopRec.measurable.comp (measurable_const.prodMk measurable_snd)
  have hR : Measurable R₀ := (measurable_killedHistory hX).comp measurable_fst
  have hM : ∀ j i t, M j i t ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
    fun _ _ _ => nullMarks_le
  have hraw : ∀ j i t, ruleMarks stopRec (fun p => max (rule i t p) (q j : ℝ≥0∞)) Y₀ R₀ ≤ M j i t := by
    intro j i t
    exact le_nullMarks (Aux61Marks.ruleMarks_le isRecordStop_stopRec
      ((measurable_capacityRule (hc i) (r i) t).max measurable_const) hY hR)
  have hcur : ∀ j i t, N i t ≤ M j i t := by
    intro j i t
    apply nullMarks_mono
    exact ruleMarks_le_max isRecordStop_stopRec (measurable_capacityRule (hc i) (r i) t)
      (isGalmarinoRule_capacityRule (c i) (r i) t) Y₀ R₀ (q j)
  have hNe : ∀ i t, D.baseMarks i t = N i t := hmarks
  have hcurD : ∀ j i t, D.baseMarks i t ≤ M j i t := fun j i t => by
    rw [hNe]; exact hcur j i t
  have hzero : ∀ j i t, D.baseMarks i 0 ≤ M j i t :=
    fun j i t => (hF.baseMarks_mono i t).trans (hcurD j i t)
  have hS : ∀ i t, MeasurableSet[D.baseMarks i t] (liveEv (D.Z i) (D.B i) (D.code i) t) :=
    fun i t => hF.measurableSet_liveEv i le_rfl
  have hL : ∀ j i t, Measurable[M j i t, hittingSigma] (D.patches j i t) := by
    intro j i t
    rw [hpatch]
    exact (measurable_comparisonHull Y₀ R₀ (rule i t) (q j)).mono (hraw j i t) le_rfl
  have hGerm : ∀ i, D.germ0 i ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) := fun i =>
    germSigma_le (hF.measurable_liveSets i 0) (measurable_centredField hF.measurable_field _)
  have hXm := (measurable_cfFieldT κ θ).comp hC.2.1
  have hgood := ae_glue_fst (μ := P) k hXm (Aux50Hit.ae_isGoodPath hC.1 hζ)
  have hreg := ae_glue_fst (μ := P) k hXm (ae_regHull_eq hC hζ)
  have hmatch : ∀ j i t, ∀ᵐ p ∂glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) hXm,
      D.patches j i t p = regHull W ζ (q j) p.1 := by
    intro j i t
    filter_upwards [hgood, hreg] with p hp hr
    rw [hpatch, hr]
    exact Aux50Hit.regHull_stopHistory_cstop hp (q j)
  have hex := fun j => exists_isLocalSetMean_flowHull_glueT (θ := θ) (k := k) hC hκ hζ hu₀ (q j) (huph j)
  choose g hg hrep using hex
  let G := nullComparisonWiringData D hF stopRec rule Y₀ R₀ q g
  refine ⟨G, {
    scale_eq := hscale
    constant_eq := fun i => by rw [hdata]; exact hconstant
    sets_marks := fun i t _ => hF.measurable_liveSets_marks i t
    patches_measurable := fun j i t _ => (hL j i t).mono (hM j i t) le_rfl
    patches_closed := fun j i t _ => Eventually.of_forall fun p => by
      change D.patches j i t p ⊆ H ∧ IsOpen (H \ D.patches j i t p)
      rw [hpatch]; exact hullAt_relClosed _ _
    patches_unbounded := fun j i t _ => Eventually.of_forall fun p => by
      change ∀ z ∈ lowerUnion (D.patches j i t p),
        ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (D.patches j i t p)) z)
      rw [hpatch]; exact not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _)
    patchMean_local := ?_
    mean_harmonic := ?_
    mean_represents := ?_
    unionMarks_le := fun j i t _ => sup_le (hM j i t) (hGerm i)
    union_measurable := ?_
    union_closed := ?_
    union_local := ?_
    marks_le := fun j i t _ => by
      change (D.baseMarks i t ⊔ D.germ0 i) ⊔ _ ≤ M j i t ⊔ D.germ0 i
      simp only [Aux61Marks.liveEv_meanHistory, Aux61Nest.liveSet_idem]
      exact sup_le (sup_le_sup_right (hcurD j i t) _) le_sup_right
    sets_subset := ?_
    patches_marks := fun j i t _ => (hL j i t).mono le_sup_left le_rfl
    patches_subset := ?_
    event_measurable := ?_
    union_eq := ?_ }⟩
  · intro j i t _
    change IsLocalSetMean (D.patches j i t) (centredField D.field D.originalMean) _ (g j)
    rw [hpatch, hfield, hmean₀]
    have he : (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) =
        centredField (fun p : Ω × HistorySpace 0 0 => h p.1) u₀ :=
      funext fun p => cenTT_cfFieldT κ θ u₀ (h p.1)
    rw [← he]
    exact hg j
  · intro j i t _
    filter_upwards [hgood] with p hp
    rw [hmean, hpatch]
    dsimp only
    rw [show hullAt (q j) (killedHistory W VL VR ζ p.1) =
      fwdHull (Ito.rpath (fun v => W v p.1)) (q j) from Aux50Hit.regHull_stopHistory_cstop hp (q j)]
    exact Sec7.SideHeight.harmonicOnNhd_couplingMean hp.continuous_rpath (q j).coe_nonneg (huph j p.1).1
  · intro j i t _
    simpa only [hpatch, hmean, hmean₀, G, nullComparisonWiringData] using hrep j
  · intro j i t _
    change Measurable[_, hittingSigma] (liveSet _ (fun p => D.liveSets i t p ∪ D.patches j i t p))
    exact (Aux61Nest.measurable_liveSet (hcurD j i t _ (hS i t))
      (@measurable_union_hitting _ (M j i t) _ _
        ((hF.measurable_liveSets_base i t).mono (hcurD j i t) le_rfl) (hL j i t))).mono (hM j i t) le_rfl
  · intro j i t _
    apply Aux61Nest.liveSet_properties
    intro p
    rw [hpatch]
    refine ⟨union_subset (hF.liveSets_closed i t p).1 (hullAt_relClosed _ _).1, ?_⟩
    rw [← sdiff_inter_sdiff]
    exact (hF.liveSets_closed i t p).2.inter (hullAt_relClosed _ _).2
  · intro j i t _
    have hloc := isHistoryAvoidanceLocal_comparison_union hC hκ hζ hθb hcf hlaw hk hu₀ s (q j)
      (measurable_capacityRule (hc i) (r i) t) (isGalmarinoRule_capacityRule (c i) (r i) t)
    have he : (fun p : Ω × HistorySpace 0 0 => centredField h u₀ p.1) =
        centredField D.field D.originalMean := by rw [hfield, hmean₀]; rfl
    rw [he] at hloc
    apply isHistoryAvoidanceLocal_null_comparison hF.zero_field (hM j i t)
      (hcurD j i t _ (hS i t))
      ((hF.measurable_liveSets_base i 0).mono (hzero j i t) le_rfl)
      (fun p => (hF.liveSets_closed i 0 p).1)
      ((hF.measurable_liveSets_base i t).mono (hcurD j i t) le_rfl) (hL j i t)
      (hF.liveSets_mono i t) hloc.nullMarks
    filter_upwards [hcontains i t, hmatch j i t] with p hp hm
    exact (unionAt_max_subset_union (q j) p).trans (union_subset_union hp hm.symm.subset)
  · intro j i t _ p z hz
    change z ∈ liveSet _ (fun p => D.liveSets i t p ∪ D.patches j i t p) p
    by_cases hp : p ∈ liveEv (D.Z i) (D.B i) (D.code i) t
    · rw [liveSet_of_mem hp]; exact Or.inl hz.1
    · rw [liveSet_of_notMem hp]; exact hz.2
  · intro j i t _ p z hz
    change z ∈ liveSet _ (fun p => D.liveSets i t p ∪ D.patches j i t p) p
    by_cases hp : p ∈ liveEv (D.Z i) (D.B i) (D.code i) t
    · rw [liveSet_of_mem hp]; exact Or.inr hz.1
    · rw [liveSet_of_notMem hp]; exact hz.2
  · intro j i t _
    change MeasurableSet[D.marks i t] (D.comparisonEvent j i t)
    rw [hevent]
    apply le_sup_left (a := D.baseMarks i t)
    apply MeasurableSet.inter ((hF.baseMarks_mono i t) _ (hS i 0))
    rw [hNe]
    apply le_nullMarks (Aux61Marks.ruleMarks_le isRecordStop_stopRec
      (measurable_capacityRule (hc i) (r i) t) hY hR)
    exact measurableSet_comparison (measurable_capacityRule (hc i) (r i) t)
      (isGalmarinoRule_capacityRule (c i) (r i) t) Y₀ R₀ (q j)
  · intro j i t _
    filter_upwards [hcontains i t, hmatch j i t] with p hp hm hE
    rw [hevent] at hE
    change liveSet _ (fun p => D.liveSets i t p ∪ D.patches j i t p) p = D.liveSets i t p
    by_cases hpt : p ∈ liveEv (D.Z i) (D.B i) (D.code i) t
    · rw [liveSet_of_mem hpt]
      apply union_eq_left.2
      intro z hz
      apply hp
      have hsub := comparison_subset_unionAt_max (fun p => regHull_mono W ζ p.1) (A := fun p => cfHullQ s p.2)
        (T := fun p => rule i t (Y₀ p, R₀ p)) (q j) p
      rw [unionAt_max_eq (T := fun p => rule i t (Y₀ p, R₀ p)) (x := p) hE.2] at hsub
      exact hsub ⟨hm ▸ hz, (by rw [hpatch] at hz; exact (hullAt_relClosed _ _).1 hz)⟩
    · rw [liveSet_of_notMem hpt]
      exact (liveSet_of_notMem hpt).symm

end Physical
end InteractingSLE.Sec5.Aux61SlitW
