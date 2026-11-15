/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LineL1
import InteractingSLE.Spec.Supplement.Q3ChainRetLaw
import InteractingSLE.WangWu.ReverseContactMartFilt2Glue
import InteractingSLE.Spec.Exist.StagedLaw3Adm
import InteractingSLE.Spec.Supplement.GB6RestartProofR1
import InteractingSLE.Spec.Sec7.SideHeightHull
import InteractingSLE.Spec.Supplement.RelSafeCore

/-!
# GB6's line locality, part 2: the flow's record as a mark of the retained set

Packet PROVE-GB6-LINELOCAL, item (L1)(a) of `planning/handoffs/PROVE-GB6-RELSAFE2.md` §4. GB6's retained set in the
counterflow frame is the inverted flow hull `−1/K^α_s`, read from the flow's record at the own time `s`
(`retSet`: `ℍ` when the flow has died before `s`). With the marks `𝓕^α_s` of the (regularized) flow's driving
filtration at `s`:

* **the record is a mark** (`Measurable[𝓕^α_s] (gb6Rec s Wα ζα)`): the record coincides almost surely with the record
  read from the stopped histories at the announcing stops `ρₙ = s ∧ σₙ` (`StagedLaw.recVersion`, measurable for
  `⋁ₙ 𝓕^α_{ρₙ} ≤ 𝓕^α_s`), and `𝓕^α_s` contains the null sets;
* **the retained set is marked local** for the centred counterflow-frame field `h₀ = R_*(h − 𝔥⁰)` with the marks
  `𝓕^α_s`, when the flow's killed histories are field-determined (Theorem 1.2's form,
  `LP.HasFieldDeterminedHistories`): on `Eₙ = {s ≤ σₙ}` the retained set is the reflected hull at the stopping time
  `ρₙ = s`, marked local for `𝓕^α_{ρₙ}` (`WangWu.isHistoryAvoidanceLocal_reflect_hull`), and every mark `F ∈ 𝓕^α_s`
  cut to `Eₙ = {s ≤ ρₙ}` lies in `𝓕^α_{ρₙ}`; off `⋃ Eₙ` (almost surely `{ζα ≤ s}`) the retained set is `ℍ`; the pieces
  are glued by `GB6LineL.isHistoryAvoidanceLocal_glue_det`.

Main result: **`exists_retained_marks`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Supp8.GB6LineL

open Exist.Staged Exist.StagedLaw Supp8.GB6 Theorem14.GW2JointKernel LocalSets Restart

/-! ### The retained set read from a record -/

/-- **The retained set read from a record**: the inverted hull `−1/K_s` of the record driver when the record is alive
at `s`, and `ℍ` otherwise. -/
def retOfRec (s : ℝ≥0) (r : RecData) : Set ℂ := if r.2.2 = false then Q3Rel.invHull (rdrv r) s else H

theorem measurable_retOfRec (s : ℝ≥0) : Measurable[inferInstance, hittingSigma] (retOfRec s) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hm : MeasurableSet {r : RecData | r.2.2 = false} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  exact Measurable.ite hm (measurable_invHull_rdrv s) measurable_const

/-- **GB6's retained set**: the inverted flow hull read from the flow's record at the own time `s`. -/
def retSet {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ω : Ω) : Set ℂ :=
  retOfRec s (gb6Rec s Wα ζα ω)

theorem retSet_of_lt {Ω : Type*} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {ω : Ω} (hs : (s : ℝ≥0∞) < ζα ω) :
    retSet s Wα ζα ω = Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s := by
  have hf : (gb6Rec s Wα ζα ω).2.2 = false := (flag_recOf_cfE s).2 hs
  simp only [retSet, retOfRec, hf, ↓reduceIte]

theorem retSet_of_le {Ω : Type*} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {ω : Ω} (hs : ζα ω ≤ s) :
    retSet s Wα ζα ω = H := by
  have hf : ¬ (gb6Rec s Wα ζα ω).2.2 = false := fun h => absurd ((flag_recOf_cfE s).1 h) (not_lt.2 hs)
  simp only [retSet, retOfRec, hf, Bool.true_eq_false, ↓reduceIte]

/-! ### Small facts -/

theorem image_negInv_H : WangWu.negInv '' H = H := by
  refine Subset.antisymm (WangWu.image_negInv_subset_H subset_rfl) fun z hz => ?_
  refine ⟨WangWu.negInv z, WangWu.negInv_mem_H hz, ?_⟩
  change -(-z⁻¹)⁻¹ = z
  rw [inv_neg, inv_inv, neg_neg]

theorem stopSeq_coe_eq {Ω : Type*} (s : ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    stopSeq (s : ℝ≥0∞) σ n ω = min s (σ n ω) := by
  rw [stopSeq, ← ENNReal.coe_min, ENNReal.toNNReal_coe]

/-- A measurable function almost surely equal to an `m`-measurable one is `m`-measurable, when `m` contains the null
sets. -/
theorem measurable_of_ae_eq_nullSets {Ω X : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {P : Measure Ω} (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {f g : Ω → X} (hf : Measurable f)
    (hg : Measurable[m] g) (hfg : f =ᵐ[P] g) : Measurable[m] f := fun S hS =>
  RelSafe.measurableSet_of_ae_eq hm hnull (hf hS) (hg hS) (hfg.mono fun ω hω => by
    change (f ω ∈ S) = (g ω ∈ S)
    rw [hω])

/-! ### The record as a mark of the retained set -/

/-- **GB6's retained set is marked local for the flow's stopped σ-algebra, which contains the record.** For a flow
line of `h` with the data of the word `c` whose killed histories are field-determined (Theorem 1.2's form), and the
centred counterflow-frame field `h₀ = R_*(h − 𝔥⁰)`: there are marks `ℋ` (the flow's driving filtration at `s`)
containing the null sets and the record `gb6Rec s Wα ζα`, contained in the field-determined events, for which the
retained set `retSet s Wα ζα` satisfies the history-marked avoidance criterion. -/
theorem exists_retained_marks {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h h₀ : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    (hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.fn c.jumps u₀) (hh₀m : Measurable h₀)
    (hcen : ∀ ω, h₀ ω = WangWu.reflectField (WholeField.centredField h u₀ ω)) (s : ℝ≥0) :
    ∃ ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets P ≤ ℋ.1 ∧ Measurable[ℋ.1] (gb6Rec s Wα ζα) ∧
      ℋ.1 ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal ℋ.1 (retSet s Wα ζα) h₀ P := by
  classical
  -- the regularized flow driver and its coupling
  set E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => cfE s Wα ζα ω with hEdef
  obtain ⟨hEm, hrecm⟩ := measurable_recOf_cfE hfl s
  have hEreg : ∀ ω, IsRegularDriver (E ω) := fun ω => Theorem14.StagedReg.isRegularDriver_regularize _ _
  have hdrv := ae_driver_zero_continuousOn hfl
  have eζ : (fun ω => (E ω).2) = ζα := funext fun ω => cfE_snd s Wα ζα ω
  have hfl₂ : IsFlowLineDriver κ c.fn c.jumps θ P h (fun t ω => (E ω).1 t) (fun ω => (E ω).2) := by
    rw [eζ]
    refine Theorem14.StagedReg.isFlowLineDriver_congr_ae hfl
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hEm)) ?_
    filter_upwards [hdrv] with ω hω
    exact ⟨(hEreg ω).2.1.trans hω.1.symm, fun t ht => cfE_fst_of_lt s hω.1 hω.2 ht⟩
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hfl₂
  have hX := hC.2.2.2.1
  -- the field identities
  obtain ⟨u₀α, hu₀α⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
    (flowLineXR c.fn c.jumps 0)
  have hrel := Q3Chain.eqOn_bhe_flow_initial hκ θ hu₀ hu₀α
  have hcc : ∀ ω, WholeField.centredField h u₀ ω = WholeField.centredField h'' u₀α ω := fun ω => by
    rw [Sec7.SideHeight.centredField_eq_flowField htr hu₀.1 hu₀α.1 hrel ω, neg_zero, Sec5.GlueCond.flowField_zero_zero]
  set D : DistOn upperHalfPlaneOpens :=
    WangWu.reflectField (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀α) with hDdef
  have hfield : (fun ω => WangWu.reflectField (h'' ω) - D) = h₀ := funext fun ω => by
    rw [hcen ω, hcc ω, WholeField.centredField, WangWu.reflectField_sub]
  have hh'' : ∀ ω, h'' ω = WangWu.reflectField (h₀ ω) +
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀α := fun ω => by
    rw [hcen ω, WangWu.reflectField_reflectField, hcc ω, WholeField.centredField, sub_add_cancel]
  have hD : IsHarmonicDistOn D H := by
    have h1 := WangWu.isHarmonicDistOn_reflectField QuantumZipper.isOpen_H subset_rfl
      (WholeField.isHarmonicDistOn_smoothDist hu₀α.1)
    rwa [image_negInv_H] at h1
  -- determination
  have hd := hdet P 𝓕 (fun t ω => (E ω).1 t) VL VR B (fun ω => (E ω).2) h'' hC
  have hcomap : MeasurableSpace.comap h'' inferInstance ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap ((WholeField.measurable_add_dist _).comp WangWu.measurable_reflectField)
      (Eventually.of_forall hh'')
  have h𝓕 : ∀ t, drivingFiltration P hX t ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P := fun t =>
    (Q3Chain.drivingFiltration_le_aeSigma hd hX t).trans (Q3Chain.aeSigma_le_of_le hcomap)
  obtain ⟨ℋ, hℋdef⟩ : ∃ ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}, ℋ.1 = drivingFiltration P hX s :=
    ⟨⟨_, (drivingFiltration P hX).le s⟩, rfl⟩
  have hℋm : ℋ.1 ≤ mΩ := ℋ.2
  have hℋn : Ito.nullSets P ≤ ℋ.1 := hℋdef ▸ Ito.nullSets_le_usualAugmentation _ _ _
  have h𝓕s : ℋ.1 ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P := hℋdef ▸ h𝓕 s
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
    (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · -- an inadmissible seed: the flow dies at once, the record is almost surely constant, the retained set is `ℍ`
    have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    have hconst : gb6Rec s Wα ζα =ᵐ[P] fun _ => recOf (s : ℝ≥0∞)
        (Theorem14.StagedReg.regularize (s : ℝ≥0∞) ((fun _ => (0 : ℝ)), 0)) := by
      filter_upwards [h0] with ω hω
      have hz : ζα ω = 0 := by rw [← cfE_snd s Wα ζα ω]; exact hω
      have hK : (fun t => cfKW Wα ζα t ω) = fun _ => (0 : ℝ) := funext fun t => by
        simp only [cfKW, hz, ENNReal.not_lt_zero, ↓reduceIte]
      change recOf (s : ℝ≥0∞) (Theorem14.StagedReg.regularize (s : ℝ≥0∞) (fun t => cfKW Wα ζα t ω, ζα ω)) = _
      rw [hK, hz]
    have hrecℋ : Measurable[ℋ.1] (gb6Rec s Wα ζα) :=
      measurable_of_ae_eq_nullSets hℋm hℋn hrecm measurable_const hconst
    refine ⟨ℋ, hℋn, hrecℋ, h𝓕s, ?_⟩
    refine isHistoryAvoidanceLocal_glue_det hh₀m (E := fun _ => ∅) h𝓕s
      (fun _ => @MeasurableSet.empty _ (aeSigma (MeasurableSpace.comap h₀ inferInstance) P))
      (fun n U G _ _ _ F _ => by
        simp only [inter_empty]
        exact @MeasurableSet.empty _ (Theorem14.WalkLaw.complSigma P G h₀)) ?_
    filter_upwards [h0] with ω hω _
    have hz : ζα ω ≤ s := by rw [← cfE_snd s Wα ζα ω]; change (E ω).2 ≤ _; rw [hω]; exact zero_le
    rw [retSet_of_le hz]
  · -- the announcing stops
    have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
      (κ := κ) (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0)
      (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
      hC.1.2.2.2.2 (hC.1.ae_tendsto_threshold hκ) hseed
    set ρ : ℕ → Ω → ℝ≥0 := stopSeq (s : ℝ≥0∞) σ with hρdef
    have hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0) :=
      isStoppingTime_stopSeq _ hσ.1
    have hρs : ∀ n ω, ρ n ω ≤ s := fun n ω => by rw [hρdef, stopSeq_coe_eq]; exact min_le_left _ _
    have hc := isStoppingTime_const (drivingFiltration P hX) s
    have hρℋ : ∀ n, (hρ n).measurableSpace ≤ ℋ.1 := fun n => by
      have h1 := (hρ n).measurableSpace_mono hc (fun ω => by
        show ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((s : ℝ≥0) : WithTop ℝ≥0)
        exact_mod_cast hρs n ω)
      rwa [IsStoppingTime.measurableSpace_const, ← hℋdef] at h1
    have hρζ : ∀ n, ∀ᵐ ω ∂P, ((ρ n ω : WithTop ℝ≥0) : ℝ≥0∞) < (E ω).2 := fun n => by
      filter_upwards [hσ.2.2.1 n] with ω hω
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le _ σ n ω)) hω
    -- the record is a mark
    have hKex : ∀ n, ∃ K : Ω → LocalExt.DrivingHist (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0),
        Measurable[(hρ n).measurableSpace] K ∧
        ∀ ω, IsIntegratedSLEPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
            (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (fun s => (E ω).1 s)
            (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) (E ω).2 →
          (ρ n ω : ℝ≥0∞) < (E ω).2 →
          K ω = Sec7.stoppedHistory (Sec7.completedState (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
            (fun ω => (ρ n ω : WithTop ℝ≥0)) ω := fun n =>
      LocalExt.exists_measurable_stoppedHistory_version hX (hρ n)
    choose K hKm hKeq using hKex
    have hR' : Measurable[ℋ.1] (recVersion (s : ℝ≥0∞) ρ K) :=
      @measurable_recVersion Ω _ _ ℋ (s : ℝ≥0∞) ρ K
        (fun n => (measurable_stopSeq_of hσ.1 n).mono (hρℋ n) le_rfl) (fun n => (hKm n).mono (hρℋ n) le_rfl)
    have hgood := ae_isGoodStopPath hκ hEreg hC.1 hseed (s : ℝ≥0∞)
    have hfin : ∀ ω, min (s : ℝ≥0∞) (E ω).2 ≠ ⊤ := fun ω =>
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    have hRR' : ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω = recVersion (s : ℝ≥0∞) ρ K ω := by
      filter_upwards [hgood, hσ.2.2.2, ae_all_iff.2 hσ.2.2.1, hC.1.2.2.2.2] with ω hg hann hlt hp
      exact (recVersion_eq (s : ℝ≥0∞) (hg (hfin ω)) (hσ.2.1 ω) hlt hann fun n =>
        hKeq n ω hp (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le _ σ n ω)) (hlt n))).symm
    have hrecℋ : Measurable[ℋ.1] (gb6Rec s Wα ζα) := measurable_of_ae_eq_nullSets hℋm hℋn hrecm hR' hRR'
    -- the avoidance events of the retained set are marks
    have hAℋ : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[ℋ.1] {ω | Disjoint (retSet s Wα ζα ω) U} :=
      fun U hU hUH => hrecℋ (measurable_retOfRec s (measurableSet_avoid hU hUH))
    -- the versions of the reflected hulls at the stops
    have hAnex : ∀ n, ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧
        ∀ᵐ ω ∂P, A' ω = WangWu.negInv '' fwdHull (fun r : ℝ => (E ω).1 r.toNNReal)
          (((fun ω => (ρ n ω : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := fun n => by
      have hloc := (hC.2.2.2.2 _ (hρ n) (hρζ n)).1
      obtain ⟨A₀, hA₀m, hA₀e, -⟩ := WholeField.IsLocalSet.exists_measurable_version hloc hC.2.1
      refine ⟨fun ω => WangWu.negInv '' A₀ ω, WangWu.measurable_image_negInv.comp hA₀m, ?_⟩
      filter_upwards [hA₀e] with ω hω
      rw [hω]
    choose An hAnm hAnK using hAnex
    set En : ℕ → Set Ω := fun n => {ω | s ≤ σ n ω} with hEndef
    have hloc : ∀ n, WholeField.IsHistoryAvoidanceLocal (hρ n).measurableSpace (An n) h₀ P := fun n => by
      have h1 := WangWu.isHistoryAvoidanceLocal_reflect_hull hC hκ hD hX (hρ n) (hρζ n) (hAnm n) (hAnK n)
      rwa [hfield] at h1
    have hE : ∀ n F, MeasurableSet[ℋ.1] F → MeasurableSet[(hρ n).measurableSpace] (F ∩ En n) := fun n F hF => by
      have hF' : MeasurableSet[hc.measurableSpace] F := by rwa [IsStoppingTime.measurableSpace_const, ← hℋdef]
      have h1 := hc.measurableSet_inter_le (hρ n) F hF'
      have hset : {ω | ((s : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ n ω : WithTop ℝ≥0)} = En n := by
        ext ω
        simp only [mem_ofPred_eq, hEndef, WithTop.coe_le_coe, hρdef, stopSeq_coe_eq, le_min_iff, le_refl,
          true_and]
      rw [hset] at h1
      exact (hc.min (hρ n)).measurableSpace_mono (hρ n) (fun ω => min_le_right _ _) _ h1
    have hpiece : ∀ n, PieceDet ℋ.1 (retSet s Wα ζα) h₀ P (En n) := fun n => by
      refine pieceDet_of_local hh₀m h𝓕s ((hρℋ n).trans h𝓕s) (fun U hU hUH => h𝓕s _ (hAℋ U hU hUH))
        (hloc n) (hE n) ?_
      filter_upwards [hAnK n, hgood, ae_all_iff.2 hσ.2.2.1] with ω hA hg hlt hωE
      have hωE' : s ≤ σ n ω := hωE
      have hsζ : (s : ℝ≥0∞) < (E ω).2 := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hωE') (hlt n)
      have hρn : ρ n ω = s := by rw [hρdef, stopSeq_coe_eq]; exact min_eq_left hωE'
      have hsle : s ≤ (min (s : ℝ≥0∞) (E ω).2).toNNReal := by
        rw [min_eq_left hsζ.le, ENNReal.toNNReal_coe]
      rw [hA, WithTop.untopD_coe, hρn, retSet_of_lt (by rwa [← cfE_snd s Wα ζα ω]),
        (hg (hfin ω)).fwdHull_eq hsle hsζ]
      rfl
    have hEd : ∀ n, MeasurableSet[aeSigma (MeasurableSpace.comap h₀ inferInstance) P] (En n) := fun n => by
      have h1 := hE n univ (@MeasurableSet.univ _ ℋ.1)
      rw [univ_inter] at h1
      exact (hρℋ n).trans h𝓕s _ h1
    refine ⟨ℋ, hℋn, hrecℋ, h𝓕s, isHistoryAvoidanceLocal_glue_det hh₀m h𝓕s hEd hpiece ?_⟩
    filter_upwards [hσ.2.2.2] with ω hann hnot
    by_cases hsζ : (s : ℝ≥0∞) < (E ω).2
    · obtain ⟨n, hn⟩ := hann s hsζ
      exact absurd hn (hnot n)
    · rw [retSet_of_le (by rw [← cfE_snd s Wα ζα ω]; exact not_lt.1 hsζ)]

end InteractingSLE.Supp8.GB6LineL
