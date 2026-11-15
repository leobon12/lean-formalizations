/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeMarksGen
import InteractingSLE.Spec.Supplement.GB6LineL2
import InteractingSLE.Spec.Supplement.BW1LinesLocal

/-!
# The record hull of a flow line at a finite own time is marked local for its record (terminal times included)

Packet PROVE-BW1-SAFELAW, the new mathematical step of BW1's retained marks. Let `E` be the (regular, measurable)
driver of an angle-`θ` flow line of `h` whose killed histories are field-determined (Theorem 1.2's form), `s` a finite
own time, `r_s = recOf s E` its record and `A_s = −1/K_{min(s, ζ)}` the inverted hull of the record driver at the
record's own time — the hull AT the lifetime when `ζ ≤ s` (a continuation threshold; the frozen coupling gives
locality only at stops `< ζ`, and the terminal hull is not a limit of those: a pocket can be swallowed at the last
instant). **`isHistoryAvoidanceLocal_recHull`**: for the centred counterflow-frame field `h₀ = R_*(h − 𝔥⁰)`, `A_s` is
history-marked local with the marks `σ(r_s) ∨ 𝒩` (and these marks are field-determined). Proof, for an open `U ⊆ ℍ`
and a Markov decomposition along `U`:

1. *unmarked*: `A_s` is a local set of `h₀` (Gaussian hull-limit theorem,
   `BW1Lines.isLocalSet_centred_fwdHull_min_life`, reflected), and `G = {A_s ∩ U = ∅}` is determined (a record
   event), so `G ∈ complSigma`;
2. *the stops before the lifetime*: with stops `τₙ = s ∧ σₙ < ζ` announcing `min(s, ζ)`, `−1/K_{τₙ}` is marked local for
   `𝓕_{τₙ}` (`WangWu.isHistoryAvoidanceLocal_reflect_hull`) and `G ⊆ {−1/K_{τₙ} ∩ U = ∅}`; the pull-out step
   `inter_mem_complSigma_of_subset` gives `G ∩ F ∈ complSigma` for `F ∈ 𝓕_{τₙ}`;
3. *the record*: `r_s` is almost surely the record read from the stopped histories (`StagedLaw.recVersion`), so
   `σ(r_s) ⊆ ⋁ₙ 𝓕_{τₙ} ∨ 𝒩`, and the marks `F` with `G ∩ F ∈ complSigma` form a σ-algebra (`WalkLaw.traceSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.Staged Exist.StagedLaw Supp8.GB6 Theorem14.GW2JointKernel LocalSets Restart BW1Ver Theorem14.WalkLaw

/-- The record of a regular driver at an own time `s ≤ T` and before the lifetime has the driver's hull. -/
theorem fwdHull_rdrv_recOf_terminal {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {W' : ℝ≥0 → ℝ} (hW'c : Continuous W')
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {t : ℝ≥0∞}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hg : IsGoodStopPath κ xL xR ρL ρR t e vL vR b)
    (hW'e : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ e.2 → W' r = e.1 r) :
    fwdHull (Ito.rpath W') (recS (recOf t e)) = fwdHull (rdrv (recOf t e)) (recS (recOf t e)) := by
  refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hW'c.comp continuous_real_toNNReal) (continuous_rdrv _)
    (recS (recOf t e)).coe_nonneg fun r hr => ?_
  have hrs : r.toNNReal ≤ (min t e.2).toNNReal := Real.toNNReal_le_iff_le_coe.2 hr.2
  have h1 := hg.eqOn_rpath (s := (min t e.2).toNNReal) le_rfl ⟨hr.1, hr.2⟩
  change W' r.toNNReal = rdrv (recOf t e) r
  rw [← h1]
  refine hW'e _ ((ENNReal.coe_le_coe.2 hrs).trans ?_)
  rw [ENNReal.coe_toNNReal hg.2.2.2.2.1]
  exact min_le_right _ _

/-- **A good stopped path is continuous through its lifetime** (continuous before it; at a finite lifetime the
regular value is the left limit, which exists). -/
theorem IsGoodStopPath.continuousOn_le {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} (hg : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) :
    ContinuousOn e.1 {r : ℝ≥0 | (r : ℝ≥0∞) ≤ e.2} := by
  have hreg := hg.2.2.1
  rcases eq_or_ne e.2 ⊤ with htop | hfin
  · have hs : {r : ℝ≥0 | (r : ℝ≥0∞) ≤ e.2} = {r : ℝ≥0 | (r : ℝ≥0∞) < e.2} := by
      ext r
      simp only [mem_ofPred_eq, htop, le_top, ENNReal.coe_lt_top]
    rw [hs]
    exact hreg.1
  · set T : ℝ≥0 := e.2.toNNReal with hTdef
    have hTe : (T : ℝ≥0∞) = e.2 := ENNReal.coe_toNNReal hfin
    have hT0 : 0 < T := by
      rw [← ENNReal.coe_lt_coe, hTe, ENNReal.coe_zero]
      exact hg.2.2.2.2.2
    obtain ⟨w₀, _, _, htend⟩ := hg.2.1 T hT0 hTe
    have hW : Tendsto e.1 (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp htend
    have hv : e.1 T = w₀ := hreg.2.2.2 hfin hg.2.2.2.2.2 w₀ hW
    have hset : {r : ℝ≥0 | (r : ℝ≥0∞) ≤ e.2} = Iic T := by
      ext r
      simp only [mem_ofPred_eq, mem_Iic, ← hTe, ENNReal.coe_le_coe]
    have hopen : {r : ℝ≥0 | (r : ℝ≥0∞) < e.2} = Iio T := by
      ext r
      simp only [mem_ofPred_eq, mem_Iio, ← hTe, ENNReal.coe_lt_coe]
    have hco : ContinuousOn e.1 (Iio T) := hopen ▸ hreg.1
    rw [hset]
    intro r hr
    rcases (mem_Iic.1 hr).lt_or_eq with hlt | heq
    · exact ((hco.continuousAt (isOpen_Iio.mem_nhds hlt)).continuousWithinAt)
    · rw [heq, ← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hv]
      exact hW

/-- An almost surely constant map generates, with the null sets, only events of every completed σ-algebra. -/
theorem comap_sup_nullSets_le_aeSigma_of_ae_const {Ω β : Type*} {𝔪 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} {f : Ω → β} {b₀ : β} (hf : ∀ᵐ ω ∂P, f ω = b₀) :
    MeasurableSpace.comap f inferInstance ⊔ Ito.nullSets P ≤ aeSigma 𝔪 P := by
  classical
  refine sup_le ?_ nullSets_le_aeSigma
  rintro _ ⟨C, -, rfl⟩
  have htriv : (f ⁻¹' C : Set Ω) =ᵐ[P] (if b₀ ∈ C then univ else ∅ : Set Ω) := by
    filter_upwards [hf] with ω hω
    change (f ω ∈ C) = (ω ∈ (if b₀ ∈ C then univ else ∅ : Set Ω))
    rw [hω]
    by_cases hC0 : b₀ ∈ C
    · simp [hC0]
    · simp [hC0]
  refine measurableSet_aeSigma_of_ae_eq ?_ htriv
  by_cases hC0 : b₀ ∈ C
  · simp only [hC0, ↓reduceIte]
    exact @MeasurableSet.univ _ (aeSigma 𝔪 P)
  · simp only [hC0, ↓reduceIte]
    exact @MeasurableSet.empty _ (aeSigma 𝔪 P)

/-! ### The marked locality of the record hull -/

/-- **The record hull of a flow line at a finite own time is marked local for its record** (the hull at the lifetime
when the flow line dies before `s`): for the centred counterflow-frame field `h₀ = R_*(h − 𝔥⁰)` and a flow line
whose killed histories are field-determined, the record `r_s` is field-determined and `−1/K_{min(s,ζ)}` (the inverted
hull of the record driver at the record's own time) satisfies the history-marked avoidance criterion with the marks
`σ(r_s) ∨ 𝒩`. (First conjunct: the killed driver itself is field-determined.) -/
theorem isHistoryAvoidanceLocal_recHull {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {h h₀ : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord}
    {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : Measurable E) (hEreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P h (fun t ω => (E ω).1 t) (fun ω => (E ω).2))
    (hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.fn c.jumps u₀)
    (hh₀ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hcen : ∀ ω, h₀ ω = WangWu.reflectField (WholeField.centredField h u₀ ω)) (s : ℝ≥0) :
    (∀ (q : ℝ≥0) (A : Set ℝ), MeasurableSet A →
      MeasurableSet[aeSigma (MeasurableSpace.comap h₀ inferInstance) P] {ω | (q : ℝ≥0∞) < (E ω).2 ∧ (E ω).1 q ∈ A}) ∧
    MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (E ω)) inferInstance ≤
        aeSigma (MeasurableSpace.comap h₀ inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal
        (MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) (E ω)) inferInstance ⊔ Ito.nullSets P)
        (fun ω => Supp8.Q3Rel.invHull (rdrv (recOf (s : ℝ≥0∞) (E ω))) (recS (recOf (s : ℝ≥0∞) (E ω)))) h₀ P := by
  classical
  have hh₀m := hh₀.measurable
  set rs : Ω → RecData := fun ω => recOf (s : ℝ≥0∞) (E ω) with hrsdef
  have hrsm : Measurable rs := measurable_recOf hEm hEreg _
  set As : Ω → Set ℂ := fun ω => Supp8.Q3Rel.invHull (rdrv (rs ω)) (recS (rs ω)) with hAsdef
  have hAsm : Measurable[mΩ, hittingSigma] As := measurable_invHull_rec.comp hrsm
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hX := hC.2.2.2.1
  -- the field identities
  obtain ⟨u₀α, hu₀α⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
    (flowLineXR c.fn c.jumps 0)
  have hrel := Supp8.Q3Chain.eqOn_bhe_flow_initial hκ θ hu₀ hu₀α
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
    rwa [Supp8.GB6LineL.image_negInv_H] at h1
  -- determination
  have hd := hdet P 𝓕 (fun t ω => (E ω).1 t) VL VR B (fun ω => (E ω).2) h'' hC
  have hcomap : MeasurableSpace.comap h'' inferInstance ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap ((WholeField.measurable_add_dist _).comp WangWu.measurable_reflectField)
      (Eventually.of_forall hh'')
  have h𝓕 : ∀ t, drivingFiltration P hX t ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P := fun t =>
    (Supp8.Q3Chain.drivingFiltration_le_aeSigma hd hX t).trans (Supp8.Q3Chain.aeSigma_le_of_le hcomap)
  refine ⟨fun q A hA => h𝓕 q _ ((Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
    (Coupling.adaptedBefore_killedDriving_W hX)) q A hA), ?_⟩
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · -- an inadmissible seed: the flow line dies at once, its record is almost surely constant, its hull empty
    have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    set r₀ : RecData := ((fun _ => (0 : ℝ)), 0, true) with hr₀
    have hconst : ∀ᵐ ω ∂P, rs ω = r₀ := by
      filter_upwards [h0] with ω hω
      have hz := (hEreg ω).2.1
      have h00 : min (s : ℝ≥0∞) (E ω).2 = 0 := by rw [hω]; simp
      show readRec (retOf (s : ℝ≥0∞) (E ω)) = r₀
      unfold retOf readRec
      rw [h00]
      simp [hω, hz, hr₀]
    have hAs0 : ∀ᵐ ω ∂P, As ω = ∅ := by
      filter_upwards [hconst] with ω hω
      have hs0 : recS r₀ = 0 := by simp [hr₀, recS]
      simp only [hAsdef, hω, Supp8.Q3Rel.invHull, hs0, NNReal.coe_zero]
      rw [QuantumZipper.RS.fwdHull_zero_eq_empty (continuous_rdrv _), image_empty]
    refine ⟨le_sup_left.trans (comap_sup_nullSets_le_aeSigma_of_ae_const hconst),
      isHistoryAvoidanceLocal_of_mem_aeSigma hh₀m fun U G hUH hG hd F hF => ?_⟩
    have hFc := comap_sup_nullSets_le_aeSigma_of_ae_const
      (𝔪 := MeasurableSpace.comap (fun ω => markovCompl G (h₀ ω)) inferInstance) hconst F hF
    refine measurableSet_aeSigma_of_ae_eq hFc ?_
    filter_upwards [hAs0] with ω hω
    simp only [mem_inter_iff, mem_ofPred_eq, hω, empty_disjoint, true_and]
  -- the announcing stops `ρₙ = s ∧ σₙ`
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
  have hρs : ∀ n ω, ρ n ω ≤ s := fun n ω => by
    rw [hρdef, Supp8.GB6LineL.stopSeq_coe_eq]; exact min_le_left _ _
  have hc := isStoppingTime_const (drivingFiltration P hX) s
  have hρ𝓕 : ∀ n, (hρ n).measurableSpace ≤ drivingFiltration P hX s := fun n => by
    have h1 := (hρ n).measurableSpace_mono hc (fun ω => by
      show ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((s : ℝ≥0) : WithTop ℝ≥0)
      exact_mod_cast hρs n ω)
    rwa [IsStoppingTime.measurableSpace_const] at h1
  have hρζ : ∀ n, ∀ᵐ ω ∂P, ((ρ n ω : WithTop ℝ≥0) : ℝ≥0∞) < (E ω).2 := fun n => by
    filter_upwards [hσ.2.2.1 n] with ω hω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le _ σ n ω)) hω
  -- the record is read from the stopped histories
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
  obtain ⟨𝒥, h𝒥def⟩ : ∃ 𝒥 : {m : MeasurableSpace Ω // m ≤ mΩ}, 𝒥.1 = ⨆ n, (hρ n).measurableSpace :=
    ⟨⟨_, iSup_le fun n => (hρ n).measurableSpace_le⟩, rfl⟩
  have hρ𝒥 : ∀ n, (hρ n).measurableSpace ≤ 𝒥.1 := fun n => h𝒥def ▸ le_iSup (fun n => (hρ n).measurableSpace) n
  have hR' : Measurable[𝒥.1] (recVersion (s : ℝ≥0∞) ρ K) :=
    @measurable_recVersion Ω _ _ 𝒥.1 (s : ℝ≥0∞) ρ K
      (fun n => (measurable_stopSeq_of hσ.1 n).mono (hρ𝒥 n) le_rfl) (fun n => (hKm n).mono (hρ𝒥 n) le_rfl)
  have hgood := ae_isGoodStopPath hκ hEreg hC.1 hseed (s : ℝ≥0∞)
  have hfin : ∀ ω, min (s : ℝ≥0∞) (E ω).2 ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hRR' : ∀ᵐ ω ∂P, rs ω = recVersion (s : ℝ≥0∞) ρ K ω := by
    filter_upwards [hgood, hσ.2.2.2, ae_all_iff.2 hσ.2.2.1, hC.1.2.2.2.2] with ω hg hann hlt hp
    exact (recVersion_eq (s : ℝ≥0∞) (hg (hfin ω)) (hσ.2.1 ω) hlt hann fun n =>
      hKeq n ω hp (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le _ σ n ω)) (hlt n))).symm
  have h𝒥d : 𝒥.1 ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P :=
    h𝒥def ▸ iSup_le fun n => (hρ𝓕 n).trans (h𝓕 s)
  -- the record is determined
  have hrs𝒥 : ∀ C : Set RecData, MeasurableSet C →
      (rs ⁻¹' C : Set Ω) =ᵐ[P] (recVersion (s : ℝ≥0∞) ρ K ⁻¹' C : Set Ω) := fun C _ => by
    filter_upwards [hRR'] with ω hω
    change (rs ω ∈ C) = (recVersion (s : ℝ≥0∞) ρ K ω ∈ C)
    rw [hω]
  have hrsd : MeasurableSpace.comap rs inferInstance ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P := by
    rintro _ ⟨C, hC', rfl⟩
    exact measurableSet_aeSigma_of_ae_eq (h𝒥d _ (hR' hC')) (hrs𝒥 C hC')
  refine ⟨hrsd, isHistoryAvoidanceLocal_of_mem_aeSigma hh₀m fun U G hUH hG hd F hF => ?_⟩
  set Gs : Set Ω := {ω | Disjoint (As ω) U} with hGsdef
  have hGm : MeasurableSet Gs := hAsm (measurableSet_avoid U.isOpen hUH)
  have hGd : MeasurableSet[aeSigma (MeasurableSpace.comap h₀ inferInstance) P] Gs :=
    hrsd _ ⟨_, measurable_invHull_rec (measurableSet_avoid U.isOpen hUH), rfl⟩
  -- (1) the record hull is a local set of `h₀`: the hull at `min(s, ζ)` (Gaussian hull limit), reflected
  set W' : ℝ≥0 → Ω → ℝ := Theorem14.BW1Lines.pieceVer (fun _ => E) with hW'def
  have hW'good : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (E ω).2 → W' r ω = (E ω).1 r := by
    filter_upwards [hgood] with ω hg r hr
    have hg' := hg (hfin ω)
    rw [hW'def, Theorem14.BW1Lines.pieceVer_of_good (E := fun _ => E) (IsGoodStopPath.continuousOn_le hg')
      (hEreg ω).2.1,
      min_eq_left hr, ENNReal.toNNReal_coe]
  have hW'W : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E ω).2 → W' t ω = (E ω).1 t :=
    hW'good.mono fun ω hω t ht => hω t ht.le
  have hloc0 := Theorem14.BW1Lines.isLocalSet_centred_fwdHull_min_life hκ hC hu₀α
    (Theorem14.BW1Lines.pieceVer_zero _) (Theorem14.BW1Lines.continuous_pieceVer _) hW'W s
  have hKK : ∀ᵐ ω ∂P, fwdHull (rdrv (rs ω)) (recS (rs ω)) =
      fwdHull (Ito.rpath (W' · ω)) ((min (E ω).2 s).toNNReal : ℝ) := by
    filter_upwards [hgood, hW'good] with ω hg hW
    have h1 := fwdHull_rdrv_recOf_terminal (Theorem14.BW1Lines.continuous_pieceVer (fun _ => E) ω) (hg (hfin ω)) hW
    rw [← h1]
    congr 2
    simp only [recS, recOf, retOf, readRec, min_comm]
  have hlocK : IsLocalSet (fun ω => fwdHull (rdrv (rs ω)) (recS (rs ω))) (WholeField.centredField h u₀) P := by
    have e : WholeField.centredField h u₀ = WholeField.centredField h'' u₀α := funext hcc
    rw [e]
    exact Coupling.IsLocalSet.congr_set hloc0 hKK
  have hlocA : IsLocalSet As h₀ P := by
    have h1 := WangWu.IsLocalSet.reflect hlocK
    have e : (fun ω => WangWu.reflectField (WholeField.centredField h u₀ ω)) = h₀ := funext fun ω => (hcen ω).symm
    rw [e] at h1
    exact h1
  have hAsc : ∀ ω, As ω ⊆ H ∧ IsOpen (H \ As ω) := fun ω => by
    have hK := isHPHull_fwdHull (continuous_rdrv (rs ω)) (recS (rs ω)).coe_nonneg
    refine ⟨WangWu.image_negInv_subset_H hK.1, ?_⟩
    change IsOpen (H \ WangWu.negInv '' fwdHull (rdrv (rs ω)) (recS (rs ω)))
    rw [WangWu.H_diff_image_negInv]
    exact WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
      (recS (rs ω)).coe_nonneg) sdiff_subset
  have hAsLoc : IsAvoidanceLocal As h₀ P :=
    ((isLocalSet_tfae hh₀ hAsm (Eventually.of_forall hAsc)).out 4 1).1 hlocA
  have hGc : MeasurableSet[complSigma P G h₀] Gs := mem_complSigma_of_isAvoidanceLocal hh₀m hAsLoc hUH hG hd hGd
  -- (2) the stops before the lifetime: the reflected hulls there are marked local for the stopped σ-algebras
  have hAnex : ∀ n, ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧
      ∀ᵐ ω ∂P, A' ω = WangWu.negInv '' fwdHull (fun r : ℝ => (E ω).1 r.toNNReal)
        (((fun ω => (ρ n ω : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := fun n => by
    have hloc := (hC.2.2.2.2 _ (hρ n) (hρζ n)).1
    obtain ⟨A₀, hA₀m, hA₀e, -⟩ := WholeField.IsLocalSet.exists_measurable_version hloc hC.2.1
    refine ⟨fun ω => WangWu.negInv '' A₀ ω, WangWu.measurable_image_negInv.comp hA₀m, ?_⟩
    filter_upwards [hA₀e] with ω hω
    rw [hω]
  choose An hAnm hAnK using hAnex
  have hlocn : ∀ n, WholeField.IsHistoryAvoidanceLocal (hρ n).measurableSpace (An n) h₀ P := fun n => by
    have h1 := WangWu.isHistoryAvoidanceLocal_reflect_hull hC hκ hD hX (hρ n) (hρζ n) (hAnm n) (hAnK n)
    rwa [hfield] at h1
  have hsub : ∀ n, ∀ᵐ ω ∂P, ω ∈ Gs → Disjoint (An n ω) U := fun n => by
    filter_upwards [hAnK n, hgood, hρζ n] with ω hA hg hlt hωG
    have hg' := hg (hfin ω)
    have hle : ρ n ω ≤ (min (s : ℝ≥0∞) (E ω).2).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hfin ω)]
      exact le_min (ENNReal.coe_le_coe.2 (hρs n ω)) hlt.le
    rw [hA, WithTop.untopD_coe, Exist.StagedLaw.IsGoodStopPath.fwdHull_eq hg' hle hlt]
    refine Disjoint.mono_left (image_mono (WangWu.fwdHull_mono ?_)) hωG
    exact_mod_cast hle
  have hstep : ∀ n F', MeasurableSet[(hρ n).measurableSpace] F' →
      MeasurableSet[complSigma P G h₀] (Gs ∩ F') := fun n F' hF' =>
    inter_mem_complSigma_of_subset hh₀m (hlocn n) hUH hG hd ((hAnm n) (measurableSet_avoid U.isOpen hUH)) hGd hGc
      (hsub n) hF' ((hρ n).measurableSpace_le _ hF') ((hρ𝓕 n).trans (h𝓕 s) _ hF')
  -- (3) the record: its events are, up to null sets, events of the stopped σ-algebras
  have h𝒥t : 𝒥.1 ≤ WalkLaw.traceSigma (complSigma P G h₀) Gs hGc := h𝒥def ▸ iSup_le fun n F' hF' => hstep n F' hF'
  have hle : MeasurableSpace.comap rs inferInstance ⊔ Ito.nullSets P ≤
      WalkLaw.traceSigma (complSigma P G h₀) Gs hGc := by
    refine sup_le ?_ ?_
    · rintro _ ⟨C, hC', rfl⟩
      have h1 : MeasurableSet[complSigma P G h₀] (Gs ∩ recVersion (s : ℝ≥0∞) ρ K ⁻¹' C) := h𝒥t _ (hR' hC')
      change MeasurableSet[complSigma P G h₀] (Gs ∩ rs ⁻¹' C)
      exact measurableSet_aeSigma_of_ae_eq h1 (EventuallyEqSet.inter EventuallyEqSet.rfl (hrs𝒥 C hC'))
    · intro S hS
      change MeasurableSet[complSigma P G h₀] (Gs ∩ S)
      exact hGc.inter (nullSets_le_aeSigma _ hS)
  exact hle F hF

end InteractingSLE.Theorem14.BW1Safe
