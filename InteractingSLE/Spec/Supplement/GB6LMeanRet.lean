/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LMeanTransfer
import InteractingSLE.Spec.Supplement.GB6LineL3

/-!
# GB6's union mean, part 3: the mean of the retained set

Packet PROVE-GB6-LINEMEAN, the retained-set half of (L3). GB6's retained set `retSet s Wα ζα` (the inverted flow hull
read from the flow's record at the own time `s`, `ℍ` when the flow has died) is history-marked local for the centred
counterflow-frame field (`GB6LineL.exists_retained_marks`). Its local-set mean is identified on `{s < ζα}`
(**`ae_eqOn_retMean`**): the harmonic representative `w₁` satisfies `w₁ + 𝔥⁰′ = G₀ ∘ Ψ − χ(16/κ) Im relLog` for every
bounded harmonic extension `G₀` of the chart field's word — the input `hind₁` of the union mean.

Route (`planning/handoffs/PROVE-GB6-LINELOCAL.md` §4 (2)): along stops `ρₙ = s ∧ σₙ` announcing the flow's lifetime,
versions `Aₙ` of the reflected hulls `R(K_{ρₙ})` have the reflected flow mean (`Q3Chain.retained_at_stop`) and are
marked local for `𝓕_{ρₙ}` (`WangWu.isHistoryAvoidanceLocal_reflect_hull`), hitting-measurable for `𝓕_{ρₙ}`
(**`measurable_stop_of_ae_eq_reflect_hull`**: the stopped σ-algebra of the usual augmentation contains the null sets,
**`nullSets_le_stop`**); `Aₙ ⊆ retSet` and `Aₙ = retSet` on `Eₙ = {s ≤ σₙ} ∈ 𝓕_{ρₙ}`; the retained set is marked local
for `ℋ ⊔ 𝓕_{ρₙ}` (the union with `Aₙ`, `WalkLaw.isHistoryAvoidanceLocal_union_of_det`); so the two means agree on `Eₙ`
(`ae_eqOn_mean_of_marked`), and the word identity at the stop (`Q3Chain.retained_mean_identity`) finishes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Supp8.GB6LMean

open LocalSets

/-! ### Stopped σ-algebras of the usual augmentation -/

section Stop

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The stopped σ-algebra of the driving filtration contains the null sets** (the driving filtration is a usual
augmentation). -/
theorem nullSets_le_stop (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) : Ito.nullSets P ≤ hτ.measurableSpace := by
  refine MeasurableSpace.generateFrom_le fun N hN => ?_
  have hN' : MeasurableSet[Ito.nullSets P] N := MeasurableSpace.measurableSet_generateFrom hN
  refine ⟨le_iSup (drivingFiltration P hX) 0 N (Ito.nullSets_le_usualAugmentation _ _ 0 N hN'), fun i => ?_⟩
  have hNi : MeasurableSet (N ∩ {ω | τ ω ≤ i}) := hN.1.inter ((drivingFiltration P hX).le i _ (hτ i))
  have h0 : P (N ∩ {ω | τ ω ≤ i}) = 0 := measure_mono_null inter_subset_left hN.2
  exact Ito.nullSets_le_usualAugmentation _ _ i _ (MeasurableSpace.measurableSet_generateFrom ⟨hNi, h0⟩)

/-- **A version of the reflected hull at a stop is hitting-measurable for the stopped σ-algebra.** -/
theorem measurable_stop_of_ae_eq_reflect_hull (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : ℕ → Ω → ℝ≥0}
    (hσ : Coupling.IsAnnouncingSeq (drivingFiltration P hX) P ζ σ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hAe : ∀ᵐ ω ∂P, A ω = WangWu.negInv '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    Measurable[hτ.measurableSpace, hittingSigma] A := by
  have hnull := nullSets_le_stop hX hτ
  have hle : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  refine measurable_iff_comap_le.2 ?_
  rw [hittingSigma, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨_, ⟨V, hVo, hVH, rfl⟩, rfl⟩
  set U : Set ℂ := WangWu.negInv '' V with hUdef
  have hUo : IsOpen U := WangWu.isOpen_image_negInv hVo hVH
  have hUH : U ⊆ H := fun z ⟨w, hw, hwz⟩ => hwz ▸ WangWu.negInv_mem_H (hVH hw)
  have hG : ∀ p : ℚ × ℚ × ℚ, ∃ G : Set Ω, MeasurableSet[hτ.measurableSpace] G ∧ ∀ᵐ ω ∂P, (ω ∈ G ↔
      (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U →
        Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
          (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)))) := fun p => by
    by_cases hp : closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U
    · obtain ⟨G, hGm, hGe⟩ := WholeField.exists_measurableSet_ae_iff_disjoint hE hX hσ hτ hτζ
        (isCompact_closedBall _ _) (hp.trans hUH)
      refine ⟨G, hGm, ?_⟩
      filter_upwards [hGe] with ω hω
      simp only [hp, true_imp_iff]
      exact hω
    · exact ⟨univ, MeasurableSet.univ, Eventually.of_forall fun ω => by simp only [mem_univ, hp, false_imp_iff]⟩
  choose G hGm hGe using hG
  have hset : A ⁻¹' {S : Set ℂ | (S ∩ V).Nonempty} = {ω | Disjoint (A ω) V}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
  rw [hset]
  refine MeasurableSet.compl (Supp8.RelSafe.measurableSet_of_ae_eq hle hnull
    (hAm (measurableSet_avoid hVo hVH)) (MeasurableSet.iInter fun p => hGm p) ?_)
  have hall := ae_all_iff.2 hGe
  filter_upwards [hAe, hall] with ω hAω hGω
  change Disjoint (A ω) V = (ω ∈ ⋂ p, G p)
  rw [hAω, Q3Chain.avoid_negInv_iff, Q3Chain.disjoint_iff_forall_ratDisc hUo, mem_iInter]
  exact propext (forall_congr' fun p => (hGω p).symm)

end Stop

/-! ### The retained set read from the flow driver -/

section RetSet

open Exist.StagedLaw GB6 GB6LineL

/-- **The retained set is the inverted hull of the flow driver itself** on `{s < ζα}` (the record driver agrees with
the flow driver on `[0, s]`; both are continuous a little past `s`). -/
theorem retSet_eq_invHull {Ω : Type*} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {ω : Ω}
    (hs : (s : ℝ≥0∞) < ζα ω) (hW0 : Wα 0 ω = 0) (hWc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω}) :
    retSet s Wα ζα ω = Q3Rel.invHull (fun r : ℝ => Wα r.toNNReal ω) s := by
  rw [retSet_of_lt hs]
  obtain ⟨t₂, hst₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hst₂' : (s : ℝ) < t₂ := by exact_mod_cast hst₂
  have hct₂ : ContinuousOn (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (t₂ : ℝ)) := by
    refine hWc.comp continuous_real_toNNReal.continuousOn fun x hx => ?_
    show ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hx.2)) ht₂ζ
  have heq : EqOn (rdrv (gb6Rec s Wα ζα ω)) (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (s : ℝ)) := fun x hx =>
    rdrv_recOf_cfE s hW0 hWc hs hx.2
  unfold Q3Rel.invHull
  rw [LocalExt.fwdHull_congr_of_continuousOn (continuous_rdrv _).continuousOn hct₂ s.coe_nonneg hst₂' heq]

end RetSet

/-! ### The retained mean -/

section Ret

open Restart Sec7.StripSysField Exist.Staged Exist.StagedLaw GB6 GB6LineL Q3Chain

/-- **GB6's retained mean** (the input `hind₁` of the union mean). For a flow line of `h` with the data of the word
`c` whose killed histories are field-determined (Theorem 1.2's form), the counterflow-frame field `h′` with initial
extension `𝔥⁰′`, and every local-set mean `g₁` of the retained set `retSet s Wα ζα` for `h′ − 𝔥⁰′`: almost surely on
`{s < ζα}`, every harmonic representative `w₁` of `g₁` off the retained set satisfies
`w₁ + 𝔥⁰′ = G₀ ∘ Ψ − χ(16/κ) Im relLog` for every bounded harmonic extension `G₀` of the chart field's word. -/
theorem ae_eqOn_retMean {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {b' : ℝ → ℝ}
    {J' : Finset ℝ} (hG : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    (hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    {u₀' : ℂ → ℝ} (hu₀' : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    (hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀') P) (s : ℝ≥0)
    {g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg₁ : IsLocalSetMean (retSet s Wα ζα) (WholeField.centredField h' u₀') P g₁) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
          (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ retSet s Wα ζα ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ retSet s Wα ζα ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀' z)
            (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
              chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
            (H \ retSet s Wα ζα ω) := by
  classical
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData c
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu₀
  have hcen := centredField_eq_reflect hκ hb hG hb' hG' hT hu₀ hu₀'
  have hh₀m : Measurable (WholeField.centredField h' u₀') := hh0'.measurable
  -- the retained set is marked local (PROVE-GB6-LINELOCAL)
  obtain ⟨ℋ, -, hrecℋ, hℋd, hlocR⟩ := exists_retained_marks hκ hfl hdet hu₀ hh₀m (fun ω => hcen ω) s
  have hRℋ : Measurable[ℋ.1, hittingSigma] (retSet s Wα ζα) := (measurable_retOfRec s).comp hrecℋ
  have hrecm := (measurable_recOf_cfE hfl s).2
  have hRm : Measurable[mΩ, hittingSigma] (retSet s Wα ζα) := (measurable_retOfRec s).comp hrecm
  have hRc : ∀ᵐ ω ∂P, retSet s Wα ζα ω ⊆ H ∧ IsOpen (H \ retSet s Wα ζα ω) := hg₁.2.1.mono fun ω _ => by
    refine ⟨?_, ?_⟩
    · unfold retSet retOfRec
      split_ifs
      · exact WangWu.image_negInv_subset_H (QuantumZipper.fwdHull_mono.2 _)
      · exact subset_rfl
    · unfold retSet retOfRec
      split_ifs
      · rw [Q3Rel.compl_invHull]
        exact WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
          s.coe_nonneg) sdiff_subset
      · simp only [Set.sdiff_self, isOpen_empty]
  -- the flow coupling
  have hfl' := hfl
  obtain ⟨h'', 𝓕, VL, VR, Bα, htr, hC⟩ := hfl'
  have hX := hC.2.2.2.1
  obtain ⟨u₀α, hu₀α⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
    (flowLineXR c.fn c.jumps 0)
  have hrel := eqOn_bhe_flow_initial hκ θ hu₀ hu₀α
  have hcc : ∀ ω, WholeField.centredField h u₀ ω = WholeField.centredField h'' u₀α ω := fun ω => by
    rw [Sec7.SideHeight.centredField_eq_flowField htr hu₀.1 hu₀α.1 hrel ω, neg_zero, Sec5.GlueCond.flowField_zero_zero]
  set D : DistOn upperHalfPlaneOpens :=
    WangWu.reflectField (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀α) with hDdef
  have hfield : (fun ω => WangWu.reflectField (h'' ω) - D) = WholeField.centredField h' u₀' := funext fun ω => by
    rw [hcen ω, hcc ω, WholeField.centredField, WangWu.reflectField_sub]
  have hh'' : ∀ ω, h'' ω = WangWu.reflectField (WholeField.centredField h' u₀' ω) +
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀α := fun ω => by
    rw [hcen ω, WangWu.reflectField_reflectField, hcc ω, WholeField.centredField, sub_add_cancel]
  have hD : IsHarmonicDistOn D H := by
    have h1 := WangWu.isHarmonicDistOn_reflectField QuantumZipper.isOpen_H subset_rfl
      (WholeField.isHarmonicDistOn_smoothDist hu₀α.1)
    rwa [image_negInv_H] at h1
  -- determination of the flow's history
  have hd := hdet P 𝓕 Wα VL VR Bα ζα h'' hC
  have hcomap : MeasurableSpace.comap h'' inferInstance ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap ((WholeField.measurable_add_dist _).comp WangWu.measurable_reflectField)
      (Eventually.of_forall hh'')
  have h𝓕 : ∀ t, drivingFiltration P hX t ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P := fun t =>
    (drivingFiltration_le_aeSigma hd hX t).trans (aeSigma_le_of_le hcomap)
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · -- an inadmissible seed: the flow dies at once
    have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    filter_upwards [h0] with ω hω hs
    rw [hω] at hs
    exact absurd hs ENNReal.not_lt_zero
  -- stops announcing the flow's lifetime
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := Bα)
    (κ := κ) (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hC.1.2.2.2.2 (hC.1.ae_tendsto_threshold hκ) hseed
  set τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => ((min s (σ n ω) : ℝ≥0) : WithTop ℝ≥0) with hτdef
  have hτ : ∀ n, IsStoppingTime (drivingFiltration P hX) (τ n) := fun n => by
    have h1 := (isStoppingTime_const (drivingFiltration P hX) s).min (hσ.1 n)
    have e : (fun ω => min ((s : ℝ≥0) : WithTop ℝ≥0) ((σ n ω : ℝ≥0) : WithTop ℝ≥0)) = τ n :=
      funext fun ω => by simp only [hτdef, WithTop.coe_min]
    rwa [e] at h1
  have hτζ : ∀ n, ∀ᵐ ω ∂P, (τ n ω : ℝ≥0∞) < ζα ω := fun n => by
    filter_upwards [hσ.2.2.1 n] with ω hω
    refine lt_of_le_of_lt ?_ hω
    simp only [hτdef]
    exact ENNReal.coe_le_coe.2 (min_le_right s (σ n ω))
  set u : ℕ → Ω → ℂ → ℝ := fun n ω => (exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
    (fun i => VL i ((τ n ω).untopD 0) ω - Wα ((τ n ω).untopD 0) ω)
    (fun i => VR i ((τ n ω).untopD 0) ω - Wα ((τ n ω).untopD 0) ω)).choose with hudef
  have hu : ∀ n ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => VL i ((τ n ω).untopD 0) ω - Wα ((τ n ω).untopD 0) ω)
        (fun i => VR i ((τ n ω).untopD 0) ω - Wα ((τ n ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ n ω).untopD 0) ω - Wα ((τ n ω).untopD 0) ω)
        (fun i => VR i ((τ n ω).untopD 0) ω - Wα ((τ n ω).untopD 0) ω)) (u n ω) := fun n ω =>
    (exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  -- the reflected hulls at the stops, with their means
  have hpack := fun n => retained_at_stop hκ htr hC hX (hτ n) (hτζ n) hu₀ hh0 hcen (hu n)
  choose A hAm hAG hAe hAloc hAmean using hpack
  have hτs : ∀ n ω, s ≤ σ n ω → ((τ n ω).untopD 0 : ℝ≥0) = s := fun n ω h => by
    simp only [hτdef, WithTop.untopD_coe, min_eq_left h]
  -- the pieces are marked local and hitting-measurable for the stopped σ-algebras
  have hAst : ∀ n, Measurable[(hτ n).measurableSpace, hittingSigma] (A n) := fun n =>
    measurable_stop_of_ae_eq_reflect_hull hC.1 hX hσ (hτ n) (hτζ n) (hAm n) (hAe n)
  have hlocA : ∀ n, WholeField.IsHistoryAvoidanceLocal (hτ n).measurableSpace (A n)
      (WholeField.centredField h' u₀') P := fun n => by
    have h1 := WangWu.isHistoryAvoidanceLocal_reflect_hull hC hκ hD hX (hτ n) (hτζ n) (hAm n) (hAe n)
    rwa [hfield] at h1
  have h𝒦d : ∀ n, (hτ n).measurableSpace ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P := fun n =>
    stopping_measurableSpace_le_aeSigma h𝓕 (hτ n) (fun _ => WithTop.coe_ne_top)
  -- the pieces lie in the retained set, and equal it on `{s ≤ σₙ}`
  have hsub : ∀ n, ∀ᵐ ω ∂P, A n ω ⊆ retSet s Wα ζα ω := fun n => by
    filter_upwards [hAe n, hC.1.2.2.2.2] with ω hAω hp
    by_cases hsζ : (s : ℝ≥0∞) < ζα ω
    · rw [retSet_eq_invHull hsζ hp.1 hp.2.2.2.1, hAω]
      refine image_mono (QuantumZipper.fwdHull_mono.1 ?_)
      simp only [hτdef, WithTop.untopD_coe, NNReal.coe_min]
      exact min_le_left _ _
    · rw [retSet_of_le (not_lt.1 hsζ)]
      exact (hAG n ω).1
  have hEq : ∀ n, ∀ᵐ ω ∂P, ω ∈ {ω | s ≤ σ n ω} → A n ω = retSet s Wα ζα ω := fun n => by
    filter_upwards [hAe n, hC.1.2.2.2.2, hσ.2.2.1 n] with ω hAω hp hσζ hωE
    have hsζ : (s : ℝ≥0∞) < ζα ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hωE) hσζ
    rw [retSet_eq_invHull hsζ hp.1 hp.2.2.2.1, hAω, hτs n ω hωE]
    rfl
  have hEm : ∀ n, MeasurableSet[(hτ n).measurableSpace] {ω | s ≤ σ n ω} := fun n => by
    have h1 := (hτ n).measurableSet_ge' s
    have e : {ω | ((s : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω} = {ω | s ≤ σ n ω} := by
      ext ω
      simp only [mem_ofPred_eq, hτdef, WithTop.coe_le_coe, le_min_iff, le_refl, true_and]
    rwa [e] at h1
  -- the retained set is marked local for `ℋ ⊔ 𝓕_{ρₙ}`
  have hlocR' : ∀ n, WholeField.IsHistoryAvoidanceLocal (ℋ.1 ⊔ (hτ n).measurableSpace) (retSet s Wα ζα)
      (WholeField.centredField h' u₀') P := fun n => by
    have hU := Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det hh₀m (A₁ := retSet s Wα ζα) (A₂ := A n)
      (fun U hUH => hRℋ (measurableSet_avoid U.isOpen hUH)) (fun U hUH => hAst n (measurableSet_avoid U.isOpen hUH))
      hℋd (h𝒦d n) hlocR (hlocA n)
    refine Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ hU
    filter_upwards [hsub n] with ω hω
    exact union_eq_left.2 hω
  -- the means agree on `{s ≤ σₙ}`
  have hgA : ∀ n, ∃ gA : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A n) (WholeField.centredField h' u₀') P gA :=
    fun n => Sec5.Aux61SlitV.exists_isLocalSetMean_of_isHistoryAvoidanceLocal hh0' (hAm n)
      (Eventually.of_forall fun ω => hAG n ω) (hlocA n)
  choose gA hgA using hgA
  have htr' : ∀ n, ∀ᵐ ω ∂P, ω ∈ {ω | s ≤ σ n ω} → ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ H \ retSet s Wα ζα ω → g₁ ω φ = gA n ω φ := fun n =>
    ae_eqOn_mean_of_marked hh0' (hAm n) hRm (Eventually.of_forall fun ω => hAG n ω) hRc le_sup_right
      (sup_le ℋ.2 (hτ n).measurableSpace_le) (hlocA n) (hlocR' n) ((hAst n).mono le_sup_right le_rfl) (hsub n)
      (hEm n) (hEq n) (hgA n) hg₁
  -- the word identity at the stop
  filter_upwards [ae_all_iff.2 htr', ae_all_iff.2 fun n => hAmean n (gA n) (hgA n), ae_all_iff.2 hEq,
    ae_all_iff.2 hAe, hC.1.2.2.2.2, ae_gap_eq_markPos hC, hσ.2.2.2] with ω htrω hmω hEqω hAeω hp hgap hann hs
    G₀ hG₀ w₁ hw₁ hr₁
  obtain ⟨n, hωE⟩ := hann s hs
  have hωE' : s ≤ σ n ω := hωE
  have hτω := hτs n ω hωE'
  have hAR : A n ω = retSet s Wα ζα ω := hEqω n hωE
  have hmn := hmω n
  have hAω := hAeω n
  rw [hτω] at hmn hAω
  rw [← hAR] at hw₁ hr₁ ⊢
  -- the record of the flow prefix
  set r := GB6.gb6Rec s Wα ζα ω with hr
  have hW0 : Wα 0 ω = 0 := hp.1
  have hWc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω} := hp.2.2.2.1
  have hrt : rtime r = s := GB6.rtime_recOf_cfE s hs
  have hrd : ∀ x : ℝ, x ≤ s → rdrv r x = Wα x.toNNReal ω := fun x hx => GB6.rdrv_recOf_cfE s hW0 hWc hs hx
  obtain ⟨hL, hR⟩ := hgap (rdrv r) (continuous_rdrv r) (rdrv_zero r) s hs fun s' hs' => by
    rw [hrd s' (by exact_mod_cast hs'), Real.toNNReal_coe]
  -- the flow's extension at `s` has the record's flowed marks
  have hus : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)))
      (forceJumpSet (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j))) (u n ω) := by
    have h1 := hu n ω
    rw [hτω] at h1
    simp only [hL, hR] at h1
    rw [hrt]
    exact h1
  -- the extensions
  have hsw := isSorted_stopWord κ (c, θ, r)
  have hFb := BoundaryWord.isBoundedHarmonicExtension_mean _ hsw
  have hFu := eqOn_bhe_stopWord κ θ c r hFb hus
  have hGret : EqOn G₀ (retFn (Real.pi * chiC κ) (chiC κ) (stopWord κ (c, θ, r)).mean) H :=
    eqOn_bhe_cfData_retWord (k := 16 / κ) (by positivity) hsw (Real.pi * chiC κ) (chiC κ) hFb hG₀
  have hu0ret := eqOn_bhe_cfData_return hκ hb hG hb' hG' hT hu₀ hu₀'
  -- a continuous driver equal to the flow driver past `s`
  obtain ⟨t₂, hst₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hst₂' : (s : ℝ) < t₂ := by exact_mod_cast hst₂
  have hct₂ : ContinuousOn (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (t₂ : ℝ)) := by
    refine hWc.comp continuous_real_toNNReal.continuousOn fun x hx => ?_
    show ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hx.2)) ht₂ζ
  set V : ℝ → ℝ := Ito.clampDrv (fun r : ℝ => Wα r.toNNReal ω) t₂ with hVdef
  have hV : Continuous V := Ito.continuous_clampDrv t₂.coe_nonneg hct₂
  have hVeq : ∀ x ∈ Icc (0 : ℝ) t₂, Wα x.toNNReal ω = V x := fun x hx =>
    (Ito.clampDrv_eqOn (W := fun r : ℝ => Wα r.toNNReal ω) (T := (t₂ : ℝ)) hx).symm
  have hfM : ∀ y, fwdMap (fun r : ℝ => Wα r.toNNReal ω) s y = fwdMap V s y := fun y =>
    fwdMap_eq_of_eqOn s.coe_nonneg fun x hx => hVeq x ⟨hx.1, hx.2.trans hst₂'.le⟩
  have hfK : fwdHull (fun r : ℝ => Wα r.toNNReal ω) s = fwdHull V s :=
    fwdHull_eq_of_eqOn s.coe_nonneg hst₂' hVeq
  -- the reflected flow mean is harmonic off `A`
  have hmaps : ∀ z ∈ H \ A n ω, -z⁻¹ ∈ H \ fwdHull (fun r : ℝ => Wα r.toNNReal ω) s := by
    intro z hz
    refine ⟨WangWu.negInv_mem_H hz.1, fun hK => hz.2 ?_⟩
    rw [hAω]
    exact ⟨-z⁻¹, hK, by change -(-z⁻¹)⁻¹ = z; rw [inv_neg, inv_inv, neg_neg]⟩
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean_rpath (κ := κ) hWc hs (hus.1)
  have hin : InnerProductSpace.HarmonicOnNhd
      (fun y => couplingMean κ (fun r : ℝ => Wα r.toNNReal ω) s (u n ω) y - θ * chiC κ - u₀ y)
      (H \ fwdHull (fun r : ℝ => Wα r.toNNReal ω) s) := fun y hy =>
    ((hcm y hy).sub (InnerProductSpace.harmonicAt_const _)).sub (hu₀.1 y hy.1)
  have hKo : IsOpen (H \ fwdHull (fun r : ℝ => Wα r.toNNReal ω) s) := by
    rw [hfK]
    exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull hV s.coe_nonneg
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => -z⁻¹) (H \ A n ω) := fun z hz =>
    ((differentiableAt_inv (mem_H_ne_zero hz.1)).neg).differentiableWithinAt
  have hcomp := LQGMetric.harmonicOnNhd_comp_holo hKo (hAG n ω).2 hin hdiff hmaps
  set m' : ℂ → ℝ := fun z => -(couplingMean κ (fun r : ℝ => Wα r.toNNReal ω) s (u n ω) (-z⁻¹) -
    θ * chiC κ - u₀ (-z⁻¹)) with hm'
  have hm'h : InnerProductSpace.HarmonicOnNhd m' (H \ A n ω) := fun z hz => (hcomp z hz).neg
  have heq : EqOn w₁ m' (H \ A n ω) :=
    Sec6.eqOn_of_integral_mul_eq (hAG n ω).2 sdiff_subset hw₁ hm'h fun φ hφ => by
      rw [← hr₁ φ hφ, htrω n hωE φ (by rw [← hAR]; exact hφ), hmn φ hφ]
  intro z hz
  have hRz := hmaps z hz
  have hξ : fwdMap (fun r : ℝ => Wα r.toNNReal ω) s (-z⁻¹) ∈ H := by
    rw [hfM]
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hV s.coe_nonneg (by rw [← hfK]; exact hRz)
  have hΨ : GB6.relMap (fun r : ℝ => Wα r.toNNReal ω) s z ∈ H := WangWu.negInv_mem_H hξ
  have key := retained_mean_identity hκ hz.1 hξ θ (u := u n ω) (u₀ := u₀) (u₀' := u₀')
    (hFu hξ) (hGret hΨ) (hu0ret hz.1)
  show w₁ z + u₀' z = _
  rw [heq hz]
  exact key

end Ret

end InteractingSLE.Supp8.GB6LMean
