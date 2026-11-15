/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LMeanRet

/-!
# GW2's stage step, part 1: the retained hull and its mean at a stopping time

Packet PROVE-GW2-STAGEMEAN (ruling R106). At stage `k + 1` of GW2's stage identity the retained counterflow is no
longer read at a deterministic own time: conditionally on the earlier pieces it is the complete counterflow of the
stage field, read up to the random own time `σ_k` at which its image of the original stopped hull is exhausted (a
stopping time of its own driving filtration). This file supplies the retained half of GB6's union mean at such a
stopping time (`Supp8.GB6LMean.ae_eqOn_retMean` is the deterministic-time case):

* **`exists_retMean_stop`**: for a flow line coupling of `h` (GB6 frame: the curve read as the retained set is the
  coupling's curve) and a finite stopping time `τ < ζα` of its driving filtration, a version `A` of the inverted hull
  `invHull Wα τ` that is hitting-measurable for the stopped σ-algebra, field-determined, history-marked local for the
  stopped σ-algebra and a local set of the centred counterflow-frame field `h′ − 𝔥⁰′`; every local-set mean `g₁` of
  `A` has harmonic representatives `w₁` with `w₁ + 𝔥⁰′ = G₀ ∘ Ψ − χ(16/κ) Im relLog` (`Ψ = relMap Wα τ`) for every
  bounded harmonic extension `G₀` of the chart field's word read from the record at `τ`.

The proof is the deterministic-time proof without its announcing comparison: at a stopping time the reflected hull
itself is the retained set (`Q3Chain.retained_at_stop`), and the word identity at the stop
(`Q3Chain.retained_mean_identity`) finishes. Conditional helper with a distinct name; it replaces no source theorem.
No `κ < 4` hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Stm

open LocalSets Restart Sec7.StripSysField Exist.Staged Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6LineL
  Supp8.Q3Chain Supp8.GB6LMean

/-- **GB6's retained set and its mean at a stopping time** (the input `hind₁` of the union mean, and the retained
set's locality, at a finite stopping time `τ < ζα` of the retained curve's driving filtration). -/
theorem exists_retMean_stop {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {b' : ℝ → ℝ}
    {J' : Finset ℝ} (hG : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {Bα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h'' ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) P 𝓕 Wα VL VR Bα ζα h'')
    (hX : IsMeasurableKilledDriving Wα VL VR ζα)
    (hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    {u₀' : ℂ → ℝ} (hu₀' : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτt : ∀ ω, τ ω ≠ ⊤)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = Q3Rel.invHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      Measurable[hτ.measurableSpace, hittingSigma] A ∧
      hτ.measurableSpace ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace A (WholeField.centredField h' u₀') P ∧
      IsLocalSet A (WholeField.centredField h' u₀') P ∧
      ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (WholeField.centredField h' u₀') P g₁ →
        ∀ᵐ ω ∂P, ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
            (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec ((τ ω).untopD 0) Wα ζα ω)).fn
              (gb6WordOfRec κ θ c (gb6Rec ((τ ω).untopD 0) Wα ζα ω)).jumps)
            (cfJumps (gb6WordOfRec κ θ c (gb6Rec ((τ ω).untopD 0) Wα ζα ω)).fn
              (gb6WordOfRec κ θ c (gb6Rec ((τ ω).untopD 0) Wα ζα ω)).jumps) G₀ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀' z)
              (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) z) -
                chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) z).im)
              (H \ A ω) := by
  classical
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData c
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu₀
  have hcen := centredField_eq_reflect hκ hb hG hb' hG' hT hu₀ hu₀'
  -- the two frames of the flow coupling
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
  have h𝒦d : hτ.measurableSpace ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P :=
    stopping_measurableSpace_le_aeSigma h𝓕 hτ hτt
  -- the force data at the stop and the reflected hull at the stop
  set u : Ω → ℂ → ℝ := fun ω => (exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
    (fun i => VL i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)
    (fun i => VR i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)).choose with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => VL i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)) (u ω) := fun ω =>
    (exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  obtain ⟨A, hAm, hAG, hAe, hAloc, hAmean⟩ := retained_at_stop hκ htr hC hX hτ hτζ hu₀ hh0 hcen hu
  have hlocA : WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace A (WholeField.centredField h' u₀') P := by
    have h1 := WangWu.isHistoryAvoidanceLocal_reflect_hull hC hκ hD hX hτ hτζ hAm hAe
    rwa [hfield] at h1
  -- hitting-measurability for the stopped σ-algebra (an announcing sequence of the lifetime)
  have hAst : Measurable[hτ.measurableSpace, hittingSigma] A := by
    by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ)
        (flowLineRhoR κ c.fn c.jumps 0 θ) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
    · exfalso
      have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
      have hF : ∀ᵐ ω ∂P, False := by
        filter_upwards [h0, hτζ] with ω hω hlt
        rw [hω] at hlt
        exact ENNReal.not_lt_zero hlt
      obtain ⟨_, hω⟩ := hF.exists
      exact hω
    have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := Bα)
      (κ := κ) (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0)
      (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
      hC.1.2.2.2.2 (hC.1.ae_tendsto_threshold hκ) hseed
    exact measurable_stop_of_ae_eq_reflect_hull hC.1 hX hσ hτ hτζ hAm hAe
  refine ⟨A, hAm, hAG, ?_, hAst, h𝒦d, hlocA, hAloc, ?_⟩
  · filter_upwards [hAe] with ω hω
    rw [hω]
    rfl
  intro g₁ hg₁
  filter_upwards [hAmean g₁ hg₁, hAe, hC.1.2.2.2.2, ae_gap_eq_markPos hC, hτζ] with ω hmω hAω hp hgap hτω
    G₀ hG₀ w₁ hw₁ hr₁
  set T : ℝ≥0 := (τ ω).untopD 0 with hTdef
  have hs : (T : ℝ≥0∞) < ζα ω := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hτt ω)
    have e : T = t := by rw [hTdef, ← ht, WithTop.untopD_coe]
    rw [e]
    rw [← ht] at hτω
    exact hτω
  -- the record of the retained prefix
  set r := gb6Rec T Wα ζα ω with hr
  have hW0 : Wα 0 ω = 0 := hp.1
  have hWc : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω} := hp.2.2.2.1
  have hrt : rtime r = T := rtime_recOf_cfE T hs
  have hrd : ∀ x : ℝ, x ≤ T → rdrv r x = Wα x.toNNReal ω := fun x hx => rdrv_recOf_cfE T hW0 hWc hs hx
  obtain ⟨hL, hR⟩ := hgap (rdrv r) (continuous_rdrv r) (rdrv_zero r) T hs fun s' hs' => by
    rw [hrd s' (by exact_mod_cast hs'), Real.toNNReal_coe]
  have hus : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)))
      (forceJumpSet (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j))) (u ω) := by
    have h1 := hu ω
    simp only [← hTdef, hL, hR] at h1
    rw [hrt]
    exact h1
  -- the extensions
  have hsw := isSorted_stopWord κ (c, θ, r)
  have hFb := BoundaryWord.isBoundedHarmonicExtension_mean _ hsw
  have hFu := eqOn_bhe_stopWord κ θ c r hFb hus
  have hGret : EqOn G₀ (retFn (Real.pi * chiC κ) (chiC κ) (stopWord κ (c, θ, r)).mean) H :=
    eqOn_bhe_cfData_retWord (k := 16 / κ) (by positivity) hsw (Real.pi * chiC κ) (chiC κ) hFb hG₀
  have hu0ret := eqOn_bhe_cfData_return hκ hb hG hb' hG' hT hu₀ hu₀'
  -- a continuous driver equal to the flow driver past `T`
  obtain ⟨t₂, hst₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hst₂' : (T : ℝ) < t₂ := by exact_mod_cast hst₂
  have hct₂ : ContinuousOn (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (t₂ : ℝ)) := by
    refine hWc.comp continuous_real_toNNReal.continuousOn fun x hx => ?_
    show ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hx.2)) ht₂ζ
  set V : ℝ → ℝ := Ito.clampDrv (fun r : ℝ => Wα r.toNNReal ω) t₂ with hVdef
  have hV : Continuous V := Ito.continuous_clampDrv t₂.coe_nonneg hct₂
  have hVeq : ∀ x ∈ Icc (0 : ℝ) t₂, Wα x.toNNReal ω = V x := fun x hx =>
    (Ito.clampDrv_eqOn (W := fun r : ℝ => Wα r.toNNReal ω) (T := (t₂ : ℝ)) hx).symm
  have hfM : ∀ y, fwdMap (fun r : ℝ => Wα r.toNNReal ω) T y = fwdMap V T y := fun y =>
    fwdMap_eq_of_eqOn T.coe_nonneg fun x hx => hVeq x ⟨hx.1, hx.2.trans hst₂'.le⟩
  have hfK : fwdHull (fun r : ℝ => Wα r.toNNReal ω) T = fwdHull V T :=
    fwdHull_eq_of_eqOn T.coe_nonneg hst₂' hVeq
  -- the reflected flow mean is harmonic off `A`
  have hmaps : ∀ z ∈ H \ A ω, -z⁻¹ ∈ H \ fwdHull (fun r : ℝ => Wα r.toNNReal ω) T := by
    intro z hz
    refine ⟨WangWu.negInv_mem_H hz.1, fun hK => hz.2 ?_⟩
    rw [hAω]
    exact ⟨-z⁻¹, hK, by change -(-z⁻¹)⁻¹ = z; rw [inv_neg, inv_inv, neg_neg]⟩
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean_rpath (κ := κ) hWc hs (hus.1)
  have hin : InnerProductSpace.HarmonicOnNhd
      (fun y => couplingMean κ (fun r : ℝ => Wα r.toNNReal ω) T (u ω) y - θ * chiC κ - u₀ y)
      (H \ fwdHull (fun r : ℝ => Wα r.toNNReal ω) T) := fun y hy =>
    ((hcm y hy).sub (InnerProductSpace.harmonicAt_const _)).sub (hu₀.1 y hy.1)
  have hKo : IsOpen (H \ fwdHull (fun r : ℝ => Wα r.toNNReal ω) T) := by
    rw [hfK]
    exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull hV T.coe_nonneg
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => -z⁻¹) (H \ A ω) := fun z hz =>
    ((differentiableAt_inv (mem_H_ne_zero hz.1)).neg).differentiableWithinAt
  have hcomp := LQGMetric.harmonicOnNhd_comp_holo hKo (hAG ω).2 hin hdiff hmaps
  set m' : ℂ → ℝ := fun z => -(couplingMean κ (fun r : ℝ => Wα r.toNNReal ω) T (u ω) (-z⁻¹) -
    θ * chiC κ - u₀ (-z⁻¹)) with hm'
  have hm'h : InnerProductSpace.HarmonicOnNhd m' (H \ A ω) := fun z hz => (hcomp z hz).neg
  have heq : EqOn w₁ m' (H \ A ω) :=
    Sec6.eqOn_of_integral_mul_eq (hAG ω).2 sdiff_subset hw₁ hm'h fun φ hφ => by
      rw [← hr₁ φ hφ, hmω φ hφ]
  intro z hz
  have hRz := hmaps z hz
  have hξ : fwdMap (fun r : ℝ => Wα r.toNNReal ω) T (-z⁻¹) ∈ H := by
    rw [hfM]
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hV T.coe_nonneg (by rw [← hfK]; exact hRz)
  have hΨ : relMap (fun r : ℝ => Wα r.toNNReal ω) T z ∈ H := WangWu.negInv_mem_H hξ
  have key := retained_mean_identity hκ hz.1 hξ θ (u := u ω) (u₀ := u₀) (u₀' := u₀')
    (hFu hξ) (hGret hΨ) (hu0ret hz.1)
  show w₁ z + u₀' z = _
  rw [heq hz]
  exact key

end InteractingSLE.Theorem14.GW2Stm
