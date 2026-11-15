/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainDet
import InteractingSLE.Spec.Sec5.CrossRestartKernelUnionMean
import InteractingSLE.Spec.Restart.MarkovChart

/-!
# The retained-set mean of GB6 (`hind₁`) and its locality (`hlA`)

Packet PROVE-Q3-REL3, inputs `hlA` and `hind₁` of `Q3Chain.ae_eqOn_unionMean_gb6`: in the counterflow frame (field
`h'`, the original field `h` read through `R(z) = −1/z`), the retained flow prefix `A = R(K^α_s)` is a local set of the
centred field, and its local-set mean is the chart field's word read through GB6's retained chart
(`G₀ ∘ Ψ − χ(16/κ) Im relLog`). Route: the flow's own hull mean
(`Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull`)
at the stopping times `τₙ = s ∧ σₙ` (`σₙ` announcing the flow's lifetime), reflected by `R`
(`WangWu.IsLocalSet.reflect`, `WangWu.IsLocalSetMean.reflect`), and the deterministic identities of `Q3ChainRet`.

* `centredField_eq_reflect`: the centred counterflow-frame field is the reflection of the centred original field
  (`h' = returnField (πχ) χ h` and the counterflow's initial extension is the return transform of the original one);
* `eqOn_bhe_flow_initial`: the flow's initial extension is the original one plus `θχ`;
* `retained_at_stop`: the retained set at one stopping time of the flow, its locality and its mean;
* **`exists_retained_package_of_coupling`**, `exists_retained_package`: the retained sets along stops announcing the
  flow's lifetime, with `hlA`, `hind₁` in `ae_eqOn_unionMean_gb6`'s form and (given a field-determined flow history)
  field determination of the retained sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Supp8.Q3Chain

open Restart Sec7.StripSysField LocalSets

/-- **The centred counterflow-frame field is the reflection of the centred original field** (GB6's frames). -/
theorem centredField_eq_reflect {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {u₀ u₀' : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    (hu₀' : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀') (ω : Ω) :
    WholeField.centredField h' u₀' ω = WangWu.reflectField (WholeField.centredField h u₀ ω) := by
  have hR := eqOn_bhe_cfData_return hκ hb hG hb' hG' hT hu₀ hu₀'
  have e1 := GB6.eq_returnField_of_isChartTransport_R hκ (hT ω)
  ext φ
  rw [WholeField.centredField_apply h' hu₀'.1, WangWu.reflectField_apply, WholeField.centredField_apply h hu₀.1,
    e1, returnField_apply]
  set ψ := Chart.pushTest isConformal_infinityReturnChart φ with hψ
  have hcm : ContinuousOn (fun z => u₀ (-z⁻¹)) H := fun z hz =>
    ((hu₀.1 _ (negInv_mem_H hz)).1.continuousAt.comp (f := fun w : ℂ => -w⁻¹)
      ((continuousAt_inv₀ (mem_H_ne_zero hz)).neg)).continuousWithinAt
  have hpush : ∫ z, u₀ z * ψ z = ∫ w, u₀ (-w⁻¹) * φ w :=
    Chart.integral_mul_pushTest isConformal_infinityReturnChart φ u₀
  have hlift := continuousOn_infinitySourceChart_lift'
  have i1 : Integrable fun w => u₀ (-w⁻¹) * φ w := WholeField.integrable_mul_testOn hcm φ φ.tsupport_subset
  have i2 : Integrable fun w => φ w := by
    simpa only [one_mul] using WholeField.integrable_mul_testOn (f := fun _ => (1 : ℝ)) continuousOn_const φ
      φ.tsupport_subset
  have i3 : Integrable fun w => infinitySourceChart.2.2 w * φ w :=
    WholeField.integrable_mul_testOn hlift φ φ.tsupport_subset
  have hu' : ∫ z, u₀' z * φ z = ∫ w, (-(u₀ (-w⁻¹) * φ w) + Real.pi * chiC κ * φ w +
      chiC κ * (infinitySourceChart.2.2 w * φ w)) := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · simp only [hR hw, retFn]
      ring
    · have : φ w = 0 := φ.zero_on_compl (show w ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hw)
      simp [this]
  have j1 : Integrable (fun w => -(u₀ (-w⁻¹) * φ w)) := i1.neg
  have j2 : Integrable (fun w => Real.pi * chiC κ * φ w) := i2.const_mul _
  have j3 : Integrable (fun w => chiC κ * (infinitySourceChart.2.2 w * φ w)) := i3.const_mul _
  have j12 : Integrable (fun w => -(u₀ (-w⁻¹) * φ w) + Real.pi * chiC κ * φ w) := j1.add j2
  rw [hu', integral_add j12 j3, integral_add j1 j2, integral_neg, integral_const_mul, integral_const_mul, hpush]
  ring


/-! ### The retained set at a stopping time of the flow -/

/-- **The flow's initial extension is the original one plus `θχ`** (`Sec4.forceBoundaryData_flowLine_seed` at the
seed `0`). -/
theorem eqOn_bhe_flow_initial {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) {c : BoundaryWord} {u₀ u₀α : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension c.fn c.jumps u₀)
    (hu₀α : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
      (forceJumpSet (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)) u₀α) :
    EqOn u₀α (fun z => u₀ (z + (0 : ℝ)) + θ * chiC κ) H := by
  set S' : Finset ℝ := insert 0 (c.jumps ∪ initJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    with hS'
  have h1 : IsBoundedHarmonicExtension (fun x => c.fn x - -(θ * chiC κ)) (S' : Set ℝ)
      (fun z => u₀ z - -(θ * chiC κ)) := by
    refine LocalExt.IsBoundedHarmonicExtension.mono_set (bhe_sub_const hu₀ (-(θ * chiC κ))) fun x hx => ?_
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    exact Or.inr (Or.inl hx)
  have h2 := LocalExt.IsBoundedHarmonicExtension.mono_set hu₀α (S' := (S' : Set ℝ)) fun x hx => by
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    rw [← coe_initJumps] at hx
    exact Or.inr (Or.inr hx)
  have h3 : IsBoundedHarmonicExtension (fun x => c.fn x - -(θ * chiC κ)) (S' : Set ℝ) u₀α := by
    refine (Restart.isBoundedHarmonicExtension_congr (fun x hx => ?_) _).1 h2
    have hx0 : x ≠ 0 := fun h => hx (Finset.mem_coe.2 (h ▸ Finset.mem_insert_self _ _))
    have hxJ : x + 0 ∉ c.jumps := by
      rw [add_zero]
      exact fun h => hx (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
    rw [Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData c) 0 θ hx0 hxJ,
      add_zero]
    ring
  intro z hz
  have := Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet S') h1 h3 hz
  simp only [this, Complex.ofReal_zero, add_zero, sub_neg_eq_add]


/-- **The retained set at a stopping time of the flow, its locality and its mean, in the counterflow frame.** For the
flow's coupling (field `h'' = h + θχ`, word of `c`), a stopping time `τ < ζα` of its driving filtration and GB6's
frames (`centred h' = R_*(centred h)`): there is a hitting-measurable version `A` of `R(K^α_τ)` (`R(z) = −1/z`),
relatively closed in `ℍ` on every sample, which is a local set of the centred `h'`, and every local-set mean `g₁` of
`A` is, off `A`, the reflected flow mean `z ↦ −(𝔥_τ(−1/z) − θχ − 𝔥⁰(−1/z))`. -/
theorem retained_at_stop {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h'' : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord}
    {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h'' ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) P 𝓕 Wα VL VR B ζα h'')
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.fn c.jumps u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {h' : Ω → DistOn upperHalfPlaneOpens} {u₀' : ℂ → ℝ}
    (hcen : ∀ ω, WholeField.centredField h' u₀' ω = WangWu.reflectField (WholeField.centredField h u₀ ω))
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => VL i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - Wα ((τ ω).untopD 0) ω)) (u ω)) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WangWu.negInv '' fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      IsLocalSet A (WholeField.centredField h' u₀') P ∧
      ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (WholeField.centredField h' u₀') P g₁ →
        ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
          g₁ ω φ = ∫ z, -(couplingMean κ (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) (-z⁻¹) -
            θ * chiC κ - u₀ (-z⁻¹)) * φ z := by
  classical
  -- the flow's initial extension
  obtain ⟨u₀α, hu₀α⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ)
    (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  have hrel := eqOn_bhe_flow_initial hκ θ hu₀ hu₀α
  -- the flow hull is a local set of the centred original field
  have hloc0 := Sec7.SideHeight.isLocalSet_flowHull hC htr hu₀.1 hu₀α hrel hX hτ hτζ
  simp only [Complex.ofReal_zero, add_zero, image_id'] at hloc0
  obtain ⟨A₀, hA₀m, hA₀e, -⟩ := WholeField.IsLocalSet.exists_measurable_version hloc0 hh0.1
  -- a version that is a relatively closed subset of `ℍ` on every sample
  set G : Set Ω := {ω | A₀ ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) ∧
    IsHPHull (fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} with hGdef
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hA₀e, hτζ, hC.1.2.2.2.2] with ω h1 h2 h3
    exact ⟨h1, Sec5.CrossRestart.isHPHull_fwdHull_rpath h3.2.2.2.1 (Coupling.coe_untopD_lt_zeta h2)⟩
  set N : Set Ω := toMeasurable P Gᶜ with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable P Gᶜ
  have hN0 : P N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 hGae
  have hGN : ∀ ω, ω ∉ N → ω ∈ G := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P Gᶜ hc)
  set Ah : Ω → Set ℂ := fun ω => if ω ∈ N then ∅ else A₀ ω with hAhdef
  have hAhm : Measurable[mΩ, hittingSigma] Ah :=
    Measurable.ite (mβ := hittingSigma) (p := fun ω => ω ∈ N) hNm
      (@measurable_const (Set ℂ) Ω hittingSigma mΩ ∅) hA₀m
  have hAhG : ∀ ω, Ah ω ⊆ H ∧ IsOpen (H \ Ah ω) := fun ω => by
    by_cases hω : ω ∈ N
    · simp only [hAhdef, hω, ↓reduceIte, empty_subset, sdiff_empty, true_and]
      exact QuantumZipper.isOpen_H
    · obtain ⟨e, hK⟩ := hGN ω hω
      simp only [hAhdef, hω, ↓reduceIte, e]
      exact ⟨hK.1, hK.2.2.1⟩
  have hAhe : ∀ᵐ ω ∂P, Ah ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, hGae] with ω h1 h2
    simp only [hAhdef, h1, ↓reduceIte, h2.1]
  have hAhloc : IsLocalSet Ah (WholeField.centredField h u₀) P := Coupling.IsLocalSet.congr_set hloc0 hAhe
  -- the reflected set
  refine ⟨fun ω => WangWu.negInv '' Ah ω, WangWu.measurable_image_negInv.comp hAhm, fun ω => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact WangWu.negInv_mem_H ((hAhG ω).1 hw)
  · rw [WangWu.H_diff_image_negInv]
    exact WangWu.isOpen_image_negInv (hAhG ω).2 sdiff_subset
  · filter_upwards [hAhe] with ω h1
    rw [h1]
  · have h1 := WangWu.IsLocalSet.reflect hAhloc
    have e : (fun ω => WangWu.reflectField (WholeField.centredField h u₀ ω)) = WholeField.centredField h' u₀' :=
      funext fun ω => (hcen ω).symm
    rwa [e] at h1
  · intro g₁ hg₁
    have hAG : ∀ ω, WangWu.negInv '' Ah ω ⊆ H ∧ IsOpen (H \ WangWu.negInv '' Ah ω) := fun ω =>
      ⟨by rintro _ ⟨w, hw, rfl⟩; exact WangWu.negInv_mem_H ((hAhG ω).1 hw),
        by rw [WangWu.H_diff_image_negInv]; exact WangWu.isOpen_image_negInv (hAhG ω).2 sdiff_subset⟩
    have hr := WangWu.IsLocalSetMean.reflect hAG hg₁
    have e1 : (fun ω => WangWu.negInv '' (WangWu.negInv '' Ah ω)) = Ah :=
      funext fun ω => WangWu.image_negInv_image_negInv' _
    have e2 : (fun ω => WangWu.reflectField (WholeField.centredField h' u₀' ω)) = WholeField.centredField h u₀ :=
      funext fun ω => by rw [hcen, WangWu.reflectField_reflectField]
    rw [e1, e2] at hr
    have hAK : ∀ᵐ ω ∂P, Ah ω =
        (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (fun s : ℝ => Wα s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
      filter_upwards [hAhe] with ω h1
      simp only [h1, Complex.ofReal_zero, add_zero, image_id']
    have hmean := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull hC hκ htr hh0 hu₀.1 hu₀α hrel hX hτ hτζ
      hAhm hAK hr hu
    filter_upwards [hmean] with ω hω φ hφ
    rw [← WangWu.reflectField_reflectField (g₁ ω), WangWu.reflectField_apply]
    have hψ : tsupport (Chart.pushTest isConformal_infinityReturnChart φ) ⊆ H \ Ah ω := by
      refine Restart.MarkovChart.tsupport_pushTest_subset_of_chartPre isConformal_infinityReturnChart
        fun w hw => ⟨(hφ hw).1, WangWu.negInv_mem_H (hφ hw).1, fun hwA => (hφ hw).2 ⟨_, hwA, ?_⟩⟩
      change -(-w⁻¹)⁻¹ = w
      rw [inv_neg, inv_inv, neg_neg]
    rw [hω _ hψ, Chart.integral_mul_pushTest isConformal_infinityReturnChart φ, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [Complex.ofReal_zero, sub_zero]
    change -((couplingMean κ (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) (-w⁻¹) - θ * chiC κ -
      u₀ (-w⁻¹)) * φ w) = _
    ring


/-! ### The retained sets along the announcing stops -/

open Exist.Staged Exist.StagedLaw in
/-- **GB6's retained set, its locality and its mean (`hlA`, `hind₁`), along stops announcing the flow's lifetime.**
GB6's frames: `h` a GFF with the data of the word `c`, `h'` the counterflow-frame field (`h` read through `R`,
a GFF with data `(b', J')`), the flow an `IsFlowLineDriver` of `(c, θ)` at `κ`, `𝔥⁰′` the counterflow's initial
extension. There are hitting-measurable random sets `A n` and events `E n` covering `{s < ζα}` almost surely such that:
`A n` is almost surely the inversion of a compact `ℍ`-hull, `A n = invHull Uω s` on `E n ∩ {s < ζα}`, `A n` is a local
set of the centred `h'`, and every local-set mean of `A n` has, on `E n ∩ {s < ζα}`, the harmonic representative
`G₀ ∘ Ψ − χ(16/κ) Im relLog − 𝔥⁰′` for every bounded harmonic extension `G₀` of the chart field's word. -/
theorem exists_retained_package_of_coupling {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {b' : ℝ → ℝ}
    {J' : Finset ℝ} (hG : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {Bα : ℝ≥0 → Ω → ℝ} (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h'' ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) P 𝓕 Wα VL VR Bα ζα h'')
    {u₀' : ℂ → ℝ} (hu₀' : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    (hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀') P) (s : ℝ≥0) :
    ∃ (A : ℕ → Ω → Set ℂ) (E : ℕ → Set Ω), (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∃ K : Set ℂ, IsHPHull K ∧ A n ω = WangWu.negInv '' K) ∧
      (∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (s : ℝ≥0∞) < ζα ω →
        A n ω = Q3Rel.invHull (fun r : ℝ => Wα r.toNNReal ω) s) ∧
      (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → ∃ n, ω ∈ E n) ∧
      (∀ n, IsLocalSet (A n) (WholeField.centredField h' u₀') P) ∧
      (∀ n (g₁ : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (A n) (WholeField.centredField h' u₀') P g₁ →
        ∀ᵐ ω ∂P, ω ∈ E n → (s : ℝ≥0∞) < ζα ω →
          ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
              (cfData (16 / κ) (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).fn
                (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).jumps)
              (cfJumps (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).fn
                (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).jumps) G₀ →
            ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A n ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A n ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
              EqOn (fun z => w₁ z + u₀' z)
                (fun z => G₀ (GB6.relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
                  chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
                (H \ A n ω)) ∧
      (LP.IsFieldDeterminedHistory P h Wα VL VR ζα → ∀ n,
        LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (A n) hittingSigma)
          (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P) := by
  classical
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData c
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu₀
  have hcen := centredField_eq_reflect hκ hb hG hb' hG' hT hu₀ hu₀'
  obtain ⟨hX, -⟩ := hC.2.2.2
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    refine ⟨fun _ _ => ∅, fun _ => ∅, fun _ => measurable_const,
      fun _ => Eventually.of_forall fun _ => ⟨∅, isHPHull_empty, (image_empty _).symm⟩,
      fun _ => Eventually.of_forall fun _ h => h.elim, ?_, fun _ => WangWu.isLocalSet_empty hh0',
      fun _ _ _ => Eventually.of_forall fun _ h => h.elim, fun _ _ S hS => ?_⟩
    · filter_upwards [h0] with ω hω hs
      rw [hω] at hs
      exact absurd hs ENNReal.not_lt_zero
    · obtain ⟨T, -, hST⟩ := hS
      by_cases hT0 : (∅ : Set ℂ) ∈ T
      · refine ⟨univ, @MeasurableSet.univ Ω (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance),
          ?_⟩
        rw [← hST]
        simp [hT0]
      · refine ⟨∅, @MeasurableSet.empty Ω (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance),
          ?_⟩
        rw [← hST]
        simp [hT0]
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
  have hpack := fun n => retained_at_stop hκ htr hC hX (hτ n) (hτζ n) hu₀ hh0 hcen (hu n)
  choose A hAm hAG hAe hAloc hAmean using hpack
  have hτs : ∀ n ω, s ≤ σ n ω → ((τ n ω).untopD 0 : ℝ≥0) = s := fun n ω h => by
    simp only [hτdef, WithTop.untopD_coe, min_eq_left h]
  refine ⟨A, fun n => {ω | s ≤ σ n ω}, hAm, fun n => ?_, fun n => ?_, ?_, hAloc, ?_, ?_⟩
  · filter_upwards [hAe n, hτζ n, hC.1.2.2.2.2] with ω he hlt hp
    exact ⟨_, Sec5.CrossRestart.isHPHull_fwdHull_rpath hp.2.2.2.1 (Coupling.coe_untopD_lt_zeta hlt), he⟩
  · filter_upwards [hAe n] with ω he hωE _
    rw [he, hτs n ω hωE]
    rfl
  · filter_upwards [hσ.2.2.2] with ω hω hs
    obtain ⟨n, hn⟩ := hω s hs
    exact ⟨n, hn⟩
  · intro n g₁ hg₁
    filter_upwards [hAmean n g₁ hg₁, hAe n, hC.1.2.2.2.2, ae_gap_eq_markPos hC] with ω hmω hAω hp hgap hωE hs
      G₀ hG₀ w₁ hw₁ hr₁
    have hωE' : s ≤ σ n ω := hωE
    have hτω := hτs n ω hωE'
    rw [hτω] at hmω hAω
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
        rw [← hr₁ φ hφ, hmω φ hφ]
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
  · intro hdet n
    have hc : ∀ ω, h ω = WangWu.reflectField (WholeField.centredField h' u₀' ω) +
        SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ := fun ω => by
      rw [hcen ω, WangWu.reflectField_reflectField]
      simp only [WholeField.centredField, sub_add_cancel]
    have hΦ : Measurable fun d : DistOn upperHalfPlaneOpens =>
        WangWu.reflectField d + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ :=
      (WholeField.measurable_add_dist _).comp WangWu.measurable_reflectField
    have hcomap : MeasurableSpace.comap h inferInstance ≤
        MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance := by
      have e : h = (fun d : DistOn upperHalfPlaneOpens => WangWu.reflectField d +
          SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ∘
          WholeField.centredField h' u₀' := funext hc
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hΦ.comap_le
    have hGd : ∀ t, drivingFiltration P hX t ≤
        aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P := fun t =>
      (drivingFiltration_le_aeSigma hdet hX t).trans (aeSigma_le_of_le (hcomap.trans (le_aeSigma _ _)))
    have h1 := hitting_reflect_hull_le_aeSigma hC.1 hX hσ (hτ n) (hτζ n) (fun _ => WithTop.coe_ne_top) hGd
      (hAe n)
    intro S hS
    obtain ⟨T, hT, he⟩ := h1 S hS
    exact ⟨T, hT, he⟩


open Exist.Staged Exist.StagedLaw in
/-- **GB6's retained set, its locality and its mean, for the flow-line driver** (`exists_retained_package_of_coupling`
without the determination clause). Along stops announcing the flow's lifetime.
GB6's frames: `h` a GFF with the data of the word `c`, `h'` the counterflow-frame field (`h` read through `R`,
a GFF with data `(b', J')`), the flow an `IsFlowLineDriver` of `(c, θ)` at `κ`, `𝔥⁰′` the counterflow's initial
extension. There are hitting-measurable random sets `A n` and events `E n` covering `{s < ζα}` almost surely such that:
`A n` is almost surely the inversion of a compact `ℍ`-hull, `A n = invHull Uω s` on `E n ∩ {s < ζα}`, `A n` is a local
set of the centred `h'`, and every local-set mean of `A n` has, on `E n ∩ {s < ζα}`, the harmonic representative
`G₀ ∘ Ψ − χ(16/κ) Im relLog − 𝔥⁰′` for every bounded harmonic extension `G₀` of the chart field's word. -/
theorem exists_retained_package {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {b' : ℝ → ℝ}
    {J' : Finset ℝ} (hG : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hF : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    {u₀' : ℂ → ℝ} (hu₀' : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    (hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀') P) (s : ℝ≥0) :
    ∃ (A : ℕ → Ω → Set ℂ) (E : ℕ → Set Ω), (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∃ K : Set ℂ, IsHPHull K ∧ A n ω = WangWu.negInv '' K) ∧
      (∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (s : ℝ≥0∞) < ζα ω →
        A n ω = Q3Rel.invHull (fun r : ℝ => Wα r.toNNReal ω) s) ∧
      (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → ∃ n, ω ∈ E n) ∧
      (∀ n, IsLocalSet (A n) (WholeField.centredField h' u₀') P) ∧
      (∀ n (g₁ : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (A n) (WholeField.centredField h' u₀') P g₁ →
        ∀ᵐ ω ∂P, ω ∈ E n → (s : ℝ≥0∞) < ζα ω →
          ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
              (cfData (16 / κ) (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).fn
                (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).jumps)
              (cfJumps (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).fn
                (GB6.gb6WordOfRec κ θ c (GB6.gb6Rec s Wα ζα ω)).jumps) G₀ →
            ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A n ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A n ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
              EqOn (fun z => w₁ z + u₀' z)
                (fun z => G₀ (GB6.relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
                  chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
                (H \ A n ω)) := by
  obtain ⟨h'', 𝓕, VL, VR, Bα, htr, hC⟩ := hF
  obtain ⟨A, E, h1, h2, h3, h4, h5, h6, -⟩ :=
    exists_retained_package_of_coupling hκ hG hb' hG' hT htr hC hu₀' hh0' s
  exact ⟨A, E, h1, h2, h3, h4, h5, h6⟩

end InteractingSLE.Supp8.Q3Chain
