/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlLaw
import InteractingSLE.Spec.Coupling.WFSLeafFreezeLocal

/-!
# The increment law without the germ-record input `hGerm`

Packet PROVE-R5-ENLARGED (continued). PROVE-POCKET-SIDEIN's `hasOldChartIncrementLaw_of_retained_kernels` (and hence
`hasOldChartIncrementLawOn_of_retained_kernels`, `…_of_enlarged_kernels`, `…_of_enlarged_marked`) asks that the record
`ℋ₁` contain the germ σ-algebra of the pulled increment for the pulled residual (`hGerm`, "the individual germ at `B`
must remain part of `𝒥`", Aux. 35 p. 193). That input is not needed: the retained kernel of the residual given `ℋ₁`
already makes the increment **history-marked local with all of `ℋ₁` as marks**
(`WFS.isHistoryAvoidanceLocal_of_retainedKernel`,
Aux. 18's criterion), the marked germ law then gives a germ-measurable mean retained by `germSigma ⊔ ℋ₁ ≥ ℋ₁`
(`Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal`), and the two nested kernels have the same mean. Only the
hitting measurability of the increment for `ℋ₁` (`hAdded`) remains.

* **`exists_localSetMean_eq_of_retained_kernel_noGerm`** — `exists_localSetMean_eq_of_retained_kernel` without `hGerm`;
* `hasOldChartIncrementLaw_of_retained_kernels_noGerm` (the landed reduction without `hGerm`);
* `hasOldChartIncrementLawOn_of_retained_kernels_noGerm` (the reference chart on an event);
* **`hasOldChartIncrementLawOn_of_enlarged_kernels_noGerm`**, **`hasOldChartIncrementLawOn_of_enlarged_marked_noGerm`**.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets PocketStopSide WholeField

section Local

variable {Ω : Type*} {ℋ ℋ₀ ℋ₁ ℋK ℋ' ℋc : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The conditional characteristic function of a retained kernel in the `rangeKerCF` form. -/
theorem condExp_exp_eq_rangeKerCF [IsFiniteMeasure P] (hℋ : ℋ ≤ mΩ) {X g : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hg : Measurable[ℋ] g) {U : Ω → Set ℂ}
    (hK : IsCondZeroBoundaryGFF P ℋ U fun ω => X ω - g ω) (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | ℋ] =ᵐ[P] fun ω => rangeKerCF (g ω) (U ω) φ := by
  filter_upwards [condExp_exp_eq_of_isCondZeroBoundaryGFF hℋ hX hg hK φ] with ω hω
  rw [hω, rangeKerCF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The mean of a retained kernel is a local-set mean** (as a whole distribution, almost surely), with no
germ-record hypothesis: the kernel makes the set history-local for the record, the marked germ law gives a
germ-measurable mean retained by the larger record `germSigma A X ⊔ ℋ`, and nested kernels share their mean. -/
theorem exists_localSetMean_eq_of_retained_kernel_noGerm [IsProbabilityMeasure P] (hℋ : ℋ ≤ mΩ)
    {A : Ω → Set ℂ} {X g : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA : Measurable[ℋ, hittingSigma] A) (hg : Measurable[ℋ] g)
    (hRegular : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hHarmonic : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω))
    (hKernel : IsCondZeroBoundaryGFF P ℋ (fun ω => H \ A ω) (fun ω => X ω - g ω)) :
    ∃ g₀ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A X P g₀ ∧ g₀ =ᵐ[P] g := by
  have hXm := hX.measurable
  have hAm : Measurable[mΩ, hittingSigma] A := hA.mono hℋ le_rfl
  have hloc : IsHistoryAvoidanceLocal ℋ A X P :=
    WFS.isHistoryAvoidanceLocal_of_retainedKernel hℋ hXm hA hRegular hHarmonic
      (condExp_exp_eq_rangeKerCF hℋ hXm hg hKernel)
  obtain ⟨g', hg'm, -, hg'k⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hX hAm hℋ hloc hRegular
  have hle : germSigma A X ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hAm hXm) hℋ
  have e1 : g =ᵐ[P] g' :=
    ae_eq_of_isCondZeroBoundaryGFF_of_le le_sup_right hle hXm hg (hg'm.mono le_sup_left le_rfl) hKernel hg'k
  obtain ⟨g₀, hg₀⟩ := (isGermConditionalLaw_iff (A := A) (h := X) (P := P)).1
    (hloc.isAvoidanceLocal.isGermConditionalLaw hX hAm hRegular)
  have e2 : g₀ =ᵐ[P] g' :=
    ae_eq_of_isCondZeroBoundaryGFF_of_le le_sup_left hle hXm hg₀.1 (hg'm.mono le_sup_left le_rfl) hg₀.2.2 hg'k
  exact ⟨g₀, hg₀, e2.trans e1.symm⟩

/-- **PROVE-POCKET-SIDEIN's increment law from retained kernels, without `hGerm`.** -/
theorem hasOldChartIncrementLaw_of_retained_kernels_noGerm
    {Ω : Type*} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ)
    {old current : Ω → Chart} (hOld : ∀ ω, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] {ω | z ∈ (old ω).dom})
    (hfwd : ∀ z, Measurable[ℋ₀]
      ({ω | z ∈ (old ω).dom}.indicator fun ω => (old ω).1 z))
    (hNested : ∀ ω, ((current ω).dom : Set ℂ) ⊆ (old ω).dom)
    {h gOld gNow : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hMeanOld : Measurable[ℋ₁] gOld) (hMeanNow : Measurable[ℋ₁] gNow)
    (hHarmOld : ∀ᵐ ω ∂P, IsHarmonicDistOn (gOld ω) (old ω).dom)
    (hHarmNow : ∀ᵐ ω ∂P, IsHarmonicDistOn (gNow ω) (current ω).dom)
    (hOldKernel : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => ((old ω).dom : Set ℂ))
      (fun ω => h ω - gOld ω))
    (hCurrentKernel : IsCondZeroBoundaryGFF P ℋ₁ (fun ω => ((current ω).dom : Set ℂ))
      (fun ω => h ω - gNow ω))
    (hAdded : Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet old current)) (M : Set Ω) :
    HasOldChartIncrementLaw P M old current gOld gNow := by
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  have hdom₁ : ∀ z, MeasurableSet[ℋ₁] {ω | z ∈ (old ω).dom} :=
    fun z => hInfo _ (hdom z)
  have hfwd₁ : ∀ z, Measurable[ℋ₁]
      ({ω | z ∈ (old ω).dom}.indicator fun ω => (old ω).1 z) :=
    fun z => (hfwd z).mono hInfo le_rfl
  have hSubOld : Measurable fun ω => h ω - gOld ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hh).sub
        ((LQGMetric.measurable_distOn_apply φ).comp (hMeanOld.mono hℋ₁ le_rfl))
  have hSubNow : Measurable fun ω => h ω - gNow ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hh).sub
        ((LQGMetric.measurable_distOn_apply φ).comp (hMeanNow.mono hℋ₁ le_rfl))
  let residual := fun ω => Chart.pullField (hOld ω) (h ω - gOld ω)
  let increment := fun ω => Chart.pullField (hOld ω) (gNow ω - gOld ω)
  have hResidual : Measurable residual := measurable_pullField_of_retained_chart hOld
    (fun z => hℋ₀ _ (hdom z)) (fun z => (hfwd z).mono hℋ₀ le_rfl) hSubOld
  have hResidualLaw := Chart.isCondZeroBoundaryGFF_pullField_random
    hℋ₀ hOld hdom hfwd hSubOld hOldKernel
  have hZero : IsZeroBoundaryGFF upperHalfPlaneOpens residual P :=
    isZeroBoundaryGFF_of_conditional_halfPlane hℋ₀ hResidual hResidualLaw
  have hDiff : Measurable[ℋ₁] fun ω => gNow ω - gOld ω := by
    let : MeasurableSpace Ω := ℋ₁
    exact LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hMeanNow).sub
        ((LQGMetric.measurable_distOn_apply φ).comp hMeanOld)
  have hIncrement : Measurable[ℋ₁] increment :=
    @measurable_pullField_of_retained_chart Ω ℋ₁ old hOld hdom₁ hfwd₁ _ hDiff
  have hRegular : ∀ᵐ ω ∂P, globalOldChartAddedSet old current ω ⊆ H ∧
      IsOpen (H \ globalOldChartAddedSet old current ω) :=
    Eventually.of_forall (globalOldChartAddedSet_regular hOld)
  have hHarmonic : ∀ᵐ ω ∂P, IsHarmonicDistOn (increment ω)
      (H \ globalOldChartAddedSet old current ω) := by
    filter_upwards [hHarmOld, hHarmNow] with ω hO hN
    rw [compl_globalOldChartAddedSet]
    exact Restart.MarkovChart.isHarmonicDistOn_pullField (hOld ω)
      (IsHarmonicDistOn.sub' (current ω).dom.isOpen hN
        (IsHarmonicDistOn.mono hO (hNested ω)))
  have hDifference (ω : Ω) : residual ω - increment ω =
      Chart.pullField (hOld ω) (h ω - gNow ω) := by
    ext φ
    simp only [residual, increment, sub_apply, Chart.pullField_apply]
    ring
  have hCurrentLaw := isCondZeroBoundaryGFF_pullField_subdomain hℋ₁ hOld hdom₁ hfwd₁
    (fun ω => (current ω).dom.isOpen) (fun ω => (hNested ω).trans (hOld ω).dom_subset)
    (fun ω => by rw [sdiff_eq_empty.2 (hNested ω)]; exact isOpen_empty)
    hSubNow hCurrentKernel
  have hKernel : IsCondZeroBoundaryGFF P ℋ₁
      (fun ω => H \ globalOldChartAddedSet old current ω)
      (fun ω => residual ω - increment ω) := by
    simpa only [hDifference, compl_globalOldChartAddedSet] using hCurrentLaw
  obtain ⟨g, hg, hEq⟩ := exists_localSetMean_eq_of_retained_kernel_noGerm hℋ₁ hZero hAdded
    hIncrement hRegular hHarmonic hKernel
  refine ⟨globalOldChartAddedSet old current, residual, g, hZero,
    hAdded.mono hℋ₁ le_rfl, hRegular, hg, ?_⟩
  filter_upwards [hEq] with ω hEq hω
  refine ⟨?_, fun _ => hEq⟩
  simp only [globalOldChartAddedSet, oldChartAddedSet, ite_eq_left hω]

/-- `hasOldChartIncrementLawOn_of_retained_kernels` without `hGerm`. -/
theorem hasOldChartIncrementLawOn_of_retained_kernels_noGerm [IsProbabilityMeasure P]
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[ℋ₀] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    {U : Ω → Set ℂ} (hUo : ∀ ω ∈ G, IsOpen (U ω)) (hNested : ∀ ω ∈ G, U ω ⊆ (old ω).dom)
    {h gOld gNow : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hMeanOld : Measurable[ℋ₁] gOld) (hMeanNow : Measurable[ℋ₁] gNow)
    (hHarmOld : ∀ᵐ ω ∂P, ω ∈ G → IsHarmonicDistOn (gOld ω) (old ω).dom)
    (hHarmNow : ∀ᵐ ω ∂P, ω ∈ G → IsHarmonicDistOn (gNow ω) (U ω))
    {Uold : Ω → Set ℂ} (hUold : ∀ᵐ ω ∂P, ω ∈ G → Uold ω = (old ω).dom)
    (hOldKernel : IsCondZeroBoundaryGFF P ℋ₀ Uold (fun ω => h ω - gOld ω))
    (hCurrentKernel : IsCondZeroBoundaryGFF P ℋ₁ U (fun ω => h ω - gNow ω))
    (hAdded : Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet (oldOn G old) (curOn G U)))
    {M : Set Ω} (hMG : M ⊆ G) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = U ω) :
    HasOldChartIncrementLawOn P M old current gOld gNow := by
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  have hGm : MeasurableSet G := hℋ₀ _ hG
  have hUH : ∀ ω ∈ G, U ω ⊆ H := fun ω hω => (hNested ω hω).trans (hOld ω hω).dom_subset
  have hcurG : ∀ ω ∈ G, ((curOn G U ω).dom : Set ℂ) = U ω := fun ω hω =>
    dom_curOn_of_mem hω (hUo ω hω) (hUH ω hω)
  refine ⟨G, hGm, hMG, fun hP => ?_⟩
  have hNested' : ∀ ω, ((curOn G U ω).dom : Set ℂ) ⊆ (oldOn G old ω).dom := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [hcurG ω hω, oldOn_of_mem hω]
      exact hNested ω hω
    · rw [dom_curOn_of_notMem hω, oldOn_of_notMem hω, dom_chart_id]
  have hHarmOld' : ∀ᵐ ω ∂P[|G], IsHarmonicDistOn (gOld ω) (oldOn G old ω).dom := by
    refine ae_cond_of_ae hGm ?_
    filter_upwards [hHarmOld] with ω hω hG'
    rw [oldOn_of_mem hG']
    exact hω hG'
  have hHarmNow' : ∀ᵐ ω ∂P[|G], IsHarmonicDistOn (gNow ω) (curOn G U ω).dom := by
    refine ae_cond_of_ae hGm ?_
    filter_upwards [hHarmNow] with ω hω hG'
    rw [hcurG ω hG']
    exact hω hG'
  have hOldKernel' : IsCondZeroBoundaryGFF (P[|G]) ℋ₀ (fun ω => ((oldOn G old ω).dom : Set ℂ))
      (fun ω => h ω - gOld ω) := by
    refine isCondZeroBoundaryGFF_cond hℋ₀ hG (measurable_sub_of_le hℋ₁ hh hMeanOld) hOldKernel ?_
    filter_upwards [hUold] with ω hω hG'
    rw [oldOn_of_mem hG']
    exact hω hG'
  have hCurrentKernel' : IsCondZeroBoundaryGFF (P[|G]) ℋ₁ (fun ω => ((curOn G U ω).dom : Set ℂ))
      (fun ω => h ω - gNow ω) :=
    isCondZeroBoundaryGFF_cond hℋ₁ (hInfo _ hG) (measurable_sub_of_le hℋ₁ hh hMeanNow) hCurrentKernel
      (Eventually.of_forall fun ω hG' => (hcurG ω hG').symm)
  have hlaw := @hasOldChartIncrementLaw_of_retained_kernels_noGerm Ω ℋ₀ ℋ₁ mΩ (P[|G]) hP hInfo hℋ₁
    (oldOn G old) (curOn G U) (isConformal_oldOn hOld)
    (fun z => measurableSet_mem_dom_oldOn hG (hdom z))
    (fun z => measurable_indicator_fwd_oldOn hG (hfwd z)) hNested' h gOld gNow hh hMeanOld hMeanNow
    hHarmOld' hHarmNow' hOldKernel' hCurrentKernel' hAdded M
  refine HasOldChartIncrementLaw.congr_on hlaw (Eventually.of_forall fun ω hM => ?_)
  exact ⟨oldOn_of_mem (hMG hM), by rw [hcurG ω (hMG hM), hcur ω hM], rfl, rfl⟩

/-- **R.5's enlarged-stop increment law from retained kernels, without `hGerm`.** -/
theorem hasOldChartIncrementLawOn_of_enlarged_kernels_noGerm [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {B K K' : Ω → Set ℂ} {g₀ g₁ gK : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ) (hg₁ : Measurable[ℋ₁] g₁)
    (hHarm₁ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₁ ω) (H \ K' ω))
    (hK₁ : IsCondZeroBoundaryGFF P ℋ₁ (fun ω => H \ K' ω) fun ω => h ω - g₁ ω)
    (hKK : germSigma K h ≤ ℋK) (hℋK : ℋK ≤ mΩ) (hgK : Measurable[germSigma K h] gK)
    (hKKer : IsCondZeroBoundaryGFF P ℋK (fun ω => H \ K ω) fun ω => h ω - gK ω)
    {E : Set Ω} (hE : MeasurableSet[ℋK] E)
    (htrace : ∀ t, MeasurableSet[ℋK] (E ∩ t) ↔ MeasurableSet[ℋ₁] (E ∩ t))
    (hKE : ∀ᵐ ω ∂P, ω ∈ E → K ω = K' ω)
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω)
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ H \ B ω)
    (hAdded : Measurable[ℋ₁, hittingSigma]
      (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)))
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  intro gOld hgOld gNow hgNow
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  -- step 1: the two-step construction in the reference chart, conditioned on `G`
  have hL := hasOldChartIncrementLawOn_of_retained_kernels_noGerm (P := P) hInfo hℋ₁ hG hOld hdom hfwd
    (U := fun ω => H \ K' ω) hK'o (fun ω hω => (hNest ω hω).trans (hOldDom ω hω).symm.subset) hh
    ((hg₀.mono hB₀ le_rfl).mono hInfo le_rfl) hg₁
    (by filter_upwards [hHarm₀] with ω hω hG'; rwa [hOldDom ω hG'])
    (hHarm₁.mono fun ω hω _ => hω) (Uold := fun ω => H \ B ω)
    (Eventually.of_forall fun ω hG' => (hOldDom ω hG').symm) hK₀ hK₁ hAdded hMG
    (current := curOn G fun ω => H \ K' ω)
    (fun ω hM => dom_curOn_of_mem (hMG hM) (hK'o ω (hMG hM))
      ((hNest ω (hMG hM)).trans sdiff_subset))
  -- step 3: every version of the means is the retained one, and the enlarged mean is the current one on `E`
  have hOldEq : gOld =ᵐ[P] g₀ := ae_eq_of_isLocalSetMean_of_retained hh hgOld hB₀ hℋ₀ hg₀ hK₀
  have hNowEq : gNow =ᵐ[P] gK := ae_eq_of_isLocalSetMean_of_retained hh hgNow hKK hℋK hgK hKKer
  have hEnl : ∀ᵐ ω ∂P, ω ∈ E → gK ω = g₁ ω :=
    ae_eq_of_isCondZeroBoundaryGFF_of_trace hℋK hℋ₁ hE htrace hh (hgK.mono hKK le_rfl) hg₁ hKKer hK₁
      (by filter_upwards [hKE] with ω hω hωE; rw [hω hωE])
  refine hL.congr_on ?_
  filter_upwards [hOldEq, hNowEq, hEnl, hKE] with ω e0 eN eE eK hM
  refine ⟨rfl, ?_, e0.symm, ?_⟩
  · rw [dom_curOn_of_mem (hMG hM) (hK'o ω (hMG hM)) ((hNest ω (hMG hM)).trans sdiff_subset),
      hcur ω hM, eK (hME hM)]
  · rw [eN, eE (hME hM)]

/-- **R.5's enlarged-stop increment law from the marked laws, without `hGerm`**: the only record-transport input left
is the hitting measurability `hAdded` of the pulled increment for the enlarged record. -/
theorem hasOldChartIncrementLawOn_of_enlarged_marked_noGerm [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {B K K' : Ω → Set ℂ} {g₀ : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hℋ' : ℋ' ≤ mΩ) (hℋc : ℋc ≤ mΩ)
    (hK'm : Measurable[mΩ, hittingSigma] K') (hK'reg : ∀ᵐ ω ∂P, K' ω ⊆ H ∧ IsOpen (H \ K' ω))
    (hK'loc : IsHistoryAvoidanceLocal ℋ' K' h P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKreg : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hKloc : IsHistoryAvoidanceLocal ℋc K h P)
    (hInfo : ℋ₀ ≤ germSigma K' h ⊔ ℋ')
    {E : Set Ω} (hE : MeasurableSet[germSigma K h ⊔ ℋc] E) (hE' : MeasurableSet[germSigma K' h ⊔ ℋ'] E)
    (hKE : ∀ ω ∈ E, K ω = K' ω)
    (hmarks : MeasurableSpace.comap ((↑) : E → Ω) ℋc = MeasurableSpace.comap ((↑) : E → Ω) ℋ')
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω)
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ H \ B ω)
    (hAdded : Measurable[germSigma K' h ⊔ ℋ', hittingSigma]
      (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)))
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  obtain ⟨g₁, hg₁, hHarm₁, hK₁⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hK'm hℋ' hK'loc hK'reg
  obtain ⟨gK, hgK, -, hKKer⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hKm hℋc hKloc hKreg
  exact hasOldChartIncrementLawOn_of_enlarged_kernels_noGerm hh.measurable hB₀ hg₀ hHarm₀ hK₀ hInfo
    (sup_le (germSigma_le hK'm hh.measurable) hℋ') (hg₁.mono le_sup_left le_rfl) hHarm₁ hK₁ le_sup_left
    (sup_le (germSigma_le hKm hh.measurable) hℋc) hgK hKKer hE
    (measurableSet_inter_germSigma_sup_iff hKE hmarks hE hE')
    (Eventually.of_forall hKE) hG hOld hdom hfwd hOldDom hK'o hNest hAdded hMG hME hcur

end Local

end InteractingSLE.Sec7.R5Enl
