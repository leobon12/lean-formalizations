/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocChart
import InteractingSLE.Spec.Supplement.GW4SafeRNextWord
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# GW4: the union kernel read in the inverted component chart

Packet PROVE-GW4-CLOC, step 3 (deterministic in the measure). Let `Q` be a probability measure (in the application,
the regular conditional law given the walks) under which the field `h` has the Gaussian kernel of a mean `M` harmonic
off a random relatively closed set `B`, given marks `𝓜` recording `B` and `M`. Read `h` in a component chart `c` of an
open component `C` (`IsComponentChart`), and then in the inverting chart (`GW4Rel.invField`), and centre it by a
deterministic harmonic function `u`. Then the complement `chartSet c B` of the double chart pre-image of `ℍ ∖ B` is a
history-marked local set of the centred field for the marks `𝓜` (`isHistoryAvoidanceLocal_chartSet`). The only
geometric premise is that `(ℍ ∖ B) ∖ C` is open (the frontier of `C` in `ℍ` lies in `B`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField Restart.MarkovChart

/-! ### The chart set -/

section ChartSet

/-- The set read in the inverted component chart: the complement of the double chart pre-image of `ℍ ∖ B`. -/
def chartSet (c : Chart) (B : Set ℂ) : Set ℂ :=
  H \ chartPre infinitySourceChart (chartPre c (H \ B))

theorem chartSet_subset_H (c : Chart) (B : Set ℂ) : chartSet c B ⊆ H := sdiff_subset

theorem H_diff_chartSet (c : Chart) (B : Set ℂ) :
    H \ chartSet c B = chartPre infinitySourceChart (chartPre c (H \ B)) := by
  rw [chartSet, Set.sdiff_sdiff_right_self, inter_eq_right.2 (chartPre_subset_H _ _)]

theorem negInv_mem_H {v : ℂ} (hv : v ∈ H) : -v⁻¹ ∈ H := by
  have : (-v⁻¹).im = v.im / Complex.normSq v := by
    simp [Complex.inv_im, neg_div]
  show 0 < (-v⁻¹).im
  rw [this]
  exact div_pos hv (Complex.normSq_pos.2 fun h0 => by
    have : v.im = 0 := by rw [h0]; rfl
    exact absurd hv (by show ¬ (0 < v.im); rw [this]; exact lt_irrefl 0))

theorem mem_chartSet_iff {c : Chart} (hc : c.IsConformal) {B : Set ℂ} {v : ℂ} (hv : v ∈ H) :
    v ∈ chartSet c B ↔ c.2.1 (-v⁻¹) ∈ B := by
  have h1 : -v⁻¹ ∈ H := negInv_mem_H hv
  have h2 : c.2.1 (-v⁻¹) ∈ H := hc.2.1 h1
  simp only [chartSet, chartPre, Set.mem_sdiff, mem_ofPred_eq, infinitySourceChart]
  tauto

theorem disjoint_chartSet_iff {c : Chart} (hc : c.IsConformal) {B U : Set ℂ} (hUH : U ⊆ H) :
    Disjoint (chartSet c B) U ↔ Disjoint B (c.2.1 '' (infinitySourceChart.2.1 '' U)) := by
  constructor
  · intro hd
    refine Set.disjoint_left.2 fun z hzB ⟨w, ⟨v, hvU, hvw⟩, hwz⟩ => ?_
    have hv : v ∈ chartSet c B := by
      rw [mem_chartSet_iff hc (hUH hvU)]
      have : infinitySourceChart.2.1 v = -v⁻¹ := rfl
      rw [← this, hvw, hwz]
      exact hzB
    exact Set.disjoint_left.1 hd hv hvU
  · intro hd
    refine Set.disjoint_left.2 fun v hvA hvU => ?_
    rw [mem_chartSet_iff hc (hUH hvU)] at hvA
    exact Set.disjoint_left.1 hd hvA ⟨-v⁻¹, ⟨v, hvU, rfl⟩, rfl⟩

theorem isOpen_image_image_infinitySourceChart {c : Chart} (hc : c.IsConformal) {U : Set ℂ} (hU : IsOpen U)
    (hUH : U ⊆ H) :
    IsOpen (c.2.1 '' (infinitySourceChart.2.1 '' U)) ∧ c.2.1 '' (infinitySourceChart.2.1 '' U) ⊆ H := by
  have hinf := Chart.isConformal_infinitySourceChart
  have h1 : infinitySourceChart.2.1 '' U ⊆ H := hinf.2.1.image_subset.trans' (image_mono hUH)
  exact ⟨hc.isOpen_image_of_subset (hinf.isOpen_image_of_subset hU hUH) h1,
    (image_mono h1).trans hc.2.1.image_subset⟩

theorem measurable_chartSet {Ω : Type*} {𝓜 : MeasurableSpace Ω} {c : Chart} (hc : c.IsConformal)
    {B : Ω → Set ℂ} (hBm : Measurable[𝓜, hittingSigma] B) :
    Measurable[𝓜, hittingSigma] fun ω => chartSet c (B ω) := by
  refine Sec5.Aux61ULoc.measurable_hitting_of_avoid fun U hU hUH => ?_
  obtain ⟨ho, hsub⟩ := isOpen_image_image_infinitySourceChart hc hU hUH
  have he : {ω | Disjoint (chartSet c (B ω)) U} =
      B ⁻¹' {S | Disjoint S (c.2.1 '' (infinitySourceChart.2.1 '' U))} := by
    ext ω
    exact disjoint_chartSet_iff hc hUH
  rw [he]
  exact hBm (measurableSet_avoid ho hsub)

end ChartSet

/-! ### Marked locality of the chart set -/

section Local

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

theorem continuousOn_of_harmonicOnNhd {f : ℂ → ℝ} {D : Set ℂ} (hf : InnerProductSpace.HarmonicOnNhd f D) :
    ContinuousOn f D := fun z hz => (hf z hz).1.continuousAt.continuousWithinAt

theorem continuousOn_lift_inv_infinitySourceChart :
    ContinuousOn (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w)) H := by
  refine (continuousOn_of_harmonicOnNhd Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift).comp
    Chart.isConformal_infinitySourceChart.1.continuousOn ?_
  exact Chart.isConformal_infinitySourceChart.2.1

/-- **The chart set is history-marked local.** Under `Q`, let `h` have the Gaussian kernel of a mean `M` harmonic
off the relatively closed set `B`, given marks `𝓜` recording `B` and `M`. Then for a component chart `c` of an open
component `C ⊆ ℍ` with `(ℍ ∖ B) ∖ C` open, the set `chartSet c B` is a history-marked local set, for the marks `𝓜`,
of the inverted component field `invField κ (hC ω)` centred by any harmonic `u`. -/
theorem isHistoryAvoidanceLocal_chartSet (h𝓜 : 𝓜 ≤ mΩ) {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) {κ : ℝ} (hκ : 0 < κ)
    {h hC : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (htr : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hC ω))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    {B : Ω → Set ℂ} {M : Ω → DistOn upperHalfPlaneOpens}
    (hBm : Measurable[𝓜, hittingSigma] B) (hMm : Measurable[𝓜] M)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hMh : ∀ᵐ ω ∂Q, IsHarmonicDistOn (M ω) (H \ B ω))
    (hBC : ∀ᵐ ω ∂Q, IsOpen ((H \ B ω) \ C))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜] =ᵐ[Q] fun ω => rangeKerCF (M ω) (H \ B ω) φ) :
    IsHistoryAvoidanceLocal 𝓜 (fun ω => chartSet c (B ω))
      (centredField (fun ω => GW4Rel.invField κ (hC ω)) u) Q := by
  have hconf : c.IsConformal := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  have hinf := Chart.isConformal_infinitySourceChart
  have hdomC : (c.dom : Set ℂ) = C := coe_dom_of_isComponentChart hch hCo hCH
  have hdomI : (infinitySourceChart.dom : Set ℂ) = H := Sec7.StripSysField.coe_dom_infinitySourceChart
  have hliftc : ContinuousOn c.2.2 c.dom := by rw [hdomC]; exact hch.2.2.2.2.2.1
  have hlift : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom := by
    rw [hdomC]; exact harmonicOnNhd_lift_of_isComponentChart hch hCo hCH
  have hliftcI : ContinuousOn infinitySourceChart.2.2 infinitySourceChart.dom := by
    rw [hdomI]
    exact continuousOn_of_harmonicOnNhd Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift
  have hliftI : InnerProductSpace.HarmonicOnNhd infinitySourceChart.2.2 infinitySourceChart.dom := by
    rw [hdomI]; exact Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift
  have hℓc : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H :=
    Chart.locallyIntegrableOn_of_continuousOn (hch.2.2.2.2.2.1.comp hconf.1.continuousOn hch.2.2.1)
  have hℓI : LocallyIntegrableOn (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w)) H :=
    Chart.locallyIntegrableOn_of_continuousOn continuousOn_lift_inv_infinitySourceChart
  -- the two chart transports
  have hhC : hC = fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) :=
    funext fun ω => (htr ω).eq_chartTransport hconf hℓc
  have hX : (fun ω => GW4Rel.invField κ (hC ω)) = fun ω =>
      Chart.chartTransport hinf (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (hC ω) :=
    funext fun ω => (isChartTransport_invField hκ (hC ω)).eq_chartTransport hinf hℓI
  set M₁ : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (M ω)
    with hM₁
  set M₂ : Ω → DistOn upperHalfPlaneOpens := fun ω =>
    Chart.chartTransport hinf (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (M₁ ω) with hM₂
  set V₁ : Ω → Set ℂ := fun ω => chartPre c (H \ B ω) with hV₁
  set V₂ : Ω → Set ℂ := fun ω => chartPre infinitySourceChart (V₁ ω) with hV₂
  have hV₁o : ∀ ω, IsOpen (V₁ ω) := fun ω => isOpen_chartPre hconf (hBc ω).2
  have hV₂o : ∀ ω, IsOpen (V₂ ω) := fun ω => isOpen_chartPre hinf (hV₁o ω)
  -- kernel in the component chart
  have hk₁ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (hC ω ψ : ℂ)) | 𝓜] =ᵐ[Q] fun ω => rangeKerCF (M₁ ω) (V₁ ω) ψ := by
    intro ψ
    rw [hhC]
    refine ae_condExp_cexp_chartTransport hconf (Or.inl rfl) 0 (chiC κ) ?_ hker ψ
    filter_upwards [hBC] with ω hω
    exact ⟨(hBc ω).2, by rw [hdomC]; exact hω⟩
  -- kernel in the inverted chart
  have hk₂ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (GW4Rel.invField κ (hC ω) ψ : ℂ)) | 𝓜] =ᵐ[Q]
        fun ω => rangeKerCF (M₂ ω) (V₂ ω) ψ := by
    intro ψ
    have h1 := ae_condExp_cexp_chartTransport (𝓜 := 𝓜) (Q := Q) hinf (Or.inr rfl) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h := hC) (M := M₁) (V := V₁)
      (Eventually.of_forall fun ω => ⟨hV₁o ω, by
        rw [hdomI, Set.sdiff_eq_empty.2 (chartPre_subset_H _ _)]; exact isOpen_empty⟩) hk₁ ψ
    have he : ∀ ω, GW4Rel.invField κ (hC ω) =
        Chart.chartTransport hinf (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (hC ω) := fun ω => congrFun hX ω
    simp_rw [he]
    exact h1
  -- centring
  set S : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u with hS
  have hk₃ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Q[fun ω => Complex.exp (Complex.I * (centredField (fun ω => GW4Rel.invField κ (hC ω)) u ω ψ : ℂ)) | 𝓜]
        =ᵐ[Q] fun ω => rangeKerCF (M₂ ω - S) (H \ chartSet c (B ω)) ψ := by
    intro ψ
    have hsplit : (fun ω => Complex.exp (Complex.I *
        (centredField (fun ω => GW4Rel.invField κ (hC ω)) u ω ψ : ℂ))) =
        Complex.exp (-(Complex.I * (S ψ : ℂ))) •
          fun ω => Complex.exp (Complex.I * (GW4Rel.invField κ (hC ω) ψ : ℂ)) := by
      funext ω
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
      simp only [centredField, sub_apply, hS]
      push_cast
      ring_nf
    rw [hsplit]
    filter_upwards [condExp_smul (Complex.exp (-(Complex.I * (S ψ : ℂ))))
      (fun ω => Complex.exp (Complex.I * (GW4Rel.invField κ (hC ω) ψ : ℂ))) 𝓜 (μ := Q), hk₂ ψ] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, H_diff_chartSet, rangeKerCF, rangeKerCF, ← Complex.exp_add,
      sub_apply]
    congr 1
    push_cast
    ring
  -- measurability and harmonicity of the mean
  have hM₂m : Measurable[𝓜] fun ω => M₂ ω - S :=
    (measurable_sub_dist S).comp ((Chart.measurable_chartTransport hinf _ _ _).comp
      ((Chart.measurable_chartTransport hconf _ _ _).comp hMm))
  have hM₂h : ∀ᵐ ω ∂Q, IsHarmonicDistOn (M₂ ω - S) (H \ chartSet c (B ω)) := by
    filter_upwards [hMh] with ω hω
    rw [H_diff_chartSet]
    have hM1 : IsHarmonicDistOn (M₁ ω) (V₁ ω) := by
      refine isHarmonicDistOn_chartTransport_pm hconf hliftc hlift (hV₁o ω) (chartPre_subset_H _ _) ?_
        (Or.inl rfl) 0 (chiC κ)
      rw [image_chartPre hconf]
      exact IsHarmonicDistOn.mono hω inter_subset_left
    have hM2 : IsHarmonicDistOn (M₂ ω) (V₂ ω) := by
      refine isHarmonicDistOn_chartTransport_pm hinf hliftcI hliftI (hV₂o ω) (chartPre_subset_H _ _) ?_
        (Or.inr rfl) _ _
      rw [image_chartPre hinf]
      exact IsHarmonicDistOn.mono hM1 inter_subset_left
    exact LocalSets.IsHarmonicDistOn.sub' (hV₂o ω) hM2
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu) (chartPre_subset_H _ _))
  have hhCm : Measurable hC := by
    rw [hhC]; exact (Chart.measurable_chartTransport hconf _ _ _).comp hhm
  exact WFS.isHistoryAvoidanceLocal_of_retainedKernel h𝓜
    (measurable_centredField ((GW4Rel.measurable_invField κ).comp hhCm) u)
    (measurable_chartSet hconf hBm)
    (Eventually.of_forall fun ω => ⟨chartSet_subset_H _ _, by rw [H_diff_chartSet]; exact hV₂o ω⟩)
    hM₂h hk₃

end Local

end InteractingSLE.Theorem14.GW4Fix.CLoc
