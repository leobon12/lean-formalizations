/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextLines

/-!
# GW4: safe law from the conditional component line input

All clock, filtration, force regularity, threshold, integrability, safe-event
measurability, and Gaussian-kernel steps are proved. The named input
`HasComponentLines` contains the conditional marked locality and the actual
finite-word mean identification; these two assertions are not proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Restart.DomainMarkov Restart.DomainMarkov.K2
  Sec7.PocketTraversal Restart.FCDet Supp8.Q3Stop Supp8.GB6.RelDrv Supp8.RelSafe Exist.StagedLaw

/-- A frame-level conditional theorem: the exact component line hypotheses
imply `HasRelSafe`. The field here is the conditional component field. -/
theorem hasRelSafe_of_componentLines {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {k : ℝ} {c₀ : BoundaryWord} {F : Frame}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞} (hF : F.IsOk)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hL : ∀ i : Fin (flowLineNL c₀.fn c₀.jumps 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL k c₀.fn c₀.jumps 0 0 l)
    (hR : ∀ i : Fin (flowLineNR c₀.fn c₀.jumps 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR k c₀.fn c₀.jumps 0 0 l)
    (hline : HasComponentLines k c₀ F ν X Wd GT R V hWm) :
    HasRelSafe k (wordType k c₀) (fun _ => c₀) univ
      (ν.map fun ω => componentPoint X R V ω) := by
  classical
  obtain ⟨u₀, ℋ, B, hu₀, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hmean⟩ := hline
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀
  have hl : ∀ t, IsLocalSet (B t) (centredField X u₀) ν := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2
      (hloc t).isAvoidanceLocal
  choose g hg using fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hl t)
  let M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens :=
    fun t ω => g t ω + smoothDist upperHalfPlaneOpens u₀
  let 𝒢L : ℝ≥0 → MeasurableSpace Ω := fun t => germSigma (B t) (centredField X u₀) ⊔ ℋ t
  have h𝒢L : ∀ t, physFilt Frame.measurable_gw4Rec hWm ν t ≤ 𝒢L t :=
    fun t => (h𝓖ℋ t).trans le_sup_right
  have h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ :=
    fun t => sup_le (germSigma_le (hBm t) hh0.measurable) (hℋ t)
  have hker : ∀ t (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂ν,
      ω ∈ (univ : Set Ω) → lineClock F Wd GT V t ω < V ω →
      tsupport φ ⊆ Chart.id.2.1 '' (H \ fwdHull (fun r : ℝ => R r.toNNReal ω)
        (lineClock F Wd GT V t ω).toNNReal) →
      ν[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) - (((1 / 2 : ℝ) *
          zeroGFFTestCov (Chart.id.2.1 '' (H \ fwdHull (fun r : ℝ => R r.toNNReal ω)
            (lineClock F Wd GT V t ω).toNNReal)) φ φ : ℝ) : ℂ)) := by
    intro t φ
    filter_upwards [ae_condExp_cexp_boundary_marked hu₀.1 hh0 (hBm t) (hBc t) (hℋ t)
      (hloc t) (hg t) φ, hBK t] with ω hk hshape _ hlt _
    rw [hk, hshape hlt]
    simp only [Chart.id, image_id']
    rfl
  have hΦ : Measurable fun ω => componentPoint X R V ω :=
    measurable_const.prodMk (measurable_relVar hX.1 hver.1.1.1 hver.1.1.2.2.2.1)
  have hWd : (fun t ω => canonDrv t (componentPoint X R V ω)) = R := by
    funext t ω
    exact relDrv_relVar (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω) t
  have hreg : ∀ᵐ ω ∂ν, ω ∈ (univ : Set Ω) →
      Aux79.IsForceReg R (componentVL k c₀ X R V) (componentVR k c₀ X R V) V ω := by
    refine Eventually.of_forall fun ω _ => ?_
    have hr := isForceReg_thr (fun y => canonDrv_zero y) (fun y => continuous_canonDrv y)
      (fun _ => typedXL k (wordType k c₀) c₀) (fun _ => typedXR k (wordType k c₀) c₀)
      canonStp (componentPoint X R V ω)
    have he : ∀ t, canonDrv t (componentPoint X R V ω) = R t ω := fun t =>
      relDrv_relVar (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω) t
    have hVd : canonStp (componentPoint X R V ω) = V ω := rfl
    simpa only [Aux79.IsForceReg, componentVL, componentVR, he, hVd] using hr
  have hdom : ∀ z, MeasurableSet[physFilt Frame.measurable_gw4Rec hWm ν 0]
      {ω : Ω | z ∈ Chart.id.dom} := by
    intro z
    by_cases hz : z ∈ Chart.id.dom <;>
      simp only [hz, ofPred_true, ofPred_false, MeasurableSet.univ, MeasurableSet.empty]
  have hfwd : ∀ z, Measurable[physFilt Frame.measurable_gw4Rec hWm ν 0]
      ({ω : Ω | z ∈ Chart.id.dom}.indicator fun _ => Chart.id.1 z) := fun z =>
    measurable_const.indicator (hdom z)
  have hliftm : ∀ z, Measurable[physFilt Frame.measurable_gw4Rec hWm ν 0]
      ({ω : Ω | z ∈ Chart.id.dom}.indicator fun _ => Chart.id.2.2 z) := fun z =>
    measurable_const.indicator (hdom z)
  have h𝓗' := fun q D (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) t =>
    Frame.measurableSet_inter_le_min_of_canonFilt hF hGT hWm hGTm hGTae hver hX.1 q hD t
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂ν, ω ∈ (univ : Set Ω) → (q : ℝ≥0∞) < V ω →
      ∃ t, (q : ℝ≥0∞) ≤ lineClock F Wd GT V t ω := fun q =>
    (Frame.reach_min_physClockG hF hGT hGTae hver.1.1 q).mono fun _ h _ => h
  have hmean' : ∀ t (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂ν,
      ω ∈ (univ : Set Ω) → lineClock F Wd GT V t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
        (lineClock F Wd GT V t ω).toNNReal) →
      Chart.chartTransport Chart.isConformal_id 1 0 0 (M t ω) ψ =
        ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω)
          (lineClock F Wd GT V t ω).toNNReal
          (bheProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R
            (componentVL k c₀ X R V) (componentVR k c₀ X R V) ω
            (lineClock F Wd GT V t ω).toNNReal) z * ψ z := fun t ψ => by
    simpa only [chartTransport_id_eq, M, mem_univ] using (hmean t (g t) (hg t) ψ).mono
      (fun _ h _ => h)
  have hlaw := BW1Lines.hasSafeLaw_life_of_lineKernel
    (𝓗' := Coupling.filtrationComap canonFilt hΦ) (a := lineClock F Wd GT V)
    MeasurableSet.univ (fun _ => Chart.isConformal_id) hdom hfwd hliftm
    (fun _ => continuousOn_const) hX.1 0 0
    (Frame.continuous_min_physClockG hF hGT) (Frame.monotone_min_physClockG hF hGT)
    (Frame.min_physClockG_zero hF hGT)
    (Frame.measurable_min_physClockG hF hGT hWm hGTm hGTae hver) h𝓗' V hreach hreg
    (fun ψ => Frame.measurableSet_lineSafe hF hGT hWm hGTm hGTae hver (isClosed_tsupport ψ))
    𝒢L h𝒢L h𝒢Lm M hker hmean'
  have hmem := BW1Lines.hasSafeMembers_life_of_lineLocal
    (VL := componentVL k c₀ X R V) (VR := componentVR k c₀ X R V)
    (𝓗' := Coupling.filtrationComap canonFilt hΦ) (F := univ) (a := lineClock F Wd GT V)
    hX.1 hu₀.1 hh0 (fun _ => Chart.isConformal_id) hdom hfwd hliftm
    (fun _ => continuousOn_const) (fun _ z _ => InnerProductSpace.harmonicAt_const (0 : ℝ))
    0 0 (Frame.continuous_min_physClockG hF hGT) (Frame.monotone_min_physClockG hF hGT)
    (Frame.min_physClockG_zero hF hGT)
    (Frame.measurable_min_physClockG hF hGT hWm hGTm hGTae hver) h𝓗' V hreach hreg
    (fun Fb => Frame.measurableSet_lineSafe hF hGT hWm hGTm hGTae hver
      (Coupling.isCompact_ballsK Fb).isClosed) ℋ h𝓖ℋ hℋ B hBm hBc hloc
    (fun t => (hBK t).mono fun _ h _ hlt => (h hlt).trans (image_id' _).symm)
  have hFld : (fun ω => Chart.chartTransport Chart.isConformal_id 1 0 0 (X ω)) = X :=
    funext fun _ => chartTransport_id_eq _ _
  rw [hFld] at hlaw hmem
  have hEv : (fun ω => componentPoint X R V ω) ⁻¹'
      typeEvent k (wordType k c₀) (fun _ => c₀) univ = univ := by
    ext ω
    simp only [typeEvent, mem_preimage, mem_inter_iff, mem_univ, mem_ofPred_eq,
      and_self, eq_self]
  refine hasRelSafe_of_space measurable_const MeasurableSet.univ measurable_const hX.1
    hver.1.1.1 hver.1.1.2.2.2.1 ?_ ?_
    (fun φ => Supp8.HullDetGen.integrable_apply_of_isGFF c₀.isPiecewiseConstantBoundaryData hX φ)
    (ae_canonStp_le_thr_component c₀ hL hR _)
  · rw [hEv, hWd]
    exact hlaw
  · rw [hEv, hWd]
    exact hmem

end InteractingSLE.Theorem14.GW4Fix
