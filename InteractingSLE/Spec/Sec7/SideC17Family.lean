/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC17Relift
import InteractingSLE.Spec.Sec7.SideC12Frame

/-! # The source mean with an explicit chart, and R100's normalization

PROVE-SIDE-COLLAR2. The principal specialization is definitionally the
landed source predicate. The relifted specialization has branch one
and zero additive source constant, on the original unrefined tests.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire
open Current LocalSets WholeField Sec7 Sec7.SideC12 Sec7.SideC17 Sec7.Aux119Heights

/-- The original source predicate with its derivative-logarithm chart
explicit. This permits the relift required by R100. -/
def InitialPocketConjugateFlowMeanWithChart {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (c : SideTest Ω → Ω → Chart)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (n : SideTest Ω → Ω → ℤ) (b : SideTest Ω → ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d →
    IsLocalSetMean (fun ω => WangWu.negInv '' j.capacityReference i d 0 ω)
      (centredField d.field d.originalMean) d.measure (G₀ j) ∧
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (G₀ j ω) (H \ WangWu.negInv '' j.capacityReference i d 0 ω) (WangWu.negInv z) +
          d.originalMean (WangWu.negInv z) =
        M j ω (conjugateFlowMap (c j ω) (WangWu.negInv z)) -
          chiC (16 / i.kappa) * (conjugateFlowLift (c j ω) (WangWu.negInv z) + 2 * π * (n j ω : ℝ)) + b j

theorem initialPocketConjugateFlowMeanWithChart_principal_iff
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (n : SideTest Ω → Ω → ℤ) (b : SideTest Ω → ℝ) :
    InitialPocketConjugateFlowMeanWithChart i d (fun j => (j.target i d).baseChart) G₀ M n b ↔
      InitialPocketConjugateFlowMean i d G₀ M n b := Iff.rfl

/-- Every samplewise source branch normalizes to one, with `b = 0`.
No branch constancy and no event refinement are needed. -/
theorem InitialPocketConjugateFlowMean.zeroFrame
    {Ω : Type} [MeasurableSpace Ω] {i : BothLow} {d : WordObjects Ω}
    {G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ} {n : SideTest Ω → Ω → ℤ}
    (h : InitialPocketConjugateFlowMean i d G₀ M n (fun _ => 0)) :
    InitialPocketConjugateFlowMeanWithChart i d
      (fun j ω => zeroFrameChart ((j.target i d).baseChart ω) (n j ω)) G₀ M (fun _ _ => 1) (fun _ => 0) := by
  intro j hj
  obtain ⟨hG, hF⟩ := h j hj
  refine ⟨hG, ?_⟩
  filter_upwards [hF] with ω hFω hω z hz
  simpa only [Int.cast_one, mul_one, conjugateFlowLift_zeroFrameChart,
    conjugateFlowMap_zeroFrameChart] using hFω hω z hz

/-- The relifted physical initial frame from the original source mean.
The displayed chart is the one actually used in the formula. -/
theorem initialPocketFlowFrame_zeroFrame_of_conjugateMean
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (n : SideTest Ω → Ω → ℤ)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd d.coupledMean H)
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hSource : InitialPocketConjugateFlowMean i d G₀ M n (fun _ => 0)) :
    ∀ j : SideTest Ω, j.Ready d →
      IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure
        (initialTransportedMeans i d G₀ j) ∧
      ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
        harmRep (initialTransportedMeans i d G₀ j ω) (H \ j.capacityReference i d 0 ω) z +
            (j.target i d).harmonic z + chiC (j.target i d).kappa *
              (zeroFrameChart ((j.target i d).baseChart ω) (n j ω)).2.2 z =
          PocketStopSide.centeredReversedMean (16 / i.kappa) (M j ω) (((j.target i d).baseChart ω).1 z) := by
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hκf : 0 < 16 / i.kappa := div_pos (by norm_num) hκ
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  intro j hj
  obtain ⟨hg₀, hFlow⟩ := hSource.zeroFrame j hj
  have hA := fun ω => WangWu.image_negInv_relClosed (j.original_filling_regular (i := i) hj 0 ω)
  have hMean := localSetMean_physicalMean hA hT hTr hu₀ hu₁ hg₀
  have hRep := ae_physicalMean_formula (a := -(π * chiC (16 / i.kappa)))
    (k := chiC i.kappa) (c := 0) hA hu₀ hu₁ hg₀
  simp only [WangWu.image_negInv_image_negInv] at hMean hRep
  refine ⟨?_, ?_⟩
  · rw [SideTest.target_zeroField]
    exact hMean
  · filter_upwards [hRep, hFlow] with ω hRepω hFlowω hω z hz
    have hBase := j.isDomainChart_baseChart hj hRc (hLc j.seed) hω
    have hComp : z ∈ H \ j.capacityReference i d 0 ω := by
      have hωj : ω ∈ j.event := by rwa [SideTest.target_event] at hω
      rw [SideTest.capacityReference, SideTest.original_filling_zero, PocketStopSide.eventFilled,
        ite_eq_left hωj]
      exact ⟨hBase.subset_H hz, fun h => (h.2.resolve_right (by simp)) hz⟩
    have hEq := frame_identity_of_conjugate_flow hκf
      (zeroFrameChart ((j.target i d).baseChart ω) (n j ω)) (M j ω)
      (fun y => harmRep (G₀ j ω) (H \ WangWu.negInv '' j.capacityReference i d 0 ω) y + d.originalMean y)
      1 0 z (hFlowω hω z hz)
    simp only [hd, Int.cast_one, sub_self, mul_zero, add_zero, sub_zero] at hEq
    rw [SideTest.target_harmonic_eq, hHarm (hBase.subset_H hz), SideTest.target_kappa_eq]
    change harmRep (physicalMean _ _ _ _ _ _) _ z + d.coupledMean z + _ = _
    have hRepz := hRepω z hComp
    change harmRep (physicalMean _ _ _ _ _ _) (H \ j.capacityReference i d 0 ω) z + d.coupledMean z = _
      at hRepz
    rw [hRepz]
    exact hEq

end InteractingSLE.Wire
