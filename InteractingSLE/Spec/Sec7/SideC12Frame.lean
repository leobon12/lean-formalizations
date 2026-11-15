/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Conjugate

/-!
# The initial physical frame from the original filled-pocket mean

PROVE-SIDE-COLLAR2. Global inversion and deterministic centering are now
theorems. The remaining source input is explicitly the original local
mean on the filled pocket, its flow-chart identity, and the compatibility
of its inherited branch with the prescribed constant offset. These are
distinct conditional inputs, not a replacement for a source theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire

open Current LocalSets WholeField Sec7 Sec7.SideC12 Sec7.Aux119Heights
open WangWu (negInv)

/-- Exact remaining original-coordinate input: the filled-pocket local
mean and its flow-chart representation, with its common integer branch.
No inversion or counterflow mean identification is assumed here. -/
def InitialPocketConjugateFlowMean {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (n : SideTest Ω → Ω → ℤ)
    (b : SideTest Ω → ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d →
    IsLocalSetMean (fun ω => negInv '' j.capacityReference i d 0 ω)
      (centredField d.field d.originalMean) d.measure (G₀ j) ∧
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (G₀ j ω) (H \ negInv '' j.capacityReference i d 0 ω) (negInv z) +
          d.originalMean (negInv z) =
        M j ω (conjugateFlowMap ((j.target i d).baseChart ω) (negInv z)) -
          chiC (16 / i.kappa) *
            (conjugateFlowLift ((j.target i d).baseChart ω) (negInv z) + 2 * π * (n j ω : ℝ)) + b j

/-- The physical family constructed from the original means. -/
def initialTransportedMeans {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens) :
    SideTest Ω → Ω → DistOn upperHalfPlaneOpens :=
  fun j ω => physicalMean (-(π * chiC (16 / i.kappa))) (chiC i.kappa) 0
    d.originalMean d.coupledMean (G₀ j ω)

/-- The complete physical frame follows from the original flow identity
and the displayed branch compatibility. Mean transport, centering, and
the initial finite-word normalization are proved in this route. -/
theorem initialPocketFlowFrame_of_conjugateMean
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (n : SideTest Ω → Ω → ℤ)
    (b : SideTest Ω → ℝ)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd d.coupledMean H)
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hSource : InitialPocketConjugateFlowMean i d G₀ M n b)
    (hBranch : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure,
      ω ∈ (j.target i d).event →
        (side j).offset = b j + 2 * π * chiC (16 / i.kappa) * (1 - (n j ω : ℝ))) :
    InitialPocketFlowFrame i d side (initialTransportedMeans i d G₀) M := by
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  intro j hj target
  obtain ⟨hg₀, hFlow⟩ := hSource j hj
  have hB : ∀ ω, j.capacityReference i d 0 ω ⊆ H ∧
      IsOpen (H \ j.capacityReference i d 0 ω) :=
    j.original_filling_regular hj 0
  have hA := fun ω => WangWu.image_negInv_relClosed (hB ω)
  have hMean := localSetMean_physicalMean hA hT hTr hu₀ hu₁ hg₀
  simp only [WangWu.image_negInv_image_negInv] at hMean
  have hRep := ae_physicalMean_formula (a := -(π * chiC (16 / i.kappa)))
    (k := chiC i.kappa) (c := 0) hA hu₀ hu₁ hg₀
  simp only [WangWu.image_negInv_image_negInv] at hRep
  refine ⟨?_, ?_⟩
  · change IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure _
    rw [Current.SideTest.target_zeroField]
    exact hMean
  · filter_upwards [hRep, hFlow, hBranch j hj] with ω hRepω hFlowω hBranchω hω z hz
    have hBase := j.isDomainChart_baseChart hj hRc (hLc j.seed) hω
    have hComp : z ∈ H \ j.capacityReference i d 0 ω := by
      have hωj : ω ∈ j.event := by rwa [Current.SideTest.target_event] at hω
      rw [Current.SideTest.capacityReference, Current.SideTest.original_filling_zero,
        Sec7.PocketStopSide.eventFilled, ite_eq_left hωj]
      refine ⟨hBase.subset_H hz, ?_⟩
      intro h
      exact (h.2.resolve_right (by simp)) hz
    have hEq := frame_identity_of_conjugate_flow (div_pos (by norm_num) hκ)
      (target.baseChart ω) (M j ω)
      (fun y => harmRep (G₀ j ω) (H \ negInv '' j.capacityReference i d 0 ω) y + d.originalMean y)
      (n j ω) (b j) z (hFlowω hω z hz)
    rw [hdual] at hEq
    change harmRep (initialTransportedMeans i d G₀ j ω)
      (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
      chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z = _
    rw [Current.SideTest.target_harmonic_eq, hHarm (hBase.subset_H hz),
      Current.SideTest.target_kappa_eq, hBranchω hω]
    change harmRep (physicalMean _ _ _ _ _ _) _ z + d.coupledMean z + _ = _
    rw [hRepω z hComp]
    exact hEq

end InteractingSLE.Wire
