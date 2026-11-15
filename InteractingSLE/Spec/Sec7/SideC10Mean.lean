/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC10Inversion
import InteractingSLE.Spec.Sec7.SideC9InitialWord
import InteractingSLE.Spec.Sec7.SideC7Mean

/-!
# Initial native means from flow-coordinate data and a common frame

PROVE-SIDE-COLLAR2. Finite-word normalization is proved by the compatible
inversion and bounded harmonic uniqueness. The actual flow mean, its
incident angle word, and the field/conditioning/branch identification are
named inputs. Neither input is asserted to follow from `Ready` alone.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current LocalSets Sec7 Sec7.PocketStopSide Sec7.Aux119Heights

/-- Remaining flow-coordinate data: a bounded harmonic pocket mean, its
incoming heights, and the finite cumulative weights at the actual marks.
There is no counterflow mean, later reference, collar or increment law. -/
def InitialPocketFlowWord {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω)
    (M : SideTest Ω → Ω → ℂ → ℝ)
    (θ₁ θ₂ : SideTest Ω → Ω → ℝ → ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
    ∀ᵐ ω ∂d.measure, ω ∈ target.event →
      (∀ a, target.marksL ω a ≤ 0) ∧ (∀ a, 0 ≤ target.marksR ω a) ∧
      InnerProductSpace.HarmonicOnNhd (M j ω) H ∧
      (∃ C : ℝ, ∀ z ∈ H, |M j ω z| ≤ C) ∧
      (∀ x : ℝ, x ∉ forceJumpSet (target.marksL ω) (target.marksR ω) →
        Tendsto (M j ω) (𝓝[H] (-((x : ℂ)⁻¹)))
          (𝓝 (cf92Lower (16 / i.kappa) (θ₁ j ω (-x⁻¹)) (θ₂ j ω (-x⁻¹)) (-x⁻¹)))) ∧
      (∀ x : ℝ, x ∉ forceJumpSet (target.marksL ω) (target.marksR ω) → x < 0 →
        ∑ a ∈ Finset.univ.filter (fun a => x < target.marksL ω a), target.rhoL a =
          cf95RhoL (16 / i.kappa) (θ₁ j ω (-x⁻¹))) ∧
      (∀ x : ℝ, x ∉ forceJumpSet (target.marksL ω) (target.marksR ω) → 0 < x →
        ∑ a ∈ Finset.univ.filter (fun a => target.marksR ω a ≤ x), target.rhoR a =
          cf95RhoR (16 / i.kappa) (θ₂ j ω (-x⁻¹)))

/-- Remaining field and frame identification, with the actual filled
initial reference, inherited base lift and the supplied common offset.
This is not a claim that arbitrary supplied offsets satisfy the identity. -/
def InitialPocketFlowFrame {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
    IsLocalSetMean (j.capacityReference i d 0) target.zeroField d.measure (G j) ∧
      ∀ᵐ ω ∂d.measure, ω ∈ target.event → ∀ z ∈ target.domain ω,
        harmRep (G j ω) (H \ j.capacityReference i d 0 ω) z + target.harmonic z +
          chiC target.kappa * (target.baseChart ω).2.2 z =
          centeredReversedMean (16 / i.kappa) (M j ω) ((target.baseChart ω).1 z) -
            (side j).offset

/-- The initial finite-word interior formula from flow data. The only
unproved inputs are the displayed flow word and its actual physical frame;
the bounded harmonic inversion and native-coordinate normalization are conclusions. -/
theorem initialPocketMeanFormula_of_flowWord_frame
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (θ₁ θ₂ : SideTest Ω → Ω → ℝ → ℝ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hWord : InitialPocketFlowWord i d M θ₁ θ₂)
    (hFrame : InitialPocketFlowFrame i d side G M) :
    InitialPocketMeanFormula i d side G := by
  intro j hj target
  obtain ⟨hG, hFrameω⟩ := hFrame j hj
  refine ⟨hG, ?_⟩
  filter_upwards [hWord j hj, hFrameω] with ω hWordω hFrameω hω z hz
  obtain ⟨hL, hR, hM, hBound, hHeight, hLeft, hRight⟩ := hWordω hω
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hDual : 16 / (16 / i.kappa) = target.kappa := by
    rw [j.target_kappa_eq i d]
    field_simp
  have hMean := centeredReversedMean_eq_meanExt (div_pos (by norm_num) hκ)
    target.rhoL target.rhoR (target.marksL ω) (target.marksR ω)
    (θ₁ j ω) (θ₂ j ω) hM hBound hHeight hLeft hRight
  rw [hDual] at hMean
  have hBase := j.isDomainChart_baseChart hj hRc (hLc j.seed) hω
  have hzH := hBase.fwd_mem hz
  have hRaw := j.initialWordExtension_eq_raw_of_signed_marks hj hω hL hR
  rw [hFrameω hω z hz, hMean hzH, hRaw]

end InteractingSLE.Wire
