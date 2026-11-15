/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Ker

/-!
# A local set's Gaussian kernel at `P`, with its local-set mean

Packet PROVE-GW2-GEOM2, round 14 (D49), for the base of Claim(k) at a root `x`. The construction of round 11's
`GW2Xk.exists_kernel_union_meanX`, for any local set with marks: a set family `B` local for marks `ℋ` has a local-set
mean `g` and, for the coarsened marks `unionMarks B g ℋ`, the Gaussian kernel identity at `P` with mean `g + u₀`
(`GW4Fix.ae_condExp_cexp_boundary_marked`).

* **`exists_kernel_of_local`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2Omx LocalSets WholeField GW2TipSystem GW2Sdi GW4Fix GW4Fix.CLoc GW2Rd GW2Xk Restart.MarkovChart

/-- **A local set's Gaussian kernel at `P`, with its local-set mean.** -/
theorem exists_kernel_of_local {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}) (hloc : IsHistoryAvoidanceLocal ℋ.1 B (centredField h u₀) P) :
    ∃ (g : Ω → DistOn upperHalfPlaneOpens) (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}),
      IsLocalSetMean B (centredField h u₀) P g ∧ ℋ.1 ≤ 𝓜.1 ∧ Measurable[𝓜.1, hittingSigma] B ∧
      (∀ᵐ ω ∂P, IsHarmonicDistOn (g ω + smoothDist upperHalfPlaneOpens u₀) (H \ B ω)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓜.1] =ᵐ[P]
          fun ω => rangeKerCF (g ω + smoothDist upperHalfPlaneOpens u₀) (H \ B ω) φ := by
  have hh0m : Measurable (centredField h u₀) := measurable_centredField hhm u₀
  have hl : IsLocalSet B (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hBm (Eventually.of_forall hBc)).out 4 1).2 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 hBm hl
  have hker := ae_condExp_cexp_boundary_marked hu₀ hh0 hBm hBc ℋ.2 hloc hg
  set M : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω + smoothDist upperHalfPlaneOpens u₀ with hM_def
  have hgM : Measurable[(unionMarks B g ℋ.1)] g := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hBM : Measurable[(unionMarks B g ℋ.1), hittingSigma] B :=
    Measurable.of_comap_le (le_sup_left.trans le_sup_left)
  have hadd : Measurable fun T : DistOn upperHalfPlaneOpens => T + smoothDist upperHalfPlaneOpens u₀ :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).add measurable_const)
  have hMM : Measurable[(unionMarks B g ℋ.1)] M := hadd.comp hgM
  have hgerm : (unionMarks B g ℋ.1) ≤ germSigma B (centredField h u₀) ⊔ ℋ.1 :=
    sup_le (sup_le (le_sup_left.trans' (comap_le_germSigma _ _)) (le_sup_left.trans' hg.1.comap_le)) le_sup_right
  have hgle : germSigma B (centredField h u₀) ⊔ ℋ.1 ≤ mΩ := sup_le (germSigma_le hBm hh0m) ℋ.2
  have hle : (unionMarks B g ℋ.1) ≤ mΩ := hgerm.trans hgle
  have hkerP : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | (unionMarks B g ℋ.1)] =ᵐ[P]
        fun ω => rangeKerCF (M ω) (H \ B ω) φ := by
    intro φ
    have hR : StronglyMeasurable[(unionMarks B g ℋ.1)] fun ω => rangeKerCF (M ω) (H \ B ω) φ :=
      (measurable_rangeKerCF hMM hBM hBc φ).stronglyMeasurable
    have hRi : Integrable (fun ω => rangeKerCF (M ω) (H \ B ω) φ) P := by
      refine Integrable.of_bound ((hR.mono hle).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => ?_)
      have hcov : 0 ≤ zeroGFFTestCov (H \ B ω) φ φ := zeroGFFTestCov_self_nonneg (hBc ω).2 sdiff_subset φ
      rw [rangeKerCF, Complex.norm_exp]
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
      rw [Real.exp_le_one_iff]
      nlinarith
    calc P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | (unionMarks B g ℋ.1)]
        =ᵐ[P] P[P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          germSigma B (centredField h u₀) ⊔ ℋ.1] | (unionMarks B g ℋ.1)] :=
          (condExp_condExp_of_le hgerm hgle).symm
      _ =ᵐ[P] P[fun ω => rangeKerCF (M ω) (H \ B ω) φ | (unionMarks B g ℋ.1)] := condExp_congr_ae (hker φ)
      _ = fun ω => rangeKerCF (M ω) (H \ B ω) φ := condExp_of_stronglyMeasurable hle hR hRi
  refine ⟨g, ⟨_, hle⟩, hg, le_sup_right, hBM, ?_, hkerP⟩
  filter_upwards [hg.2.1] with ω hω
  exact Coupling.IsHarmonicDistOn.add' (hBc ω).2 hω
    (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu₀) sdiff_subset)

end InteractingSLE.Theorem14.GW2Kx
