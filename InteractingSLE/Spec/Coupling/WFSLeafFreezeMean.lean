/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFreezeLocal
import InteractingSLE.Spec.Coupling.WFSLeafRetData

/-!
# The retained germ mean from a history Gaussian kernel

After marked locality is proved, the cover law supplies the Gaussian kernel
given the germ joined with the history. Its covariance equals the covariance
of the history kernel. The nested Gaussian mean comparison therefore
identifies both means, giving the scalar limits required by `hFreeze`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField QuantumZipper
open Sec6.Prop65 Sec7.FlatClockProof

/-- The distribution-valued retained kernel gives a scalar conditional
Gaussian law, with the deterministic variance bound of the ambient GFF. -/
theorem isCondGaussian_of_retainedKernel
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h M : Ω → DistOn upperHalfPlaneOpens}
    {A : Ω → Set ℂ} (hℋ : ℋ ≤ mΩ) (hhm : Measurable h)
    (hA : Measurable[ℋ, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hMm : Measurable[ℋ] M)
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | ℋ] =ᵐ[P]
        fun ω => rangeKerCF (M ω) (H \ A ω) φ) (φ : TestOn upperHalfPlaneOpens) :
    IsCondGaussian ℋ P (fun ω => h ω φ) (fun ω => M ω φ)
      (fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) (zeroGFFTestCov H φ φ) := by
  refine ⟨hℋ, (measurable_distOn_apply φ).comp hhm, (measurable_distOn_apply φ).comp hMm,
    (measurable_comap_zeroGFFTestCov_compl A φ φ).mono hA.comap_le le_rfl,
    (fun ω => zeroGFFTestCov_self_nonneg (isOpen_H_diff_relClosureH _) sdiff_subset φ),
    (fun ω => zeroGFFTestCov_mono (isOpen_H_diff_relClosureH _) isOpen_H sdiff_subset subset_rfl φ),
    fun t => ?_⟩
  have he : (fun ω => Complex.exp (Complex.I * ((t * h ω φ : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * (h ω (t • φ) : ℂ)) := by
    funext ω
    rw [map_smul, smul_eq_mul]
  rw [he]
  filter_upwards [hker (t • φ)] with ω hω
  rw [hω, rangeKerCF, map_smul, smul_eq_mul,
    zeroGFFTestCov_smul_self (hAc ω).2 sdiff_subset t φ,
    relClosureH_eq (hAc ω).1 (hAc ω).2, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Equal retained covariances at the history and germ-history levels force
their conditional means to agree. -/
theorem ae_condExp_germ_history_eq_of_retainedKernel
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h M : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : Ω → Set ℂ}
    (hℋ : ℋ ≤ mΩ) (hA : Measurable[ℋ, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hMm : Measurable[ℋ] M)
    (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | ℋ] =ᵐ[P]
        fun ω => rangeKerCF (M ω) (H \ A ω) φ) (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => h ω φ | germSigma A h ⊔ ℋ] =ᵐ[P] fun ω => M ω φ := by
  have hAm : Measurable[mΩ, hittingSigma] A := hA.mono hℋ le_rfl
  have hAce : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := Eventually.of_forall hAc
  have hl : IsLocalSet A h P := ((isLocalSet_tfae hh hAm hAce).out 1 4).1 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh hAm hl
  have hmk := isCoverMarking_history hh hAm hℋ hloc
  have hle : germSigma A h ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hAm hh.measurable) hℋ
  have htr : ∀ j, germSigma A h ⊔ ℋ ≤
      aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ ℋ) j A h) P := fun j =>
    sup_le (fun E hE => germSigmaAt_le_aeSigmaM hh hmk.comap_le j E
      (measurableSet_germSigmaAt_coverRad hE j))
      ((le_sup_right : ℋ ≤ MeasurableSpace.comap A hittingSigma ⊔ ℋ).trans
        ((le_sup_left : _ ≤ coverSigmaM _ j A h).trans (le_aeSigma _ P)))
  have G₁ := isCondGaussian_of_retainedKernel hℋ hh.measurable hA hAc hMm hker φ
  have G₂ := isCondGaussian_of_cover hh hAm hmk hAce le_sup_left hle htr hg φ
  filter_upwards [IsCondGaussian.ae_mean_eq_of_var_eq (le_sup_right : ℋ ≤ germSigma A h ⊔ ℋ) G₁ G₂,
    ae_localSetMean_eq_condExp_history hh hAm hℋ hloc hAce hg φ] with ω heq hce
  exact hce.symm.trans (heq rfl).symm

/-- For a common history mean reader, constant scalar approximants already
satisfy the exact `HasRetainedTraceLimits` input. -/
theorem hasRetainedTraceLimits_of_retainedKernel
    {nL nR : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {Y : Ω → LawUnique.HistorySpace nL nR} (hY : Measurable Y)
    {M : LawUnique.HistorySpace nL nR → DistOn upperHalfPlaneOpens} (hMm : Measurable M)
    (hMh : ∀ᵐ ω ∂P, IsHarmonicDistOn (M (Y ω)) (H \ retainedTraceReader (Y ω)))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | MeasurableSpace.comap Y inferInstance] =ᵐ[P]
        fun ω => rangeKerCF (M (Y ω)) (H \ retainedTraceReader (Y ω)) φ) :
    HasRetainedTraceLimits P h Y (fun c _ γ => M γ (comb upperHalfPlaneOpens c)) := by
  have hA : Measurable[MeasurableSpace.comap Y inferInstance, hittingSigma] (retainedTraceReader ∘ Y) :=
    measurable_retainedTraceReader.comp (Measurable.of_comap_le le_rfl)
  have hAc := fun ω => retainedTraceReader_geometry (Y ω)
  have hloc := isHistoryAvoidanceLocal_of_retainedKernel hY.comap_le hh.measurable hA
    (Eventually.of_forall hAc) hMh hker
  refine ⟨hloc, fun c => ?_⟩
  have hce := ae_condExp_germ_history_eq_of_retainedKernel hh hY.comap_le hA hAc
    (hMm.comp (Measurable.of_comap_le le_rfl)) hloc hker (comb upperHalfPlaneOpens c)
  filter_upwards [hce] with ω hω
  rw [hω]
  exact tendsto_const_nhds

end InteractingSLE.WFS
