/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocKernel

/-! # GW4: the union kernel at any selected countable family of physical times

The coarsened-mark transfer of GW4CLocKernel works for any countable index
set. In particular the actual rational reference times require no new
Gaussian-law hypothesis. The mean and retained sets remain the same
original-space union means, not a separately chosen reference family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField WalkLaw Sec5.GlueCond Sec5.Cond44Ref

/-- The actual joint union kernel, conditioned on the walks, at every
time in an arbitrary countable family, simultaneously for all tests. -/
theorem exists_ae_condExpKernel_kernel_at
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {ι : Type*} [Countable ι] (τ : ι → ℝ≥0)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b J P h spec (E spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (E spec))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ (B : ℝ≥0 → Ω → Set ℂ) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
      (𝓜 : ℝ≥0 → {m : MeasurableSpace Ω // m ≤ mΩ}),
      (∀ t, jointPast κ b J E ≤ (𝓜 t).1) ∧
      (∀ t, MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t) ≤ (𝓜 t).1) ∧
      (∀ t, Measurable[(𝓜 t).1, hittingSigma] (B t)) ∧ (∀ t, Measurable[(𝓜 t).1] (M t)) ∧
      (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
      (∀ t, ∀ᵐ ω ∂P, B t ω = relClosureH
        (walkUnionSet κ b J E ω ∪ cfHullQ t (cfHistory W ζ ω))) ∧
      (∀ t, ∀ᵐ ω ∂P, IsHarmonicDistOn (M t ω) (H \ B t ω)) ∧
      ∀ᵐ ω₀ ∂P, ∀ p : ι, ∀ φ : TestOn upperHalfPlaneOpens,
        (condExpKernel P (jointPast κ b J E) ω₀)[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) |
          (𝓜 (τ p)).1] =ᵐ[condExpKernel P (jointPast κ b J E) ω₀]
          fun ω => rangeKerCF (M (τ p) ω) (H \ B (τ p) ω) φ := by
  obtain ⟨B, g, hℋ, hBm, hBc, hBeq, -, hg, hker⟩ :=
    GW4Fix.exists_walkCfUnion_kernel h12p h13 hκ hκ4 hb hh hcf hζ hE hreg hu₀
  have hhm : Measurable h := hh.1
  have hh0m : Measurable (centredField h u₀) := measurable_centredField hhm u₀
  set M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens := fun t ω => g t ω + smoothDist upperHalfPlaneOpens u₀
    with hM_def
  -- the coarsened marks
  let 𝓜₀ : ℝ≥0 → MeasurableSpace Ω := fun t =>
    MeasurableSpace.comap (B t) hittingSigma ⊔ MeasurableSpace.comap (g t) inferInstance ⊔
      walkCfMarks κ b J E W ζ t
  have hg𝓜 : ∀ t, Measurable[𝓜₀ t] (g t) := fun t =>
    Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hB𝓜 : ∀ t, Measurable[𝓜₀ t, hittingSigma] (B t) := fun t =>
    Measurable.of_comap_le (le_sup_left.trans le_sup_left)
  have hadd : Measurable fun T : DistOn upperHalfPlaneOpens => T + smoothDist upperHalfPlaneOpens u₀ :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).add measurable_const)
  have hM𝓜 : ∀ t, Measurable[𝓜₀ t] (M t) := fun t => hadd.comp (hg𝓜 t)
  have hgerm : ∀ t, 𝓜₀ t ≤ germSigma (B t) (centredField h u₀) ⊔ walkCfMarks κ b J E W ζ t := fun t =>
    sup_le (sup_le (le_sup_left.trans' (comap_le_germSigma _ _))
      (le_sup_left.trans' (hg t).1.comap_le)) le_sup_right
  have hle : ∀ t, 𝓜₀ t ≤ mΩ := fun t =>
    (hgerm t).trans (sup_le (germSigma_le (hBm t) hh0m) (hℋ t))
  have hcg : ∀ t, @MeasurableSpace.CountablyGenerated Ω (𝓜₀ t) := fun t =>
    MeasurableSpace.CountablyGenerated.sup (MeasurableSpace.CountablyGenerated.sup
      (@MeasurableSpace.CountablyGenerated.comap _ _ hittingSigma countablyGenerated_hittingSigma _)
      (MeasurableSpace.CountablyGenerated.comap _)) (countablyGenerated_walkCfMarks κ b J E W ζ t)
  have hJ : ∀ t, jointPast κ b J E ≤ 𝓜₀ t := fun t => le_sup_left.trans le_sup_right
  -- the kernel given the coarsened marks under `P`
  have hkerP : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens),
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓜₀ t] =ᵐ[P]
        fun ω => rangeKerCF (M t ω) (H \ B t ω) φ := by
    intro t φ
    have hle' : germSigma (B t) (centredField h u₀) ⊔ walkCfMarks κ b J E W ζ t ≤ mΩ :=
      sup_le (germSigma_le (hBm t) hh0m) (hℋ t)
    have hR : StronglyMeasurable[𝓜₀ t] fun ω => rangeKerCF (M t ω) (H \ B t ω) φ :=
      (measurable_rangeKerCF (hM𝓜 t) (hB𝓜 t) (hBc t) φ).stronglyMeasurable
    have hRi : Integrable (fun ω => rangeKerCF (M t ω) (H \ B t ω) φ) P := by
      refine Integrable.of_bound ((hR.mono (hle t)).aestronglyMeasurable) 1
        (Eventually.of_forall fun ω => ?_)
      have hcov : 0 ≤ zeroGFFTestCov (H \ B t ω) φ φ :=
        zeroGFFTestCov_self_nonneg (hBc t ω).2 sdiff_subset φ
      rw [rangeKerCF, Complex.norm_exp]
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
      rw [Real.exp_le_one_iff]
      nlinarith
    calc P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓜₀ t]
        =ᵐ[P] P[P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          germSigma (B t) (centredField h u₀) ⊔ walkCfMarks κ b J E W ζ t] | 𝓜₀ t] :=
          (condExp_condExp_of_le (hgerm t) hle').symm
      _ =ᵐ[P] P[fun ω => rangeKerCF (M t ω) (H \ B t ω) φ | 𝓜₀ t] := condExp_congr_ae (hker t φ)
      _ = fun ω => rangeKerCF (M t ω) (H \ B t ω) φ := condExp_of_stronglyMeasurable (hle t) hR hRi
  -- the transfer, at the selected countable times and rational combinations
  have hν : ∀ᵐ ω₀ ∂P, ∀ (p : ι) (k : Restart.RatComb),
      (condExpKernel P (jointPast κ b J E) ω₀)[fun ω => Complex.exp
        (Complex.I * (h ω (Restart.ratComb upperHalfPlaneOpens k) : ℂ)) | 𝓜₀ (τ p)]
        =ᵐ[condExpKernel P (jointPast κ b J E) ω₀]
          fun ω => rangeKerCF (M (τ p) ω) (H \ B (τ p) ω)
            (Restart.ratComb upperHalfPlaneOpens k) := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun k => ?_
    refine ae_ae_condExp_eq_of_le (hJ _) (hle _) (hcg _)
      (GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hhm)) (C := 1)
      (fun ω => (Complex.norm_exp_I_mul_ofReal _).le) (hkerP _ _)
  refine ⟨B, M, fun t => ⟨𝓜₀ t, hle t⟩, hJ, fun t => le_sup_right.trans le_sup_right, hB𝓜, hM𝓜, hBc, hBeq,
    fun t => ?_, ?_⟩
  · filter_upwards [(hg t).2.1] with ω hω
    exact Coupling.IsHarmonicDistOn.add' (hBc t ω).2 hω
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu₀.1) sdiff_subset)
  · filter_upwards [hν] with ω₀ hω₀ p φ
    exact ae_condExp_cexp_eq_rangeKerCF_of_ratComb (Q := condExpKernel P (jointPast κ b J E) ω₀)
      (hle _) hhm (Eventually.of_forall fun ω => ⟨(hBc _ ω).2, sdiff_subset⟩) (hω₀ p) φ


end InteractingSLE.Theorem14.GW4Fix.CLoc
