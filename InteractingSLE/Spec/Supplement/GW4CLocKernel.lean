/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocTower
import InteractingSLE.Spec.Supplement.GW4SafeRKernel
import InteractingSLE.Spec.Coupling.WholeField2Hull
import InteractingSLE.Spec.Coupling.Locality11Gauss

/-!
# GW4: the union kernel of the walks and the counterflow under the conditional law given the walks

Packet PROVE-GW4-CLOC, step 1. PROVE-GW4-SAFER's `exists_walkCfUnion_kernel` gives, under the original measure `P`,
the Gaussian kernel of the field given the germs of the union `B t` of the two walks and the counterflow hull, and the
retained walk and counterflow records. Here the conditioning is coarsened to the countably generated σ-algebra
`𝓜 t = σ(B t) ∨ σ(M t) ∨ walkCfMarks t` (which still contains the walk pasts and the counterflow record), and the
kernel is transferred, for `P`-almost every `ω₀`, to the regular conditional law `ν = condExpKernel P 𝒲 ω₀` given the
walk pasts `𝒲`, simultaneously at all dyadic times and all tests (`exists_ae_condExpKernel_kernel`).

No relative restart, no conditional independence after disintegration and no finite-word mean is used: the transfer is
the tower property for a countably generated σ-algebra (`ae_ae_condExp_eq_of_le`) and the identification of the
conditional law from countably many characteristic values (`ae_condExp_cexp_eq_rangeKerCF_of_ratComb`).
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

/-- The walk records and the counterflow record at `t` form a countably generated σ-algebra. -/
theorem countablyGenerated_walkCfMarks {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) :
    @MeasurableSpace.CountablyGenerated Ω (walkCfMarks κ b J E W ζ t) := by
  refine MeasurableSpace.CountablyGenerated.sup (MeasurableSpace.CountablyGenerated.sup ?_ ?_) ?_
  · rw [Exist.Staged.pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  · rw [Exist.Staged.pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  · rw [WangWu.stopSigma, MeasurableSpace.comap_comp]
    exact MeasurableSpace.CountablyGenerated.comap _

/-- The Gaussian kernel functional is measurable for any σ-algebra recording the mean and the set. -/
theorem measurable_rangeKerCF {Ω : Type*} {m : MeasurableSpace Ω} {M : Ω → DistOn upperHalfPlaneOpens}
    (hM : Measurable[m] M) {B : Ω → Set ℂ} (hB : Measurable[m, hittingSigma] B)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) (φ : TestOn upperHalfPlaneOpens) :
    Measurable[m] fun ω => rangeKerCF (M ω) (H \ B ω) φ := by
  have hcov : Measurable[m] fun ω => zeroGFFTestCov (H \ B ω) φ φ := by
    have h1 := (measurable_comap_zeroGFFTestCov_compl B φ φ).mono hB.comap_le le_rfl
    have he : (fun ω => zeroGFFTestCov (H \ relClosureH (B ω)) φ φ) =
        fun ω => zeroGFFTestCov (H \ B ω) φ φ := funext fun ω => by
      rw [relClosureH_eq (hBc ω).1 (hBc ω).2]
    rwa [he] at h1
  refine Complex.measurable_exp.comp ?_
  refine (measurable_const.mul (Complex.measurable_ofReal.comp
    ((LQGMetric.measurable_distOn_apply φ).comp hM))).sub ?_
  exact Complex.measurable_ofReal.comp (measurable_const.mul hcov)

/-- **The union kernel under the conditional law given the walks.** For the GW4 configuration there are random
relatively closed sets `B t` (almost surely the relative closure of the walk union and the counterflow hull), means
`M t` (almost surely harmonic off `B t`) and countably generated σ-algebras `𝓜 t ⊇ 𝒲 ∨ σ(counterflow record at t)`
recording `B t` and `M t`, such that for `P`-almost every `ω₀`, under `ν = condExpKernel P 𝒲 ω₀`, at every dyadic
time and every test `φ`, `E_ν[e^{i h(φ)} | 𝓜 q] = exp(i (M q)(φ) − ½ σ²_{ℍ ∖ B q}(φ))`. -/
theorem exists_ae_condExpKernel_kernel
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
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
      ∀ᵐ ω₀ ∂P, ∀ p : ℕ × ℕ, ∀ φ : TestOn upperHalfPlaneOpens,
        (condExpKernel P (jointPast κ b J E) ω₀)[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) |
          (𝓜 (LawUnique.dyadicTime p)).1] =ᵐ[condExpKernel P (jointPast κ b J E) ω₀]
          fun ω => rangeKerCF (M (LawUnique.dyadicTime p) ω) (H \ B (LawUnique.dyadicTime p) ω) φ := by
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
  -- the transfer, at dyadic times and rational combinations
  have hν : ∀ᵐ ω₀ ∂P, ∀ (p : ℕ × ℕ) (k : Restart.RatComb),
      (condExpKernel P (jointPast κ b J E) ω₀)[fun ω => Complex.exp
        (Complex.I * (h ω (Restart.ratComb upperHalfPlaneOpens k) : ℂ)) | 𝓜₀ (LawUnique.dyadicTime p)]
        =ᵐ[condExpKernel P (jointPast κ b J E) ω₀]
          fun ω => rangeKerCF (M (LawUnique.dyadicTime p) ω) (H \ B (LawUnique.dyadicTime p) ω)
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
