import InteractingSLE.Spec.Coupling.ResampleFamily
import InteractingSLE.Spec.Coupling.CompactFamily
import InteractingSLE.Spec.Ito.Mean

/-!
# The finite-family step in the form of the compactness step (Theorem 1.1, obligation 3)

Packet PROVE-T11-KER. `exists_finiteFamilyKernel` restated for PROVE-T11-ASM's compactness step
(`exists_isSampledCoupling_of_finite`, `Assembly11Provider.FiniteFamilyStatement`): for an integrated evolution,
a countable family of **open** regions `U i ⊆ ℍ` and stops `s i < ζ` with `U i ∩ K_{s i} = ∅`, the field law
`α = fieldLaw0 u₀` (a zero-boundary GFF plus the time-zero harmonic mean, for every bounded harmonic extension `u₀`
of the time-zero data) and, for every finite subfamily, a coupling `P ⊗ η` of the driving law and `α` sampled at all
its members (`IsSampledCoupling`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open LQGMetric GFF Ito

/-- Under `fieldLaw0 u₀`, the centred field `x ↦ x − u₀` is a zero-boundary GFF on `ℍ`. -/
theorem isZBGFFProcess_fieldLaw0 {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) :
    IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z) (fieldLaw0 u₀) := by
  have hZ := isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl
  set c : DistOn upperHalfPlaneOpens := Distribution.ofFun upperHalfPlaneOpens u₀ volume ⊤ with hc
  have hcφ : ∀ φ : TestOn upperHalfPlaneOpens, c φ = ∫ z, u₀ z * φ z := fun φ => by
    rw [hc, Distribution.ofFun_apply (hu₀.locallyIntegrableOn upperHalfPlaneOpens.isOpen.measurableSet)]
    simp only [smul_eq_mul, mul_comm (φ _)]
  set F : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens :=
    fun g => restrictDist upperHalfPlaneOpens g + c with hF
  have hFm : Measurable F := measurable_add_const_restrictDist upperHalfPlaneOpens c
  have hcomp : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun x : DistOn upperHalfPlaneOpens => x φ - ∫ z, u₀ z * φ z) ∘ F = fun g => g φ := by
    intro φ
    funext g
    show (restrictDist upperHalfPlaneOpens g + c) φ - ∫ z, u₀ z * φ z = g φ
    rw [show (restrictDist upperHalfPlaneOpens g + c) φ = restrictDist upperHalfPlaneOpens g φ + c φ
      from rfl, restrictDist_apply, hcφ, add_sub_cancel_right]
    congr 1
    ext z
    rw [coe_testIncl le_rfl]
  have hlaw : fieldLaw0 u₀ = (zbLaw upperHalfPlaneOpens).map F := rfl
  have hXm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun x : DistOn upperHalfPlaneOpens => x φ - ∫ z, u₀ z * φ z := fun φ =>
    (measurable_distOn_apply φ).sub_const _
  refine
    { measurable := hXm
      gaussian := ⟨fun I => ?_⟩
      centered := fun φ => ?_
      covariance_eq := fun φ ψ => ?_ }
  · have hm : Measurable fun x : DistOn upperHalfPlaneOpens =>
        I.restrict fun φ => x φ - ∫ z, u₀ z * φ z := measurable_pi_iff.2 fun φ => hXm φ.1
    refine ⟨hm.aemeasurable, ?_⟩
    rw [hlaw, Measure.map_map hm hFm]
    have : ((fun x : DistOn upperHalfPlaneOpens => I.restrict fun φ => x φ - ∫ z, u₀ z * φ z) ∘ F) =
        fun g => I.restrict fun φ => (id g : DistOn upperHalfPlaneOpens) φ := by
      funext g
      funext φ
      exact congrFun (hcomp φ.1) g
    rw [this]
    exact (hZ.process.gaussian.hasGaussianLaw I).isGaussian_map
  · rw [hlaw, integral_map hFm.aemeasurable (hXm φ).aestronglyMeasurable, ← hZ.process.centered φ]
    exact congrArg (fun f => ∫ g, f g ∂zbLaw upperHalfPlaneOpens) (hcomp φ)
  · rw [hlaw, covariance_map (hXm φ).aestronglyMeasurable (hXm ψ).aestronglyMeasurable
      hFm.aemeasurable, hcomp φ, hcomp ψ]
    exact hZ.process.covariance_eq φ ψ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The finite-family step for the compactness step** (Astra pp. 5–6; the conclusion of
`Assembly11Provider.FiniteFamilyStatement` for open regions). -/
theorem exists_fieldLaw_finiteFamily (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {ι : Type*} (U : ι → Set ℂ) (hUo : ∀ i, IsOpen (U i)) (hUH : ∀ i, U i ⊆ H)
    (s : ι → Ω → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0))
    (hsU : ∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) :
    ∃ α : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure α ∧
      (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
          (forceJumpSet xL xR) u₀ →
        IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z) α) ∧
      ∀ F : Finset ι, ∃ μ : Measure (Ω × DistOn upperHalfPlaneOpens),
        IsProbabilityMeasure μ ∧ μ.map Prod.fst = P ∧ μ.map Prod.snd = α ∧
          ∀ i ∈ F, IsSampledCoupling κ W u P (U i) (hs i) μ := by
  classical
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  -- a bounded harmonic extension of the time-zero data
  obtain ⟨ω₀, hp⟩ := (hE.2.2.2.2).exists
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR)
      (u ω₀ 0) := by
    have h := hu ω₀ 0
    have hL : (fun i => VL i 0 ω₀ - W 0 ω₀) = xL := by
      funext i
      have h1 : VL i 0 ω₀ = xL i := hp.2.1 i
      have h2 : W 0 ω₀ = 0 := hp.1
      rw [h1, h2, sub_zero]
    have hR : (fun i => VR i 0 ω₀ - W 0 ω₀) = xR := by
      funext i
      have h1 : VR i 0 ω₀ = xR i := hp.2.2.1 i
      have h2 : W 0 ω₀ = 0 := hp.1
      rw [h1, h2, sub_zero]
    rwa [hL, hR] at h
  set u₀ := u ω₀ 0 with hu₀def
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  refine ⟨fieldLaw0 u₀, inferInstance, fun u₀' hu₀' => ?_, fun F => ?_⟩
  · have heq : EqOn u₀' u₀ H := Impl.eqOn_of_isBoundedHarmonicExtension
      (Impl.forceJumpSet_finite (weightWord ρL ρR) xL xR) hu₀ hu₀'
    have hint : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, u₀' z * φ z = ∫ z, u₀ z * φ z := fun φ => by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ H
      · simp only [heq hz]
      · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)
        simp [this]
    simp_rw [hint]
    exact isZBGFFProcess_fieldLaw0 hu₀c
  · -- the coupling `P ⊗ η` from a kernel `η`
    have hcoupling : ∀ η : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η →
        (∀ S, MeasurableSet S → ∫⁻ ω, η ω S ∂P = fieldLaw0 u₀ S) →
        IsProbabilityMeasure (P ⊗ₘ η) ∧ (P ⊗ₘ η).map Prod.fst = P ∧
          (P ⊗ₘ η).map Prod.snd = fieldLaw0 u₀ := by
      intro η hη hmarg
      refine ⟨inferInstance, Measure.fst_compProd P η, Measure.ext fun S hS => ?_⟩
      rw [Measure.map_apply measurable_snd hS, show (Prod.snd ⁻¹' S : Set (Ω × _)) = univ ×ˢ S by
        ext; simp, Measure.compProd_apply_prod MeasurableSet.univ hS, Measure.restrict_univ, hmarg S hS]
    have hsampled : ∀ (η : Kernel Ω (DistOn upperHalfPlaneOpens)), IsMarkovKernel η → ∀ i,
        (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U i → ∀ A,
          MeasurableSet[(hs i).measurableSpace] A →
            ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω) ∂P =
              ∫ ω in A, cfAt κ W u ψ 1 (s i) ω ∂P) →
        IsSampledCoupling κ W u P (U i) (hs i) (P ⊗ₘ η) := by
      intro η hη i h ψ hψ A hA
      have hA' : MeasurableSet A := (hs i).measurableSpace_le A hA
      have hmeas : Measurable fun g : DistOn upperHalfPlaneOpens =>
          Complex.exp (Complex.I * (g ψ : ℂ)) := measurable_exp_I_mul (measurable_distOn_apply ψ)
      rw [show (Prod.fst ⁻¹' A : Set (Ω × DistOn upperHalfPlaneOpens)) = A ×ˢ univ by ext; simp,
        Measure.setIntegral_compProd hA' MeasurableSet.univ]
      · simp only [Measure.restrict_univ]
        exact h ψ hψ A hA
      · exact (Integrable.of_bound (hmeas.comp measurable_snd).aestronglyMeasurable 1
          (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)).integrableOn
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · set η : Kernel Ω (DistOn upperHalfPlaneOpens) := Kernel.const Ω (fieldLaw0 u₀)
      obtain ⟨h1, h2, h3⟩ := hcoupling η inferInstance fun S _ => by
        simp [η, Kernel.const_apply, lintegral_const, measure_univ]
      exact ⟨P ⊗ₘ η, h1, h2, h3, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · have : Nonempty F := hFne.coe_sort
      obtain ⟨η, hηM, hmarg, hpair⟩ := exists_finiteFamilyKernel hE hκ u hu hu₀
        (ι := F) (fun j => ⟨U j, hUo j⟩) (fun j => hUH j) (fun j => s j) (fun j => hs j)
        (fun j => hsU j)
      obtain ⟨h1, h2, h3⟩ := hcoupling η hηM hmarg
      exact ⟨P ⊗ₘ η, h1, h2, h3, fun i hi => hsampled η hηM i (hpair ⟨i, hi⟩)⟩

end Coupling

end InteractingSLE
