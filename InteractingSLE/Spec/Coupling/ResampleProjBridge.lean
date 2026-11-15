import InteractingSLE.Spec.Coupling.ResampleProjFamily
import InteractingSLE.Spec.Coupling.Assembly11BProvider

/-!
# Theorem 1.1: the finite-family step with projection independence is a theorem

Packet PROVE-T11-PROJ. PROVE-T11-LOC's named input `FiniteFamilyProjStatement` (Astra §1, (1.9)–(1.10)) holds for
every `κ > 0` (`finiteFamilyProjStatement`): the field law is `fieldLaw0 u₀`, and for every finite subfamily the
coupling `P ⊗ η` of `exists_finiteFamilyKernelProj` is sampled and projection-independent at every member.

With it, PROVE-T11-LOC's provider `exists_isOptionalHullCoupling_of_finiteFamilyProj` needs only the conclusion of the
frozen Theorem 2.2 (`exists_isOptionalHullCoupling_of_thm22`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace Coupling

open LQGMetric GFF Ito LocalSets

/-- Set integrals over `A × 𝒟'` of the coupling `P ⊗ η` are integrals against the integrated law. -/
theorem setIntegral_fst_preimage_eq_integral_secMeas {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace X] {P : Measure Ω} [IsFiniteMeasure P] {η : Kernel Ω X} [IsMarkovKernel η]
    {A : Set Ω} (hA : MeasurableSet A) {F : X → ℂ} (hF : Measurable F) (hb : ∀ x, ‖F x‖ ≤ 1) :
    ∫ p in Prod.fst ⁻¹' A, F p.2 ∂(P ⊗ₘ η) = ∫ x, F x ∂secMeas P A η := by
  rw [integral_secMeas hF hb, show (Prod.fst ⁻¹' A : Set (Ω × X)) = A ×ˢ univ by ext; simp,
    Measure.setIntegral_compProd hA MeasurableSet.univ]
  · simp only [Measure.restrict_univ]
  · exact (Integrable.of_bound (hF.comp measurable_snd).aestronglyMeasurable 1
      (Eventually.of_forall fun p => hb p.2)).integrableOn

/-- **The finite-family step with projection independence** (Astra pp. 5–6, (1.9)–(1.10)): PROVE-T11-LOC's named
input `FiniteFamilyProjStatement` holds for every `κ > 0`. -/
theorem finiteFamilyProjStatement {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : FiniteFamilyProjStatement.{u} κ xL xR ρL ρR := by
  classical
  intro Ω₀ mΩ₀ P hP 𝓕 W VL VR B ζ hE u hu ι _ U K hUo hK s hs hsK
  have hUH : ∀ i, U i ⊆ H := fun i => (hK i).2.2.trans (hK i).2.1
  have hsU : ∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)) := fun i =>
    (hsK i).mono fun ω h => ⟨h.1, h.2.mono_left (hK i).2.2⟩
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
    have hcoupling : ∀ η : Kernel Ω₀ (DistOn upperHalfPlaneOpens), IsMarkovKernel η →
        (∀ S, MeasurableSet S → ∫⁻ ω, η ω S ∂P = fieldLaw0 u₀ S) →
        IsProbabilityMeasure (P ⊗ₘ η) ∧ (P ⊗ₘ η).map Prod.fst = P ∧
          (P ⊗ₘ η).map Prod.snd = fieldLaw0 u₀ := by
      intro η hη hmarg
      refine ⟨inferInstance, Measure.fst_compProd P η, Measure.ext fun S hS => ?_⟩
      rw [Measure.map_apply measurable_snd hS, show (Prod.snd ⁻¹' S : Set (Ω₀ × _)) = univ ×ˢ S by
        ext; simp, Measure.compProd_apply_prod MeasurableSet.univ hS, Measure.restrict_univ, hmarg S hS]
    have hsampled : ∀ (η : Kernel Ω₀ (DistOn upperHalfPlaneOpens)), IsMarkovKernel η → ∀ i,
        (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U i → ∀ A,
          MeasurableSet[(hs i).measurableSpace] A →
            ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω) ∂P =
              ∫ ω in A, cfAt κ W u ψ 1 (s i) ω ∂P) →
        IsSampledCoupling κ W u P (U i) (hs i) (P ⊗ₘ η) := by
      intro η hη i h ψ hψ A hA
      have hA' : MeasurableSet A := (hs i).measurableSpace_le A hA
      have hmeas : Measurable fun g : DistOn upperHalfPlaneOpens =>
          Complex.exp (Complex.I * (g ψ : ℂ)) := measurable_exp_I_mul (measurable_distOn_apply ψ)
      rw [show (Prod.fst ⁻¹' A : Set (Ω₀ × DistOn upperHalfPlaneOpens)) = A ×ˢ univ by ext; simp,
        Measure.setIntegral_compProd hA' MeasurableSet.univ]
      · simp only [Measure.restrict_univ]
        exact h ψ hψ A hA
      · exact (Integrable.of_bound (hmeas.comp measurable_snd).aestronglyMeasurable 1
          (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)).integrableOn
    have hprojc : ∀ (η : Kernel Ω₀ (DistOn upperHalfPlaneOpens)), IsMarkovKernel η → ∀ i,
        (∀ A, MeasurableSet[(hs i).measurableSpace] A →
          IsProjIndepMeasure ⟨U i, hUo i⟩ (secMeas P A η)) →
        IsProjIndepCoupling ⟨U i, hUo i⟩ (hs i) (P ⊗ₘ η) := by
      intro η hη i h f Ξ A hA
      have hA' : MeasurableSet A := (hs i).measurableSpace_le A hA
      have hb : ∀ (Ψ : TestOn upperHalfPlaneOpens) (x : DistOn upperHalfPlaneOpens),
          ‖Complex.exp (Complex.I * (x Ψ : ℂ))‖ ≤ 1 := fun Ψ x => (Complex.norm_exp_I_mul_ofReal _).le
      rw [setIntegral_fst_preimage_eq_integral_secMeas hA'
          (measurable_exp_I_mul (measurable_distOn_apply _)) (hb _),
        setIntegral_fst_preimage_eq_integral_secMeas hA'
          (measurable_exp_I_mul (measurable_distOn_apply _)) (hb _)]
      exact h A hA f Ξ
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · set η : Kernel Ω₀ (DistOn upperHalfPlaneOpens) := Kernel.const Ω₀ (fieldLaw0 u₀)
      obtain ⟨h1, h2, h3⟩ := hcoupling η inferInstance fun S _ => by
        simp [η, Kernel.const_apply, lintegral_const, measure_univ]
      exact ⟨P ⊗ₘ η, h1, h2, h3, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · have : Nonempty F := hFne.coe_sort
      obtain ⟨η, hηM, hmarg, hpair, hproj⟩ := exists_finiteFamilyKernelProj hE hκ u hu hu₀
        (ι := F) (fun j => ⟨U j, hUo j⟩) (fun j => hUH j) (fun j => s j) (fun j => hs j)
        (fun j => hsU j)
      obtain ⟨h1, h2, h3⟩ := hcoupling η hηM hmarg
      exact ⟨P ⊗ₘ η, h1, h2, h3, fun i hi =>
        ⟨hsampled η hηM i (hpair ⟨i, hi⟩), hprojc η hηM i (hproj ⟨i, hi⟩)⟩⟩

/-- **Theorem 1.1 from the conclusion of the frozen Theorem 2.2 alone** (conditional helper; its only hypothesis is
exactly the conclusion of the frozen `exists_isIntegratedSLEEvolution`). PROVE-T11-LOC's provider with its second
input discharged by `finiteFamilyProjStatement`. -/
theorem exists_isOptionalHullCoupling_of_thm22 {κ : ℝ} (hκ : 0 < κ := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption)
    (hI1 : ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h :=
  exists_isOptionalHullCoupling_of_finiteFamilyProj hκ hF hI1 (finiteFamilyProjStatement hκ xL xR ρL ρR)

end Coupling

end InteractingSLE
