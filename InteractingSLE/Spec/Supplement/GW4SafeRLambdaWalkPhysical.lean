/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaWalk
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaPhysical
import InteractingSLE.Spec.Supplement.KernelTower2

/-! # GW4: the walk union is local and determined by the physical field -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField WalkLaw Sec7.SideC12

/-- The original centered field is a measurable affine function of its
actual physical source transport. No background-identification premise is
required for transporting field determination. -/
theorem comap_centred_le_aeSigma_physical {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) (u₀ u₁ : ℂ → ℝ) :
    MeasurableSpace.comap (centredField h u₀) inferInstance ≤
      aeSigma (MeasurableSpace.comap (centredField h'' u₁) inferInstance) P := by
  let T : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens (sourceShift a k c) -
    smoothDist upperHalfPlaneOpens u₁
  let S := -WangWu.reflectField T - smoothDist upperHalfPlaneOpens u₀
  apply KernelTower.comap_le_aeSigma_comap
    ((WholeField.measurable_add_dist S).comp WangWu.measurable_reflectField)
  apply Eventually.of_forall
  intro ω
  change h ω - smoothDist upperHalfPlaneOpens u₀ = WangWu.reflectField
    (h'' ω - smoothDist upperHalfPlaneOpens u₁) + S
  rw [field_eq_reflect_add (hT ω) (hTr ω)]
  have he : WangWu.reflectField (h ω) + smoothDist upperHalfPlaneOpens (sourceShift a k c) -
      smoothDist upperHalfPlaneOpens u₁ = WangWu.reflectField (h ω) + T := by dsimp only [T]; abel
  rw [he, WangWu.reflectField_add, WangWu.reflectField_reflectField]
  dsimp only [S]
  abel

/-- The actual original walk local set, read in the counterflow physical
chart, has a closed measurable version local for and determined by the
centered physical field. Theorems 1.2--1.3 provide the original walk laws. -/
theorem exists_physical_walk_union_version
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    {u₀ u₁ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    (hh₁ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h'' u₁) P)
    {D : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hD : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (D spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (D spec)) :
    ∃ E : Ω → Set ℂ, (∀ ω, E ω ⊆ H ∧ IsOpen (H \ E ω)) ∧
      Measurable[mΩ, hittingSigma] E ∧
      E =ᵐ[P] (fun ω => WangWu.negInv '' walkUnionSet κ b J D ω) ∧
      MeasurableSpace.comap E hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h'' u₁) inferInstance) P ∧
      IsLocalSet E (centredField h'' u₁) P := by
  obtain ⟨A, hAc, hAm, hAeq, hAdet, hAl⟩ :=
    exists_closed_walk_union_version h12 h13 hκ hκ4 hb hh hD hreg hu₀
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hAm hAl
  have hPhys := localSetMean_physicalMean hAc hT hTr hu₀.1 hu₁ hg
  have hEc : ∀ ω, WangWu.negInv '' A ω ⊆ H ∧ IsOpen (H \ WangWu.negInv '' A ω) :=
    fun ω => WangWu.image_negInv_relClosed (hAc ω)
  have hEm : Measurable[mΩ, hittingSigma] (fun ω => WangWu.negInv '' A ω) :=
    WangWu.measurable_image_negInv.comp hAm
  have hEd : MeasurableSpace.comap (fun ω => WangWu.negInv '' A ω) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h'' u₁) inferInstance) P := by
    have hImage : MeasurableSpace.comap (fun ω => WangWu.negInv '' A ω) hittingSigma ≤
        MeasurableSpace.comap A hittingSigma :=
      (WangWu.measurable_image_negInv.comp (comap_measurable A)).comap_le
    exact hImage.trans (hAdet.trans (Supp8.Q3Chain.aeSigma_le_of_le
      (comap_centred_le_aeSigma_physical hT hTr u₀ u₁)))
  refine ⟨fun ω => WangWu.negInv '' A ω, hEc, hEm,
    hAeq.mono (fun ω he => congrArg (fun S => WangWu.negInv '' S) he), hEd, ?_⟩
  apply ((isLocalSet_tfae hh₁ hEm (Eventually.of_forall hEc)).out 3 4).1
  exact ⟨_, hPhys⟩

end InteractingSLE.Theorem14.GW4Fix
