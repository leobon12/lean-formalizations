import SupercriticalConformalCovariance.Reversal.Field
import SupercriticalConformalCovariance.Domain.Axioms
import LQGMetric.Papers.DFGPS.L2_17Core2H

/-!
# Field-level algebra for the assembly of Theorem 1.1

* `restrictTo_addFun`: `(k + F)|_U = k|_U + F|_U`;
* `confPullbackField_add`, `precomp_ofFun_extZ`: the conformal pullback of a field plus a continuous
  correction `G` on `U` is the pullback of the field plus `G ∘ ψ` (paper l. 529–530: "Under the
  conformal map, the same correction is composed with the inverse map");
* `isDomainRealization_congr`, `isDomainRealization_comp`: realizations are stable under a.s.
  equality of the field and under measure-preserving extensions of the probability space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function TopologicalSpace
open scoped ENNReal Distributions

namespace SupercriticalConformalCovariance.Root

open LQGMetric (DistC DistOn TestOn restrictTo addFun ofCont IsGFFPlusCont IsWholePlaneGFF)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest confPullbackField
  IsDomainRealization)
open SmallGammaGeodesics.CC (confPullFun differentiableOn_leftInv injOn_leftInv
  image_leftInv_image apply_leftInv integral_confPullFun_mul)

/-! ## Restriction of `k + F` -/

theorem restrictTo_addFun (U : Opens ℂ) (k : DistC) (F : C(ℂ, ℝ)) :
    restrictTo U (addFun k F) = restrictTo U k +
      Distribution.ofFun U (Function.extend Subtype.val
        (F.restrict (U : Set ℂ)) 0) volume ⊤ := by
  have hloc : LocallyIntegrableOn (Function.extend Subtype.val (F.restrict (U : Set ℂ)) 0)
      (U : Set ℂ) volume :=
    (SupercriticalConformalCovariance.Domain.continuousOn_extZ (F.restrict (U : Set ℂ))).locallyIntegrableOn
      U.isOpen.measurableSet
  ext φ
  rw [add_apply]
  change (k + ofCont F) _ = _
  rw [add_apply, Distribution.ofFun_apply hloc, LQGMetric.ofCont_apply]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.coe_coe]
  rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top, smul_eq_mul]
  by_cases hx : φ x = 0
  · simp [hx]
  · have hxU : x ∈ (U : Set ℂ) := φ.tsupport_subset (subset_tsupport _ hx)
    have e := SupercriticalConformalCovariance.Domain.extZ_of_mem (F.restrict (U : Set ℂ)) hxU
    unfold SupercriticalConformalCovariance.Domain.extZ at e
    rw [e]
    rfl

/-! ## The conformal pullback of a continuous correction -/

/-- `ψ : V → U` as a continuous map of the subtypes. -/
def mapsToCM {ψ : ℂ → ℂ} {V U : Opens ℂ} (hψ : IsConformalBijection ψ V U) : C(V, U) :=
  ⟨fun y => ⟨ψ y, hψ.2.mapsTo y.2⟩,
    (hψ.1.continuousOn.comp_continuous continuous_subtype_val fun y => y.2).subtype_mk _⟩

theorem confPullbackField_add (Q : ℝ) {ψ : ℂ → ℂ} {V U : Opens ℂ}
    (hψ : IsConformalBijection ψ V U) (x y : DistOn U) :
    confPullbackField Q hψ (x + y) =
      confPullbackField Q hψ x + (confPushTest hψ).precompCompactConvergenceCLM ℝ y := by
  unfold confPullbackField
  rw [map_add]
  abel

/-- **Change of variables for the correction.** For `G ∈ C(U)`,
`⟨G, 1_U |(ψ⁻¹)′|² (χ ∘ ψ⁻¹)⟩ = ⟨G ∘ ψ, χ⟩` for `χ ∈ 𝓓(V)`. -/
theorem precomp_ofFun_extZ {ψ : ℂ → ℂ} {V U : Opens ℂ} (hψ : IsConformalBijection ψ V U)
    (G : C(U, ℝ)) :
    (confPushTest hψ).precompCompactConvergenceCLM ℝ
        (Distribution.ofFun U (Function.extend Subtype.val G 0) volume ⊤) =
      Distribution.ofFun V (Function.extend Subtype.val (G.comp (mapsToCM hψ)) 0) volume ⊤ := by
  have hψφ : ∀ z ∈ (V : Set ℂ), invFunOn ψ V (ψ z) = z := fun _ hz =>
    hψ.2.injOn.leftInvOn_invFunOn hz
  have hd : DifferentiableOn ℂ (invFunOn ψ V) U := by
    have h := differentiableOn_leftInv V.isOpen hψ.1 hψ.2.injOn hψφ
    rwa [hψ.2.image_eq] at h
  have hi : InjOn (invFunOn ψ V) U := by
    have h := injOn_leftInv hψφ
    rwa [hψ.2.image_eq] at h
  have hφψ : ∀ y ∈ (U : Set ℂ), ψ (invFunOn ψ V y) = y := fun _ hy =>
    apply_leftInv hψφ (hψ.2.image_eq.symm ▸ hy)
  have himg : invFunOn ψ V '' (U : Set ℂ) = V := by
    rw [← hψ.2.image_eq, image_leftInv_image hψφ subset_rfl]
  have hlocU : LocallyIntegrableOn (Function.extend Subtype.val G 0) (U : Set ℂ) volume :=
    (SupercriticalConformalCovariance.Domain.continuousOn_extZ G).locallyIntegrableOn U.isOpen.measurableSet
  have hlocV : LocallyIntegrableOn (Function.extend Subtype.val (G.comp (mapsToCM hψ)) 0)
      (V : Set ℂ) volume :=
    (SupercriticalConformalCovariance.Domain.continuousOn_extZ (G.comp (mapsToCM hψ))).locallyIntegrableOn
      V.isOpen.measurableSet
  ext χ
  change Distribution.ofFun U (Function.extend Subtype.val G 0) volume ⊤ (confPushTest hψ χ) = _
  rw [Distribution.ofFun_apply hlocU, Distribution.ofFun_apply hlocV]
  simp only [smul_eq_mul]
  have hzero : ∀ y ∉ invFunOn ψ V '' (U : Set ℂ), (χ : ℂ → ℝ) y = 0 := by
    intro y hy
    rw [himg] at hy
    exact χ.zero_on_compl hy
  have hcv := integral_confPullFun_mul U.isOpen hd hi hφψ hzero
    (Function.extend Subtype.val G 0)
  have hpush : ((confPushTest hψ χ : TestOn U) : ℂ → ℝ) = confPullFun (invFunOn ψ V) U χ := rfl
  rw [hpush, hcv]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  by_cases hy : y ∈ (V : Set ℂ)
  · have e1 := SupercriticalConformalCovariance.Domain.extZ_of_mem G (hψ.2.mapsTo hy)
    have e2 := SupercriticalConformalCovariance.Domain.extZ_of_mem (G.comp (mapsToCM hψ)) hy
    unfold SupercriticalConformalCovariance.Domain.extZ at e1 e2
    erw [e1, e2]
    rfl
  · have h0 : (χ : ℂ → ℝ) y = 0 := by simpa using χ.zero_on_compl hy
    rw [h0, zero_mul, zero_mul]

/-! ## Realizations -/

theorem isDomainRealization_congr {V : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h h' : Ω → DistOn V} {h₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f) (hm : Measurable h') (he : ∀ᵐ ω ∂P, h' ω = h ω) :
    IsDomainRealization V P h' h₀ f := by
  refine ⟨hm, hR.2.1, hR.2.2.1, ?_⟩
  filter_upwards [he, hR.2.2.2] with ω h1 h2
  rw [h1, h2]

theorem isWholePlaneGFF_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsWholePlaneGFF (h ∘ π) P' :=
  LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq (hh.measurable.comp hπ.measurable) hh
    (by rw [← Measure.map_map hh.measurable hπ.measurable, hπ.map_eq])

theorem isGFFPlusCont_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    {h : Ω → DistC} (hh : IsGFFPlusCont h P) : IsGFFPlusCont (h ∘ π) P' := by
  obtain ⟨hm, F, hF, hg⟩ := hh
  exact ⟨hm.comp hπ.measurable, F ∘ π, hF.comp hπ.measurable, isWholePlaneGFF_comp hπ hg⟩

/-- A realization survives a measure-preserving extension of the probability space. -/
theorem isDomainRealization_comp {V : Opens ℂ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω}
    (hπ : MeasurePreserving π P' P) {h : Ω → DistOn V} {h₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f) :
    IsDomainRealization V P' (h ∘ π) (h₀ ∘ π) (f ∘ π) :=
  ⟨hR.1.comp hπ.measurable, isGFFPlusCont_comp hπ hR.2.1, hR.2.2.1.comp hπ.measurable,
    hπ.quasiMeasurePreserving.ae hR.2.2.2⟩

theorem measurable_confPullbackField (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) :
    Measurable (confPullbackField Q hφ) := by
  apply LQGMetric.measurable_distOn_iff.mpr
  intro ψ
  exact (LQGMetric.measurable_distOn_apply (confPushTest hφ ψ)).add_const _

theorem isProbabilityMeasure_of_measurePreserving {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
    {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) : IsProbabilityMeasure P' := by
  constructor
  have h := hπ.measure_preimage (s := univ) MeasurableSet.univ.nullMeasurableSet
  rw [preimage_univ] at h
  rw [h, measure_univ]

end SupercriticalConformalCovariance.Root
