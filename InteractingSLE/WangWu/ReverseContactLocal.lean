/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418RangeMain
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.WangWu.UnboundedComponent
import SupercriticalConformalCovariance.ZBConformal.Covariance

/-!
# Local sets under the reflection `R(z) = −1/z` and along equal laws

Packet PROVE-WW-B11. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1604–1611): "Conditionally on `h`, sample a forward line `α` and a reverse line `β`
independently. … the independent-union lemma makes the two stopped slits a local set." The reverse line is the
forward line of the reflected coupling read through `R`; this file supplies the two lemmas that PROVE-WW-B10 found
missing for that step (its obstruction (S2) (a), (b)):

* `IsLocalSet.reflect`: **conformal covariance of local sets under `R`.** If `A` is a local set of `h`, then `R(A)` is
  a local set of the reflected field `−h ∘ R` (`reflectField`). The ingredients are the measurability of `S ↦ R(S)`
  for the hitting σ-algebra (`measurable_image_negInv`), the transport of harmonic representatives
  (`isHarmonicDistOn_reflectField`), and the conformal invariance of the zero-boundary covariance on a subdomain
  (`zeroGFFTestCov_image_negInv`: `Cov_{R(U)}(φ, φ) = Cov_U(φ', φ')` with `φ' = |R'|² φ ∘ R`), which gives the
  conditional GFF on the reflected random domain (`isCondZeroBoundaryGFF_reflect`).
* `IsLocalSet.of_map_eq`: **local sets transfer along equal laws** of `(A, h)`, given the almost sure clause
  `A ⊆ ℍ`, `ℍ \ A` open on the new space (the clause is not an event of the hitting σ-algebra).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

universe u

/-! ### The image of a set under `R` -/

section Image

/-- `R(S) ∩ U ≠ ∅` iff `S ∩ R(U) ≠ ∅` (`R` is an involution). -/
theorem image_negInv_inter_nonempty_iff (S U : Set ℂ) :
    (negInv '' S ∩ U).Nonempty ↔ (S ∩ negInv '' U).Nonempty := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
    exact ⟨z, hz, negInv z, hzU, negInv_negInv z⟩
  · rintro ⟨z, hz, w, hw, rfl⟩
    exact ⟨w, ⟨negInv w, hz, negInv_negInv w⟩, hw⟩

/-- **`S ↦ R(S)` is measurable for the hitting σ-algebra.** -/
theorem measurable_image_negInv :
    Measurable[hittingSigma, hittingSigma] fun S : Set ℂ => negInv '' S := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ (fun S : Set ℂ => negInv '' S) ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : (fun S : Set ℂ => negInv '' S) ⁻¹' {A | (A ∩ U).Nonempty} =
      {A | (A ∩ negInv '' U).Nonempty} := by
    ext S
    exact image_negInv_inter_nonempty_iff S U
  rw [e]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨negInv '' U, isOpen_image_negInv hUo hUH, image_negInv_subset_H hUH, rfl⟩

theorem image_negInv_image_negInv' (S : Set ℂ) : negInv '' (negInv '' S) = S :=
  image_negInv_image_negInv S

/-- `ℍ \ R(S) = R(ℍ \ S)`. -/
theorem H_diff_image_negInv (S : Set ℂ) : H \ negInv '' S = negInv '' (H \ S) := by
  ext z
  constructor
  · rintro ⟨hzH, hzS⟩
    refine ⟨negInv z, ⟨negInv_mem_H hzH, fun h => hzS ⟨negInv z, h, negInv_negInv z⟩⟩, negInv_negInv z⟩
  · rintro ⟨w, ⟨hwH, hwS⟩, rfl⟩
    refine ⟨negInv_mem_H hwH, ?_⟩
    rintro ⟨v, hv, e⟩
    have : v = w := by
      have := congrArg negInv e
      rwa [negInv_negInv, negInv_negInv] at this
    exact hwS (this ▸ hv)

/-- The almost sure clause of a local set is preserved by `R`. -/
theorem image_negInv_relClosed {S : Set ℂ} (hS : S ⊆ H ∧ IsOpen (H \ S)) :
    negInv '' S ⊆ H ∧ IsOpen (H \ negInv '' S) := by
  refine ⟨image_negInv_subset_H hS.1, ?_⟩
  rw [H_diff_image_negInv]
  exact isOpen_image_negInv hS.2 sdiff_subset

/-- The comap of an involutive measurable self-map is the σ-algebra itself. -/
theorem comap_eq_of_involutive {α : Type*} {m : MeasurableSpace α} {f : α → α}
    (hf : Measurable[m, m] f) (hinv : Function.Involutive f) : m.comap f = m := by
  refine le_antisymm hf.comap_le ?_
  calc m = m.comap (f ∘ f) := by rw [hinv.comp_self, MeasurableSpace.comap_id]
    _ = (m.comap f).comap f := (MeasurableSpace.comap_comp).symm
    _ ≤ m.comap f := MeasurableSpace.comap_mono hf.comap_le

theorem negInvImage_involutive : Function.Involutive fun S : Set ℂ => negInv '' S :=
  image_negInv_image_negInv

theorem reflectField_involutive : Function.Involutive reflectField := reflectField_reflectField

end Image

/-! ### The zero-boundary covariance under `R` on a subdomain -/

section Covariance

open QuantumZipper (zeroGFFTestCov testMeasPos testMeasNeg dualCov zeroSpace)

/-- **Covariance transport with pairings tested only against the test space of the target** (the proof of
SupercriticalConformalCovariance's `dualCov_transport`, which only uses the pairings against `zeroSpace V`). -/
theorem dualCov_transport_zeroSpace {φ : ℂ → ℂ} {U V : TopologicalSpace.Opens ℂ}
    (hφ : IsConformalBijection φ U V) {μ₁ μ₂ μ₁' μ₂' : Measure ℂ}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₁'] [IsFiniteMeasure μ₂']
    (hpair₁ : ∀ f ∈ zeroSpace V, ∫ y, f y ∂μ₁' = ∫ y, f y ∂((μ₁.restrict U).map φ))
    (hpair₂ : ∀ f ∈ zeroSpace V, ∫ y, f y ∂μ₂' = ∫ y, f y ∂((μ₂.restrict U).map φ)) :
    dualCov V (zeroSpace V) μ₁' μ₂' = dualCov U (zeroSpace U) μ₁ μ₂ := by
  have hae₁ : AEMeasurable φ (μ₁.restrict U) :=
    ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  have hae₂ : AEMeasurable φ (μ₂.restrict U) :=
    ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  have hpairAdd : ∀ f ∈ zeroSpace V,
      ∫ y, f y ∂(μ₁' + μ₂') = ∫ y, f y ∂(((μ₁ + μ₂).restrict U).map φ) := by
    intro f hf
    have hfint₁' : Integrable f μ₁' := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₂' : Integrable f μ₂' := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₁ : Integrable f ((μ₁.restrict U).map φ) :=
      hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₂ : Integrable f ((μ₂.restrict U).map φ) :=
      hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    rw [Measure.restrict_add, AEMeasurable.map_add₀ hae₁ hae₂,
      integral_add_measure hfint₁' hfint₂', integral_add_measure hfint₁ hfint₂, hpair₁ f hf, hpair₂ f hf]
  unfold dualCov
  rw [SupercriticalConformalCovariance.ZBConformal.dualNormSq_transport hφ hpairAdd,
    SupercriticalConformalCovariance.ZBConformal.dualNormSq_transport hφ hpair₁,
    SupercriticalConformalCovariance.ZBConformal.dualNormSq_transport hφ hpair₂]

/-- The covariance only sees `ψ` through `ψ ↦ −ψ` symmetrically. -/
theorem zeroGFFTestCov_neg_neg (U : Set ℂ) (ψ : ℂ → ℝ) :
    zeroGFFTestCov U (-ψ) (-ψ) = zeroGFFTestCov U ψ ψ := by
  have h1 : testMeasPos (-ψ) = testMeasNeg ψ := rfl
  have h2 : testMeasNeg (-ψ) = testMeasPos ψ := by
    simp only [testMeasNeg, testMeasPos, Pi.neg_apply, neg_neg]
  have hsymm : ∀ μ ν : Measure ℂ, dualCov U (zeroSpace U) μ ν = dualCov U (zeroSpace U) ν μ := by
    intro μ ν
    unfold dualCov
    rw [add_comm μ ν]
    ring
  unfold zeroGFFTestCov
  rw [h1, h2, hsymm (testMeasNeg ψ) (testMeasPos ψ)]
  ring

/-- The return chart's inverse map is `R`. -/
theorem infinityReturnChart_inv_eq (w : ℂ) : Sec7.StripSysField.infinityReturnChart.2.1 w = negInv w := rfl

/-- The transported test function `φ' = |R'|² φ ∘ R` vanishes off `ℍ`. -/
theorem pushTest_return_eq_zero_of_notMem (φ : TestOn upperHalfPlaneOpens) {x : ℂ} (hx : x ∉ H) :
    Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ x = 0 := by
  refine Chart.pushTest_apply_of_notMem _ _ ?_
  rw [← SetLike.mem_coe, Sec7.StripSysField.coe_dom_infinityReturnChart]
  exact hx

/-- The transported test function as SupercriticalConformalCovariance's `confPushTest`. -/
theorem coe_pushTest_return (φ : TestOn upperHalfPlaneOpens) :
    ⇑(Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) =
      ⇑(confPushTest Sec7.StripSysField.isConformal_infinityReturnChart.isConformalBijection φ) :=
  GFF.coe_testIncl Sec7.StripSysField.isConformal_infinityReturnChart.dom_le _

/-- **Positive parts under `R`**: `∫ max(φ', 0) · u = ∫ max(φ, 0) · u ∘ R`. -/
theorem integral_max_pushTest_return (φ : TestOn upperHalfPlaneOpens) (u : ℂ → ℝ) :
    ∫ y, max (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ y) 0 * u y =
      ∫ x, max (φ x) 0 * u (negInv x) := by
  rw [coe_pushTest_return]
  exact SupercriticalConformalCovariance.ZBConformal.integral_max_confPushTest _ φ u

/-- **Pairings of a test function with the reflected subdomain.** For `f` smooth with compact support in `R(U)`,
`∫ f max(±φ, 0) = ∫_U (f ∘ R) max(±φ', 0)`, `φ' = |R'|² φ ∘ R`. -/
theorem integral_testMeas_reflect {U : Set ℂ} (hUo : IsOpen U) (s : ℝ)
    (φ : TestOn upperHalfPlaneOpens) (f : ℂ → ℝ) (hf : f ∈ zeroSpace (negInv '' U)) :
    ∫ y, max (s * φ y) 0 * f y =
      ∫ x in U, max (s * Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ x) 0 *
        f (negInv x) := by
  set ψ := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ
  have hψs : ∀ x, s * ψ x = (s • ψ) x := fun x => rfl
  have hφs : ∀ x, s * φ x = (s • φ) x := fun x => rfl
  have hpush : s • ψ = Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart (s • φ) :=
    (map_smul _ s φ).symm
  simp_rw [hφs, hψs, hpush]
  rw [← integral_indicator hUo.measurableSet]
  have key : ∀ x, U.indicator (fun x => max (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart
      (s • φ) x) 0 * f (negInv x)) x =
      max (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart (s • φ) x) 0 * f (negInv x) := by
    intro x
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
    · rw [indicator_of_notMem hxU]
      by_cases hxH : x ∈ H
      · have hf0 : f (negInv x) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hmem => hxU ?_
          obtain ⟨w, hw, e⟩ := hf.2.2 hmem
          have : w = x := by
            have := congrArg negInv e
            rwa [negInv_negInv, negInv_negInv] at this
          exact this ▸ hw
        rw [hf0, mul_zero]
      · rw [pushTest_return_eq_zero_of_notMem _ hxH, max_self, zero_mul]
  simp_rw [key]
  rw [integral_max_pushTest_return]
  simp_rw [negInv_negInv]

/-- `R` restricted to an open `U ⊆ ℍ` is a conformal bijection onto `R(U)`. -/
theorem isConformalBijection_negInv_restrict {U : Set ℂ} (hU : U ⊆ H) :
    IsConformalBijection negInv U (negInv '' U) :=
  ⟨differentiableOn_negInv.mono hU, negInv_involutive.injective.injOn.bijOn_image⟩

/-- **Conformal invariance of the zero-boundary covariance on a subdomain under `R`**: for `U ⊆ ℍ` open and `φ` a
test function on `ℍ`, `Cov_{R(U)}(φ, φ) = Cov_U(φ', φ')` with `φ' = |R'|² φ ∘ R`. -/
theorem zeroGFFTestCov_image_negInv {U : Set ℂ} (hUo : IsOpen U) (hU : U ⊆ H) (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (negInv '' U) φ φ =
      zeroGFFTestCov U (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ)
        (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) := by
  set ψ := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ
  let U' : TopologicalSpace.Opens ℂ := ⟨U, hUo⟩
  let V' : TopologicalSpace.Opens ℂ := ⟨negInv '' U, isOpen_image_negInv hUo hU⟩
  have hφ : IsConformalBijection negInv U' V' := isConformalBijection_negInv_restrict hU
  have : IsFiniteMeasure (testMeasPos φ) := (QuantumZipper.K3.isGoodMeas_withDensity φ.continuous
    φ.hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg φ) := (QuantumZipper.K3.isGoodMeas_withDensity φ.continuous.neg
    φ.hasCompactSupport.neg).1
  have : IsFiniteMeasure (testMeasPos ψ) := (QuantumZipper.K3.isGoodMeas_withDensity ψ.continuous
    ψ.hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg ψ) := (QuantumZipper.K3.isGoodMeas_withDensity ψ.continuous.neg
    ψ.hasCompactSupport.neg).1
  have hpos : ∀ f ∈ zeroSpace V', ∫ y, f y ∂(testMeasPos φ) =
      ∫ y, f y ∂(((testMeasPos ψ).restrict U').map negInv) := by
    intro f hf
    have hm : AEMeasurable negInv ((testMeasPos ψ).restrict U') :=
      (continuousOn_negInv.mono hU).aemeasurable hUo.measurableSet
    rw [integral_map hm hf.1.continuous.aestronglyMeasurable,
      QuantumZipper.K3.integral_testMeasPos_K3 φ.continuous.measurable]
    have h := integral_testMeas_reflect hUo 1 φ f hf
    simp only [one_mul] at h
    change _ = ∫ x in U, f (negInv x) ∂(testMeasPos ψ)
    rw [h, ← integral_indicator hUo.measurableSet, ← integral_indicator hUo.measurableSet,
      QuantumZipper.K3.integral_testMeasPos_K3 ψ.continuous.measurable]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]; rfl
    · simp only [indicator_of_notMem hx, mul_zero]
  have hneg : ∀ f ∈ zeroSpace V', ∫ y, f y ∂(testMeasNeg φ) =
      ∫ y, f y ∂(((testMeasNeg ψ).restrict U').map negInv) := by
    intro f hf
    have hm : AEMeasurable negInv ((testMeasNeg ψ).restrict U') :=
      (continuousOn_negInv.mono hU).aemeasurable hUo.measurableSet
    rw [integral_map hm hf.1.continuous.aestronglyMeasurable,
      QuantumZipper.K3.integral_testMeasNeg_K3 φ.continuous.measurable]
    have h := integral_testMeas_reflect hUo (-1) φ f hf
    simp only [neg_one_mul] at h
    change _ = ∫ x in U, f (negInv x) ∂(testMeasNeg ψ)
    rw [h, ← integral_indicator hUo.measurableSet, ← integral_indicator hUo.measurableSet,
      QuantumZipper.K3.integral_testMeasNeg_K3 ψ.continuous.measurable]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]; rfl
    · simp only [indicator_of_notMem hx, mul_zero]
  have e1 := dualCov_transport_zeroSpace hφ hpos hpos
  have e2 := dualCov_transport_zeroSpace hφ hpos hneg
  have e3 := dualCov_transport_zeroSpace hφ hneg hpos
  have e4 := dualCov_transport_zeroSpace hφ hneg hneg
  simp only [U', V', TopologicalSpace.Opens.coe_mk] at e1 e2 e3 e4
  unfold zeroGFFTestCov
  rw [e1, e2, e3, e4]

end Covariance

/-! ### Local sets under `R` -/

section Reflect

/-- The support of the transported test function `φ' = |R'|² φ ∘ R` lies in `R(supp φ)`. -/
theorem tsupport_pushTest_return_subset (φ : TestOn upperHalfPlaneOpens) :
    tsupport (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) ⊆ negInv '' tsupport φ := by
  rw [coe_pushTest_return]
  exact tsupport_confPushTest_subset _ φ

/-- `reflectField` is additive. -/
theorem reflectField_add (f g : DistOn upperHalfPlaneOpens) :
    reflectField (f + g) = reflectField f + reflectField g := by
  ext φ
  simp only [reflectField_apply, add_apply, neg_add]

/-- **Harmonic distributions under `R`.** If `T` is harmonic on `U ⊆ ℍ` (open), then `−T ∘ R` is harmonic on
`R(U)`, with representative `−v ∘ R`. -/
theorem isHarmonicDistOn_reflectField {T : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hUo : IsOpen U) (hU : U ⊆ H)
    (hT : IsHarmonicDistOn T U) : IsHarmonicDistOn (reflectField T) (negInv '' U) := by
  obtain ⟨v, hv, hrep⟩ := hT
  refine ⟨-(v ∘ negInv), (harmonicOnNhd_comp_negInv hUo hU hv).neg, fun φ hφ => ?_⟩
  have hsupp : tsupport (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) ⊆ U := by
    refine (tsupport_pushTest_return_subset φ).trans ?_
    calc negInv '' tsupport φ ⊆ negInv '' (negInv '' U) := image_mono hφ
      _ = U := image_negInv_image_negInv U
  rw [reflectField_apply, hrep _ hsupp, Chart.integral_mul_pushTest, ← integral_neg]
  congr 1
  funext w
  simp only [Pi.neg_apply, Function.comp_apply, neg_mul]
  rfl

/-- **The conditional zero-boundary GFF under `R`.** If, given `𝒢`, `X` is a zero-boundary GFF on `ℍ \ A` (with
`A ⊆ ℍ`, `ℍ \ A` open), then `−X ∘ R` is, given `𝒢`, a zero-boundary GFF on `ℍ \ R(A)`. -/
theorem isCondZeroBoundaryGFF_reflect {Ω : Type*} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) X) :
    IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ negInv '' A ω) (fun ω => reflectField (X ω)) := by
  intro φ
  set ψ := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ
  have h := hX (-ψ)
  have e : (fun ω => Complex.exp (Complex.I * ((reflectField (X ω) φ : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((X ω (-ψ) : ℝ) : ℂ)) := by
    funext ω
    rw [reflectField_apply, map_neg]
  rw [e]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  have hc : QuantumZipper.zeroGFFTestCov (H \ A ω) ⇑(-ψ) ⇑(-ψ) =
      QuantumZipper.zeroGFFTestCov (H \ negInv '' A ω) φ φ := by
    rw [H_diff_image_negInv, zeroGFFTestCov_image_negInv (hA ω).2 sdiff_subset φ]
    exact zeroGFFTestCov_neg_neg _ _
  simp only [hc]

/-- **Conformal covariance of local sets under `R(z) = −1/z`.** If `A` is a local set of `h`, then `R(A)` is a local
set of the reflected field `−h ∘ R`. -/
theorem IsLocalSet.reflect {Ω : Type u} [MeasurableSpace Ω] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    {P : Measure Ω} (hA : IsLocalSet A h P) :
    IsLocalSet (fun ω => negInv '' A ω) (fun ω => reflectField (h ω)) P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hae, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁, hh₂, hA'c, hhar, hcond, hlaw⟩ := hA
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => (negInv '' p.1, reflectField p.2) :=
    (measurable_image_negInv.comp measurable_fst).prodMk (measurable_reflectField.comp measurable_snd)
  have hσ : MeasurableSpace.comap (fun ω' => negInv '' A' ω') hittingSigma ⊔
      MeasurableSpace.comap (fun ω' => reflectField (h₁ ω')) inferInstance =
      MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance := by
    have e1 : MeasurableSpace.comap (fun ω' => negInv '' A' ω') hittingSigma =
        MeasurableSpace.comap A' hittingSigma := by
      change MeasurableSpace.comap ((fun S : Set ℂ => negInv '' S) ∘ A') hittingSigma = _
      rw [← MeasurableSpace.comap_comp, comap_eq_of_involutive measurable_image_negInv negInvImage_involutive]
    have e2 : MeasurableSpace.comap (fun ω' => reflectField (h₁ ω')) (inferInstance :
        MeasurableSpace (DistOn upperHalfPlaneOpens)) = MeasurableSpace.comap h₁ inferInstance := by
      change MeasurableSpace.comap (reflectField ∘ h₁) _ = _
      rw [← MeasurableSpace.comap_comp, comap_eq_of_involutive measurable_reflectField reflectField_involutive]
    rw [e1, e2]
  refine ⟨hF.comp_aemeasurable hm, hae.mono fun ω hω => image_negInv_relClosed hω,
    Ω', mΩ', P', hP', fun ω' => negInv '' A' ω', fun ω' => reflectField (h₁ ω'),
    fun ω' => reflectField (h₂ ω'), measurable_image_negInv.comp hA'm, measurable_reflectField.comp hh₁,
    measurable_reflectField.comp hh₂, fun ω' => image_negInv_relClosed (hA'c ω'), ?_, ?_, ?_⟩
  · filter_upwards [hhar] with ω' hω'
    rw [H_diff_image_negInv]
    exact isHarmonicDistOn_reflectField (hA'c ω').2 sdiff_subset hω'
  · rw [hσ]
    exact isCondZeroBoundaryGFF_reflect hA'c hcond
  · have e : (fun ω' => (negInv '' A' ω', reflectField (h₁ ω') + reflectField (h₂ ω'))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (negInv '' p.1, reflectField p.2)) ∘
          fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, reflectField_add]
    have e' : (fun ω => (negInv '' A ω, reflectField (h ω))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (negInv '' p.1, reflectField p.2)) ∘
          fun ω => (A ω, h ω) := rfl
    have hm' : Measurable fun ω' => (A' ω', h₁ ω' + h₂ ω') :=
      hA'm.prodMk (LQGMetric.measurable_distOn_iff.2 fun φ => by
        simp only [add_apply]
        exact ((LQGMetric.measurable_distOn_apply φ).comp hh₁).add
          ((LQGMetric.measurable_distOn_apply φ).comp hh₂))
    rw [e, e', ← Measure.map_map hF hm', hlaw, AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hm]

end Reflect

/-! ### Local sets along equal laws -/

/-- **Local sets transfer along equal laws.** If `A` is a local set of `h` under `P`, and `(A₂, h₂)` under `P₂` has
the law of `(A, h)` (and is a.e. measurable), with `A₂ ⊆ ℍ` relatively closed almost surely, then `A₂` is a local
set of `h₂`. The almost sure clause is a hypothesis because it is not an event of the hitting σ-algebra; on a glued
space it holds by construction. -/
theorem IsLocalSet.of_map_eq {Ω Ω₂ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω} {A₂ : Ω₂ → Set ℂ} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    {P₂ : Measure Ω₂} (hA : IsLocalSet A h P)
    (hm : letI : MeasurableSpace (Set ℂ) := hittingSigma; AEMeasurable (fun ω => (A₂ ω, h₂ ω)) P₂)
    (hae : ∀ᵐ ω ∂P₂, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hlaw : letI : MeasurableSpace (Set ℂ) := hittingSigma
      P₂.map (fun ω => (A₂ ω, h₂ ω)) = P.map (fun ω => (A ω, h ω))) :
    IsLocalSet A₂ h₂ P₂ := by
  obtain ⟨-, -, Ω', mΩ', P', hP', A', h₁, h₂', hA'm, hh₁, hh₂, hA'c, hhar, hcond, hlaw'⟩ := hA
  exact ⟨hm, hae, Ω', mΩ', P', hP', A', h₁, h₂', hA'm, hh₁, hh₂, hA'c, hhar, hcond, hlaw'.trans hlaw.symm⟩

/-! ### The zero-boundary GFF along a measure-preserving map -/

/-- **A zero-boundary GFF stays one along a measure-preserving map.** -/
theorem isZeroBoundaryGFF_comp_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {U : TopologicalSpace.Opens ℂ} {g : Ω → LQGMetric.DistOn U} {P : Measure Ω} {P' : Measure Ω'} {f : Ω' → Ω}
    (hf : Measurable f) (hfP : P'.map f = P) (hg : LQGMetric.IsZeroBoundaryGFF U g P) :
    LQGMetric.IsZeroBoundaryGFF U (fun ω' => g (f ω')) P' := by
  obtain ⟨hgm, hm, hgauss, hcent, hcov⟩ := hg
  have hI : ∀ I : Finset (LQGMetric.TestOn U), Measurable fun ω => I.restrict (fun φ => g ω φ) :=
    fun I => measurable_pi_iff.2 fun i => hm i
  refine ⟨hgm.comp hf, ⟨fun φ => (hm φ).comp hf, ⟨fun I => ⟨((hI I).comp hf).aemeasurable, ?_⟩⟩,
    fun φ => ?_, fun φ ψ => ?_⟩⟩
  · have h1 := (hgauss.hasGaussianLaw I).isGaussian_map
    rw [← hfP, Measure.map_map (hI I) hf] at h1
    exact h1
  · rw [← hcent φ, ← hfP, integral_map hf.aemeasurable (hm φ).aestronglyMeasurable]
  · rw [← hcov φ ψ, ← hfP, covariance_map (hm φ).aestronglyMeasurable (hm ψ).aestronglyMeasurable
      hf.aemeasurable]
    rfl

/-! ### Local sets on a glued space -/

section Glue

variable {Ω : Type u} {β : Type} {mΩ : MeasurableSpace Ω} [mβ : MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
  (k : Kernel (DistOn upperHalfPlaneOpens) β) [IsMarkovKernel k]

include hh in
/-- **The glued pair `(X, κ(X))` has the law `law(X) ⊗ κ`.** -/
theorem glueMeasure_map_pair :
    (glueMeasure P k h hh).map (fun p => (h p.1, p.2)) = P.map h ⊗ₘ k := by
  have hm : Measurable fun p : Ω × β => (h p.1, p.2) := (hh.comp measurable_fst).prodMk measurable_snd
  refine Measure.ext_prod fun {A C} hA hC => ?_
  rw [Measure.map_apply hm (hA.prod hC), Measure.compProd_apply_prod hA hC]
  have e : (fun p : Ω × β => (h p.1, p.2)) ⁻¹' (A ×ˢ C) = (h ⁻¹' A) ×ˢ C := by ext; simp
  rw [e, glueMeasure_apply_prod k hh (hh hA) hC, setLIntegral_map hA (k.measurable_coe hC) hh]

include hh in
/-- **A local set of the first coordinate stays local on the glued space** (for any measurable function `T` of the
field). -/
theorem IsLocalSet.glue_fst {T : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
    (hA : IsLocalSet A (fun ω => T (h ω)) P) :
    IsLocalSet (fun p : Ω × β => A p.1) (fun p => T (h p.1)) (glueMeasure P k h hh) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hfst := glueMeasure_fst (μ := P) k hh
  have hAE : AEMeasurable (fun ω => (A ω, T (h ω))) ((glueMeasure P k h hh).map Prod.fst) := by
    rw [hfst]; exact hA.1
  refine IsLocalSet.of_map_eq hA (hAE.comp_measurable measurable_fst) (ae_glue_fst k hh hA.2.1) ?_
  have e := AEMeasurable.map_map_of_aemeasurable hAE measurable_fst.aemeasurable
  rw [hfst] at e
  exact e.symm

include hh in
/-- **A local set read from the glued sample.** Let `(X₂, D₂)` on `Ω₂` be such that `X₂` has the law of `h` and `k` is
a conditional law of `D₂` given `X₂`. If `G(D₂)` is a local set of `T(X₂)`, then `G` read from the glued sample is a
local set of `T(h)` on the glued space. -/
theorem IsLocalSet.glue_snd {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {X₂ : Ω₂ → DistOn upperHalfPlaneOpens} {D₂ : Ω₂ → β} (hX₂ : Measurable X₂) (hD₂ : Measurable D₂)
    (hlaw : P.map h = P₂.map X₂) (hk : P₂.map (fun ω => (X₂ ω, D₂ ω)) = P₂.map X₂ ⊗ₘ k)
    {T : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT : Measurable T) {G : β → Set ℂ}
    (hG : Measurable[mβ, hittingSigma] G) {S : Set β} (hS : MeasurableSet S)
    (hSG : ∀ y ∈ S, G y ⊆ H ∧ IsOpen (H \ G y)) (hDS : ∀ᵐ ω ∂P₂, D₂ ω ∈ S)
    (hloc : IsLocalSet (fun ω => G (D₂ ω)) (fun ω => T (X₂ ω)) P₂) :
    IsLocalSet (fun p : Ω × β => G p.2) (fun p => T (h p.1)) (glueMeasure P k h hh) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hF : Measurable fun q : DistOn upperHalfPlaneOpens × β => (G q.2, T q.1) :=
    (hG.comp measurable_snd).prodMk (hT.comp measurable_fst)
  have hpair : Measurable fun p : Ω × β => (h p.1, p.2) := (hh.comp measurable_fst).prodMk measurable_snd
  refine IsLocalSet.of_map_eq hloc (hF.comp hpair).aemeasurable ?_ ?_
  · filter_upwards [ae_glue_snd hh hX₂ hD₂ hlaw k hk hS hDS] with p hp using hSG _ hp
  · have e1 : (fun p : Ω × β => (G p.2, T (h p.1))) =
        (fun q : DistOn upperHalfPlaneOpens × β => (G q.2, T q.1)) ∘ fun p => (h p.1, p.2) := rfl
    have e2 : (fun ω => (G (D₂ ω), T (X₂ ω))) =
        (fun q : DistOn upperHalfPlaneOpens × β => (G q.2, T q.1)) ∘ fun ω => (X₂ ω, D₂ ω) := rfl
    rw [e1, e2, ← Measure.map_map hF hpair, ← Measure.map_map hF (hX₂.prodMk hD₂), glueMeasure_map_pair hh k,
      hlaw, hk]

include hh in
/-- **The two stopped sets are a local set on the glued space** (Wang–Wu, proof of Proposition 4.18: "the
independent-union lemma makes the two stopped slits a local set"). If `F = T(h)` is a zero-boundary GFF, `A` (read
from the first coordinate) and `G` (read from the glued sample) are local sets of `F` on the glued space, then so is
their union: the glued sample is conditionally independent of the first coordinate given `h`. -/
theorem IsLocalSet.glue_union {T : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT : Measurable T)
    {T' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT' : Measurable T') (hTT : ∀ f, T' (T f) = f)
    (hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => T (h ω)) P) {A : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) {G : β → Set ℂ} (hG : Measurable[mβ, hittingSigma] G)
    (hA : IsLocalSet (fun p : Ω × β => A p.1) (fun p => T (h p.1)) (glueMeasure P k h hh))
    (hGl : IsLocalSet (fun p : Ω × β => G p.2) (fun p => T (h p.1)) (glueMeasure P k h hh)) :
    IsLocalSet (fun p : Ω × β => A p.1 ∪ G p.2) (fun p => T (h p.1)) (glueMeasure P k h hh) := by
  have hF' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × β => T (h p.1))
      (glueMeasure P k h hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => T (h ω)) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hh) hF
  have hci := condIndepEv_glue_fst (μ := P) k hh
  have hσ : MeasurableSpace.comap (fun p : Ω × β => T (h p.1)) inferInstance =
      MeasurableSpace.comap (fun p : Ω × β => h p.1) inferInstance := by
    refine le_antisymm ?_ ?_
    · change MeasurableSpace.comap (T ∘ fun p : Ω × β => h p.1) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hT.comap_le
    · calc MeasurableSpace.comap (fun p : Ω × β => h p.1) inferInstance
          = MeasurableSpace.comap (T' ∘ fun p : Ω × β => T (h p.1)) inferInstance := by
            congr 1; funext p; exact (hTT _).symm
        _ ≤ _ := by
            rw [← MeasurableSpace.comap_comp]
            exact MeasurableSpace.comap_mono hT'.comap_le
  refine LocalSets.IsLocalSet.isLocalSet_union hF' (hAm.comp measurable_fst) (hG.comp measurable_snd) ?_ hA hGl
  rw [hσ]
  intro a b ha hb
  refine hci a b ?_ ?_
  · obtain ⟨s, hs, rfl⟩ := ha
    exact ⟨A ⁻¹' s, hAm hs, rfl⟩
  · obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨G ⁻¹' s, hG hs, rfl⟩

end Glue

end InteractingSLE.WangWu
