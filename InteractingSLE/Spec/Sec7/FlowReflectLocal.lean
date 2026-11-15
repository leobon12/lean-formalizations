/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FlowReflectCov
import InteractingSLE.Frozen.Spec.IsLocalSet

/-!
# Harmonic functions, conditional GFFs and local sets under `R(z) = −z̄`

Packet PROVE-LEMMA76C. The anti-conformal reflection `R` preserves harmonicity (the Laplacian commutes with every
linear isometry: compute it in the orthonormal basis `R(e₁), R(e₂)`), and therefore transports the frozen
`IsHarmonicDistOn`, `IsCondZeroBoundaryGFF` and `IsLocalSet` (the same scheme as WangWu's `IsLocalSet.reflect` for
the conformal inversion `−1/z`):

* `laplacian_comp_reflectC`: `Δ(f ∘ R) = (Δf) ∘ R`; `harmonicAt_comp_reflectC`, `harmonicOnNhd_comp_reflectC`;
* `measurable_image_reflectC`: `S ↦ R(S)` is measurable for the hitting σ-algebra;
* `isHarmonicDistOn_reflField`, `isCondZeroBoundaryGFF_reflField`;
* **`IsLocalSet.reflectC`**: if `A` is a local set of `h`, then `R(A)` is a local set of `−h ∘ R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H zeroGFFTestCov testMeasPos testMeasNeg dualCov zeroSpace)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Sec7

namespace FlowReflect

open LP (reflectC)

/-! ### Harmonic functions -/

theorem iteratedFDeriv_comp_reflectC {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℂ → F) (x : ℂ)
    (i : ℕ) : iteratedFDeriv ℝ i (fun z => f (reflectC z)) x =
      (iteratedFDeriv ℝ i f (reflectC x)).compContinuousLinearMap fun _ => reflCLM := by
  simp only [← iteratedFDerivWithin_univ]
  have h := reflLIE.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x)
    (mem_univ _) i
  rw [preimage_univ] at h
  exact h

/-- **The Laplacian commutes with `R`.** -/
theorem laplacian_comp_reflectC (f : ℂ → ℝ) :
    Laplacian.laplacian (fun z => f (reflectC z)) = fun x => Laplacian.laplacian f (reflectC x) := by
  set v := stdOrthonormalBasis ℝ ℂ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ v,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (v.map reflLIE)]
  funext x
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_comp_reflectC, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

theorem harmonicAt_comp_reflectC {f : ℂ → ℝ} {x : ℂ} (hf : InnerProductSpace.HarmonicAt f (reflectC x)) :
    InnerProductSpace.HarmonicAt (fun z => f (reflectC z)) x := by
  refine ⟨hf.1.comp x reflCLM.contDiff.contDiffAt, ?_⟩
  rw [laplacian_comp_reflectC]
  exact hf.2.comp_tendsto (LP.continuous_reflectC.tendsto x)

theorem harmonicOnNhd_comp_reflectC {f : ℂ → ℝ} {U : Set ℂ} (hf : InnerProductSpace.HarmonicOnNhd f U) :
    InnerProductSpace.HarmonicOnNhd (fun z => f (reflectC z)) (reflectC '' U) := by
  rintro _ ⟨w, hw, rfl⟩
  apply harmonicAt_comp_reflectC
  rw [LP.reflectC_reflectC]
  exact hf w hw

/-! ### The hitting σ-algebra -/

theorem isOpen_image_reflectC {U : Set ℂ} (hU : IsOpen U) : IsOpen (reflectC '' U) :=
  LP.reflectHomeo.isOpenMap U hU

theorem image_reflectC_subset_H {U : Set ℂ} (hU : U ⊆ H) : reflectC '' U ⊆ H := by
  rintro _ ⟨w, hw, rfl⟩
  exact reflectC_mem_H (hU hw)

theorem image_reflectC_inter_nonempty_iff (S U : Set ℂ) :
    (reflectC '' S ∩ U).Nonempty ↔ (S ∩ reflectC '' U).Nonempty := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
    exact ⟨z, hz, reflectC z, hzU, LP.reflectC_reflectC z⟩
  · rintro ⟨z, hz, w, hw, rfl⟩
    exact ⟨w, ⟨reflectC w, hz, LP.reflectC_reflectC w⟩, hw⟩

/-- **`S ↦ R(S)` is measurable for the hitting σ-algebra.** -/
theorem measurable_image_reflectC :
    Measurable[hittingSigma, hittingSigma] fun S : Set ℂ => reflectC '' S := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ (fun S : Set ℂ => reflectC '' S) ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : (fun S : Set ℂ => reflectC '' S) ⁻¹' {A | (A ∩ U).Nonempty} =
      {A | (A ∩ reflectC '' U).Nonempty} := by
    ext S
    exact image_reflectC_inter_nonempty_iff S U
  rw [e]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨reflectC '' U, isOpen_image_reflectC hUo, image_reflectC_subset_H hUH, rfl⟩

theorem imageReflectC_involutive : Function.Involutive fun S : Set ℂ => reflectC '' S :=
  reflectC_image_image

theorem comap_eq_of_involutive' {α : Type*} {m : MeasurableSpace α} {f : α → α}
    (hf : Measurable[m, m] f) (hinv : Function.Involutive f) : m.comap f = m := by
  refine le_antisymm hf.comap_le ?_
  calc m = m.comap (f ∘ f) := by rw [hinv.comp_self, MeasurableSpace.comap_id]
    _ = (m.comap f).comap f := (MeasurableSpace.comap_comp).symm
    _ ≤ m.comap f := MeasurableSpace.comap_mono hf.comap_le

theorem image_reflectC_relClosed {S : Set ℂ} (hS : S ⊆ H ∧ IsOpen (H \ S)) :
    reflectC '' S ⊆ H ∧ IsOpen (H \ reflectC '' S) := by
  refine ⟨image_reflectC_subset_H hS.1, ?_⟩
  rw [LP.H_diff_reflectC_image]
  exact isOpen_image_reflectC hS.2

/-! ### Harmonic distributions and conditional GFFs -/

/-- **Harmonic distributions under `R`**: if `T` is harmonic on `U`, then `−T ∘ R` is harmonic on `R(U)`. -/
theorem isHarmonicDistOn_reflField {T : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hT : IsHarmonicDistOn T U) :
    IsHarmonicDistOn (reflField T) (reflectC '' U) := by
  obtain ⟨v, hv, hrep⟩ := hT
  refine ⟨fun z => -v (reflectC z), (harmonicOnNhd_comp_reflectC hv).neg, fun φ hφ => ?_⟩
  have hsupp : tsupport (reflTest φ) ⊆ U := by
    rw [tsupport_reflTest]
    calc reflectC '' tsupport φ ⊆ reflectC '' (reflectC '' U) := image_mono hφ
      _ = U := reflectC_image_image U
  rw [reflField_apply, hrep _ hsupp, ← integral_neg, ← integral_comp_reflectC]
  congr 1
  funext z
  simp only [reflTest_apply, LP.reflectC_reflectC, neg_mul]

theorem zeroGFFTestCov_neg_neg' (U : Set ℂ) (ψ : ℂ → ℝ) :
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

theorem zeroGFFTestCov_reflTest {A : Set ℂ} (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (H \ A) ⇑(-reflTest φ) ⇑(-reflTest φ) = zeroGFFTestCov (H \ reflectC '' A) φ φ := by
  rw [LP.H_diff_reflectC_image, zeroGFFTestCov_image_reflectC]
  have e : ⇑(-reflTest φ) = -fun z => φ (reflectC z) := rfl
  rw [e, zeroGFFTestCov_neg_neg']

/-- **The conditional zero-boundary GFF under `R`.** -/
theorem isCondZeroBoundaryGFF_reflField {Ω : Type*} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) X) :
    IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ reflectC '' A ω) (fun ω => reflField (X ω)) := by
  intro φ
  have h := hX (-reflTest φ)
  have e : (fun ω => Complex.exp (Complex.I * ((reflField (X ω) φ : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((X ω (-reflTest φ) : ℝ) : ℂ)) := by
    funext ω
    rw [reflField_apply_eq]
  rw [e]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  simp only [zeroGFFTestCov_reflTest]

/-! ### Local sets -/

/-- **Local sets under `R(z) = −z̄`.** If `A` is a local set of `h`, then `R(A)` is a local set of the reflected field
`−h ∘ R`. -/
theorem IsLocalSet.reflectC {Ω : Type u} [MeasurableSpace Ω] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    {P : Measure Ω} (hA : IsLocalSet A h P) :
    IsLocalSet (fun ω => LP.reflectC '' A ω) (fun ω => reflField (h ω)) P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hae, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁, hh₂, hA'c, hhar, hcond, hlaw⟩ := hA
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => (LP.reflectC '' p.1, reflField p.2) :=
    (measurable_image_reflectC.comp measurable_fst).prodMk (measurable_reflField.comp measurable_snd)
  have hσ : MeasurableSpace.comap (fun ω' => LP.reflectC '' A' ω') hittingSigma ⊔
      MeasurableSpace.comap (fun ω' => reflField (h₁ ω')) inferInstance =
      MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance := by
    have e1 : MeasurableSpace.comap (fun ω' => LP.reflectC '' A' ω') hittingSigma =
        MeasurableSpace.comap A' hittingSigma := by
      change MeasurableSpace.comap ((fun S : Set ℂ => LP.reflectC '' S) ∘ A') hittingSigma = _
      rw [← MeasurableSpace.comap_comp, comap_eq_of_involutive' measurable_image_reflectC
        imageReflectC_involutive]
    have e2 : MeasurableSpace.comap (fun ω' => reflField (h₁ ω')) (inferInstance :
        MeasurableSpace (DistOn upperHalfPlaneOpens)) = MeasurableSpace.comap h₁ inferInstance := by
      change MeasurableSpace.comap (reflField ∘ h₁) _ = _
      rw [← MeasurableSpace.comap_comp, comap_eq_of_involutive' measurable_reflField reflField_involutive]
    rw [e1, e2]
  refine ⟨hF.comp_aemeasurable hm, hae.mono fun ω hω => image_reflectC_relClosed hω,
    Ω', mΩ', P', hP', fun ω' => LP.reflectC '' A' ω', fun ω' => reflField (h₁ ω'),
    fun ω' => reflField (h₂ ω'), measurable_image_reflectC.comp hA'm, measurable_reflField.comp hh₁,
    measurable_reflField.comp hh₂, fun ω' => image_reflectC_relClosed (hA'c ω'), ?_, ?_, ?_⟩
  · filter_upwards [hhar] with ω' hω'
    rw [LP.H_diff_reflectC_image]
    exact isHarmonicDistOn_reflField hω'
  · rw [hσ]
    exact isCondZeroBoundaryGFF_reflField hcond
  · have e : (fun ω' => (LP.reflectC '' A' ω', reflField (h₁ ω') + reflField (h₂ ω'))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (LP.reflectC '' p.1, reflField p.2)) ∘
          fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, reflField_add]
    have e' : (fun ω => (LP.reflectC '' A ω, reflField (h ω))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (LP.reflectC '' p.1, reflField p.2)) ∘
          fun ω => (A ω, h ω) := rfl
    have hm' : Measurable fun ω' => (A' ω', h₁ ω' + h₂ ω') :=
      hA'm.prodMk (LQGMetric.measurable_distOn_iff.2 fun φ => by
        simp only [add_apply]
        exact ((LQGMetric.measurable_distOn_apply φ).comp hh₁).add
          ((LQGMetric.measurable_distOn_apply φ).comp hh₂))
    rw [e, e', ← Measure.map_map hF hm', hlaw, AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hm]

end FlowReflect

end Sec7

end InteractingSLE
