/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.Reflect
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import LQGMetric.Field.ZeroBoundary

/-!
# The reflection `R(z) = −z̄` on test functions and on fields of `ℍ`

Packet PROVE-LEMMA76C (Lemma 7.6's swapped half: "Reflection and exchange of the path labels gives its corresponding
opposite-side form", specification p. 270). The reflection `R(z) = −z̄` (`LP.reflectC`) is an involutive linear
isometry of `ℂ` preserving `ℍ`, but it is **anti**-conformal, so the conformal-chart transport of `GFF/Pushforward`
does not apply. This file builds the transport directly:

* `reflLIE`: `R` as a real linear isometry equivalence;
* **`reflTest : 𝓓(ℍ) →L[ℝ] 𝓓(ℍ)`**, `φ ↦ φ ∘ R` (continuity on every `𝓓_K` through the structure maps: the `i`-th
  derivative of `f ∘ R` is that of `f` at `R x` composed with `R` in each argument);
* **`reflField h = −h ∘ R`** (the field tested against `reflTest`), measurable, additive, involutive;
* change of variables `∫ f ∘ R = ∫ f` (`R` preserves Lebesgue measure).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal ComplexConjugate Distributions BoundedContinuousFunction

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Sec7

namespace FlowReflect

open LP (reflectC)

/-! ### `R` as a linear isometry -/

/-- The reflection `R(z) = −z̄` as a real linear isometry equivalence of `ℂ`. -/
def reflLIE : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

theorem reflLIE_apply (z : ℂ) : reflLIE z = reflectC z := rfl

theorem coe_reflLIE : ⇑reflLIE = reflectC := rfl

theorem reflectC_involutive : Function.Involutive reflectC := LP.reflectC_reflectC

theorem reflectC_mem_H {z : ℂ} (hz : z ∈ H) : reflectC z ∈ H := LP.reflectC_mem_H_iff.2 hz

theorem reflectC_image_H : reflectC '' H = H := by
  ext z
  refine ⟨fun ⟨w, hw, e⟩ => e ▸ reflectC_mem_H hw, fun hz => ⟨reflectC z, reflectC_mem_H hz, LP.reflectC_reflectC z⟩⟩

theorem reflectC_image_image (S : Set ℂ) : reflectC '' (reflectC '' S) = S := by
  rw [image_image]
  simp only [LP.reflectC_reflectC, image_id']

theorem preimage_reflectC (S : Set ℂ) : reflectC ⁻¹' S = reflectC '' S :=
  (LP.reflectC_image_eq_preimage S).symm

theorem tsupport_comp_reflectC {F : Type*} [Zero F] (φ : ℂ → F) :
    tsupport (fun z => φ (reflectC z)) = reflectC '' tsupport φ := by
  have h := tsupport_comp_eq_preimage φ LP.reflectHomeo
  rw [LP.coe_reflectHomeo, preimage_reflectC] at h
  exact h

theorem hasCompactSupport_comp_reflectC {F : Type*} [Zero F] {φ : ℂ → F} (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z => φ (reflectC z)) :=
  hφ.comp_homeomorph LP.reflectHomeo

/-- **`R` preserves Lebesgue measure.** -/
theorem measurePreserving_reflectC : MeasurePreserving reflectC volume volume :=
  reflLIE.measurePreserving

theorem measurableEmbedding_reflectC : MeasurableEmbedding reflectC :=
  LP.reflectHomeo.measurableEmbedding

/-- **Change of variables `z = R w`.** -/
theorem integral_comp_reflectC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    ∫ z, f (reflectC z) = ∫ z, f z :=
  measurePreserving_reflectC.integral_comp measurableEmbedding_reflectC f


/-! ### The reflected test function -/

/-- `R` as a continuous real linear map. -/
def reflCLM : ℂ →L[ℝ] ℂ := reflLIE.toContinuousLinearEquiv.toContinuousLinearMap

theorem reflCLM_apply (z : ℂ) : reflCLM z = reflectC z := rfl

theorem contDiff_comp_reflectC {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {φ : ℂ → F} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (fun z => φ (reflectC z)) :=
  hφ.comp reflCLM.contDiff

/-- `φ ∘ R` as a test function on `ℍ`. -/
def reflTestFun (φ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens where
  toFun z := φ (reflectC z)
  contDiff' := contDiff_comp_reflectC φ.contDiff
  hasCompactSupport' := hasCompactSupport_comp_reflectC φ.hasCompactSupport
  tsupport_subset' := by
    rw [tsupport_comp_reflectC]
    rintro _ ⟨w, hw, rfl⟩
    exact reflectC_mem_H (φ.tsupport_subset hw)

/-- The reflected compact set `R(K)`. -/
def reflCompacts (K : Compacts ℂ) : Compacts ℂ := K.map reflectC LP.continuous_reflectC

theorem coe_reflCompacts (K : Compacts ℂ) : (reflCompacts K : Set ℂ) = reflectC '' K :=
  Compacts.coe_map _ _

/-- `f ↦ f ∘ R` from `𝓓_K` to `𝓓_{R(K)}`. -/
def reflK (K : Compacts ℂ) (f : 𝓓_{K}(ℂ, ℝ)) : 𝓓_{reflCompacts K}(ℂ, ℝ) where
  toFun z := f (reflectC z)
  contDiff' := contDiff_comp_reflectC f.contDiff
  zero_on_compl' := fun z hz => f.zero_on_compl fun h => hz (by
    rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_reflCompacts]
    exact ⟨reflectC z, h, LP.reflectC_reflectC z⟩)

/-- The action of `R` on the `i`-th structure map: precompose with `R` and compose every argument with `R`. -/
def reflBCF (i : ℕ) : (ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ)) → (ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ)) := fun G =>
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => reflCLM)).compLeftContinuousBounded ℂ
    (G.compContinuous ⟨reflectC, LP.continuous_reflectC⟩)

theorem continuous_reflBCF (i : ℕ) : Continuous (reflBCF i) :=
  (ContinuousLinearMap.continuous _).comp (BoundedContinuousFunction.continuous_compContinuous _)

theorem structureMap_reflK (K : Compacts ℂ) (i : ℕ) (f : 𝓓_{K}(ℂ, ℝ)) :
    ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (reflK K f) =
      reflBCF i (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f) := by
  ext x : 1
  have e : (reflK K f : ℂ → ℝ) = (f : ℂ → ℝ) ∘ reflCLM := rfl
  have h2 : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f) (reflectC x) =
      iteratedFDeriv ℝ i f (reflectC x) := by
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, e,
    reflCLM.iteratedFDeriv_comp_right f.contDiff x (by exact_mod_cast le_top)]
  change _ = ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => reflCLM)
    ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f) (reflectC x))
  rw [h2]
  rfl

theorem continuous_reflK (K : Compacts ℂ) : Continuous (reflK K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  have e : ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ reflK K =
      reflBCF i ∘ ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := funext (structureMap_reflK K i)
  rw [e]
  exact (continuous_reflBCF i).comp (ContinuousLinearMap.continuous _)

/-- **The reflection of test functions** `φ ↦ φ ∘ R`, a continuous linear map of `𝓓(ℍ)`. -/
def reflTest : TestOn upperHalfPlaneOpens →L[ℝ] TestOn upperHalfPlaneOpens :=
  TestFunction.mkCLM ℝ reflTestFun (fun _ _ => by ext; rfl) (fun _ _ => by ext; rfl)
    (fun K hK => by
      have hK' : (reflCompacts K : Set ℂ) ⊆ upperHalfPlaneOpens := by
        rw [coe_reflCompacts]
        rintro _ ⟨w, hw, rfl⟩
        exact reflectC_mem_H (hK hw)
      have e : reflTestFun ∘ TestFunction.ofSupportedIn hK = TestFunction.ofSupportedIn hK' ∘ reflK K := by
        funext f; ext; rfl
      rw [e]
      exact (TestFunction.continuous_ofSupportedIn hK').comp (continuous_reflK K))

@[simp] theorem reflTest_apply (φ : TestOn upperHalfPlaneOpens) (z : ℂ) : reflTest φ z = φ (reflectC z) := rfl

theorem reflTest_reflTest (φ : TestOn upperHalfPlaneOpens) : reflTest (reflTest φ) = φ := by
  ext z
  simp only [reflTest_apply, LP.reflectC_reflectC]

theorem tsupport_reflTest (φ : TestOn upperHalfPlaneOpens) : tsupport (reflTest φ) = reflectC '' tsupport φ :=
  tsupport_comp_reflectC φ

/-! ### The reflected field `−h ∘ R` -/

/-- **The reflected field** `−h ∘ R`: `⟨reflField h, φ⟩ = −⟨h, φ ∘ R⟩`. -/
def reflField (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens := -(h.comp reflTest)

theorem reflField_apply (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    reflField h φ = -h (reflTest φ) := rfl

theorem reflField_reflField (h : DistOn upperHalfPlaneOpens) : reflField (reflField h) = h := by
  ext φ
  simp only [reflField_apply, reflTest_reflTest, neg_neg]

theorem reflField_involutive : Function.Involutive reflField := reflField_reflField

theorem reflField_add (f g : DistOn upperHalfPlaneOpens) : reflField (f + g) = reflField f + reflField g := by
  ext φ
  simp only [reflField_apply, add_apply, neg_add]

theorem measurable_reflField : Measurable reflField :=
  LQGMetric.measurable_distOn_iff.2 fun φ => (LQGMetric.measurable_distOn_apply (reflTest φ)).neg

theorem reflTest_neg (φ : TestOn upperHalfPlaneOpens) : reflTest (-φ) = -reflTest φ := map_neg _ _

theorem reflField_apply_eq (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    reflField h φ = h (-reflTest φ) := by
  rw [reflField_apply, map_neg]

end FlowReflect

end Sec7

end InteractingSLE
