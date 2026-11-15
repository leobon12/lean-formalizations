/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FlowReflect

/-!
# The affine map `A(z) = a z + m` (`a > 0`, `m ∈ ℝ`) on test functions and on fields of `ℍ`

Packet PROVE-RLC-J, item (g) of `planning/handoffs/PROVE-RLC-G.md` ("What remains"): Lemma G8's "positive affine
normalization" (supplement p. 501: "Normalize it affinely so that the current tip coordinates become the prescribed
`w₂, w₁`"). The map `A(z) = a z + m` with `a > 0`, `m` real, is a conformal automorphism of `ℍ` with `A' = a > 0`, so
the coordinate change (1.4) adds no winding term: the field of the image picture is `h ∘ A⁻¹`, i.e.
`⟨h ∘ A⁻¹, φ⟩ = ⟨h, a² φ ∘ A⟩`. This file is the deterministic base (the template is `Sec7.FlowReflect` for
`R(z) = −z̄`):

* `aff a m`, its inverse `affInv a m`, the homeomorphism `affHomeo`, `A(ℍ) = ℍ`;
* **`affTest : 𝓓(ℍ) →L[ℝ] 𝓓(ℍ)`**, `φ ↦ a² φ ∘ A` (continuity on every `𝓓_K` through the structure maps: the `i`-th
  derivative of `f ∘ A` is that of `f` at `A x` with every argument multiplied by `a`);
* **`affField h = h ∘ A⁻¹`** (the field tested against `affTest`), measurable, additive, inverted by the inverse map;
* change of variables `∫ f ∘ A = a⁻² ∫ f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Distributions BoundedContinuousFunction

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace FlowDilate

/-! ### The affine map -/

/-- The real affine map `A(z) = a z + m`. -/
def aff (a m : ℝ) (z : ℂ) : ℂ := a • z + (m : ℂ)

/-- The inverse affine map `A⁻¹(z) = a⁻¹ z − m/a`. -/
def affInv (a m : ℝ) : ℂ → ℂ := aff a⁻¹ (-m / a)

variable {a m : ℝ}

@[simp] theorem aff_re (a m : ℝ) (z : ℂ) : (aff a m z).re = a * z.re + m := by simp [aff]

@[simp] theorem aff_im (a m : ℝ) (z : ℂ) : (aff a m z).im = a * z.im := by simp [aff]

theorem aff_ofReal (a m x : ℝ) : aff a m (x : ℂ) = ((a * x + m : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

theorem aff_affInv (ha : a ≠ 0) (z : ℂ) : aff a m (affInv a m z) = z := by
  apply Complex.ext
  · simp only [affInv, aff_re]; field_simp; ring
  · simp only [affInv, aff_im]; field_simp

theorem affInv_aff (ha : a ≠ 0) (z : ℂ) : affInv a m (aff a m z) = z := by
  apply Complex.ext
  · simp only [affInv, aff_re]; field_simp; ring
  · simp only [affInv, aff_im]; field_simp

theorem continuous_aff (a m : ℝ) : Continuous (aff a m) := by
  unfold aff; fun_prop

theorem measurable_aff (a m : ℝ) : Measurable (aff a m) := (continuous_aff a m).measurable

/-- `A` as a homeomorphism of `ℂ`. -/
def affHomeo (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun := aff a m
  invFun := affInv a m
  left_inv := affInv_aff ha
  right_inv := aff_affInv ha
  continuous_toFun := continuous_aff a m
  continuous_invFun := continuous_aff _ _

@[simp] theorem coe_affHomeo (ha : a ≠ 0) : ⇑(affHomeo (m := m) ha) = aff a m := rfl

theorem affInv_eq_symm (ha : a ≠ 0) : ⇑(affHomeo (m := m) ha).symm = affInv a m := rfl

theorem aff_mem_H_iff (ha : 0 < a) {z : ℂ} : aff a m z ∈ H ↔ z ∈ H := by
  show 0 < (aff a m z).im ↔ 0 < z.im
  rw [aff_im]
  exact ⟨fun h => pos_of_mul_pos_right h ha.le, fun h => mul_pos ha h⟩

theorem affInv_mem_H_iff (ha : 0 < a) {z : ℂ} : affInv a m z ∈ H ↔ z ∈ H :=
  aff_mem_H_iff (inv_pos.2 ha)

theorem preimage_aff (ha : a ≠ 0) (S : Set ℂ) : aff a m ⁻¹' S = affInv a m '' S := by
  ext z
  refine ⟨fun h => ⟨aff a m z, h, affInv_aff ha z⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  show aff a m (affInv a m w) ∈ S
  rw [aff_affInv ha]
  exact hw

theorem preimage_affInv (ha : a ≠ 0) (S : Set ℂ) : affInv a m ⁻¹' S = aff a m '' S := by
  ext z
  refine ⟨fun h => ⟨affInv a m z, h, aff_affInv ha z⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  show affInv a m (aff a m w) ∈ S
  rw [affInv_aff ha]
  exact hw

theorem affInv_image_aff_image (ha : a ≠ 0) (S : Set ℂ) : affInv a m '' (aff a m '' S) = S := by
  rw [image_image]
  simp only [affInv_aff ha, image_id']

theorem aff_image_affInv_image (ha : a ≠ 0) (S : Set ℂ) : aff a m '' (affInv a m '' S) = S := by
  rw [image_image]
  simp only [aff_affInv ha, image_id']

theorem aff_image_H (ha : 0 < a) : aff a m '' H = H := by
  ext z
  refine ⟨fun ⟨w, hw, e⟩ => e ▸ (aff_mem_H_iff ha).2 hw, fun hz => ⟨affInv a m z, ?_, aff_affInv ha.ne' z⟩⟩
  exact (affInv_mem_H_iff ha).2 hz

theorem affInv_image_H (ha : 0 < a) : affInv a m '' H = H := by
  have h := aff_image_H (m := -m / a) (inv_pos.2 ha)
  exact h

theorem aff_image_subset_H (ha : 0 < a) {U : Set ℂ} (hU : U ⊆ H) : aff a m '' U ⊆ H := by
  rintro _ ⟨w, hw, rfl⟩
  exact (aff_mem_H_iff ha).2 (hU hw)

theorem affInv_image_subset_H (ha : 0 < a) {U : Set ℂ} (hU : U ⊆ H) : affInv a m '' U ⊆ H :=
  aff_image_subset_H (inv_pos.2 ha) hU

theorem aff_image_diff_H (ha : 0 < a) (S : Set ℂ) : aff a m '' (H \ S) = H \ aff a m '' S := by
  have h := image_sdiff (affHomeo (m := m) ha.ne').injective H S
  rw [coe_affHomeo, aff_image_H ha] at h
  exact h

theorem tsupport_comp_aff (ha : a ≠ 0) {F : Type*} [Zero F] (φ : ℂ → F) :
    tsupport (fun z => φ (aff a m z)) = affInv a m '' tsupport φ := by
  have h := tsupport_comp_eq_preimage φ (affHomeo (m := m) ha)
  rw [coe_affHomeo, preimage_aff ha] at h
  exact h

theorem hasCompactSupport_comp_aff (ha : a ≠ 0) {F : Type*} [Zero F] {φ : ℂ → F}
    (hφ : HasCompactSupport φ) : HasCompactSupport (fun z => φ (aff a m z)) :=
  hφ.comp_homeomorph (affHomeo ha)

/-- The linear part `z ↦ a z` of `A`, as a continuous real linear map. -/
def affCLM (a : ℝ) : ℂ →L[ℝ] ℂ := a • ContinuousLinearMap.id ℝ ℂ

@[simp] theorem affCLM_apply (a : ℝ) (z : ℂ) : affCLM a z = a • z := rfl

theorem aff_eq_affCLM (a m : ℝ) (z : ℂ) : aff a m z = affCLM a z + (m : ℂ) := rfl

theorem contDiff_comp_aff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {φ : ℂ → F} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (fun z => φ (aff a m z)) :=
  hφ.comp (by unfold aff; fun_prop)

/-! ### Lebesgue measure under `A` -/

/-- **Change of variables `z = A w`**: `∫ f ∘ A = a⁻² ∫ f`. -/
theorem integral_comp_aff (ha : 0 < a) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    ∫ z, f (aff a m z) = (a ^ 2)⁻¹ • ∫ z, f z := by
  have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ) (fun y : ℂ => f (y + (m : ℂ))) a
    (hR := ha.le)
  rw [Complex.finrank_real_complex, integral_add_right_eq_self (fun y => f y) (m : ℂ)] at h1
  exact h1

/-- `volume ∘ A⁻¹ = a⁻² volume`. -/
theorem map_aff_volume (ha : 0 < a) :
    (volume : Measure ℂ).map (aff a m) = ENNReal.ofReal ((a ^ 2)⁻¹) • volume := by
  have e : aff a m = (fun y : ℂ => y + (m : ℂ)) ∘ fun z : ℂ => a • z := rfl
  rw [e, ← Measure.map_map (measurable_add_const (m : ℂ)) (measurable_const_smul a),
    Measure.map_addHaar_smul volume ha.ne', Complex.finrank_real_complex, Measure.map_smul,
    map_add_right_eq_self volume (m : ℂ), abs_of_nonneg (by positivity)]
  exact (measurable_add_const _).aemeasurable

/-! ### The transported test function `a² φ ∘ A` -/

/-- `a² φ ∘ A` as a test function on `ℍ`. -/
def affTestFun (m : ℝ) (ha : 0 < a) (φ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens where
  toFun z := a ^ 2 * φ (aff a m z)
  contDiff' := contDiff_const.mul (contDiff_comp_aff φ.contDiff)
  hasCompactSupport' := (hasCompactSupport_comp_aff ha.ne' φ.hasCompactSupport).mul_left
  tsupport_subset' := by
    refine (tsupport_mul_subset_right (f := fun _ : ℂ => a ^ 2) (g := fun z => φ (aff a m z))).trans ?_
    rw [tsupport_comp_aff ha.ne']
    exact affInv_image_subset_H ha φ.tsupport_subset

/-- The compact set `A⁻¹(K)`. -/
def affCompacts (m : ℝ) (_ha : a ≠ 0) (K : Compacts ℂ) : Compacts ℂ := K.map (affInv a m) (continuous_aff _ _)

theorem coe_affCompacts (ha : a ≠ 0) (K : Compacts ℂ) :
    (affCompacts m ha K : Set ℂ) = affInv a m '' K :=
  Compacts.coe_map _ _

/-- `f ↦ a² f ∘ A` from `𝓓_K` to `𝓓_{A⁻¹(K)}`. -/
def affK (m : ℝ) (ha : a ≠ 0) (K : Compacts ℂ) (f : 𝓓_{K}(ℂ, ℝ)) : 𝓓_{affCompacts m ha K}(ℂ, ℝ) where
  toFun z := a ^ 2 * f (aff a m z)
  contDiff' := contDiff_const.mul (contDiff_comp_aff f.contDiff)
  zero_on_compl' := fun z hz => by
    have h0 : f (aff a m z) = 0 := f.zero_on_compl fun h => hz (by
      rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_affCompacts]
      exact ⟨aff a m z, h, affInv_aff ha z⟩)
    show a ^ 2 * f (aff a m z) = 0
    rw [h0, mul_zero]

/-- The action of `A` on the `i`-th structure map: precompose with `A`, multiply every argument by `a`, and multiply
by `a²`. -/
def affBCF (a m : ℝ) (i : ℕ) : (ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ)) → (ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ)) := fun G =>
  ((a ^ 2) • ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => affCLM a)).compLeftContinuousBounded
    ℂ (G.compContinuous ⟨aff a m, continuous_aff a m⟩)

theorem continuous_affBCF (a m : ℝ) (i : ℕ) : Continuous (affBCF a m i) :=
  (ContinuousLinearMap.continuous _).comp (BoundedContinuousFunction.continuous_compContinuous _)

theorem iteratedFDeriv_comp_aff {f : ℂ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) {i : ℕ}
    (hi : (i : WithTop ℕ∞) ≤ n) (x : ℂ) :
    iteratedFDeriv ℝ i (fun z => f (aff a m z)) x =
      (iteratedFDeriv ℝ i f (aff a m x)).compContinuousLinearMap fun _ => affCLM a := by
  have e : (fun z => f (aff a m z)) = (fun y => f (y + (m : ℂ))) ∘ affCLM a := rfl
  have hf' : ContDiff ℝ n (fun y => f (y + (m : ℂ))) := hf.comp (contDiff_id.add contDiff_const)
  rw [e, (affCLM a).iteratedFDeriv_comp_right hf' x hi,
    iteratedFDeriv_comp_add_right]
  rfl

theorem structureMap_affK (ha : a ≠ 0) (K : Compacts ℂ) (i : ℕ) (f : 𝓓_{K}(ℂ, ℝ)) :
    ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (affK m ha K f) =
      affBCF a m i (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f) := by
  ext x : 1
  have e : (affK m ha K f : ℂ → ℝ) = fun z => a ^ 2 • f (aff a m z) := rfl
  have hfc := f.contDiff
  have h2 : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f) (aff a m x) =
      iteratedFDeriv ℝ i f (aff a m x) := by
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, e,
    iteratedFDeriv_const_smul_apply' ((contDiff_comp_aff hfc).contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_aff hfc (by exact_mod_cast le_top)]
  change _ = ((a ^ 2) • ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => affCLM a))
    ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f) (aff a m x))
  rw [h2]
  rfl

theorem continuous_affK (ha : a ≠ 0) (K : Compacts ℂ) : Continuous (affK m ha K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  have e : ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ affK m ha K =
      affBCF a m i ∘ ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := funext (structureMap_affK ha K i)
  rw [e]
  exact (continuous_affBCF a m i).comp (ContinuousLinearMap.continuous _)

/-- **The transport of test functions** `φ ↦ a² φ ∘ A`, a continuous linear map of `𝓓(ℍ)`. -/
def affTest (m : ℝ) (ha : 0 < a) : TestOn upperHalfPlaneOpens →L[ℝ] TestOn upperHalfPlaneOpens :=
  TestFunction.mkCLM ℝ (affTestFun m ha) (fun _ _ => by ext; simp [affTestFun, mul_add])
    (fun _ _ => by ext; simp [affTestFun]; ring)
    (fun K hK => by
      have hK' : (affCompacts m ha.ne' K : Set ℂ) ⊆ upperHalfPlaneOpens := by
        rw [coe_affCompacts]
        exact affInv_image_subset_H ha hK
      have e : affTestFun m ha ∘ TestFunction.ofSupportedIn hK =
          TestFunction.ofSupportedIn hK' ∘ affK m ha.ne' K := by
        funext f; ext; rfl
      rw [e]
      exact (TestFunction.continuous_ofSupportedIn hK').comp (continuous_affK (m := m) ha.ne' K))

@[simp] theorem affTest_apply (ha : 0 < a) (φ : TestOn upperHalfPlaneOpens) (z : ℂ) :
    affTest m ha φ z = a ^ 2 * φ (aff a m z) := rfl

theorem tsupport_affTest (ha : 0 < a) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (affTest m ha φ) = affInv a m '' tsupport φ := by
  have e : ⇑(affTest m ha φ) = fun z => a ^ 2 * φ (aff a m z) := rfl
  rw [e]
  refine le_antisymm ((tsupport_mul_subset_right (f := fun _ : ℂ => a ^ 2)
    (g := fun z => φ (aff a m z))).trans (tsupport_comp_aff ha.ne' φ).le) ?_
  have hs : Function.support (fun z => a ^ 2 * φ (aff a m z)) = Function.support (fun z => φ (aff a m z)) := by
    ext z
    simp [ha.ne']
  have ht : tsupport (fun z => a ^ 2 * φ (aff a m z)) = tsupport (fun z => φ (aff a m z)) := by
    rw [tsupport, hs, ← tsupport]
  rw [ht, tsupport_comp_aff ha.ne']

theorem affTest_affTest_inv (ha : 0 < a) (φ : TestOn upperHalfPlaneOpens) :
    affTest m ha (affTest (-m / a) (inv_pos.2 ha) φ) = φ := by
  ext z
  simp only [affTest_apply]
  have e : aff a⁻¹ (-m / a) (aff a m z) = z := affInv_aff ha.ne' z
  rw [e]
  field_simp

theorem affTest_inv_affTest (ha : 0 < a) (φ : TestOn upperHalfPlaneOpens) :
    affTest (-m / a) (inv_pos.2 ha) (affTest m ha φ) = φ := by
  ext z
  simp only [affTest_apply]
  have e : aff a m (aff a⁻¹ (-m / a) z) = z := aff_affInv ha.ne' z
  rw [e]
  field_simp

/-! ### The transported field `h ∘ A⁻¹` -/

/-- **The transported field** `h ∘ A⁻¹`: `⟨affField h, φ⟩ = ⟨h, a² φ ∘ A⟩`. -/
def affField (m : ℝ) (ha : 0 < a) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  h.comp (affTest m ha)

@[simp] theorem affField_apply (ha : 0 < a) (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    affField m ha h φ = h (affTest m ha φ) := rfl

theorem affField_inv_affField (ha : 0 < a) (h : DistOn upperHalfPlaneOpens) :
    affField (-m / a) (inv_pos.2 ha) (affField m ha h) = h := by
  ext φ
  simp only [affField_apply, affTest_affTest_inv]

theorem affField_affField_inv (ha : 0 < a) (h : DistOn upperHalfPlaneOpens) :
    affField m ha (affField (-m / a) (inv_pos.2 ha) h) = h := by
  ext φ
  simp only [affField_apply, affTest_inv_affTest]

theorem affField_add (ha : 0 < a) (f g : DistOn upperHalfPlaneOpens) :
    affField m ha (f + g) = affField m ha f + affField m ha g := by
  ext φ
  simp only [affField_apply, add_apply]

theorem measurable_affField (ha : 0 < a) : Measurable (affField m ha) :=
  LQGMetric.measurable_distOn_iff.2 fun φ => LQGMetric.measurable_distOn_apply (affTest m ha φ)

/-- `∫ u · (a² φ ∘ A) = ∫ (u ∘ A⁻¹) · φ`. -/
theorem integral_mul_affTest (ha : 0 < a) (u : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, u z * affTest m ha φ z = ∫ z, u (affInv a m z) * φ z := by
  have h := integral_comp_aff (m := m) ha (fun w => u (affInv a m w) * φ w)
  simp only [affInv_aff ha.ne', smul_eq_mul] at h
  simp only [affTest_apply]
  have e : (fun z => u z * (a ^ 2 * φ (aff a m z))) = fun z => a ^ 2 * (u z * φ (aff a m z)) := by
    funext z; ring
  rw [e, integral_const_mul, h]
  field_simp

end FlowDilate

end InteractingSLE
