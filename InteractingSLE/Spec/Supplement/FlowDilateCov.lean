/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.FlowDilate
import InteractingSLE.Spec.Sec7.FlowReflectLocal

/-!
# The zero-boundary covariance, harmonic functions and local sets under `A(z) = a z + m`

Packet PROVE-RLC-J, item (g) (Lemma G8's affine normalization). `A` is conformal with `A' = a > 0`, so the Dirichlet
energy is `A`-invariant (`dirichletEnergyOn_comp_aff`), the dual Dirichlet norm transports
(`dualNormSq_map_aff`), and the zero-boundary covariance of `ℍ` is invariant under `φ ↦ a² φ ∘ A`
(`zeroGFFTestCov_affTest_H`); the Laplacian scales by `a²` (`laplacian_comp_aff`), so harmonicity is preserved.
Consequences (the analogues of `Sec7.FlowReflectCov`, `Sec7.FlowReflectLocal`):

* `isZBGFFProcess_aff`; `IsBoundedHarmonicExtension.comp_aff`;
* **`IsGFFWithBoundaryData.affine`**: a GFF with boundary data `b` (off `S`) is carried to a GFF with data
  `b ∘ A⁻¹` (off `A(S)`).

The pure dilation case (`m = 0`) of the field statements is also in `Sec7.Lemma725RefFullDilField` (PROVE-LEMMA725REF2,
through LQGMetric's `zeroGFFTestCov_affine_ind`); the covariance computation here (Dirichlet energy and dual norm under
`A`) is the specialization of LQGMetric's `zeroGFFTestCov_affine` to test functions on `ℍ` and a real shift.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

open QuantumZipper (H zeroGFFTestCov testMeasPos testMeasNeg dualCov dualNormSq zeroSpace dirichletEnergyOn)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace FlowDilate

variable {a m : ℝ}

/-! ### Derivatives -/

/-- `z ↦ a z` as a continuous linear equivalence (`a ≠ 0`). -/
def affCLE (ha : a ≠ 0) : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ a ha).toContinuousLinearEquiv

@[simp] theorem affCLE_apply (ha : a ≠ 0) (z : ℂ) : affCLE ha z = a • z := rfl

theorem affCLE_toCLM (ha : a ≠ 0) : (affCLE ha : ℂ →L[ℝ] ℂ) = affCLM a :=
  ContinuousLinearMap.ext fun _ => rfl

theorem comp_aff_eq (ha : a ≠ 0) {F : Type*} (f : ℂ → F) :
    (fun z => f (aff a m z)) = (fun y => f (y + (m : ℂ))) ∘ affCLE ha := rfl

theorem iteratedFDeriv_comp_aff' (ha : a ≠ 0) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℂ → F)
    (x : ℂ) (i : ℕ) : iteratedFDeriv ℝ i (fun z => f (aff a m z)) x =
      (iteratedFDeriv ℝ i f (aff a m x)).compContinuousLinearMap fun _ => affCLM a := by
  rw [comp_aff_eq ha]
  simp only [← iteratedFDerivWithin_univ]
  have h := (affCLE ha).iteratedFDerivWithin_comp_right (fun y => f (y + (m : ℂ))) uniqueDiffOn_univ (x := x)
    (mem_univ _) i
  rw [preimage_univ] at h
  rw [h, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, iteratedFDeriv_comp_add_right, affCLE_toCLM]
  rfl

theorem fderiv_comp_aff (ha : a ≠ 0) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℂ → F) (z : ℂ) :
    fderiv ℝ (fun w => f (aff a m w)) z = (fderiv ℝ f (aff a m z)).comp (affCLM a) := by
  rw [comp_aff_eq ha, (affCLE ha).comp_right_fderiv, fderiv_comp_add_right, affCLE_toCLM]
  rfl

theorem norm_fderiv_comp_aff (ha : 0 < a) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℂ → F)
    (z : ℂ) : ‖fderiv ℝ (fun w => f (aff a m w)) z‖ = a * ‖fderiv ℝ f (aff a m z)‖ := by
  rw [fderiv_comp_aff ha.ne', affCLM, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul,
    Real.norm_of_nonneg ha.le]

/-- **The Laplacian under `A`**: `Δ(f ∘ A) = a² (Δf) ∘ A`. -/
theorem laplacian_comp_aff (ha : a ≠ 0) (f : ℂ → ℝ) :
    Laplacian.laplacian (fun z => f (aff a m z)) = fun x => a ^ 2 * Laplacian.laplacian f (aff a m x) := by
  set v := stdOrthonormalBasis ℝ ℂ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ v,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ v]
  funext x
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_comp_aff' ha, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have e' : (fun j : Fin 2 => affCLM a (![v i, v i] j)) = fun j : Fin 2 => a • ![v i, v i] j := by
    funext j; simp
  rw [e', ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

theorem harmonicAt_comp_aff (ha : a ≠ 0) {f : ℂ → ℝ} {x : ℂ}
    (hf : InnerProductSpace.HarmonicAt f (aff a m x)) :
    InnerProductSpace.HarmonicAt (fun z => f (aff a m z)) x := by
  refine ⟨hf.1.comp x (contDiff_comp_aff (φ := id) contDiff_id).contDiffAt, ?_⟩
  rw [laplacian_comp_aff ha]
  have h := hf.2.comp_tendsto ((continuous_aff a m).tendsto x)
  filter_upwards [h] with z hz
  simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
  rw [hz, mul_zero]

theorem harmonicOnNhd_comp_aff (ha : a ≠ 0) {f : ℂ → ℝ} {U : Set ℂ} (hf : InnerProductSpace.HarmonicOnNhd f U) :
    InnerProductSpace.HarmonicOnNhd (fun z => f (aff a m z)) (affInv a m '' U) := by
  rintro _ ⟨w, hw, rfl⟩
  apply harmonicAt_comp_aff ha
  rw [aff_affInv ha]
  exact hf w hw

/-! ### Lebesgue measure: set integrals and densities -/

theorem aff_injective (ha : a ≠ 0) : Function.Injective (aff a m) := (affHomeo ha).injective

theorem measurableEmbedding_aff (ha : a ≠ 0) : MeasurableEmbedding (aff a m) :=
  (affHomeo ha).measurableEmbedding

theorem measurable_affInv (a m : ℝ) : Measurable (affInv a m) := measurable_aff _ _

theorem image_aff_eq_preimage (ha : a ≠ 0) (S : Set ℂ) : aff a m '' S = affInv a m ⁻¹' S :=
  (preimage_affInv ha S).symm

/-- **`∫_U g ∘ A = a⁻² ∫_{A(U)} g`.** -/
theorem setIntegral_comp_aff (ha : 0 < a) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℂ → E)
    (U : Set ℂ) : ∫ z in U, g (aff a m z) = (a ^ 2)⁻¹ • ∫ y in aff a m '' U, g y := by
  have h := (measurableEmbedding_aff (m := m) ha.ne').setIntegral_map (μ := volume) g (aff a m '' U)
  rw [map_aff_volume ha, Measure.restrict_smul, integral_smul_measure,
    preimage_image_eq _ (aff_injective ha.ne'), ENNReal.toReal_ofReal (by positivity)] at h
  rw [← h]

/-- **`∫⁻_{A(s)} g = a² ∫⁻_s g ∘ A`.** -/
theorem setLIntegral_image_aff (ha : 0 < a) (g : ℂ → ℝ≥0∞) (s : Set ℂ) :
    ∫⁻ y in aff a m '' s, g y = ENNReal.ofReal (a ^ 2) * ∫⁻ z in s, g (aff a m z) := by
  have h : ∫⁻ y in aff a m '' s, g y ∂((volume : Measure ℂ).map (aff a m)) =
      ∫⁻ z in s, g (aff a m z) := by
    rw [(measurableEmbedding_aff (m := m) ha.ne').restrict_map,
      (measurableEmbedding_aff (m := m) ha.ne').lintegral_map,
      preimage_image_eq _ (aff_injective ha.ne')]
  rw [map_aff_volume ha, Measure.restrict_smul, lintegral_smul_measure] at h
  rw [← h, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

theorem withDensity_comp_aff (ha : 0 < a) (g : ℂ → ℝ≥0∞) :
    (volume.withDensity fun z => ENNReal.ofReal (a ^ 2) * g (aff a m z)) =
      (volume.withDensity g).map (affInv a m) := by
  ext s hs
  rw [Measure.map_apply (measurable_affInv a m) hs, withDensity_apply _ ((measurable_affInv a m) hs),
    withDensity_apply _ hs, ← image_aff_eq_preimage ha.ne', setLIntegral_image_aff ha,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem testMeasPos_comp_aff (ha : 0 < a) (φ : ℂ → ℝ) :
    testMeasPos (fun z => a ^ 2 * φ (aff a m z)) = (testMeasPos φ).map (affInv a m) := by
  rw [testMeasPos, testMeasPos, ← withDensity_comp_aff ha]
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (by positivity)]

theorem testMeasNeg_comp_aff (ha : 0 < a) (φ : ℂ → ℝ) :
    testMeasNeg (fun z => a ^ 2 * φ (aff a m z)) = (testMeasNeg φ).map (affInv a m) := by
  rw [testMeasNeg, testMeasNeg, ← withDensity_comp_aff ha]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (by positivity), mul_neg]

/-! ### Dirichlet energy and the dual norm -/

/-- **Conformal invariance of the Dirichlet energy**: `E_U(f ∘ A) = E_{A(U)}(f)`. -/
theorem dirichletEnergyOn_comp_aff (ha : 0 < a) (U : Set ℂ) (f : ℂ → ℝ) :
    dirichletEnergyOn U (fun w => f (aff a m w)) = dirichletEnergyOn (aff a m '' U) f := by
  unfold dirichletEnergyOn
  congr 1
  simp_rw [norm_fderiv_comp_aff ha, mul_pow]
  rw [integral_const_mul, setIntegral_comp_aff ha (fun z => ‖fderiv ℝ f z‖ ^ 2) U, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

theorem comp_aff_mem_zeroSpace (ha : 0 < a) {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace (aff a m '' U)) :
    (fun w => f (aff a m w)) ∈ zeroSpace U := by
  obtain ⟨hc, hs, ht⟩ := hf
  refine ⟨contDiff_comp_aff hc, hasCompactSupport_comp_aff ha.ne' hs, ?_⟩
  rw [tsupport_comp_aff ha.ne']
  calc affInv a m '' tsupport f ⊆ affInv a m '' (aff a m '' U) := image_mono ht
    _ = U := affInv_image_aff_image ha.ne' U

theorem integral_map_aff (ha : a ≠ 0) (μ : Measure ℂ) (f : ℂ → ℝ) :
    ∫ z, f z ∂(μ.map (aff a m)) = ∫ z, f (aff a m z) ∂μ :=
  (measurableEmbedding_aff ha).integral_map f

/-- One direction of the dual-norm transport. -/
theorem dualNormSq_map_aff_le (ha : 0 < a) (U : Set ℂ) (μ : Measure ℂ) :
    dualNormSq (aff a m '' U) (zeroSpace (aff a m '' U)) (μ.map (aff a m)) ≤ dualNormSq U (zeroSpace U) μ := by
  unfold dualNormSq
  refine iSup₂_le fun f hf => ?_
  have hg : (fun w => f (aff a m w)) ∈ {g ∈ zeroSpace U | 0 < dirichletEnergyOn U g} := by
    refine ⟨comp_aff_mem_zeroSpace ha hf.1, ?_⟩
    rw [dirichletEnergyOn_comp_aff ha]
    exact hf.2
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun g (_ : g ∈ {g ∈ zeroSpace U | 0 < dirichletEnergyOn U g}) =>
    ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2 / dirichletEnergyOn U g)) _ hg)
  rw [integral_map_aff ha.ne', dirichletEnergyOn_comp_aff ha]

theorem map_map_aff_affInv (ha : a ≠ 0) (μ : Measure ℂ) : (μ.map (aff a m)).map (affInv a m) = μ := by
  rw [Measure.map_map (measurable_affInv a m) (measurable_aff a m)]
  have e : affInv a m ∘ aff a m = id := funext (affInv_aff ha)
  rw [e, Measure.map_id]

/-- **The dual Dirichlet norm under `A`**: `‖μ ∘ A⁻¹‖_{A(U)} = ‖μ‖_U`. -/
theorem dualNormSq_map_aff (ha : 0 < a) (U : Set ℂ) (μ : Measure ℂ) :
    dualNormSq (aff a m '' U) (zeroSpace (aff a m '' U)) (μ.map (aff a m)) = dualNormSq U (zeroSpace U) μ := by
  refine le_antisymm (dualNormSq_map_aff_le ha U μ) ?_
  have h := dualNormSq_map_aff_le (m := -m / a) (inv_pos.2 ha) (aff a m '' U) (μ.map (aff a m))
  have e1 : aff a⁻¹ (-m / a) '' (aff a m '' U) = U := affInv_image_aff_image ha.ne' U
  have e2 : (μ.map (aff a m)).map (aff a⁻¹ (-m / a)) = μ := map_map_aff_affInv ha.ne' μ
  rwa [e1, e2] at h

theorem dualCov_map_aff (ha : 0 < a) (U : Set ℂ) (μ ν : Measure ℂ) :
    dualCov (aff a m '' U) (zeroSpace (aff a m '' U)) (μ.map (aff a m)) (ν.map (aff a m)) =
      dualCov U (zeroSpace U) μ ν := by
  unfold dualCov
  rw [← Measure.map_add _ _ (measurable_aff a m), dualNormSq_map_aff ha, dualNormSq_map_aff ha,
    dualNormSq_map_aff ha]

/-- **The zero-boundary covariance under `A`**: `Cov_U(a² φ ∘ A, a² ψ ∘ A) = Cov_{A(U)}(φ, ψ)`. -/
theorem zeroGFFTestCov_comp_aff (ha : 0 < a) (U : Set ℂ) (φ ψ : ℂ → ℝ) :
    zeroGFFTestCov U (fun z => a ^ 2 * φ (aff a m z)) (fun z => a ^ 2 * ψ (aff a m z)) =
      zeroGFFTestCov (aff a m '' U) φ ψ := by
  have hU : U = aff a⁻¹ (-m / a) '' (aff a m '' U) := (affInv_image_aff_image ha.ne' U).symm
  unfold zeroGFFTestCov
  simp only [testMeasPos_comp_aff ha, testMeasNeg_comp_aff ha]
  conv_lhs => rw [hU]
  simp only [affInv, dualCov_map_aff (inv_pos.2 ha)]

/-- The covariance of `ℍ` is invariant under `φ ↦ a² φ ∘ A`. -/
theorem zeroGFFTestCov_affTest_H (ha : 0 < a) (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov H (affTest m ha φ) (affTest m ha ψ) = zeroGFFTestCov H φ ψ := by
  have e : ∀ χ : TestOn upperHalfPlaneOpens, ⇑(affTest m ha χ) = fun z => a ^ 2 * χ (aff a m z) :=
    fun _ => rfl
  rw [e, e, zeroGFFTestCov_comp_aff ha, aff_image_H ha]

/-! ### The zero-boundary GFF process and the GFF with boundary data under `A` -/

/-- **`φ ↦ X(a² φ ∘ A)` is a zero-boundary GFF process on `ℍ` when `X` is.** -/
theorem isZBGFFProcess_aff (ha : 0 < a) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : TestOn upperHalfPlaneOpens → Ω → ℝ} (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens X P) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X (affTest m ha φ) ω) P :=
  ⟨fun φ => hX.measurable _, hX.gaussian.comp_right (affTest m ha), fun φ => hX.centered _,
    fun φ ψ => by rw [hX.covariance_eq]; exact zeroGFFTestCov_affTest_H ha φ ψ⟩

theorem affInv_inv (ha : a ≠ 0) : affInv a⁻¹ (-m / a) = aff a m := by
  funext z
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  simp only [affInv, aff, inv_inv]
  congr 1
  push_cast
  field_simp

theorem affInv_ofReal (ha : a ≠ 0) (x : ℝ) : affInv a m (x : ℂ) = (((x - m) / a : ℝ) : ℂ) := by
  rw [affInv, aff_ofReal]
  congr 1
  field_simp
  ring

theorem tendsto_aff_nhdsWithin_H (ha : 0 < a) (z : ℂ) :
    Tendsto (aff a m) (𝓝[H] z) (𝓝[H] (aff a m z)) :=
  tendsto_nhdsWithin_iff.2 ⟨((continuous_aff a m).tendsto z).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hw => (aff_mem_H_iff ha).2 hw⟩

/-- **Bounded harmonic extensions under `A`**: if `u` extends `g` off `S`, and `g' x = g(a x + m)` with
`a x + m ∉ S` off `S'`, then `u ∘ A` extends `g'` off `S'`. -/
theorem _root_.InteractingSLE.IsBoundedHarmonicExtension.comp_aff (ha : 0 < a) {g g' : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hg : ∀ x, x ∉ S' → a * x + m ∉ S ∧ g' x = g (a * x + m)) :
    IsBoundedHarmonicExtension g' S' fun z => u (aff a m z) := by
  obtain ⟨hh, ⟨C, hC⟩, hlim⟩ := hu
  refine ⟨?_, ⟨C, fun z hz => hC _ ((aff_mem_H_iff ha).2 hz)⟩, fun x hx => ?_⟩
  · have h := harmonicOnNhd_comp_aff (m := m) ha.ne' hh
    rwa [affInv_image_H ha] at h
  · obtain ⟨hxS, hgx⟩ := hg x hx
    have hA := tendsto_aff_nhdsWithin_H (m := m) ha (x : ℂ)
    rw [aff_ofReal] at hA
    rw [hgx]
    exact (hlim _ hxS).comp hA

/-- The boundary data `y ↦ b((y − m)/a)` of the image picture. -/
def affData (a m : ℝ) (b : ℝ → ℝ) : ℝ → ℝ := fun y => b ((y - m) / a)

/-- The real affine map `x ↦ a x + m`. -/
def raff (a m : ℝ) (x : ℝ) : ℝ := a * x + m

theorem raff_injective (ha : a ≠ 0) : Function.Injective (raff a m) := fun x y h => by
  simp only [raff] at h
  have := mul_left_cancel₀ ha (add_right_cancel h)
  exact this

theorem affData_raff (ha : a ≠ 0) (b : ℝ → ℝ) (x : ℝ) : affData a m b (raff a m x) = b x := by
  simp only [affData, raff]
  congr 1
  field_simp
  ring

theorem raff_div (ha : a ≠ 0) (y : ℝ) : raff a m ((y - m) / a) = y := by
  simp only [raff]
  field_simp
  ring

/-- The mean term: `∫ u · (a² φ ∘ A) = ∫ (u ∘ A⁻¹) · φ`, written with `u = u' ∘ A`. -/
theorem integral_comp_aff_mul_affTest (ha : 0 < a) (u' : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, (fun y => u' (aff a m y)) z * affTest m ha φ z = ∫ z, u' z * φ z := by
  rw [integral_mul_affTest]
  congr 1
  funext z
  simp only [aff_affInv ha.ne']

/-- **The GFF with boundary data under `A`**: if `h` is a GFF on `ℍ` whose mean is the bounded harmonic extension of
`b` off `S`, then `h ∘ A⁻¹` is a GFF whose mean is the bounded harmonic extension of `b ∘ A⁻¹` off `A(S)`. -/
theorem _root_.InteractingSLE.IsGFFWithBoundaryData.affine (ha : 0 < a) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {S : Set ℝ} (hh : IsGFFWithBoundaryData P h b S) :
    IsGFFWithBoundaryData P (fun ω => affField m ha (h ω)) (affData a m b) (raff a m '' S) := by
  refine ⟨(measurable_affField ha).comp hh.1, fun u' hu' => ?_⟩
  have hu : IsBoundedHarmonicExtension b S fun z => u' (aff a m z) :=
    IsBoundedHarmonicExtension.comp_aff ha hu' fun x hx =>
      ⟨fun h' => hx ((raff_injective ha.ne').mem_set_image.1 h'), (affData_raff ha.ne' b x).symm⟩
  have hZ := isZBGFFProcess_aff (m := m) ha (hh.2 _ hu)
  have e : (fun φ ω => affField m ha (h ω) φ - ∫ z, u' z * φ z) = fun φ ω =>
      h ω (affTest m ha φ) - ∫ z, (fun y => u' (aff a m y)) z * affTest m ha φ z := by
    funext φ ω
    rw [integral_comp_aff_mul_affTest, affField_apply]
  rw [e]
  exact hZ

end FlowDilate

end InteractingSLE
