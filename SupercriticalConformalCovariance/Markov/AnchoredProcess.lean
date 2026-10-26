import SupercriticalConformalCovariance.Markov.GeneralPoincare

/-!
# Smooth-test extension of the Dirichlet projection with an interior mass anchor

The anchor removes the global constant from an arbitrary whole-plane test. The resulting
Hilbert-space vector represents the canonical zero-boundary pairing on every smooth global test.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovGerm LQGMetric.MarkovGauss
  QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

/-- Subtract the mass of a global test against an interior unit-mass test. -/
def meanZeroSub (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) : TestC0 :=
  ⟨φ - (∫ x, φ x) • extC V β, by
    have hiφ : Integrable (φ : ℂ → ℝ) :=
      φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hiβ : Integrable ((extC V β : TestC) : ℂ → ℝ) :=
      (extC V β).continuous.integrable_of_hasCompactSupport (extC V β).hasCompactSupport
    have hext : ∫ x, (extC V β : TestC) x = 1 := by
      rw [show ((extC V β : TestC) : ℂ → ℝ) = β from coe_extC β]
      exact hβ
    change ∫ x, (φ x - (∫ x, φ x) * (extC V β : TestC) x) = 0
    rw [integral_sub hiφ (hiβ.const_mul _), integral_const_mul, hext]
    ring⟩

/-- The global smooth-test projection, expressed using an interior mass anchor. -/
def anchoredPair (hh : IsWholePlaneGFF h P) (β : TestOn V)
    (hβ : ∫ x, β x = 1) (φ : TestC) : Lp ℝ 2 P :=
  projectedPair hh V (meanZeroSub β hβ φ) +
    (∫ x, φ x) • zbVec hh β

lemma anchoredPair_mem_cmRange (hh : IsWholePlaneGFF h P) (β : TestOn V)
    (hβ : ∫ x, β x = 1) (φ : TestC) : anchoredPair hh β hβ φ ∈ cmRange hh V :=
  Submodule.add_mem _ (projectedPair_mem_cmRange hh V _)
    (Submodule.smul_mem _ _ ⟨_, rfl⟩)

/-- The anchored projection represents integration against any smooth global test on `V`. -/
theorem inner_anchoredPair_gradLin (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) (f : zsSub V) :
    ⟪anchoredPair hh β hβ φ, cmIso hh V (gradLin V f)⟫ =
      ∫ x, φ x * f.1 x := by
  let m : ℝ := ∫ x, φ x
  have hp := inner_projectedPair_gradLin hh V (meanZeroSub β hβ φ) f
  have hb := inner_zbRiesz_gradFeat hV hpos β f.2
  have hb' : ⟪zbVec hh β, cmIso hh V (gradLin V f)⟫ =
      ∫ x, β x * f.1 x := by
    rw [zbVec, LinearIsometry.inner_map_map, Submodule.coe_inner]
    change ⟪zbRiesz V β, gradFeat V f.1⟫ = _
    rw [hb]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hφfi : Integrable (fun x => φ x * f.1 x) :=
    (φ.continuous.mul f.2.1.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  have hβfi : Integrable (fun x => β x * f.1 x) :=
    (β.continuous.mul f.2.1.continuous).integrable_of_hasCompactSupport
      β.hasCompactSupport.mul_right
  have hψeq : ∫ x, (meanZeroSub β hβ φ).1 x * f.1 x =
      (∫ x, φ x * f.1 x) - m * ∫ x, β x * f.1 x := by
    have e : (fun x => (meanZeroSub β hβ φ).1 x * f.1 x) =
        fun x => φ x * f.1 x - m * (β x * f.1 x) := by
      funext x
      simp only [meanZeroSub, FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      rw [show (extC V β : TestC) x = β x from congrFun (coe_extC β) x]
      ring
    rw [e, integral_sub hφfi (hβfi.const_mul m), integral_const_mul]
  rw [anchoredPair, inner_add_left, real_inner_smul_left, hp, hb', hψeq]
  ring

/-- The smooth-test projection is independent of the interior mass anchor. -/
theorem anchoredPair_anchor_indep (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β γ : TestOn V) (hβ : ∫ x, β x = 1) (hγ : ∫ x, γ x = 1)
    (φ : TestC) : anchoredPair hh β hβ φ = anchoredPair hh γ hγ φ := by
  obtain ⟨v, hv⟩ := anchoredPair_mem_cmRange hh β hβ φ
  obtain ⟨w, hw⟩ := anchoredPair_mem_cmRange hh γ hγ φ
  have he : (v : GradSpace V) = (w : GradSpace V) := by
    apply LQGMetric.eq_of_mem_gradClosure v.2 w.2
    intro f hf
    let f' : zsSub V := ⟨f, hf⟩
    have hβf := inner_anchoredPair_gradLin hh hV hpos β hβ φ f'
    have hγf := inner_anchoredPair_gradLin hh hV hpos γ hγ φ f'
    rw [← hv] at hβf
    rw [← hw] at hγf
    change ⟪cmIso hh V v, cmIso hh V (gradLin V f')⟫ = _ at hβf
    change ⟪cmIso hh V w, cmIso hh V (gradLin V f')⟫ = _ at hγf
    rw [LinearIsometry.inner_map_map, Submodule.coe_inner] at hβf hγf
    exact hβf.trans hγf.symm
  have he' : v = w := Subtype.ext he
  calc
    anchoredPair hh β hβ φ = cmIso hh V v := hv.symm
    _ = cmIso hh V w := by rw [he']
    _ = anchoredPair hh γ hγ φ := hw

theorem eq_of_cmRange_inner (hh : IsWholePlaneGFF h P)
    {a b : Lp ℝ 2 P} (ha : a ∈ cmRange hh V) (hb : b ∈ cmRange hh V)
    (he : ∀ f : zsSub V,
      ⟪a, cmIso hh V (gradLin V f)⟫ = ⟪b, cmIso hh V (gradLin V f)⟫) :
    a = b := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  have hsub : v = w := Subtype.ext (LQGMetric.eq_of_mem_gradClosure v.2 w.2
    fun f hf => by
      have he' := he ⟨f, hf⟩
      rw [← hv, ← hw] at he'
      change ⟪cmIso hh V v, cmIso hh V (gradLin V ⟨f, hf⟩)⟫ =
        ⟪cmIso hh V w, cmIso hh V (gradLin V ⟨f, hf⟩)⟫ at he'
      rw [LinearIsometry.inner_map_map, LinearIsometry.inner_map_map,
        Submodule.coe_inner, Submodule.coe_inner] at he'
      exact he')
  calc
    a = cmIso hh V v := hv.symm
    _ = cmIso hh V w := by rw [hsub]
    _ = b := hw

/-- The global anchored process restricts to the canonical zero-boundary process on `V`. -/
theorem anchoredPair_extC_eq_zbVec (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (η : TestOn V) :
    anchoredPair hh β hβ (extC V η) = zbVec hh η := by
  apply eq_of_cmRange_inner hh (anchoredPair_mem_cmRange hh β hβ _)
    (show zbVec hh η ∈ cmRange hh V from ⟨_, rfl⟩)
  intro f
  rw [inner_anchoredPair_gradLin hh hV hpos β hβ]
  have hb := inner_zbRiesz_gradFeat hV hpos η f.2
  rw [zbVec, LinearIsometry.inner_map_map, Submodule.coe_inner]
  change _ = ⟪zbRiesz V η, gradFeat V f.1⟫
  rw [hb]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    change (extC V η : TestC) x * f.1 x = f.1 x * η x
    rw [show (extC V η : TestC) x = η x from congrFun (coe_extC η) x]
    exact mul_comm _ _)

/-- The Dirichlet representative of a smooth global test exists and is unique, regardless of
the whole-plane GFF realization used to prove existence. -/
theorem existsUnique_riesz_test (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) :
    ∃! u : gradClosure (V : Set ℂ) (zeroSpace V),
      ∀ f ∈ zeroSpace V,
        ⟪(u : GradSpace V), gradFeat V f⟫ = ∫ x, φ x * f x := by
  obtain ⟨u, hu⟩ := exists_riesz_test_of_unit hh hV hpos β hβ φ
  refine ⟨u, hu, fun v hv => ?_⟩
  apply Subtype.ext
  apply LQGMetric.eq_of_mem_gradClosure v.2 u.2
  intro f hf
  rw [hv f hf, hu f hf]

/-- The unique smooth-test Dirichlet representative. The choice is from a unique witness. -/
def rTest (hh : IsWholePlaneGFF h P) (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) :
    gradClosure (V : Set ℂ) (zeroSpace V) :=
  (existsUnique_riesz_test hh hV hpos β hβ φ).exists.choose

theorem rTest_pair (hh : IsWholePlaneGFF h P) (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) (f : ℂ → ℝ)
    (hf : f ∈ zeroSpace V) :
    ⟪(rTest hh hV hpos β hβ φ : GradSpace V), gradFeat V f⟫ =
      ∫ x, φ x * f x :=
  (existsUnique_riesz_test hh hV hpos β hβ φ).exists.choose_spec f hf

theorem anchoredPair_eq_cmIso_rTest (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) :
    anchoredPair hh β hβ φ = cmIso hh V (rTest hh hV hpos β hβ φ) := by
  apply eq_of_cmRange_inner hh (anchoredPair_mem_cmRange hh β hβ _)
    (show cmIso hh V (rTest hh hV hpos β hβ φ) ∈ cmRange hh V from ⟨_, rfl⟩)
  intro f
  rw [inner_anchoredPair_gradLin hh hV hpos β hβ]
  rw [LinearIsometry.inner_map_map, Submodule.coe_inner]
  change _ = ⟪(rTest hh hV hpos β hβ φ : GradSpace V), gradFeat V f.1⟫
  rw [rTest_pair hh hV hpos β hβ φ f.1 f.2]

/-- The Dirichlet representative depends only on the domain and the smooth test. -/
theorem rTest_model_indep
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P')
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) :
    rTest hh hV hpos β hβ φ = rTest hh' hV hpos β hβ φ := by
  apply Subtype.ext
  apply LQGMetric.eq_of_mem_gradClosure (rTest hh hV hpos β hβ φ).2
    (rTest hh' hV hpos β hβ φ).2
  intro f hf
  rw [rTest_pair hh hV hpos β hβ φ f hf,
    rTest_pair hh' hV hpos β hβ φ f hf]

/-- The full smooth-test covariance of the projection is intrinsic to `V`. -/
theorem anchoredPair_inner_model_indep
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P')
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ ψ : TestC) :
    ⟪anchoredPair hh β hβ φ, anchoredPair hh β hβ ψ⟫ =
      ⟪anchoredPair hh' β hβ φ, anchoredPair hh' β hβ ψ⟫ := by
  rw [anchoredPair_eq_cmIso_rTest hh hV hpos β hβ φ,
    anchoredPair_eq_cmIso_rTest hh hV hpos β hβ ψ,
    anchoredPair_eq_cmIso_rTest hh' hV hpos β hβ φ,
    anchoredPair_eq_cmIso_rTest hh' hV hpos β hβ ψ,
    LinearIsometry.inner_map_map, LinearIsometry.inner_map_map,
    rTest_model_indep hh hh' hV hpos β hβ φ,
    rTest_model_indep hh hh' hV hpos β hβ ψ]

theorem anchoredPair_meanZero (hh : IsWholePlaneGFF h P)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (ψ : TestC0) :
    anchoredPair hh β hβ ψ.1 = projectedPair hh V ψ := by
  have hψ : meanZeroSub β hβ ψ.1 = ψ := by
    apply Subtype.ext
    simp [meanZeroSub, ψ.2]
  rw [anchoredPair, hψ, ψ.2, zero_smul, add_zero]

/-- Full mean-zero complement independence for the canonical smooth-test projection. -/
theorem indepFun_anchored_remainder (hh : IsWholePlaneGFF h P)
    (β : TestOn V) (hβ : ∫ x, β x = 1) :
    IndepFun (fun ω (φ : TestC0) => (anchoredPair hh β hβ φ.1 : Ω → ℝ) ω)
      (fun ω (ψ : TestC0) => (remainderPair hh V ψ : Ω → ℝ) ω) P := by
  simpa only [anchoredPair_meanZero hh β hβ] using
    indepFun_projected_remainder hh V

end SupercriticalConformalCovariance.Markov
