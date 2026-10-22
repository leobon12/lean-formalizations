import HigherDimLQGMetric.Frozen.AddConst
import HigherDimLQGMetric.Frozen.RestrictTo
import HigherDimLQGMetric.Frozen.TestRd0
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The distribution layer on `ℝ^d`: algebra of `ofCont`, `addFun`, `addConst`, `restrictTo`

Packet F1 (Phase A, block A1). Port of LQGMetric's 2D field algebra
(`lqg_metric/LQGMetric/Field/Measurable.lean` (`ofCont_apply`), `Field/GFFInvariance.lean`
(`addConst_apply`), `Field/GFFLaw.lean` (`addConst_addConst`), `Papers/MQ/SphereCover.lean`
(`ofCont_add`, `addFun_addFun`, `addFun_addConst`), `Papers/GM/S1/FieldAux.lean`
(`ofCont_zero`, `addFun_zero`), `Papers/DG/L2_2D.lean` (`restrictTo_*`),
`Papers/DFGPS/L2_8GffLoc.lean` (`testOnOf`)) from `ℂ` to `Rd d = EuclideanSpace ℝ (Fin d)`
(ruling M10), on top of the frozen definitions `ofCont`, `addFun`, `addConst`, `restrictTo`
(`HigherDimLQGMetric/Frozen/`).

* Pairings: `ofCont_apply` (`⟨f, φ⟩ = ∫ φ f`), `addFun_apply`, `addConst_apply`,
  `addConst_apply_of_integral_eq_zero` (mean-zero test functions do not see constants).
* `ofCont` is linear and injective (`ofCont_add`, `ofCont_smul`, ..., `ofCont_injective`), packaged
  as `ofContLM`.
* `addFun`/`addConst`: `addFun_zero`, `addFun_addFun`, `addConst_addConst`, `addFun_const`,
  `addFun_addConst`, `addConst_addFun`, cancellation lemmas.
* Restriction: `restrictTo` is linear (`restrictToLM`), `restrictTo_top`, the restriction
  `restrictOn` between open sets with `restrictOn_restrictTo` (composition), `restrictTo_addFun`,
  `restrictTo_ofCont_congr` (`(h + f)|_U` only sees `f` on `U`), and the characterization
  `restrictTo_eq_restrictTo_iff` through test functions supported in `U` (`testOnOf`).

Standard facts (no specific published source); own elementary proofs, as in the 2D layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Function TopologicalSpace
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Test functions -/

/-- Test functions are integrable. -/
theorem integrable_testOn {U : Opens (Rd d)} (φ : TestOn U) : Integrable (fun x => φ x) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- A test function times a continuous function is integrable. -/
theorem integrable_testOn_mul {U : Opens (Rd d)} (φ : TestOn U) {g : Rd d → ℝ}
    (hg : Continuous g) : Integrable (fun x => φ x * g x) :=
  (φ.continuous.mul hg).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

/-- The inclusion `𝓓(U) ⊆ 𝓓(ℝ^d)` (mathlib's `monoCLM`, the map inside `restrictTo`). -/
abbrev testIncl (U : Opens (Rd d)) : TestOn U →L[ℝ] TestRd d :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤)

@[simp]
theorem coe_testIncl {U : Opens (Rd d)} (φ : TestOn U) : ⇑(testIncl U φ) = ⇑φ := by
  rw [TestFunction.monoCLM_apply, ite_eq_left ⟨le_rfl, le_top⟩]

theorem testIncl_apply {U : Opens (Rd d)} (φ : TestOn U) (x : Rd d) : testIncl U φ x = φ x := by
  rw [coe_testIncl]

/-- A test function on `ℝ^d` whose support lies in `U`, as a test function on `U`. -/
def testOnOf (U : Opens (Rd d)) (φ : TestRd d) (hφ : tsupport (⇑φ) ⊆ U) : TestOn U where
  toFun := φ
  contDiff' := φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport
  tsupport_subset' := hφ

@[simp]
theorem coe_testOnOf (U : Opens (Rd d)) (φ : TestRd d) (hφ : tsupport (⇑φ) ⊆ U) :
    ⇑(testOnOf U φ hφ) = ⇑φ := rfl

@[simp]
theorem testIncl_testOnOf (U : Opens (Rd d)) (φ : TestRd d) (hφ : tsupport (⇑φ) ⊆ U) :
    testIncl U (testOnOf U φ hφ) = φ :=
  TestFunction.ext fun x => by rw [testIncl_apply, coe_testOnOf]

/-! ### `ofCont` -/

/-- `⟨f, φ⟩ = ∫ φ f` for a continuous `f` (the zero branch of `Distribution.ofFun` is never
taken). -/
theorem ofCont_apply (f : C(Rd d, ℝ)) (φ : TestRd d) : ofCont f φ = ∫ x, φ x * f x := by
  rw [ofCont, Distribution.ofFun_apply (f.continuous.locallyIntegrable.locallyIntegrableOn _)]
  rfl

@[simp]
theorem ofCont_zero : ofCont (0 : C(Rd d, ℝ)) = 0 := by
  rw [ofCont, ContinuousMap.coe_zero, Distribution.ofFun_zero]

theorem ofCont_add (f g : C(Rd d, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  rw [ofCont, ofCont, ofCont, ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

theorem ofCont_neg (f : C(Rd d, ℝ)) : ofCont (-f) = -ofCont f := by
  rw [ofCont, ofCont, ContinuousMap.coe_neg, Distribution.ofFun_neg]

theorem ofCont_sub (f g : C(Rd d, ℝ)) : ofCont (f - g) = ofCont f - ofCont g := by
  rw [sub_eq_add_neg, ofCont_add, ofCont_neg, sub_eq_add_neg]

theorem ofCont_smul (c : ℝ) (f : C(Rd d, ℝ)) : ofCont (c • f) = c • ofCont f := by
  rw [ofCont, ofCont, ContinuousMap.coe_smul, Distribution.ofFun_smul]

/-- `ofCont` as a linear map `C(ℝ^d, ℝ) →ₗ[ℝ] 𝒟'(ℝ^d)`. -/
def ofContLM (d : ℕ) : C(Rd d, ℝ) →ₗ[ℝ] DistRd d where
  toFun := ofCont
  map_add' := ofCont_add
  map_smul' := ofCont_smul

@[simp]
theorem ofContLM_apply (f : C(Rd d, ℝ)) : ofContLM d f = ofCont f := rfl

theorem ofCont_sum {ι : Type*} (s : Finset ι) (f : ι → C(Rd d, ℝ)) :
    ofCont (∑ i ∈ s, f i) = ∑ i ∈ s, ofCont (f i) :=
  map_sum (ofContLM d) f s

/-- `⟨c, φ⟩ = c ∫ φ`. -/
theorem ofCont_const_apply (c : ℝ) (φ : TestRd d) :
    ofCont (ContinuousMap.const (Rd d) c) φ = c * ∫ x, φ x := by
  rw [ofCont_apply, ← integral_const_mul]
  simp only [ContinuousMap.const_apply, mul_comm]

/-- A continuous function is determined by its distribution. -/
theorem ofCont_injective : Injective (ofCont : C(Rd d, ℝ) → DistRd d) := by
  intro f g hfg
  have hae : (⇑f : Rd d → ℝ) =ᵐ[(volume : Measure (Rd d)).restrict
      ((⊤ : Opens (Rd d)) : Set (Rd d))] ⇑g :=
    Distribution.ofFun_injective (f.continuous.locallyIntegrable.locallyIntegrableOn _)
      (g.continuous.locallyIntegrable.locallyIntegrableOn _) hfg
  rw [Opens.coe_top, Measure.restrict_univ] at hae
  exact ContinuousMap.ext (congrFun ((f.continuous.ae_eq_iff_eq volume g.continuous).1 hae))

theorem ofCont_inj {f g : C(Rd d, ℝ)} : ofCont f = ofCont g ↔ f = g :=
  ofCont_injective.eq_iff

/-! ### `addFun` -/

theorem addFun_def (h : DistRd d) (f : C(Rd d, ℝ)) : addFun h f = h + ofCont f := rfl

/-- `⟨h + f, φ⟩ = ⟨h, φ⟩ + ∫ φ f`. -/
theorem addFun_apply (h : DistRd d) (f : C(Rd d, ℝ)) (φ : TestRd d) :
    addFun h f φ = h φ + ∫ x, φ x * f x := by
  rw [addFun, add_apply, ofCont_apply]

@[simp]
theorem addFun_zero (h : DistRd d) : addFun h 0 = h := by
  rw [addFun, ofCont_zero, add_zero]

theorem zero_addFun (f : C(Rd d, ℝ)) : addFun 0 f = ofCont f := by
  rw [addFun, zero_add]

theorem addFun_addFun (h : DistRd d) (f g : C(Rd d, ℝ)) :
    addFun (addFun h f) g = addFun h (f + g) := by
  rw [addFun, addFun, addFun, ofCont_add, add_assoc]

theorem add_addFun (h k : DistRd d) (f : C(Rd d, ℝ)) : h + addFun k f = addFun (h + k) f := by
  rw [addFun, addFun, add_assoc]

theorem addFun_add (h k : DistRd d) (f g : C(Rd d, ℝ)) :
    addFun h f + addFun k g = addFun (h + k) (f + g) := by
  rw [addFun, addFun, addFun, ofCont_add]
  abel

theorem addFun_sub_addFun (h k : DistRd d) (f g : C(Rd d, ℝ)) :
    addFun h f - addFun k g = addFun (h - k) (f - g) := by
  rw [addFun, addFun, addFun, ofCont_sub]
  abel

theorem addFun_sub_ofCont (h : DistRd d) (f : C(Rd d, ℝ)) : addFun h f - ofCont f = h := by
  rw [addFun, add_sub_cancel_right]

theorem addFun_neg (h : DistRd d) (f : C(Rd d, ℝ)) : addFun (addFun h f) (-f) = h := by
  rw [addFun_addFun, add_neg_cancel, addFun_zero]

theorem addFun_eq_iff {h k : DistRd d} {f : C(Rd d, ℝ)} : addFun h f = k ↔ h = addFun k (-f) := by
  constructor
  · rintro rfl; rw [addFun_neg]
  · rintro rfl; rw [addFun_addFun, neg_add_cancel, addFun_zero]

theorem addFun_left_injective (f : C(Rd d, ℝ)) : Injective fun h : DistRd d => addFun h f :=
  fun h k hhk => by simpa only [addFun, add_left_inj] using hhk

theorem addFun_right_injective (h : DistRd d) : Injective (addFun h) := fun f g hfg =>
  ofCont_injective (by simpa only [addFun, add_right_inj] using hfg)

theorem smul_addFun (c : ℝ) (h : DistRd d) (f : C(Rd d, ℝ)) :
    c • addFun h f = addFun (c • h) (c • f) := by
  rw [addFun, addFun, ofCont_smul, smul_add]

/-! ### `addConst` -/

/-- `addFun h c = addConst h c` for the constant function `c` (definitional). -/
theorem addFun_const (h : DistRd d) (c : ℝ) :
    addFun h (ContinuousMap.const (Rd d) c) = addConst h c := rfl

theorem addConst_def (h : DistRd d) (c : ℝ) :
    addConst h c = h + ofCont (ContinuousMap.const (Rd d) c) := rfl

/-- `⟨h + c, φ⟩ = ⟨h, φ⟩ + c ∫ φ`. -/
theorem addConst_apply (h : DistRd d) (c : ℝ) (φ : TestRd d) :
    addConst h c φ = h φ + c * ∫ x, φ x := by
  rw [addConst_def, add_apply, ofCont_const_apply]

/-- Mean-zero test functions do not see additive constants. -/
theorem addConst_apply_of_integral_eq_zero (h : DistRd d) (c : ℝ) {φ : TestRd d}
    (hφ : ∫ x, φ x = 0) : addConst h c φ = h φ := by
  rw [addConst_apply, hφ, mul_zero, add_zero]

theorem addConst_apply_testRd0 (h : DistRd d) (c : ℝ) (φ : TestRd0 d) :
    addConst h c φ.1 = h φ.1 :=
  addConst_apply_of_integral_eq_zero h c φ.2

@[simp]
theorem addConst_zero (h : DistRd d) : addConst h 0 = h := by
  rw [addConst, ContinuousMap.const_zero, addFun_zero]

theorem addConst_addConst (h : DistRd d) (a b : ℝ) :
    addConst (addConst h a) b = addConst h (a + b) := by
  rw [addConst, addConst, addConst, addFun_addFun]
  rfl

theorem addConst_neg (h : DistRd d) (c : ℝ) : addConst (addConst h c) (-c) = h := by
  rw [addConst_addConst, add_neg_cancel, addConst_zero]

theorem addConst_eq_iff {h k : DistRd d} {c : ℝ} : addConst h c = k ↔ h = addConst k (-c) := by
  constructor
  · rintro rfl; rw [addConst_neg]
  · rintro rfl; rw [addConst_addConst, neg_add_cancel, addConst_zero]

theorem addConst_left_injective (c : ℝ) : Injective fun h : DistRd d => addConst h c :=
  addFun_left_injective _

theorem addFun_addConst (h : DistRd d) (f : C(Rd d, ℝ)) (c : ℝ) :
    addFun (addConst h c) f = addConst (addFun h f) c := by
  rw [addConst, addConst, addFun_addFun, addFun_addFun, add_comm]

theorem addConst_addFun (h : DistRd d) (f : C(Rd d, ℝ)) (c : ℝ) :
    addConst (addFun h f) c = addFun h (f + ContinuousMap.const (Rd d) c) := by
  rw [addConst, addFun_addFun]

theorem add_addConst (h k : DistRd d) (c : ℝ) : h + addConst k c = addConst (h + k) c :=
  add_addFun h k _

theorem smul_addConst (a : ℝ) (h : DistRd d) (c : ℝ) :
    a • addConst h c = addConst (a • h) (a * c) := by
  rw [addConst, addConst, smul_addFun]
  rfl

/-! ### Restriction to an open set -/

theorem restrictTo_apply (U : Opens (Rd d)) (h : DistRd d) (φ : TestOn U) :
    restrictTo U h φ = h (testIncl U φ) := rfl

/-- `(h|_U)(φ) = h(φ)` for a test function supported in `U`. -/
theorem restrictTo_testOnOf (U : Opens (Rd d)) (h : DistRd d) (φ : TestRd d)
    (hφ : tsupport (⇑φ) ⊆ U) : restrictTo U h (testOnOf U φ hφ) = h φ := by
  rw [restrictTo_apply, testIncl_testOnOf]

theorem restrictTo_add (U : Opens (Rd d)) (h k : DistRd d) :
    restrictTo U (h + k) = restrictTo U h + restrictTo U k := by
  ext φ
  simp only [restrictTo_apply, add_apply]

theorem restrictTo_neg (U : Opens (Rd d)) (h : DistRd d) :
    restrictTo U (-h) = -restrictTo U h := by
  ext φ
  simp only [restrictTo_apply, neg_apply]

theorem restrictTo_sub (U : Opens (Rd d)) (h k : DistRd d) :
    restrictTo U (h - k) = restrictTo U h - restrictTo U k := by
  ext φ
  simp only [restrictTo_apply, sub_apply]

theorem restrictTo_smul (U : Opens (Rd d)) (c : ℝ) (h : DistRd d) :
    restrictTo U (c • h) = c • restrictTo U h := by
  ext φ
  simp only [restrictTo_apply, smul_apply]

@[simp]
theorem restrictTo_zero (U : Opens (Rd d)) : restrictTo U (0 : DistRd d) = 0 := by
  ext φ
  simp only [restrictTo_apply, zero_apply]

/-- `h ↦ h|_U` as a linear map. -/
def restrictToLM (U : Opens (Rd d)) : DistRd d →ₗ[ℝ] DistOn U where
  toFun := restrictTo U
  map_add' := restrictTo_add U
  map_smul' := restrictTo_smul U

@[simp]
theorem restrictToLM_apply (U : Opens (Rd d)) (h : DistRd d) :
    restrictToLM U h = restrictTo U h := rfl

/-- Restriction to the whole space is the identity. -/
@[simp]
theorem restrictTo_top (h : DistRd d) : restrictTo ⊤ h = h := by
  ext φ
  rw [restrictTo_apply]
  congr 1
  exact TestFunction.ext fun x => testIncl_apply φ x

/-- `⟨f|_U, φ⟩ = ∫ φ f`. -/
theorem restrictTo_ofCont_apply (U : Opens (Rd d)) (f : C(Rd d, ℝ)) (φ : TestOn U) :
    restrictTo U (ofCont f) φ = ∫ x, φ x * f x := by
  rw [restrictTo_apply, ofCont_apply]
  simp only [testIncl_apply]

theorem restrictTo_addFun (U : Opens (Rd d)) (h : DistRd d) (f : C(Rd d, ℝ)) :
    restrictTo U (addFun h f) = restrictTo U h + restrictTo U (ofCont f) :=
  restrictTo_add U h (ofCont f)

theorem restrictTo_addFun_apply (U : Opens (Rd d)) (h : DistRd d) (f : C(Rd d, ℝ))
    (φ : TestOn U) : restrictTo U (addFun h f) φ = restrictTo U h φ + ∫ x, φ x * f x := by
  rw [restrictTo_addFun, add_apply, restrictTo_ofCont_apply]

theorem restrictTo_addConst_apply (U : Opens (Rd d)) (h : DistRd d) (c : ℝ) (φ : TestOn U) :
    restrictTo U (addConst h c) φ = restrictTo U h φ + c * ∫ x, φ x := by
  rw [restrictTo_apply, restrictTo_apply, addConst_apply]
  simp only [testIncl_apply]

/-- The restriction of a continuous function to `U` only depends on its values on `U`. -/
theorem restrictTo_ofCont_congr (U : Opens (Rd d)) {f g : C(Rd d, ℝ)}
    (hfg : EqOn (⇑f) (⇑g) U) : restrictTo U (ofCont f) = restrictTo U (ofCont g) := by
  ext φ
  rw [restrictTo_ofCont_apply, restrictTo_ofCont_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ (U : Set (Rd d))
  · simp only [hfg hx]
  · simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_mul]

theorem restrictTo_addFun_congr (U : Opens (Rd d)) (h : DistRd d) {f g : C(Rd d, ℝ)}
    (hfg : EqOn (⇑f) (⇑g) U) : restrictTo U (addFun h f) = restrictTo U (addFun h g) := by
  rw [restrictTo_addFun, restrictTo_addFun, restrictTo_ofCont_congr U hfg]

/-- Two distributions have the same restriction to `U` iff they agree on all test functions
supported in `U`. -/
theorem restrictTo_eq_restrictTo_iff (U : Opens (Rd d)) {h k : DistRd d} :
    restrictTo U h = restrictTo U k ↔ ∀ φ : TestRd d, tsupport (⇑φ) ⊆ U → h φ = k φ := by
  constructor
  · intro hk φ hφ
    rw [← restrictTo_testOnOf U h φ hφ, ← restrictTo_testOnOf U k φ hφ, hk]
  · intro hk
    ext φ
    rw [restrictTo_apply, restrictTo_apply]
    exact hk _ (by rw [coe_testIncl]; exact φ.tsupport_subset)

/-! ### Restriction between open sets (composition of restrictions) -/

/-- The inclusion `𝓓(V) ⊆ 𝓓(U)` for `V ≤ U`. -/
abbrev testInclOn {U V : Opens (Rd d)} (_hVU : V ≤ U) : TestOn V →L[ℝ] TestOn U :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := U)

@[simp]
theorem coe_testInclOn {U V : Opens (Rd d)} (hVU : V ≤ U) (φ : TestOn V) :
    ⇑(testInclOn hVU φ) = ⇑φ := by
  rw [TestFunction.monoCLM_apply, ite_eq_left ⟨le_rfl, hVU⟩]

/-- `k|_V ∈ 𝒟'(V)` for `k ∈ 𝒟'(U)` and `V ≤ U`. -/
def restrictOn {U V : Opens (Rd d)} (hVU : V ≤ U) (k : DistOn U) : DistOn V :=
  k.comp (testInclOn hVU)

theorem restrictOn_apply {U V : Opens (Rd d)} (hVU : V ≤ U) (k : DistOn U) (φ : TestOn V) :
    restrictOn hVU k φ = k (testInclOn hVU φ) := rfl

/-- Composition of restrictions: `(h|_U)|_V = h|_V`. -/
theorem restrictOn_restrictTo {U V : Opens (Rd d)} (hVU : V ≤ U) (h : DistRd d) :
    restrictOn hVU (restrictTo U h) = restrictTo V h := by
  ext φ
  rw [restrictOn_apply, restrictTo_apply, restrictTo_apply]
  congr 1
  refine TestFunction.ext fun x => ?_
  rw [testIncl_apply, testIncl_apply, coe_testInclOn]

theorem restrictOn_restrictOn {U V W : Opens (Rd d)} (hVU : V ≤ U) (hWV : W ≤ V)
    (k : DistOn U) : restrictOn hWV (restrictOn hVU k) = restrictOn (hWV.trans hVU) k := by
  ext φ
  rw [restrictOn_apply, restrictOn_apply, restrictOn_apply]
  congr 1
  refine TestFunction.ext fun x => ?_
  rw [coe_testInclOn, coe_testInclOn, coe_testInclOn]

@[simp]
theorem restrictOn_refl {U : Opens (Rd d)} (k : DistOn U) : restrictOn le_rfl k = k := by
  ext φ
  rw [restrictOn_apply]
  congr 1
  refine TestFunction.ext fun x => ?_
  rw [coe_testInclOn]

theorem restrictOn_add {U V : Opens (Rd d)} (hVU : V ≤ U) (k l : DistOn U) :
    restrictOn hVU (k + l) = restrictOn hVU k + restrictOn hVU l := by
  ext φ
  simp only [restrictOn_apply, add_apply]

theorem restrictOn_smul {U V : Opens (Rd d)} (hVU : V ≤ U) (c : ℝ) (k : DistOn U) :
    restrictOn hVU (c • k) = c • restrictOn hVU k := by
  ext φ
  simp only [restrictOn_apply, smul_apply]

/-- Equal restrictions to `U` give equal restrictions to every `V ≤ U`. -/
theorem restrictTo_eq_of_le {U V : Opens (Rd d)} (hVU : V ≤ U) {h k : DistRd d}
    (hk : restrictTo U h = restrictTo U k) : restrictTo V h = restrictTo V k := by
  rw [← restrictOn_restrictTo hVU, hk, restrictOn_restrictTo]

end HigherDimLQGMetric
