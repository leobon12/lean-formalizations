import SmallGammaGeodesics.NIC.Dual
import SmallGammaGeodesics.NIC.Laplacian
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# NIC, part 1 (T3): the Hilbert space `H_*`, the operator `τ̃`, the Gram operator `G`

Packet P-G1, target T3; GA2 D5 Step 4.

* `testL2` is linear (`testL2_add`, `testL2_smul`; from the linearity of `kerFun`), giving
  `testL2ₗ : 𝓓(ℂ) →ₗ L²(ℝ × ℂ)`.
* `testC0Sub`: mean-zero test functions as a submodule of `𝓓(ℂ)`;
  `Hstar := closure (J 𝓓₀)` inside `WNSpace = L²(ℝ × ℂ)` with `J = testL2` (complete);
  `jH : 𝓓₀ →ₗ Hstar` has dense range (`denseRange_jH`) and `⟪jH g, jH g'⟫ = logCov g g'`
  (`inner_jH`, from `GFFExist.inner_testL2_testL2`).
* `NearIdPair.transport0`: the transport `τ` as a linear equivalence of `𝓓₀`.
* `NearIdPair.tauH : Hstar ≃L[ℝ] Hstar`: the bounded extension of `J g ↦ J (τ g)`, with bounded
  inverse extending `J g ↦ J (τ_Ψ g)` (Mathlib's `LinearEquiv.extend`; `tauH_jH`,
  `tauH_symm_jH`); `κ⁻¹‖v‖² ≤ ‖τ̃ v‖² ≤ κ‖v‖²` on all of `Hstar` (`norm_sq_le_tauH`,
  `norm_tauH_sq_le`).
* `NearIdPair.gram := τ̃† τ̃`, self-adjoint, `⟪G v, w⟫ = ⟪τ̃ v, τ̃ w⟫`, and
  `‖G − 1‖ ≤ κ − 1 ≤ 6δ` (`norm_gram_sub_one_le`; Rayleigh quotients).
* **Key identity** (`gram_jH_cmTest`): `G (J ρ_χ) = J ρ_χ` for `ρ_χ = −Δχ/(2π)` and every test
  function `χ` supported in an open `U` on which `Ψ` is holomorphic. Proof: for mean-zero `g`,
  `⟪G J ρ_χ, J g⟫ = logCov (τ ρ_χ) (τ g) = logCov (τ g) ρ_{χ∘Φ} = ∫ τ g · (χ ∘ Φ) = ∫ g χ
  = logCov g ρ_χ = ⟪J ρ_χ, J g⟫` (`transport_cmTest`, Green's identity, change of variables),
  then density.
* Packet form (`C₅ = 12`, `δ = 2ε`): `norm_gram_sub_one_le_ofDiffeo`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.GFFExist LQGMetric.WhiteNoise

/-! ## Linearity of `testL2` -/

lemma integrable_testC (g : TestC) : Integrable (g : ℂ → ℝ) :=
  g.contDiff.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

lemma integrable_kerInner_integrand (g : TestC) {t : ℝ} (ht : 0 < t) (y : ℂ) :
    Integrable fun u => g u * (heatKernel (t / 2) u y -
      (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 y) t) := by
  have h := integrable_mul_heat (integrable_testC g) (by linarith : (0 : ℝ) < t / 2)
    ((Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ)) t) y
  refine h.congr (Eventually.of_forall fun u => ?_)
  by_cases h1 : t ∈ Ioi (1 : ℝ)
  · simp only [indicator_of_mem h1, one_mul]
  · simp only [indicator_of_notMem h1, zero_mul]

lemma kerFun_add (φ ψ : TestC) : kerFun (⇑(φ + ψ)) = kerFun φ + kerFun ψ := by
  funext q
  simp only [kerFun, Pi.add_apply]
  by_cases hq : q.1 ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hq, indicator_of_mem hq, indicator_of_mem hq, ← mul_add]
    congr 1
    unfold kerInner
    rw [← integral_add (integrable_kerInner_integrand φ hq q.2)
      (integrable_kerInner_integrand ψ hq q.2)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (φ u + ψ u) * _ = _
    ring
  · simp only [indicator_of_notMem hq, mul_zero, add_zero]

lemma kerFun_smul (c : ℝ) (φ : TestC) : kerFun (⇑(c • φ)) = c • kerFun φ := by
  funext q
  simp only [kerFun, Pi.smul_apply, smul_eq_mul]
  by_cases hq : q.1 ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hq, indicator_of_mem hq]
    unfold kerInner
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show Real.sqrt Real.pi * ((c * φ u) * _) = c * (Real.sqrt Real.pi * (φ u * _))
    ring
  · simp only [indicator_of_notMem hq, mul_zero]

lemma testL2_add (φ ψ : TestC) : testL2 (φ + ψ) = testL2 φ + testL2 ψ := by
  unfold testL2
  rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
  exact Eventually.of_forall fun q => congrFun (kerFun_add φ ψ) q

lemma testL2_smul (c : ℝ) (φ : TestC) : testL2 (c • φ) = c • testL2 φ := by
  unfold testL2
  rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
  exact Eventually.of_forall fun q => congrFun (kerFun_smul c φ) q

/-- `J = testL2` as a linear map `𝓓(ℂ) →ₗ L²(ℝ × ℂ)` -/
def testL2ₗ : TestC →ₗ[ℝ] WNSpace where
  toFun := testL2
  map_add' := testL2_add
  map_smul' := testL2_smul

@[simp] lemma testL2ₗ_apply (φ : TestC) : testL2ₗ φ = testL2 φ := rfl

/-! ## The Hilbert space `H_*` -/

/-- mean-zero test functions, as a submodule of `𝓓(ℂ)` -/
def testC0Sub : Submodule ℝ TestC where
  carrier := {g | ∫ x, g x = 0}
  add_mem' {f g} hf hg := by
    show ∫ x, (f x + g x) = 0
    rw [integral_add (integrable_testC f) (integrable_testC g), hf, hg, add_zero]
  zero_mem' := by
    show ∫ _ : ℂ, (0 : ℝ) = 0
    simp
  smul_mem' c g hg := by
    show ∫ x, c * g x = 0
    rw [integral_const_mul, hg, mul_zero]

lemma mem_testC0Sub {g : TestC} : g ∈ testC0Sub ↔ ∫ x, g x = 0 := Iff.rfl

/-- `ρ_χ = −Δχ/(2π)` as an element of `𝓓₀` -/
def cmTest0' (χ : TestC) : testC0Sub := ⟨cmTest χ, integral_cmTest χ⟩

/-- **The Hilbert space** `H_* := closure J(𝓓₀) ⊆ L²(ℝ × ℂ)` -/
def Hstar : Submodule ℝ WNSpace := (testC0Sub.map testL2ₗ).topologicalClosure

instance : CompleteSpace Hstar :=
  have : IsClosed (Hstar : Set WNSpace) := Submodule.isClosed_topologicalClosure _
  this.completeSpace_coe

lemma testL2_mem_Hstar (g : testC0Sub) : testL2 g ∈ Hstar :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem g.2)

/-- `J : 𝓓₀ →ₗ H_*` -/
def jH : testC0Sub →ₗ[ℝ] Hstar :=
  LinearMap.codRestrict Hstar (testL2ₗ ∘ₗ testC0Sub.subtype) testL2_mem_Hstar

@[simp] lemma coe_jH (g : testC0Sub) : (jH g : WNSpace) = testL2 g := rfl

/-- `⟪J g, J g'⟫ = logCov g g'` -/
lemma inner_jH (g g' : testC0Sub) : ⟪jH g, jH g'⟫ = logCov g g' := by
  rw [Submodule.coe_inner, coe_jH, coe_jH]
  exact inner_testL2_testL2 g g' g.2 g'.2

lemma norm_jH_sq (g : testC0Sub) : ‖jH g‖ ^ 2 = logCov g g := by
  rw [← real_inner_self_eq_norm_sq, inner_jH]

/-- `J(𝓓₀)` is dense in `H_*` -/
theorem denseRange_jH : DenseRange jH := by
  intro v
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
  have hv : (v : WNSpace) ∈ closure (testC0Sub.map testL2ₗ : Set WNSpace) := by
    rw [← Submodule.topologicalClosure_coe]; exact v.2
  refine closure_mono ?_ hv
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨jH ⟨g, hg⟩, ⟨_, rfl⟩, rfl⟩

/-- two vectors with the same inner products against `J(𝓓₀)` are equal -/
lemma eq_of_inner_jH {v v' : Hstar} (h : ∀ g : testC0Sub, ⟪v, jH g⟫ = ⟪v', jH g⟫) : v = v' := by
  have h1 : ∀ w : Hstar, ⟪v - v', w⟫ = 0 := fun w =>
    denseRange_jH.induction_on w (isClosed_eq (continuous_const.inner continuous_id)
      continuous_const) fun g => by rw [inner_sub_left, h g, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (h1 _))

/-! ## The transport on `𝓓₀` and its extension `τ̃` -/

namespace NearIdPair

variable (D : NearIdPair)

/-- the transport as a linear equivalence of `𝓓₀` -/
def transport0 : testC0Sub ≃ₗ[ℝ] testC0Sub where
  toFun g := ⟨D.transport g, D.integral_transport_eq_zero g.2⟩
  invFun g := ⟨D.symm.transport g, D.symm.integral_transport_eq_zero g.2⟩
  map_add' f g := Subtype.ext (map_add D.transport (f : TestC) g)
  map_smul' c g := Subtype.ext (map_smul D.transport c (g : TestC))
  left_inv g := Subtype.ext (D.transport_symm_transport g)
  right_inv g := Subtype.ext (D.transport_transport_symm g)

@[simp] lemma coe_transport0 (g : testC0Sub) : (D.transport0 g : TestC) = D.transport g := rfl

@[simp] lemma coe_transport0_symm (g : testC0Sub) :
    (D.transport0.symm g : TestC) = D.symm.transport g := rfl

lemma norm_jH_transport0_le (g : testC0Sub) :
    ‖jH (D.transport0 g)‖ ≤ kappa D.δ * ‖jH g‖ := by
  have hκ := one_le_kappa D.δ_nonneg
  have h1 : ‖jH (D.transport0 g)‖ ^ 2 ≤ kappa D.δ * ‖jH g‖ ^ 2 := by
    rw [norm_jH_sq, norm_jH_sq]
    exact D.logCov_transport_le g g.2
  have h2 : ‖jH (D.transport0 g)‖ ^ 2 ≤ (kappa D.δ * ‖jH g‖) ^ 2 := by
    rw [mul_pow]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

lemma norm_jH_transport0_symm_le (g : testC0Sub) :
    ‖jH (D.transport0.symm g)‖ ≤ kappa D.δ * ‖jH g‖ :=
  D.symm.norm_jH_transport0_le g

/-- **T3**: `τ̃ : H_* ≃L H_*`, the bounded extension of `J g ↦ J (τ g)`, with bounded inverse. -/
def tauH : Hstar ≃L[ℝ] Hstar :=
  D.transport0.extend jH jH denseRange_jH ⟨_, D.norm_jH_transport0_le⟩ denseRange_jH
    ⟨_, D.norm_jH_transport0_symm_le⟩

/-- `τ̃ (J g) = J (τ g)` -/
theorem tauH_jH (g : testC0Sub) : D.tauH (jH g) = jH (D.transport0 g) :=
  LinearEquiv.extend_eq _ _ _ _ _ _ _ g

/-- in `L²(ℝ × ℂ)`: `τ̃ (testL2 g) = testL2 (τ g)` -/
theorem coe_tauH_jH (g : testC0Sub) : (D.tauH (jH g) : WNSpace) = testL2 (D.transport g) := by
  rw [tauH_jH, coe_jH, coe_transport0]

/-- `τ̃⁻¹ (J g) = J (τ_Ψ g)` -/
theorem tauH_symm_jH (g : testC0Sub) : D.tauH.symm (jH g) = jH (D.transport0.symm g) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, tauH_jH, LinearEquiv.apply_symm_apply]

/-- `‖τ̃ v‖² ≤ κ ‖v‖²` -/
theorem norm_tauH_sq_le (v : Hstar) : ‖D.tauH v‖ ^ 2 ≤ kappa D.δ * ‖v‖ ^ 2 :=
  denseRange_jH.induction_on v
    (isClosed_le ((D.tauH.continuous.norm).pow 2) (continuous_const.mul (continuous_norm.pow 2)))
    fun g => by
      rw [tauH_jH, norm_jH_sq, norm_jH_sq]
      exact D.logCov_transport_le g g.2

/-- `‖v‖² ≤ κ ‖τ̃ v‖²` -/
theorem norm_sq_le_tauH (v : Hstar) : ‖v‖ ^ 2 ≤ kappa D.δ * ‖D.tauH v‖ ^ 2 :=
  denseRange_jH.induction_on v
    (isClosed_le (continuous_norm.pow 2) (continuous_const.mul ((D.tauH.continuous.norm).pow 2)))
    fun g => by
      rw [tauH_jH, norm_jH_sq, norm_jH_sq]
      exact D.logCov_le_logCov_transport g g.2

/-! ## The Gram operator -/

/-- **The Gram operator** `G := τ̃† τ̃`, i.e. `⟪G v, w⟫ = ⟪τ̃ v, τ̃ w⟫`. -/
def gram : Hstar →L[ℝ] Hstar :=
  star (D.tauH : Hstar →L[ℝ] Hstar) * (D.tauH : Hstar →L[ℝ] Hstar)

lemma isSelfAdjoint_gram : IsSelfAdjoint D.gram :=
  IsSelfAdjoint.star_mul_self (D.tauH : Hstar →L[ℝ] Hstar)

lemma inner_gram (v w : Hstar) : ⟪D.gram v, w⟫ = ⟪D.tauH v, D.tauH w⟫ := by
  show ⟪star (D.tauH : Hstar →L[ℝ] Hstar) (D.tauH v), w⟫ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rfl

lemma inner_gram_self (v : Hstar) : ⟪D.gram v, v⟫ = ‖D.tauH v‖ ^ 2 := by
  rw [inner_gram, real_inner_self_eq_norm_sq]

lemma isSelfAdjoint_gram_sub_one : IsSelfAdjoint (D.gram - 1) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub,
    ContinuousLinearMap.isSelfAdjoint_iff'.1 D.isSelfAdjoint_gram]
  rw [show (1 : Hstar →L[ℝ] Hstar) = ContinuousLinearMap.id ℝ Hstar from rfl,
    ContinuousLinearMap.adjoint_id]

lemma isSymmetric_gram_sub_one :
    ((D.gram - 1 : Hstar →L[ℝ] Hstar) : Hstar →ₗ[ℝ] Hstar).IsSymmetric :=
  D.isSelfAdjoint_gram_sub_one.isSymmetric

/-- `|a − n| ≤ (κ − 1) n` from `a ≤ κ n`, `n ≤ κ a`, `κ ≥ 1`, `a, n ≥ 0` -/
lemma abs_sub_le_of_two_sided {a n κ : ℝ} (hn : 0 ≤ n) (hκ : 1 ≤ κ)
    (h1 : a ≤ κ * n) (h2 : n ≤ κ * a) : |a - n| ≤ (κ - 1) * n := by
  rw [abs_le]
  constructor
  · have hκ0 : 0 < κ := by linarith
    have h3 : κ * ((2 - κ) * n) ≤ κ * a := by nlinarith [sq_nonneg (κ - 1)]
    have h4 : (2 - κ) * n ≤ a := le_of_mul_le_mul_left h3 hκ0
    linarith
  · linarith

/-- **T3**: `‖G − 1‖ ≤ κ(δ) − 1`. -/
theorem norm_gram_sub_one_le : ‖D.gram - 1‖ ≤ kappa D.δ - 1 := by
  have hκ := one_le_kappa D.δ_nonneg
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ D.isSymmetric_gram_sub_one]
  refine ciSup_le fun x => ?_
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real]
  have hin : ⟪(D.gram - 1) x, x⟫ = ‖D.tauH x‖ ^ 2 - ‖x‖ ^ 2 := by
    rw [sub_apply, inner_sub_left, inner_gram_self, one_apply_eq_self,
      real_inner_self_eq_norm_sq]
  rw [hin]
  by_cases hx : ‖x‖ = 0
  · rw [hx]; simp; linarith
  · have hx2 : 0 < ‖x‖ ^ 2 := by positivity
    rw [abs_div, abs_of_pos hx2, div_le_iff₀ hx2]
    exact abs_sub_le_of_two_sided (sq_nonneg _) hκ (D.norm_tauH_sq_le x)
      (D.norm_sq_le_tauH x)

/-- `‖G − 1‖ ≤ 6δ ≤ 3/8` -/
theorem norm_gram_sub_one_le' : ‖D.gram - 1‖ ≤ 6 * D.δ :=
  D.norm_gram_sub_one_le.trans (by linarith [kappa_le D.δ_nonneg D.δ_le])

/-- **T3, key identity**: `G (J ρ_χ) = J ρ_χ` for `ρ_χ = −Δχ/(2π)`, `tsupport χ ⊆ U`, where `U` is
open and `Ψ` is holomorphic on `U`. -/
theorem gram_jH_cmTest {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U) (χ : TestC)
    (hχ : tsupport (χ : ℂ → ℝ) ⊆ U) : D.gram (jH (cmTest0' χ)) = jH (cmTest0' χ) := by
  refine eq_of_inner_jH fun g => ?_
  rw [inner_gram, tauH_jH, tauH_jH, inner_jH, inner_jH]
  show logCov (D.transport (cmTest χ)) (D.transport g) = logCov (cmTest χ) g
  have hg := g.2
  rw [D.transport_cmTest hU hΨ χ hχ,
    logCov_comm _ _ (integral_cmTest _) (D.integral_transport_eq_zero hg), logCov_cmTest_right,
    logCov_comm _ _ (integral_cmTest _) hg, logCov_cmTest_right, D.integral_transport_mul]
  simp only [compTest_apply, D.right_inv]

end NearIdPair

/-- **T3 in the packet's form** (`C₅ = 12`): `‖G − 1‖ ≤ 12 ε` for the pair of
`CC.IsNearIdDiffeo Φ Ψ U ε`, `0 ≤ ε ≤ 1/32`. -/
theorem norm_gram_sub_one_le_ofDiffeo {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε : ℝ}
    (hΦ : CC.IsNearIdDiffeo Φ Ψ U ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 32) :
    ‖(NearIdPair.ofDiffeo hΦ hε0 hε).gram - 1‖ ≤ 12 * ε := by
  have := (NearIdPair.ofDiffeo hΦ hε0 hε).norm_gram_sub_one_le'
  rw [NearIdPair.ofDiffeo_δ] at this
  linarith

end NIC
end SmallGammaGeodesics
