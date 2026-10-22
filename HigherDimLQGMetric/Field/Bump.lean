import HigherDimLQGMetric.Field.Measurable
import HigherDimLQGMetric.Frozen.BumpTest
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The radial mollifiers `bumpTest n x` on `ℝ^d`

Packet F1 (basic sphere-average layer). Port of LQGMetric's
`lqg_metric/LQGMetric/Field/Measurable.lean`
(`testFamK`, `continuous_testFamK`), `Field/MeasurableAvg.lean` (`bumpTest_apply_eq`,
`continuous_bumpTest`, `measurable_apply_bumpTest`) and `Field/CircleAvgCont.lean`
(`tendsto_ofCont_bumpTest`, `abs_ofCont_bumpTest_le`) from `ℂ` to `Rd d` (ruling M10). The 2D
mollifier was mathlib's `ContDiffBump.normed`; the frozen `bumpTest` uses the explicit radial
profile `radialProfile d` (`ρ(y) = smoothTransition(2 - ‖y‖)`), so the facts below are proved from
the explicit formula:

* `radialProfile`: values in `[0,1]`, `= 1` on `B̄(0,1)`, `= 0` off `B(0,2)`, radial, positive
  integral;
* closed form `bumpTest_apply`: `ψ_{n,x}(y) = (2^{n+1})^d (∫ρ)⁻¹ ρ(2^{n+1}(y - x))`; unit mass
  (`integral_bumpTest`), nonnegativity, support in `B(x, 2^{-n})`;
* translation `bumpTest_add`, `testAffinePull_one_bumpTest`, and the exact dyadic rescaling
  `smul_testAffinePull_two_pow_bumpTest`, `smul_testAffinePull_two_pow_inv_bumpTest`
  (`2^{-kd} ψ_{n+k,x}((· - z)/2^k) = ψ_{n, 2^k x + z}`);
* `ofCont f (bumpTest n x) → f x` (`tendsto_ofCont_bumpTest`) with the bound
  `abs_ofCont_bumpTest_le`;
* `x ↦ ψ_{n,x}` is continuous into `𝓓(ℝ^d)` (`continuous_bumpTest`), so `(h, x) ↦ ⟨h, ψ_{n,x}⟩` is
  jointly measurable (`measurable_apply_bumpTest`).

Standard facts; own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Function TopologicalSpace Filter Topology Metric
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The radial profile -/

theorem radialProfile_apply (y : Rd d) :
    radialProfile d y = Real.smoothTransition ((2 - ‖y‖) / (2 - 1)) := rfl

theorem radialProfile_nonneg (y : Rd d) : 0 ≤ radialProfile d y :=
  ((ContDiffBumpBase.ofInnerProductSpace (Rd d)).mem_Icc 2 y).1

theorem radialProfile_le_one (y : Rd d) : radialProfile d y ≤ 1 :=
  ((ContDiffBumpBase.ofInnerProductSpace (Rd d)).mem_Icc 2 y).2

theorem radialProfile_eq_one {y : Rd d} (hy : ‖y‖ ≤ 1) : radialProfile d y = 1 :=
  (ContDiffBumpBase.ofInnerProductSpace (Rd d)).eq_one 2 one_lt_two y hy

theorem radialProfile_eq_zero {y : Rd d} (hy : 2 ≤ ‖y‖) : radialProfile d y = 0 := by
  have hs := (ContDiffBumpBase.ofInnerProductSpace (Rd d)).support 2 one_lt_two
  have : y ∉ support ((ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun 2) := by
    rw [hs, mem_ball, dist_zero_right]; exact not_lt.2 hy
  exact notMem_support.1 this

theorem radialProfile_eq_of_norm_eq {y w : Rd d} (h : ‖y‖ = ‖w‖) :
    radialProfile d y = radialProfile d w := by
  rw [radialProfile_apply, radialProfile_apply, h]

theorem integrable_radialProfile : Integrable (fun y => radialProfile d y) :=
  integrable_testOn (radialProfile d)

theorem integral_radialProfile_pos : 0 < ∫ y, radialProfile d y := by
  rw [integral_pos_iff_support_of_nonneg (fun y => radialProfile_nonneg y)
    integrable_radialProfile]
  have hball : ball (0 : Rd d) 1 ⊆ support fun y => radialProfile d y := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    simp [mem_support, radialProfile_eq_one hw.le]
  exact lt_of_lt_of_le (measure_ball_pos volume (0 : Rd d) one_pos) (measure_mono hball)

/-! ### Closed form of `bumpTest` -/

/-- The normalizing integral: `∫ ρ(c(w - x)) dw = c^{-d} ∫ ρ` for `c = 2^{n+1}`. -/
theorem integral_radialProfile_smul_sub (n : ℕ) (x : Rd d) :
    ∫ w, radialProfile d ((2 : ℝ) ^ (n + 1) • (w - x)) =
      (((2 : ℝ) ^ (n + 1)) ^ d)⁻¹ * ∫ w, radialProfile d w := by
  rw [integral_sub_right_eq_self (fun w => radialProfile d ((2 : ℝ) ^ (n + 1) • w)) x,
    Measure.integral_comp_smul_of_nonneg volume (fun w => radialProfile d w) _
      (hR := by positivity),
    finrank_rd, smul_eq_mul]

/-- `ψ_{n,x}(y) = (2^{n+1})^d (∫ ρ)⁻¹ ρ(2^{n+1}(y - x))`. -/
theorem bumpTest_apply (n : ℕ) (x y : Rd d) :
    bumpTest n x y = ((2 : ℝ) ^ (n + 1)) ^ d * (∫ w, radialProfile d w)⁻¹ *
      radialProfile d ((2 : ℝ) ^ (n + 1) • (y - x)) := by
  change (∫ w, radialProfile d ((2 : ℝ) ^ (n + 1) • (w - x)))⁻¹ *
      radialProfile d ((2 : ℝ) ^ (n + 1) • (y - x)) = _
  rw [integral_radialProfile_smul_sub, mul_inv, inv_inv]

theorem bumpTest_nonneg (n : ℕ) (x y : Rd d) : 0 ≤ bumpTest n x y := by
  rw [bumpTest_apply]
  exact mul_nonneg (mul_nonneg (pow_nonneg (pow_nonneg zero_le_two _) _)
    (inv_nonneg.2 integral_radialProfile_pos.le)) (radialProfile_nonneg _)

/-- `ψ_{n,x}` vanishes outside `B(x, 2^{-n})`. -/
theorem bumpTest_eq_zero {n : ℕ} {x y : Rd d} (hy : ((2 : ℝ) ^ n)⁻¹ ≤ ‖y - x‖) :
    bumpTest n x y = 0 := by
  rw [bumpTest_apply, radialProfile_eq_zero, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), pow_succ]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  calc (2 : ℝ) = 2 ^ n * 2 * (2 ^ n)⁻¹ := by field_simp
    _ ≤ 2 ^ n * 2 * ‖y - x‖ := by gcongr

theorem support_bumpTest_subset (n : ℕ) (x : Rd d) :
    support (⇑(bumpTest n x)) ⊆ ball x ((2 : ℝ) ^ n)⁻¹ := by
  intro y hy
  rw [mem_ball, dist_eq_norm]
  by_contra h
  exact hy (bumpTest_eq_zero (not_lt.1 h))

theorem tsupport_bumpTest_subset (n : ℕ) (x : Rd d) :
    tsupport (⇑(bumpTest n x)) ⊆ closedBall x ((2 : ℝ) ^ n)⁻¹ :=
  closure_minimal ((support_bumpTest_subset n x).trans ball_subset_closedBall)
    isClosed_closedBall

/-- Unit mass. -/
theorem integral_bumpTest (n : ℕ) (x : Rd d) : ∫ y, bumpTest n x y = 1 := by
  change ∫ y, (∫ w, radialProfile d ((2 : ℝ) ^ (n + 1) • (w - x)))⁻¹ *
      radialProfile d ((2 : ℝ) ^ (n + 1) • (y - x)) = 1
  rw [integral_const_mul]
  refine inv_mul_cancel₀ ?_
  rw [integral_radialProfile_smul_sub]
  exact mul_ne_zero (inv_ne_zero (by positivity)) integral_radialProfile_pos.ne'

/-! ### Translations and dyadic rescalings -/

theorem bumpTest_apply_sub (n : ℕ) (x y : Rd d) : bumpTest n x y = bumpTest n 0 (y - x) := by
  rw [bumpTest_apply, bumpTest_apply, sub_zero]

theorem bumpTest_add (n : ℕ) (x z y : Rd d) : bumpTest n (x + z) y = bumpTest n x (y - z) := by
  rw [bumpTest_apply, bumpTest_apply, sub_sub, add_comm z x]

/-- `ψ_{n,x}(· - z) = ψ_{n, x + z}`. -/
theorem testAffinePull_one_bumpTest (z : Rd d) (n : ℕ) (x : Rd d) :
    testAffinePull 1 z (bumpTest n x) = bumpTest n (x + z) :=
  TestFunction.ext fun y => by rw [testAffinePull_one_apply, bumpTest_add]

/-- Exact dyadic rescaling: `2^{-kd} ψ_{n+k,x}((· - z)/2^k) = ψ_{n, 2^k x + z}`. -/
theorem smul_testAffinePull_two_pow_bumpTest (n k : ℕ) (z x : Rd d) :
    (((2 : ℝ) ^ k) ^ d)⁻¹ • testAffinePull ((2 : ℝ) ^ k) z (bumpTest (n + k) x) =
      bumpTest n ((2 : ℝ) ^ k • x + z) := by
  have hb : (2 : ℝ) ^ k ≠ 0 := by positivity
  refine TestFunction.ext fun y => ?_
  rw [smul_apply, smul_eq_mul, testAffinePull_apply hb, bumpTest_apply, bumpTest_apply]
  have e1 : (2 : ℝ) ^ (n + k + 1) = 2 ^ (n + 1) * 2 ^ k := by rw [← pow_add]; ring_nf
  have e2 : (2 : ℝ) ^ (n + k + 1) • (((2 : ℝ) ^ k)⁻¹ • (y - z) - x) =
      (2 : ℝ) ^ (n + 1) • (y - ((2 : ℝ) ^ k • x + z)) := by
    rw [e1, smul_sub, smul_smul, mul_assoc, mul_inv_cancel₀ hb, mul_one, mul_smul,
      smul_sub, smul_sub, smul_add]
    abel
  rw [e2, e1, mul_pow, ← mul_assoc, ← mul_assoc, mul_comm (((2 : ℝ) ^ k) ^ d)⁻¹,
    mul_assoc (((2 : ℝ) ^ (n + 1)) ^ d), mul_inv_cancel₀ (pow_ne_zero d hb), mul_one]

/-- Exact dyadic rescaling, the other direction:
`2^{kd} ψ_{n,x}(2^k(· - z)) = ψ_{n+k, 2^{-k} x + z}`. -/
theorem smul_testAffinePull_two_pow_inv_bumpTest (n k : ℕ) (z x : Rd d) :
    ((((2 : ℝ) ^ k)⁻¹) ^ d)⁻¹ • testAffinePull ((2 : ℝ) ^ k)⁻¹ z (bumpTest n x) =
      bumpTest (n + k) (((2 : ℝ) ^ k)⁻¹ • x + z) := by
  have hb : (2 : ℝ) ^ k ≠ 0 := by positivity
  refine TestFunction.ext fun y => ?_
  rw [smul_apply, smul_eq_mul, testAffinePull_apply (inv_ne_zero hb), bumpTest_apply,
    bumpTest_apply, inv_inv]
  have e1 : (2 : ℝ) ^ (n + k + 1) = 2 ^ (n + 1) * 2 ^ k := by rw [← pow_add]; ring_nf
  have e2 : (2 : ℝ) ^ (n + 1) • ((2 : ℝ) ^ k • (y - z) - x) =
      (2 : ℝ) ^ (n + k + 1) • (y - (((2 : ℝ) ^ k)⁻¹ • x + z)) := by
    rw [e1, mul_smul, smul_sub ((2 : ℝ) ^ k) y (((2 : ℝ) ^ k)⁻¹ • x + z), smul_add, smul_smul,
      mul_inv_cancel₀ hb, one_smul, smul_sub, smul_sub, smul_sub, smul_sub, smul_add]
    abel
  rw [e2, e1, inv_pow, inv_inv, mul_pow]
  ring

/-! ### Pairing with continuous functions -/

theorem ofCont_bumpTest_sub (f : C(Rd d, ℝ)) (n : ℕ) (x : Rd d) :
    ofCont f (bumpTest n x) - f x = ∫ y, bumpTest n x y * (f y - f x) := by
  rw [ofCont_apply]
  have h1 : f x = ∫ y, bumpTest n x y * f x := by
    rw [integral_mul_const, integral_bumpTest, one_mul]
  rw [h1, ← integral_sub (integrable_testOn_mul _ f.continuous)
    ((integrable_testOn (bumpTest n x)).mul_const _)]
  · simp only [mul_sub]
    rw [← h1]

/-- If `|f - f(x)| ≤ ε` on `B(x, 2^{-n})` then `|⟨f, ψ_{n,x}⟩ - f(x)| ≤ ε`. -/
theorem abs_ofCont_bumpTest_sub_le (f : C(Rd d, ℝ)) {n : ℕ} {x : Rd d} {ε : ℝ}
    (hε : ∀ y, ‖y - x‖ < ((2 : ℝ) ^ n)⁻¹ → |f y - f x| ≤ ε) :
    |ofCont f (bumpTest n x) - f x| ≤ ε := by
  rw [ofCont_bumpTest_sub]
  have hb : ∀ y, ‖bumpTest n x y * (f y - f x)‖ ≤ bumpTest n x y * ε := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bumpTest_nonneg n x y)]
    by_cases hy : ‖y - x‖ < ((2 : ℝ) ^ n)⁻¹
    · exact mul_le_mul_of_nonneg_left (hε y hy) (bumpTest_nonneg n x y)
    · rw [bumpTest_eq_zero (not_lt.1 hy), zero_mul, zero_mul]
  have h1 := norm_integral_le_of_norm_le ((integrable_testOn (bumpTest n x)).mul_const ε)
    (Eventually.of_forall hb)
  rwa [integral_mul_const, integral_bumpTest, one_mul, Real.norm_eq_abs] at h1

/-- `|⟨f, ψ_{n,x}⟩| ≤ M` if `|f| ≤ M` on `B̄(x, 1)`. -/
theorem abs_ofCont_bumpTest_le (f : C(Rd d, ℝ)) (n : ℕ) {x : Rd d} {M : ℝ}
    (hM : ∀ y ∈ closedBall x 1, |f y| ≤ M) : |ofCont f (bumpTest n x)| ≤ M := by
  rw [ofCont_apply]
  have hn : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have hb : ∀ y, ‖bumpTest n x y * f y‖ ≤ bumpTest n x y * M := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bumpTest_nonneg n x y)]
    by_cases hy : ‖y - x‖ < ((2 : ℝ) ^ n)⁻¹
    · refine mul_le_mul_of_nonneg_left (hM y ?_) (bumpTest_nonneg n x y)
      rw [mem_closedBall, dist_eq_norm]; exact (hy.trans_le hn).le
    · rw [bumpTest_eq_zero (not_lt.1 hy), zero_mul, zero_mul]
  have h1 := norm_integral_le_of_norm_le ((integrable_testOn (bumpTest n x)).mul_const M)
    (Eventually.of_forall hb)
  rwa [integral_mul_const, integral_bumpTest, one_mul, Real.norm_eq_abs] at h1

/-- `⟨f, ψ_{n,x}⟩ → f(x)` for continuous `f`. -/
theorem tendsto_ofCont_bumpTest (f : C(Rd d, ℝ)) (x : Rd d) :
    Tendsto (fun n => ofCont f (bumpTest n x)) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.1 f.continuous x (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_ofCont_bumpTest_sub_le f fun y hy => ?_) (half_lt_self hε)
  have hpow : ((2 : ℝ) ^ n)⁻¹ ≤ (2 : ℝ)⁻¹ ^ N := by
    rw [← inv_pow]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have := hfδ y (by rw [dist_eq_norm]; exact hy.trans_le (hpow.trans hN.le))
  rw [Real.dist_eq] at this
  exact this.le

/-! ### Continuity of `x ↦ ψ_{n,x}` in `𝓓(ℝ^d)` -/

section family

/-- the family `x ↦ Ψ x` as elements of `𝓓_K` -/
def testFamK {X : Type*} (K : Compacts (Rd d)) (Ψ : X → Rd d → ℝ)
    (hs : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x))
    (hK : ∀ x, ∀ y ∉ (K : Set (Rd d)), Ψ x y = 0) (x : X) : 𝓓^{⊤}_{K}(Rd d, ℝ) where
  toFun := Ψ x
  contDiff' := hs x
  zero_on_compl' := fun y hy => hK x y hy

/-- A family of test functions supported in a fixed compact, whose `y`-derivatives are jointly
continuous, is continuous into `𝓓_K` (Heine–Cantor). -/
theorem continuous_testFamK {X : Type*} [UniformSpace X] [WeaklyLocallyCompactSpace X]
    (K : Compacts (Rd d)) (Ψ : X → Rd d → ℝ)
    (hs : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x))
    (hK : ∀ x, ∀ y ∉ (K : Set (Rd d)), Ψ x y = 0)
    (hD : ∀ i : ℕ, Continuous fun p : X × Rd d => iteratedFDeriv ℝ i (Ψ p.1) p.2) :
    Continuous (testFamK K Ψ hs hK) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hu := Continuous.tendstoUniformly (fun (x : X) (y : (K : Set (Rd d))) =>
      iteratedFDeriv ℝ i (Ψ x) (y : Rd d))
    ((hD i).comp (X := X × (K : Set (Rd d)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) x₀
  rw [Metric.tendstoUniformly_iff] at hu
  filter_upwards [hu (ε / 2) (half_pos hε)] with x hx
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
  by_cases hy : y ∈ (K : Set (Rd d))
  · rw [dist_comm]; exact (hx ⟨y, hy⟩).le
  · rw [(testFamK K Ψ hs hK x).iteratedFDeriv_zero_on_compl hy,
      (testFamK K Ψ hs hK x₀).iteratedFDeriv_zero_on_compl hy]
    simp [(half_pos hε).le]

end family

/-- the inclusion `𝓓_K ⊆ 𝓓(ℝ^d)` -/
def ofSuppRd (K : Compacts (Rd d)) : 𝓓^{⊤}_{K}(Rd d, ℝ) →L[ℝ] TestRd d :=
  TestFunction.ofSupportedInCLM ℝ (subset_univ _)

theorem bumpTest_zero_eq_zero (n : ℕ) {w : Rd d} (hw : 1 ≤ ‖w‖) : bumpTest n 0 w = 0 :=
  bumpTest_eq_zero (by
    rw [sub_zero]; exact (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)).trans hw)

/-- `x ↦ ψ_{n,x}` is continuous into `𝓓(ℝ^d)`. -/
theorem continuous_bumpTest (n : ℕ) : Continuous (bumpTest (d := d) n) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let S := closedBall x₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Compacts (Rd d) := ⟨closedBall 0 (‖x₀‖ + 2), isCompact_closedBall _ _⟩
  let g := bumpTest (d := d) n 0
  have hs : ∀ x : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => g (y + -(x : Rd d)) :=
    fun x => g.contDiff.comp (contDiff_id.add contDiff_const)
  have hK : ∀ x : S, ∀ y ∉ (K : Set (Rd d)), g (y + -(x : Rd d)) = 0 := by
    intro x y hy
    apply bumpTest_zero_eq_zero
    have hx : ‖(x : Rd d) - x₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact mem_closedBall.1 x.2
    have hy' : ‖x₀‖ + 2 < ‖y‖ := by simpa [K] using hy
    have h1 : ‖y‖ ≤ ‖y + -(x : Rd d)‖ + ‖(x : Rd d) - x₀‖ + ‖x₀‖ := by
      calc ‖y‖ = ‖(y + -(x : Rd d)) + ((x : Rd d) - x₀) + x₀‖ := by
            congr 1; abel
        _ ≤ _ := norm_add₃_le
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × Rd d =>
      iteratedFDeriv ℝ i (fun y => g (y + -(p.1 : Rd d))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (g.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K (fun (x : S) y => g (y + -(x : Rd d))) hs hK hD
  have e : (fun x : S => bumpTest n (x : Rd d)) = ofSuppRd K ∘ testFamK K _ hs hK := by
    funext x
    refine TestFunction.ext fun y => ?_
    show bumpTest n (x : Rd d) y = g (y + -(x : Rd d))
    rw [bumpTest_apply_sub, sub_eq_add_neg]
  have h2 : Continuous fun x : S => bumpTest n (x : Rd d) := by
    rw [e]; exact (ofSuppRd K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- `x ↦ ⟨h, ψ_{n,x}⟩` is continuous for every distribution `h`. -/
theorem continuous_apply_bumpTest (h : DistRd d) (n : ℕ) :
    Continuous fun x : Rd d => h (bumpTest n x) :=
  (map_continuous h).comp (continuous_bumpTest n)

/-- `(h, x) ↦ ⟨h, ψ_{n,x}⟩` is jointly measurable. -/
theorem measurable_apply_bumpTest (n : ℕ) :
    Measurable fun p : DistRd d × Rd d => p.1 (bumpTest n p.2) := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (x : Rd d) (h : DistRd d) =>
      h (bumpTest n x)) (fun h => continuous_apply_bumpTest h n)
    (fun x => measurable_distOn_apply _)
  exact this.comp measurable_swap

end HigherDimLQGMetric
