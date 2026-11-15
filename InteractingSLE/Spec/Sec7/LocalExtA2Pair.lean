/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAField
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.GFF.LocalSets.GreenBound
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import InteractingSLE.GFF.LocalSets.SubdomainMGF

/-!
# The local comparison of Aux. lemma 55: the GFF pairing with the source

Packet PROVE-LOCEXT-A2, step 3. Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L146–L161, pp. 247–248):
"Its pairing with the GFF is defined by approximating it by smooth tests supported in `ℍ` outside the same
neighborhood of `F`. Green-energy convergence justifies this approximation."

The source `v = vSrc` of `LocalExtACutoff` is not a test function on `ℍ` (its support meets `ℝ`). Its approximations
`v_n = vApproxTest n` are. Here:

* `tsupport_vApprox_subset_norm`: every `v_n` vanishes on `B(0, 6r)`, so its support avoids every hull through the
  local stop (`K_t ⊆ B̄(0, 5r/8)`);
* `pairSeq`: a deterministic fast subsequence `n_k` with `G_ℍ(v_n − v_m, v_n − v_m) < 16^{-k}` for `n, m ≥ n_k`
  (from `tendsto_greenEnergy_vApprox_sub`);
* **`srcPair hF hr : DistOn ℍ → ℝ`**, a Borel function of the field: `T ↦ lim_k T(v_{n_k})`
  (`measurable_srcPair`);
* **`ae_tendsto_srcPair`**: for every field `h` whose centred pairings `h(φ) − ∫ u₀ φ` form a zero-boundary GFF
  process on `ℍ` (`u₀` a bounded harmonic extension: the second clause of the frozen optional hull coupling),
  `h(v_{n_k}) → srcPair (h)` almost surely. So `srcPair ∘ h` is the GFF pairing `(h, v)` of the source.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H greenH)
open LQGMetric (TestOn DistOn)

section Pair

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

/-! ### The supports of the approximations -/

/-- **The approximations vanish on `B(0, 6r)`**: their supports avoid every hull through the local stop. -/
theorem tsupport_vApprox_subset_norm (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    tsupport (vApprox κ xL xR ρL ρR r n) ⊆ {z : ℂ | 6 * r ≤ ‖z‖} := by
  refine closure_minimal (fun z hz => ?_) (isClosed_le continuous_const continuous_norm)
  by_contra hn
  exact hz (vApprox_eq_zero_of_not hF hr n fun h => hn h.2.1)

/-- The support of `v_n` is disjoint from every set inside `B̄(0, 5r/8)`. -/
theorem disjoint_tsupport_vApprox (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ)
    {K : Set ℂ} (hK : K ⊆ closedBall 0 (5 * r / 8)) : Disjoint (tsupport (vApprox κ xL xR ρL ρR r n)) K := by
  rw [Set.disjoint_left]
  intro z hz hzK
  have h1 := tsupport_vApprox_subset_norm (κ := κ) (ρL := ρL) (ρR := ρR) hF hr n hz
  have h2 := hK hzK
  rw [mem_closedBall, dist_zero_right] at h2
  have := hr.1
  simp only [mem_ofPred_eq] at h1
  linarith

/-! ### A deterministic fast subsequence -/

/-- For every `ε > 0`, eventually `G_ℍ(v_n − v_m, v_n − v_m) < ε` for all `n, m` beyond. -/
theorem eventually_greenEnergy_vApprox_sub_lt (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, ∀ n m : ℕ, N ≤ n → N ≤ m →
      greenEnergy (fun z => vApprox κ xL xR ρL ρR r n z - vApprox κ xL xR ρL ρR r m z)
        (fun z => vApprox κ xL xR ρL ρR r n z - vApprox κ xL xR ρL ρR r m z) < ε := by
  have h := (tendsto_order.1 (tendsto_greenEnergy_vApprox_sub (κ := κ) (ρL := ρL) (ρR := ρR) hF hr)).2 ε hε
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self'] at h
  obtain ⟨a, ha⟩ := h
  filter_upwards [eventually_ge_atTop a] with N hN n m hn hm
  exact ha n (hN.trans hn) m (hN.trans hm)

theorem exists_pairSeq (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k n m : ℕ, φ k ≤ n → φ k ≤ m →
      greenEnergy (fun z => vApprox κ xL xR ρL ρR r n z - vApprox κ xL xR ρL ρR r m z)
        (fun z => vApprox κ xL xR ρL ρR r n z - vApprox κ xL xR ρL ρR r m z) < (1 / 16 : ℝ) ^ k :=
  extraction_forall_of_eventually fun k =>
    eventually_greenEnergy_vApprox_sub_lt hF hr (by positivity)

variable (κ ρL ρR) in
/-- **The fast subsequence `n_k`**: `G_ℍ(v_n − v_m, v_n − v_m) < 16^{-k}` for `n, m ≥ n_k`. -/
def pairSeq (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) : ℕ → ℕ :=
  Classical.choose (exists_pairSeq (κ := κ) (ρL := ρL) (ρR := ρR) hF hr)

theorem strictMono_pairSeq (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    StrictMono (pairSeq κ ρL ρR hF hr) :=
  (Classical.choose_spec (exists_pairSeq (κ := κ) (ρL := ρL) (ρR := ρR) hF hr)).1

theorem greenEnergy_pairSeq_lt (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {k n m : ℕ}
    (hn : pairSeq κ ρL ρR hF hr k ≤ n) (hm : pairSeq κ ρL ρR hF hr k ≤ m) :
    greenEnergy (fun z => vApprox κ xL xR ρL ρR r n z - vApprox κ xL xR ρL ρR r m z)
      (fun z => vApprox κ xL xR ρL ρR r n z - vApprox κ xL xR ρL ρR r m z) < (1 / 16 : ℝ) ^ k :=
  (Classical.choose_spec (exists_pairSeq (κ := κ) (ρL := ρL) (ρR := ρR) hF hr)).2 k n m hn hm

theorem tendsto_pairSeq (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Tendsto (pairSeq κ ρL ρR hF hr) atTop atTop :=
  (strictMono_pairSeq hF hr).tendsto_atTop

/-! ### The pairing as a Borel function of the field -/

variable (κ ρL ρR) in
/-- The approximating test function `v_{n_k}`. -/
def srcTest (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (k : ℕ) : TestOn upperHalfPlaneOpens :=
  vApproxTest (κ := κ) (ρL := ρL) (ρR := ρR) hF hr (pairSeq κ ρL ρR hF hr k)

theorem srcTest_apply (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (k : ℕ) (z : ℂ) :
    srcTest κ ρL ρR hF hr k z = vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k) z := rfl

variable (κ ρL ρR) in
/-- **The GFF pairing with the source**, as a Borel function of the field: `(T, v) := lim_k T(v_{n_k})`
(`limUnder`; the limit exists almost surely for the fields of the optional hull coupling, `ae_tendsto_srcPair`). -/
def srcPair (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (T : DistOn upperHalfPlaneOpens) : ℝ :=
  limUnder atTop fun k => T (srcTest κ ρL ρR hF hr k)

theorem measurable_srcPair (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Measurable (srcPair κ ρL ρR hF hr) := by
  have h : ∀ k, StronglyMeasurable fun T : DistOn upperHalfPlaneOpens => T (srcTest κ ρL ρR hF hr k) :=
    fun k => ((measurable_pi_apply (srcTest κ ρL ρR hF hr k)).comp
      (LQGMetric.measurable_distEval upperHalfPlaneOpens)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder h).measurable

end Pair

/-! ### Almost sure convergence of the approximate pairings -/

section Conv

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- The pairing of a test function with a function continuous on `ℍ` is integrable. -/
theorem integrable_mul_testOn (hu₀ : ContinuousOn u₀ H) (φ : TestOn upperHalfPlaneOpens) :
    Integrable fun z => u₀ z * φ z :=
  Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₀ φ φ.tsupport_subset

/-- **The variance of a centred GFF pairing** is the half-plane Green energy. -/
theorem integral_sq_zbProcess [IsProbabilityMeasure P]
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω, (h ω ψ - ∫ z, u₀ z * ψ z) ^ 2 ∂P = greenEnergy ψ ψ := by
  have hm : AEMeasurable (fun ω => h ω ψ - ∫ z, u₀ z * ψ z) P := (hY.measurable ψ).aemeasurable
  rw [← variance_of_integral_eq_zero hm (hY.centered ψ), ← covariance_self hm, hY.covariance_eq ψ ψ,
    LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl GFF.isConformalOnto_id_H ψ ψ]
  rfl

theorem memLp_zbProcess
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P)
    (ψ : TestOn upperHalfPlaneOpens) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω => h ω ψ - ∫ z, u₀ z * ψ z) p P :=
  (hY.gaussian.hasGaussianLaw_eval ψ).memLp hp

/-- The means `∫ u₀ v_{n_k}` converge to `∫ u₀ v`. -/
theorem tendsto_integral_mul_srcTest (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hu₀ : ContinuousOn u₀ H) {C : ℝ} (hC : ∀ z ∈ H, |u₀ z| ≤ C) :
    Tendsto (fun k => ∫ z, u₀ z * srcTest κ ρL ρR hF hr k z) atTop
      (𝓝 (∫ z, u₀ z * vSrc κ xL xR ρL ρR r z)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => C * |vSrc κ xL xR ρL ρR r z|)
    (fun k => (integrable_mul_testOn hu₀ (srcTest κ ρL ρR hF hr k)).aestronglyMeasurable)
    ((integrable_vSrc hF hr).abs.const_mul C) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul, srcTest_apply]
    by_cases hz : z ∈ H
    · exact mul_le_mul (hC z hz) (abs_vApprox_le _ z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))
    · have h0 : vSrc κ xL xR ρL ρR r z = 0 := by rw [vSrc, Set.indicator_of_notMem hz]
      have h1 := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r)
        (pairSeq κ ρL ρR hF hr k) z
      rw [h0, abs_zero] at h1
      rw [abs_nonpos_iff.1 h1, h0, abs_zero, mul_zero, mul_zero]
  · exact tendsto_const_nhds.mul ((tendsto_vApprox z).comp (tendsto_pairSeq hF hr))

/-- The `L²` distance of two centred approximate pairings. -/
theorem integral_sq_sub_srcTest [IsProbabilityMeasure P] (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hu₀ : ContinuousOn u₀ H)
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) (n m : ℕ) :
    ∫ ω, ((h ω (srcTest κ ρL ρR hF hr n) - ∫ z, u₀ z * srcTest κ ρL ρR hF hr n z) -
        (h ω (srcTest κ ρL ρR hF hr m) - ∫ z, u₀ z * srcTest κ ρL ρR hF hr m z)) ^ 2 ∂P =
      greenEnergy (fun z => vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr n) z -
          vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr m) z)
        (fun z => vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr n) z -
          vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr m) z) := by
  set ψ := srcTest κ ρL ρR hF hr n - srcTest κ ρL ρR hF hr m with hψ
  have e : ∀ ω, (h ω (srcTest κ ρL ρR hF hr n) - ∫ z, u₀ z * srcTest κ ρL ρR hF hr n z) -
      (h ω (srcTest κ ρL ρR hF hr m) - ∫ z, u₀ z * srcTest κ ρL ρR hF hr m z) =
      h ω ψ - ∫ z, u₀ z * ψ z := fun ω => by
    have hi : ∫ z, u₀ z * ψ z = (∫ z, u₀ z * srcTest κ ρL ρR hF hr n z) -
        ∫ z, u₀ z * srcTest κ ρL ρR hF hr m z := by
      rw [← integral_sub (integrable_mul_testOn hu₀ _) (integrable_mul_testOn hu₀ _)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hψ]
      change u₀ z * (srcTest κ ρL ρR hF hr n z - srcTest κ ρL ρR hF hr m z) = _
      ring
    rw [hi, hψ, map_sub]
    ring
  simp_rw [e]
  rw [integral_sq_zbProcess hY ψ]
  rfl

/-- **The approximate pairings converge almost surely** to the Borel pairing `srcPair`, for every field whose
centred pairings form a zero-boundary GFF process on `ℍ` around a bounded function `u₀` continuous on `ℍ`. -/
theorem ae_tendsto_srcPair [IsProbabilityMeasure P] (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hu₀ : ContinuousOn u₀ H) {C : ℝ} (hC : ∀ z ∈ H, |u₀ z| ≤ C)
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) :
    ∀ᵐ ω ∂P, Tendsto (fun k => h ω (srcTest κ ρL ρR hF hr k)) atTop
      (𝓝 (srcPair κ ρL ρR hF hr (h ω))) := by
  set f : ℕ → Ω → ℝ := fun k ω => h ω (srcTest κ ρL ρR hF hr k) - ∫ z, u₀ z * srcTest κ ρL ρR hF hr k z with hf
  have hB : ∑' i : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ i) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) 2 P < ENNReal.ofReal ((1 / 4 : ℝ) ^ N) := by
    intro N n m hn hm
    have hL2 : MemLp (f n - f m) 2 P :=
      (memLp_zbProcess hY _ ENNReal.ofNat_ne_top).sub (memLp_zbProcess hY _ ENNReal.ofNat_ne_top)
    rw [Girsanov.eLpNorm_two_eq_sqrt hL2]
    have hI : ∫ ω, (f n - f m) ω ^ 2 ∂P < (1 / 16 : ℝ) ^ N := by
      simp only [hf, Pi.sub_apply]
      rw [integral_sq_sub_srcTest hF hr hu₀ hY n m]
      exact greenEnergy_pairSeq_lt hF hr ((strictMono_pairSeq hF hr).monotone hn)
        ((strictMono_pairSeq hF hr).monotone hm)
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    rw [show (1 / 4 : ℝ) ^ N = Real.sqrt ((1 / 16 : ℝ) ^ N) by
      rw [show (1 / 16 : ℝ) ^ N = ((1 / 4 : ℝ) ^ N) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (integral_nonneg fun ω => sq_nonneg _) hI
  have hae := Lp.ae_tendsto_of_cauchy_eLpNorm (f := f) (p := 2)
    (fun n => (hY.measurable _).aestronglyMeasurable) one_le_two hB hcau
  have hmean := tendsto_integral_mul_srcTest (κ := κ) (ρL := ρL) (ρR := ρR) hF hr hu₀ hC
  filter_upwards [hae] with ω ⟨l, hl⟩
  have hconv : Tendsto (fun k => h ω (srcTest κ ρL ρR hF hr k)) atTop
      (𝓝 (l + ∫ z, u₀ z * vSrc κ xL xR ρL ρR r z)) :=
    (hl.add hmean).congr fun k => by simp only [hf]; ring
  rw [srcPair, hconv.limUnder_eq]
  exact hconv

end Conv

/-! ### Limits of conditional Gaussian characteristic functions -/

section CondLimit

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The Gaussian characteristic-function value `exp(i a − ½ q)`, in the form of the frozen kernel. -/
def cfVal (a q : ℝ) : ℂ := Complex.exp (Complex.I * (a : ℂ) - (((1 / 2 : ℝ) * q : ℝ) : ℂ))

theorem continuous_cfVal : Continuous fun p : ℝ × ℝ => cfVal p.1 p.2 := by
  unfold cfVal; fun_prop

theorem norm_cfVal (a q : ℝ) : ‖cfVal a q‖ = Real.exp (-(1 / 2 * q)) := by
  rw [cfVal, Complex.norm_exp]
  congr 1
  simp [Complex.sub_re, Complex.mul_re]

theorem norm_cfVal_le_one {a q : ℝ} (hq : 0 ≤ q) : ‖cfVal a q‖ ≤ 1 := by
  rw [norm_cfVal, Real.exp_le_one_iff]
  linarith

theorem norm_cexp_I_mul (y : ℝ) : ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I y

/-- **Conditional bounded convergence of Gaussian characteristic functions.** If `E[e^{i Y_k} | m] = exp(i a_k − q_k/2)`
and `Y_k → Y`, `a_k → a`, `q_k → q` almost surely, then `E[e^{i Y} | m] = exp(i a − q/2)`. -/
theorem ae_condExp_cexp_of_tendsto [IsFiniteMeasure P] (hm : m ≤ mΩ) {Y : ℕ → Ω → ℝ} {Y' : Ω → ℝ}
    {a q : ℕ → Ω → ℝ} {a' q' : Ω → ℝ} (hYm : ∀ k, AEMeasurable (Y k) P)
    (hk : ∀ k, P[fun ω => Complex.exp (Complex.I * (Y k ω : ℂ)) | m] =ᵐ[P] fun ω => cfVal (a k ω) (q k ω))
    (hY : ∀ᵐ ω ∂P, Tendsto (fun k => Y k ω) atTop (𝓝 (Y' ω)))
    (ha : ∀ᵐ ω ∂P, Tendsto (fun k => a k ω) atTop (𝓝 (a' ω)))
    (hq' : ∀ᵐ ω ∂P, Tendsto (fun k => q k ω) atTop (𝓝 (q' ω))) :
    P[fun ω => Complex.exp (Complex.I * (Y' ω : ℂ)) | m] =ᵐ[P] fun ω => cfVal (a' ω) (q' ω) := by
  set fs : ℕ → Ω → ℂ := fun k ω => Complex.exp (Complex.I * (Y k ω : ℂ)) with hfs
  set gs : ℕ → Ω → ℂ := fun k ω => cfVal (a k ω) (q k ω) with hgs
  have hfsm : ∀ k, AEStronglyMeasurable (fs k) P := fun k =>
    (Complex.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable (hYm k)))).aestronglyMeasurable
  have hfsb : ∀ k, ∀ᵐ ω ∂P, ‖fs k ω‖ ≤ 1 := fun k => ae_of_all _ fun ω => (norm_cexp_I_mul _).le
  have hfsi : ∀ k, Integrable (fs k) P := fun k => Integrable.of_bound (hfsm k) 1 (hfsb k)
  -- the right sides are a.e. equal to conditional expectations, hence `m`-measurable
  have hgsm' : ∀ k, AEStronglyMeasurable[m] (gs k) P := fun k =>
    ⟨_, stronglyMeasurable_condExp, (hk k).symm⟩
  have hgsm : ∀ k, AEStronglyMeasurable (gs k) P := fun k => (hgsm' k).mono hm
  have hgsb : ∀ k, ∀ᵐ ω ∂P, ‖gs k ω‖ ≤ 1 := fun k => by
    filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) (hfsb k), hk k] with ω h1 h2
    have h3 : gs k ω = (P[fs k | m]) ω := h2.symm
    rw [h3]; exact h1
  have hgsi : ∀ k, Integrable (gs k) P := fun k => Integrable.of_bound (hgsm k) 1 (hgsb k)
  have hgs_lim : ∀ᵐ ω ∂P, Tendsto (fun k => gs k ω) atTop (𝓝 (cfVal (a' ω) (q' ω))) := by
    filter_upwards [ha, hq'] with ω h1 h2
    exact (continuous_cfVal.tendsto _).comp (h1.prodMk_nhds h2)
  have hfs_lim : ∀ᵐ ω ∂P, Tendsto (fun k => fs k ω) atTop (𝓝 (Complex.exp (Complex.I * (Y' ω : ℂ)))) := by
    filter_upwards [hY] with ω h1
    exact (Complex.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp h1)))
  have hgm' : AEStronglyMeasurable[m] (fun ω => cfVal (a' ω) (q' ω)) P := by
    refine ⟨fun ω => limUnder atTop fun k => (P[fs k | m]) ω,
      @StronglyMeasurable.limUnder ℕ Ω ℂ m _ _ atTop _ _ _ _ fun k => stronglyMeasurable_condExp, ?_⟩
    filter_upwards [hgs_lim, ae_all_iff.2 hk] with ω h1 h2
    have h3 : Tendsto (fun k => (P[fs k | m]) ω) atTop (𝓝 (cfVal (a' ω) (q' ω))) :=
      h1.congr fun k => (h2 k).symm
    exact h3.limUnder_eq.symm
  have hg_int : Integrable (fun ω => cfVal (a' ω) (q' ω)) P := by
    refine Integrable.of_bound (hgm'.mono hm) 1 ?_
    filter_upwards [hgs_lim, ae_all_iff.2 hgsb] with ω h1 h2
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp h1) h2
  have key := tendsto_condExp_unique (m := m) fs gs _ _ hfsi hgsi hfs_lim hgs_lim (fun _ => 1)
    (integrable_const 1) (fun _ => 1) (integrable_const 1) hfsb hgsb
    (fun k => (hk k).trans (condExp_of_aestronglyMeasurable' hm (hgsm' k) (hgsi k)).symm)
  exact key.trans (condExp_of_aestronglyMeasurable' hm hgm' hg_int)

theorem cfVal_eq (a q : ℝ) :
    cfVal a q = ((Real.exp (-(1 / 2 * q)) : ℝ) : ℂ) * (Complex.cos a + Complex.sin a * Complex.I) := by
  rw [cfVal, ← Complex.exp_mul_I, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem arg_cfVal {a q : ℝ} (ha : a ∈ Ioc (-Real.pi) Real.pi) : Complex.arg (cfVal a q) = a := by
  rw [cfVal_eq, Complex.arg_real_mul _ (Real.exp_pos _), Complex.arg_cos_add_sin_mul_I ha]

/-- **Measurable versions of a conditional Gaussian's parameters.** If
`E[e^{i c X} | m] = exp(i c a − ½ c² q)` for every real `c`, then `a` and `q` agree almost surely with
`m`-strongly measurable functions (read off from the conditional characteristic functions: `q` from the modulus at
`c = 1`, `a` as the limit of `(n+1) arg E[e^{i X/(n+1)} | m]`). -/
theorem exists_stronglyMeasurable_condGauss {X a q : Ω → ℝ}
    (h : ∀ c : ℝ, P[fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (c * a ω) (c ^ 2 * q ω)) :
    ∃ a' q' : Ω → ℝ, StronglyMeasurable[m] a' ∧ StronglyMeasurable[m] q' ∧ a =ᵐ[P] a' ∧ q =ᵐ[P] q' := by
  set g : ℝ → Ω → ℂ := fun c => P[fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) | m] with hg
  have hgm : ∀ c, StronglyMeasurable[m] (g c) := fun c => stronglyMeasurable_condExp
  refine ⟨fun ω => limUnder atTop fun n : ℕ => ((n : ℝ) + 1) * Complex.arg (g (1 / ((n : ℝ) + 1)) ω),
    fun ω => -2 * Real.log ‖g 1 ω‖, ?_, ?_, ?_, ?_⟩
  · refine @StronglyMeasurable.limUnder ℕ Ω ℝ m _ _ atTop _ _ _ _ fun n => ?_
    exact (measurable_const.mul (Complex.measurable_arg.comp (hgm _).measurable)).stronglyMeasurable
  · exact (measurable_const.mul (Real.measurable_log.comp
      (continuous_norm.measurable.comp (hgm 1).measurable))).stronglyMeasurable
  · filter_upwards [ae_all_iff.2 fun n : ℕ => h (1 / ((n : ℝ) + 1))] with ω hω
    have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * Complex.arg (g (1 / ((n : ℝ) + 1)) ω) = a ω := by
      obtain ⟨N, hN⟩ := exists_nat_gt (|a ω| / Real.pi)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsmall : |1 / ((n : ℝ) + 1) * a ω| < Real.pi := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)), one_div, inv_mul_lt_iff₀ hpos]
        have h1 : |a ω| < Real.pi * N := by rwa [div_lt_iff₀ Real.pi_pos, mul_comm] at hN
        have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [Real.pi_pos]
      simp only [hg]
      rw [hω n, arg_cfVal ⟨(neg_lt_of_abs_lt hsmall), (lt_of_abs_lt hsmall).le⟩]
      field_simp
    exact (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)).limUnder_eq.symm
  · filter_upwards [h 1] with ω hω
    simp only [hg]
    rw [hω, norm_cfVal, Real.log_exp]
    ring

/-- Centring a conditional Gaussian at an `m`-measurable version of its mean. -/
theorem condExp_cexp_sub_of_condGauss (hm : m ≤ mΩ) [IsFiniteMeasure P] {X a q a' : Ω → ℝ} (hXm : Measurable X)
    (ha' : StronglyMeasurable[m] a') (haa : a =ᵐ[P] a')
    (h : ∀ c : ℝ, P[fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (c * a ω) (c ^ 2 * q ω)) (c : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((c * (X ω - a' ω) : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (c ^ 2 * q ω)) : ℝ) : ℂ) := by
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((-(c * a' ω) : ℝ) : ℂ)) with hf
  set g : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) with hg
  have hfm : StronglyMeasurable[m] f :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul ha'.measurable).neg))).stronglyMeasurable
  have hgm : Measurable g := Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_const.mul hXm)))
  have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => (norm_cexp_I_mul _).le)
  have hfgi : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) P := by
    refine Integrable.of_bound ((hfm.measurable.mono hm le_rfl).mul hgm).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    show ‖f ω * g ω‖ ≤ 1
    rw [norm_mul]
    simp only [hf, hg, norm_cexp_I_mul, mul_one, le_refl]
  have e : (fun ω => Complex.exp (Complex.I * ((c * (X ω - a' ω) : ℝ) : ℂ))) =
      fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω) := by
    funext ω
    simp only [ContinuousLinearMap.mul_apply', hf, hg, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [e]
  filter_upwards [condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hfm hfgi hgi, h c, haa]
    with ω h1 h2 h3
  rw [h1, ContinuousLinearMap.mul_apply', hg, h2]
  simp only [hf, cfVal]
  rw [h3, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Conditional exponential moments of a conditional Gaussian**: if `E[e^{i c X} | m] = exp(i c a − ½ c² q)` for every
real `c`, then `E[W e^{λ X}] = E[W e^{λ a + λ² q/2}]` for every `m`-measurable `W ≥ 0`. -/
theorem lintegral_mul_exp_of_condGauss (hm : m ≤ mΩ) [IsProbabilityMeasure P] {X a q : Ω → ℝ} (hXm : Measurable X)
    (h : ∀ c : ℝ, P[fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (c * a ω) (c ^ 2 * q ω))
    {W : Ω → ℝ≥0∞} (hW : Measurable[m] W) (lam : ℝ) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * X ω)) ∂P =
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * a ω + lam ^ 2 * q ω / 2)) ∂P := by
  obtain ⟨a', q', ha', hq', haa, hqq⟩ := exists_stronglyMeasurable_condGauss h
  have hc := condExp_cexp_sub_of_condGauss hm hXm ha' haa h
  have hc' : ∀ c : ℝ, P[fun ω => Complex.exp (Complex.I * ((c * (X ω - a' ω) : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (c ^ 2 * q' ω)) : ℝ) : ℂ) := fun c => by
    filter_upwards [hc c, hqq] with ω h1 h2; rw [h1, h2]
  have hq0 : ∀ᵐ ω ∂P, 0 ≤ q' ω := by
    filter_upwards [hc' 1, ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) (μ := P)
      (f := fun ω => Complex.exp (Complex.I * (((1 : ℝ) * (X ω - a' ω) : ℝ) : ℂ)))
      (ae_of_all _ fun ω => (norm_cexp_I_mul _).le)] with ω h1 h2
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff] at h2
    linarith
  have hW' : Measurable[m] fun ω => W ω * ENNReal.ofReal (Real.exp (lam * a' ω)) :=
    hW.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul ha'.measurable)))
  have key := LocalSets.lintegral_mul_exp_of_condCharFun (P := P) hm (hXm.sub (ha'.measurable.mono hm le_rfl))
    (hq'.measurable.mono hm le_rfl) hq0 hc' hW' lam
  have e1 : ∀ ω, W ω * ENNReal.ofReal (Real.exp (lam * a' ω)) * ENNReal.ofReal (Real.exp (lam * (X ω - a' ω))) =
      W ω * ENNReal.ofReal (Real.exp (lam * X ω)) := fun ω => by
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3; ring
  have e2 : ∀ ω, W ω * ENNReal.ofReal (Real.exp (lam * a' ω)) * ENNReal.ofReal (Real.exp (lam ^ 2 * q' ω / 2)) =
      W ω * ENNReal.ofReal (Real.exp (lam * a' ω + lam ^ 2 * q' ω / 2)) := fun ω => by
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp only [Pi.sub_apply, e1, e2] at key
  rw [key]
  refine lintegral_congr_ae ?_
  filter_upwards [haa, hqq] with ω h1 h2
  rw [h1, h2]

end CondLimit

end LocalExt

end InteractingSLE
