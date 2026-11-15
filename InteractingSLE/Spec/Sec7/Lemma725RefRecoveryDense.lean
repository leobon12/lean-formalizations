/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.PushforwardLaw
import InteractingSLE.GFF.LocalSets.Projection
import InteractingSLE.Spec.Sec7.LocalExtDCov
import SupercriticalConformalCovariance.Reversal.Inverse

/-!
# The ambient recovery, analytic part: chart tests are dense in the pocket's dual Dirichlet norm

Packet PROVE-LEMMA725REF5. Specification §7.4, Aux. lemma 125's proof, "Recovering the local curve from its local
field" (`source/spec/p385-432.md` L197–L250, p. 398); Astra's shortcut note, Proposition 2.1 step 3
(`source/external/AstraIG1/ig1_shortcuts_audited.txt` L276–L285): "The Green potentials of smooth tests supported in
`C` span a dense subspace of `H¹₀(C)`: an element orthogonal to all such potentials has zero distributional pairing
with every such test and is zero. The Gaussian isometry recovers each ambient test pairing from these interior
coordinates as an `L²` limit."

For a conformal chart `c` with domain `U = inv(ℍ)` and the dual Dirichlet norm `‖φ‖²_{H⁻¹(U)} = Cov_U(φ, φ)`
(`zeroGFFTestCov`), every test function `φ` on `ℍ` (not only those supported in `U`) is approximated in this norm by
the transported test functions `pushTest φ'` of the chart, and `φ'` can be taken from the countable family of
LQGMetric's generators of `𝒟'(ℍ)` (`LQGMetric.distGen`):

* `exists_genTest_cov_lt`: the generators are dense for the half-plane norm `Cov_ℍ` (sup-norm bound on a compact
  support, `LocalExt.exists_zeroGFFTestCov_H_le`, and density in `𝓓_K`);
* `sqrt_cov_sub_le`: the triangle inequality for `√Cov_V` (Gram vectors `covVec`);
* `exists_pushTest_cov_lt`: density of `pushTest φ'` in `H⁻¹(U)` for every open `U` inside the chart domain
  (QuantumZipper's density of `C_c^∞(U)` gradients, `LocalSets.exists_tendsto_gradFeat_covVec`, Green's identity
  `covVec_lapTest`, and the surjectivity of the transport onto `𝓓(U)`, `confPushTest_inverse_right`);
* **`exists_genTest_pushTest_cov_lt`**: for every `ε > 0` some generator `g_j` has `Cov_U(φ − pushTest g_j) < ε`
  (`U` open inside the chart domain; domain monotonicity `zeroGFFTestCov_mono`).

Deterministic; no named input. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace Distributions
open QuantumZipper (H isOpen_H zeroGFFTestCov)
open QuantumZipper.Thm11Asm (covVec)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Sec7.Lemma725RefRecovery

open LocalSets LocalExt Chart

/-- The countable test family: LQGMetric's generators of `𝒟'(ℍ)` (dense sequences in `𝓓_{K_n}` for a compact
exhaustion `K_n` of `ℍ`). -/
abbrev genTest (j : ℕ × ℕ) : TestOn upperHalfPlaneOpens := LQGMetric.distGen upperHalfPlaneOpens j

/-- **The generators are dense for the half-plane dual Dirichlet norm.** -/
theorem exists_genTest_cov_lt (φ : TestOn upperHalfPlaneOpens) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, zeroGFFTestCov H ⇑(φ - genTest j) ⇑(φ - genTest j) < ε := by
  obtain ⟨n, hn⟩ := LQGMetric.exists_exhaustK_superset upperHalfPlaneOpens φ.hasCompactSupport.isCompact
    φ.tsupport_subset
  set K : Compacts ℂ := LQGMetric.exhaustK upperHalfPlaneOpens n with hK
  obtain ⟨C, hC⟩ := exists_zeroGFFTestCov_H_le (K : Set ℂ) K.isCompact
  let ψ : 𝓓^{⊤}_{K}(ℂ, ℝ) :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hn h)⟩
  set ι := ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ (E := ℂ) (F := ℝ) (n := ⊤) (K := K) with hι
  set δ : ℝ := Real.sqrt (ε / (|C| + 1)) with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hopen : IsOpen {χ : 𝓓^{⊤}_{K}(ℂ, ℝ) | ‖ι (ψ - χ)‖ < δ} :=
    isOpen_lt (continuous_norm.comp (ι.continuous.comp (continuous_const.sub continuous_id)))
      continuous_const
  obtain ⟨k, hk⟩ := (LQGMetric.denseRange_denseSeqK upperHalfPlaneOpens n).exists_mem_open hopen
    ⟨ψ, show ‖ι (ψ - ψ)‖ < δ by rw [sub_self, map_zero, norm_zero]; exact hδ0⟩
  refine ⟨(n, k), ?_⟩
  set χ := LQGMetric.denseSeqK upperHalfPlaneOpens n k with hχ
  have hval : ∀ x, (φ - genTest (n, k)) x = ι (ψ - χ) x := fun x => rfl
  have hB : ∀ x, |(φ - genTest (n, k)) x| ≤ ‖ι (ψ - χ)‖ := fun x => by
    rw [hval, ← Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm _ x
  have hsupp : tsupport ⇑(φ - genTest (n, k)) ⊆ (K : Set ℂ) := (ψ - χ).tsupport_subset
  have h1 := hC (φ - genTest (n, k)) _ hB hsupp
  have hlt : ‖ι (ψ - χ)‖ < δ := hk
  have hsq : ‖ι (ψ - χ)‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
  have hδ2 : δ ^ 2 = ε / (|C| + 1) := Real.sq_sqrt (by positivity)
  calc zeroGFFTestCov H ⇑(φ - genTest (n, k)) ⇑(φ - genTest (n, k)) ≤ ‖ι (ψ - χ)‖ ^ 2 * C := h1
    _ ≤ ‖ι (ψ - χ)‖ ^ 2 * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) (sq_nonneg _)
    _ ≤ δ ^ 2 * |C| := mul_le_mul_of_nonneg_right hsq (abs_nonneg C)
    _ = ε * (|C| / (|C| + 1)) := by rw [hδ2]; ring
    _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (lt_add_one _)) hε
    _ = ε := mul_one ε

/-- **The triangle inequality for `√Cov_V`.** -/
theorem sqrt_cov_sub_le {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (a b c : TestOn upperHalfPlaneOpens) :
    Real.sqrt (zeroGFFTestCov V ⇑(a - c) ⇑(a - c)) ≤
      Real.sqrt (zeroGFFTestCov V ⇑(a - b) ⇑(a - b)) + Real.sqrt (zeroGFFTestCov V ⇑(b - c) ⇑(b - c)) := by
  rw [sqrt_zeroGFFTestCov_self hV hVH, sqrt_zeroGFFTestCov_self hV hVH, sqrt_zeroGFFTestCov_self hV hVH,
    covVec_sub hV hVH, covVec_sub hV hVH, covVec_sub hV hVH]
  calc ‖covVec V ⇑a - covVec V ⇑c‖ = ‖(covVec V ⇑a - covVec V ⇑b) + (covVec V ⇑b - covVec V ⇑c)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _

/-- The dual Dirichlet norm of a difference of transported test functions is the half-plane norm of the difference
(conformal invariance, `Chart.zeroGFFTestCov_pushTest`). -/
theorem cov_dom_pushTest_sub {c : Chart} (hc : c.IsConformal) (φ' φ'' : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (c.dom : Set ℂ) ⇑(pushTest hc φ' - pushTest hc φ'') ⇑(pushTest hc φ' - pushTest hc φ'') =
      zeroGFFTestCov H ⇑(φ' - φ'') ⇑(φ' - φ'') := by
  rw [← map_sub]
  exact zeroGFFTestCov_pushTest hc _ _

/-- **Density of the transported test functions in `H⁻¹(U)`**: for a conformal chart and an open `U` inside its
domain, every test function `φ` on `ℍ` is approximated in the norm `Cov_U` by some `pushTest φ'`. -/
theorem exists_pushTest_cov_lt {c : Chart} (hc : c.IsConformal) {U : Set ℂ} (hUo : IsOpen U)
    (hUd : U ⊆ c.dom) (φ : TestOn upperHalfPlaneOpens) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ' : TestOn upperHalfPlaneOpens, zeroGFFTestCov U ⇑(φ - pushTest hc φ') ⇑(φ - pushTest hc φ') < ε := by
  have hUH : U ⊆ H := hUd.trans hc.dom_subset
  set Uo : Opens ℂ := ⟨U, hUo⟩ with hUodef
  have hUoH : Uo ≤ upperHalfPlaneOpens := hUH
  have hUod : Uo ≤ c.dom := hUd
  obtain ⟨f, hf⟩ := exists_tendsto_gradFeat_covVec Uo φ
  have hf' : Tendsto (fun n => QuantumZipper.K3.gradFeat U (f n).1) atTop (𝓝 (covVec U ⇑φ)) := hf
  have hlim : Tendsto (fun n => ‖covVec U ⇑(φ - lapTest Uo (f n))‖) atTop (𝓝 0) := by
    have e : ∀ n, covVec U ⇑(φ - lapTest Uo (f n)) = covVec U ⇑φ - QuantumZipper.K3.gradFeat U (f n).1 :=
      fun n => by rw [covVec_sub hUo hUH, covVec_lapTest hUoH hUo hUH subset_rfl]
    simp_rw [e]
    have := (tendsto_const_nhds (x := covVec U ⇑φ)).sub hf'
    rw [sub_self] at this
    simpa using this.norm
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (Real.sqrt_pos.2 hε))).exists
  set g : TestOn c.dom := GFF.testIncl Uo c.dom (LQGMetric.MarkovHarm.cmTestOn (f n)) with hg
  have hφ := hc.isConformalBijection
  refine ⟨SupercriticalConformalCovariance.confPushTest
    (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) g, ?_⟩
  have hpush : pushTest hc (SupercriticalConformalCovariance.confPushTest
      (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) g) = lapTest Uo (f n) := by
    change GFF.testIncl c.dom upperHalfPlaneOpens (SupercriticalConformalCovariance.confPushTest hφ
      (SupercriticalConformalCovariance.confPushTest
        (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) g)) = _
    rw [SupercriticalConformalCovariance.Reversal.confPushTest_inverse_right hφ g]
    ext z
    change (GFF.testIncl c.dom upperHalfPlaneOpens g : ℂ → ℝ) z =
      (GFF.testIncl Uo upperHalfPlaneOpens (LQGMetric.MarkovHarm.cmTestOn (f n)) : ℂ → ℝ) z
    rw [GFF.coe_testIncl hc.dom_le, hg, GFF.coe_testIncl hUod, GFF.coe_testIncl hUoH]
  rw [hpush, zeroGFFTestCov_self_eq_norm_sq hUo hUH]
  have h0 := norm_nonneg (covVec U ⇑(φ - lapTest Uo (f n)))
  calc ‖covVec U ⇑(φ - lapTest Uo (f n))‖ ^ 2 < Real.sqrt ε ^ 2 := pow_lt_pow_left₀ hn h0 two_ne_zero
    _ = ε := Real.sq_sqrt hε.le

/-- **The ambient recovery's density, in the countable family**: for a conformal chart, an open `U` inside its domain
and every test function `φ` on `ℍ`, some generator `g_j` has `Cov_U(φ − pushTest g_j, φ − pushTest g_j) < ε`. -/
theorem exists_genTest_pushTest_cov_lt {c : Chart} (hc : c.IsConformal) {U : Set ℂ} (hUo : IsOpen U)
    (hUd : U ⊆ c.dom) (φ : TestOn upperHalfPlaneOpens) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, zeroGFFTestCov U ⇑(φ - pushTest hc (genTest j)) ⇑(φ - pushTest hc (genTest j)) < ε := by
  have hUH : U ⊆ H := hUd.trans hc.dom_subset
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨φ', hφ'⟩ := exists_pushTest_cov_lt hc hUo hUd φ hε4
  obtain ⟨j, hj⟩ := exists_genTest_cov_lt φ' hε4
  refine ⟨j, ?_⟩
  have htri := sqrt_cov_sub_le hUo hUH φ (pushTest hc φ') (pushTest hc (genTest j))
  have hmono : zeroGFFTestCov U ⇑(pushTest hc φ' - pushTest hc (genTest j))
      ⇑(pushTest hc φ' - pushTest hc (genTest j)) ≤ zeroGFFTestCov H ⇑(φ' - genTest j) ⇑(φ' - genTest j) := by
    rw [← cov_dom_pushTest_sub hc]
    exact zeroGFFTestCov_mono hUo c.dom.isOpen hUd hc.dom_subset _
  have hs4 : Real.sqrt (ε / 4) = Real.sqrt ε / 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have h1 : Real.sqrt (zeroGFFTestCov U ⇑(φ - pushTest hc φ') ⇑(φ - pushTest hc φ')) < Real.sqrt ε / 2 := by
    rw [← hs4]
    exact Real.sqrt_lt_sqrt (zeroGFFTestCov_self_nonneg hUo hUH _) hφ'
  have h2 : Real.sqrt (zeroGFFTestCov U ⇑(pushTest hc φ' - pushTest hc (genTest j))
      ⇑(pushTest hc φ' - pushTest hc (genTest j))) < Real.sqrt ε / 2 := by
    rw [← hs4]
    exact (Real.sqrt_le_sqrt hmono).trans_lt
      (Real.sqrt_lt_sqrt (zeroGFFTestCov_self_nonneg isOpen_H subset_rfl _) hj)
  have h3 : Real.sqrt (zeroGFFTestCov U ⇑(φ - pushTest hc (genTest j)) ⇑(φ - pushTest hc (genTest j))) <
      Real.sqrt ε := by linarith
  exact (Real.sqrt_lt_sqrt_iff (zeroGFFTestCov_self_nonneg hUo hUH _)).1 h3

end InteractingSLE.Sec7.Lemma725RefRecovery
