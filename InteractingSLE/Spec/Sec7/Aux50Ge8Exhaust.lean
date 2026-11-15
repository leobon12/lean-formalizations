/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Limit

/-!
# Aux. lemma 50 for `κ ≥ 8`: the covariance exhaustion, (HGV11)–(HGV12)

Packet PROVE-AUX50C. Specification Aux. lemma 50, proof (`source/spec/p241-288.md` L1–L14): "Expanding the squared
`L²` norm of `N_t(φ) − N_0(φ) − I_t(φ) − J_t(φ)`, and using (HGV5), (HGV8), and (HGV11), gives exactly zero. Thus
`N_t(φ) = N_0(φ) + I_t(φ) + J_t(φ)`. This variance identity rules out every additional component, without first
classifying all possible martingale jumps or assuming removability of the full trace."

Here the Brownian part `I_t(φ)` is replaced by the **frozen piece means** `A_n = ∑ₖ E[(h, ψ_{n,k}) | 𝓕_{τ_{n,k}}]`
(each piece of `φ` at scale `2⁻ⁿ` frozen at its safe exit time `τ_{n,k}`) and the jumps `J_t(φ)` by the **pocket
fluctuations** `Y_S = ∑ₖ 1_{Eₖ} ((h, ψ_{n,k}) − E[(h, ψ_{n,k}) | 𝓕_N])`. For a coupling with infinite lifetime and a
continuous trace:

* `integral_sq_exhaust_eq`: `E[(N_N(φ) − A_n − Y_S)²] = E[Dₙ]`, `Dₙ` the pathwise variance defect of `Aux50Ge8Limit`
  (from (HGV5) in the form `integral_sq_germ_sub_sum_eq`, (HGV11) in the form `integral_mul_pocket_eq` and the pocket
  variance `integral_sq_pocketSum_eq`);
* **`tendsto_integral_sq_exhaust`**: `E[(N_N(φ) − A_n − Y_S)²] → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3 LQGMetric LocalSets WholeField Coupling Aux50Hit Sec4 LawUnique WangWu

section Coupling

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The frozen time of the piece `k` of `φ` at scale `n`, read on the killed history. -/
def pieceT (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (k : ℤ × ℤ) (ω : Ω) : ℝ≥0 :=
  safeKRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n (killedHistory W VL VR ζ ω)

omit [IsProbabilityMeasure P] in
theorem isStoppingTime_pieceT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) (φ : TestOn upperHalfPlaneOpens)
    (N n : ℕ) (k : ℤ × ℤ) :
    IsStoppingTime (drivingFiltration P hX) fun ω => (pieceT W VL VR ζ φ N n k ω : WithTop ℝ≥0) :=
  isStoppingTime_safeKRule hC.1 hζ hX (pouTest φ n k).tsupport_subset (testLow_pos _) N n

omit mΩ in
theorem pieceT_le (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (k : ℤ × ℤ) (ω : Ω) :
    pieceT W VL VR ζ φ N n k ω ≤ N :=
  safeRule_le _ _ _ _ _

omit mΩ in
/-- On a good path the frozen time is the deterministic frozen time of the driver. -/
theorem pieceT_eq {ω : Ω} (hg : IsGoodPath W VL VR ζ ω) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ)
    (k : ℤ × ℤ) : pieceT W VL VR ζ φ N n k ω = frzT (fun t => W t ω) φ N n k := by
  rw [pieceT, safeKRule, safeRule_eq hg]
  rfl

omit [IsProbabilityMeasure P] in
theorem ae_disjoint_pieceT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (k : ℤ × ℤ) :
    ∀ᵐ ω ∂P, Disjoint (tsupport (pouTest φ n k))
      (fwdHull (fun s : ℝ => W s.toNNReal ω) (pieceT W VL VR ζ φ N n k ω)) := by
  filter_upwards [ae_isGoodPath hC.1 hζ] with ω hg
  exact (safeKRule_props hg (pouTest φ n k).hasCompactSupport.isCompact (pouTest φ n k).tsupport_subset
    (testLow_pos _) (fun z hz => testLow_le _ hz) N).2.2.1 n

/-! ### The pocket field is frozen in the germ at `N` -/

/-- **A pocket test is determined by the germ at `N`**: almost surely on the pocket event of `tsupport ψ`,
`(h⁰, ψ) = E[(h⁰, ψ) | Γ_N]` (the conditional variance `G_{D_N}(ψ, ψ)` vanishes there). -/
theorem ae_eq_germMean_of_pocket (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {N : ℕ}
    (hN : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0)) {AN : Ω → Set ℂ}
    (hAN : Measurable[mΩ, hittingSigma] AN)
    (hANK : ∀ᵐ ω ∂P, AN ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((N : ℝ≥0) : ℝ)) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) →
      centredField h u₀ ω ψ =
        (P[fun ω' => centredField h u₀ ω' ψ | histGerm hN.measurableSpace AN (centredField h u₀)]) ω := by
  have hlt : ∀ᵐ ω ∂P, (((N : ℝ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  set E : Set Ω := {ω | histPoc N (tsupport ψ) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))} with hEdef
  have hh0m := measurable_centredField hC.2.1 u₀
  have hΓle : histGerm hN.measurableSpace AN (centredField h u₀) ≤ mΩ :=
    histGerm_le hN.measurableSpace_le hAN hh0m
  have hN' : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ) := hN
  have hEΓ : MeasurableSet[histGerm hN.measurableSpace AN (centredField h u₀)] E :=
    le_histGerm AN (centredField h u₀) E (measurableSet_pocketEvent hX hN' ψ)
  have hEm : MeasurableSet E := hΓle E hEΓ
  set X : Ω → ℝ := fun ω => centredField h u₀ ω ψ with hXdef
  set M := P[X | histGerm hN.measurableSpace AN (centredField h u₀)] with hM
  have hX2 : MemLp X 2 P := memLp_centredField hC hu₀ ψ
  have hM2 : MemLp M 2 P := hX2.condExp one_le_two
  have hsq := ae_condExp_sq_germ_eq hC hκ hu₀ hX hN hlt hAN hANK ψ
  -- the variance of a pocket test vanishes
  have hcov : ∀ᵐ ω ∂P, ω ∈ E → covAt W N ψ ψ ω = 0 := by
    filter_upwards [ae_isGoodPath hC.1 hζ] with ω hg hωE
    by_cases hne : (tsupport ψ).Nonempty
    · obtain ⟨β, hβN, hβ⟩ := (histPoc_iff hg N ψ.tsupport_subset hne).1 hωE
      have hw0 : Ito.rpath (fun t => W t ω) 0 = 0 := by simp [Ito.rpath, hg.2.1]
      rw [covAt, show (actDom (fun s : ℝ => W s.toNNReal ω) (N : ℝ≥0)) =
        actDom (Ito.rpath fun t => W t ω) ((N : ℝ≥0) : ℝ) from rfl,
        zeroGFFTestCov_actDom_eq (continuous_rpath_of hg.continuous) hw0 (NNReal.coe_nonneg _) ψ ψ]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun a => integral_eq_zero_of_ae
        (Eventually.of_forall fun b => ?_))
      by_cases ha : a ∈ tsupport ψ
      · have hnot : a ∉ actDom (Ito.rpath fun t => W t ω) ((N : ℝ≥0) : ℝ) := by
          intro hD
          have h1 := (mem_actDom_iff.1 hD).2
          rw [hβ a ha] at h1
          have h2 : ((β : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal ((N : ℝ≥0) : ℝ) := by
            rw [ENNReal.ofReal_coe_nnreal]; exact_mod_cast hβN
          exact absurd h1 (not_lt.2 h2)
        show ψ a * ψ b * aGreen _ _ a b = 0
        rw [aGreen_of_not_mem_left hnot, mul_zero]
      · show ψ a * ψ b * aGreen _ _ a b = 0
        rw [image_eq_zero_of_notMem_tsupport ha]; ring
    · exfalso
      exact hωE.2 (by rw [Set.not_nonempty_iff_eq_empty.1 hne]; exact Set.empty_disjoint _)
  -- `E[1_E (X − M)²] = 0`
  have hint : ∫ ω, E.indicator (fun ω => (X ω - M ω) ^ 2) ω ∂P = 0 := by
    have e1 : ∫ ω, E.indicator (fun ω => X ω ^ 2) ω ∂P =
        ∫ ω, E.indicator (fun ω => covAt W N ψ ψ ω + M ω ^ 2) ω ∂P := by
      rw [integral_indicator hEm, integral_indicator hEm, ← setIntegral_condExp hΓle hX2.integrable_sq hEΓ]
      exact setIntegral_congr_ae hEm (hsq.mono fun ω hω _ => hω)
    have e2 : ∫ ω, X ω * E.indicator M ω ∂P = ∫ ω, M ω * E.indicator M ω ∂P :=
      (integral_condExp_mul_eq hΓle hX2 (hM2.indicator hEm) (stronglyMeasurable_condExp.indicator hEΓ)).symm
    have i1 : Integrable (fun ω => E.indicator (fun ω => X ω ^ 2) ω) P := hX2.integrable_sq.indicator hEm
    have i2 : Integrable (fun ω => X ω * E.indicator M ω) P := hX2.integrable_mul (hM2.indicator hEm)
    have i3 : Integrable (fun ω => E.indicator (fun ω => M ω ^ 2) ω) P := hM2.integrable_sq.indicator hEm
    have i4 : Integrable (fun ω => 2 * (X ω * E.indicator M ω)) P := i2.const_mul 2
    have e : ∀ ω, E.indicator (fun ω => (X ω - M ω) ^ 2) ω =
        E.indicator (fun ω => X ω ^ 2) ω - 2 * (X ω * E.indicator M ω) + E.indicator (fun ω => M ω ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ E
      · simp only [indicator_of_mem hω]; ring
      · simp only [indicator_of_notMem hω]; ring
    have i14 : Integrable (fun ω => E.indicator (fun ω => X ω ^ 2) ω - 2 * (X ω * E.indicator M ω)) P :=
      i1.sub i4
    rw [integral_congr_ae (Eventually.of_forall e), integral_add i14 i3, integral_sub i1 i4,
      integral_const_mul, e1, e2]
    have i5 : Integrable (fun ω => E.indicator (fun ω => covAt W N ψ ψ ω) ω) P := by
      refine (integrable_zero Ω ℝ P).congr ?_
      filter_upwards [hcov] with ω hω
      by_cases hωE : ω ∈ E
      · rw [indicator_of_mem hωE, hω hωE]; rfl
      · rw [indicator_of_notMem hωE]; rfl
    have e3 : ∫ ω, E.indicator (fun ω => covAt W N ψ ψ ω + M ω ^ 2) ω ∂P =
        ∫ ω, E.indicator (fun ω => covAt W N ψ ψ ω) ω ∂P + ∫ ω, E.indicator (fun ω => M ω ^ 2) ω ∂P := by
      rw [← integral_add i5 i3]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ E
      · simp only [indicator_of_mem hω]
      · simp only [indicator_of_notMem hω, add_zero]
    have e4 : ∫ ω, M ω * E.indicator M ω ∂P = ∫ ω, E.indicator (fun ω => M ω ^ 2) ω ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ E
      · simp only [indicator_of_mem hω]; ring
      · simp only [indicator_of_notMem hω, mul_zero]
    have e5 : ∫ ω, E.indicator (fun ω => covAt W N ψ ψ ω) ω ∂P = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hcov] with ω hω
      by_cases hωE : ω ∈ E
      · rw [indicator_of_mem hωE, hω hωE]; rfl
      · rw [indicator_of_notMem hωE]; rfl
    rw [e3, e4, e5]
    ring
  have hnn : ∀ ω, 0 ≤ E.indicator (fun ω => (X ω - M ω) ^ 2) ω := fun ω =>
    indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hzero := (integral_eq_zero_iff_of_nonneg hnn
    (((hX2.sub hM2).integrable_sq).indicator hEm)).1 hint
  filter_upwards [hzero] with ω hω hωE
  rw [Pi.zero_apply, indicator_of_mem (show ω ∈ E from hωE)] at hω
  have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hω
  linarith

end Coupling

/-! ### The pathwise identity -/

section Pathwise

variable {w : ℝ≥0 → ℝ}

theorem integral_prod_test_aGreen (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (actDom (Ito.rpath w) t) φ ψ =
      ∫ q, φ q.1 * ψ q.2 * aGreen (Ito.rpath w) t q.1 q.2 ∂((volume : Measure ℂ).prod volume) := by
  have hW := continuous_rpath_of hw
  have hW0 : Ito.rpath w 0 = 0 := by simp [Ito.rpath, hw0]
  rw [zeroGFFTestCov_actDom_eq hW hW0 ht φ ψ]
  exact (integral_prod _ (integrable_test_aGreen hW hW0 ht φ ψ)).symm

theorem integral_prod_test_VT (hw : Continuous w) (hw0 : w 0 = 0) (N : ℝ≥0) (φ ψ : TestOn upperHalfPlaneOpens) :
    ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath w) N a b =
      ∫ q, φ q.1 * ψ q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) :=
  (integral_prod _ (integrable_test_VT hw hw0 N φ ψ)).symm

theorem integrable_test_VT_nat (hw : Continuous w) (hw0 : w 0 = 0) (N : ℕ) (φ ψ : TestOn upperHalfPlaneOpens) :
    Integrable (fun q : ℂ × ℂ => φ q.1 * ψ q.2 * VT (Ito.rpath w) N q.1 q.2) ((volume : Measure ℂ).prod volume) := by
  have := integrable_test_VT hw hw0 (N : ℝ≥0) φ ψ
  simpa only [NNReal.coe_natCast] using this

theorem integral_prod_test_VT_nat (hw : Continuous w) (hw0 : w 0 = 0) (N : ℕ) (φ ψ : TestOn upperHalfPlaneOpens) :
    ∫ a, ∫ b, φ a * ψ b * VT (Ito.rpath w) N a b =
      ∫ q, φ q.1 * ψ q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) :=
  (integral_prod _ (integrable_test_VT_nat hw hw0 N φ ψ)).symm

theorem sum_sum_integral {μ : Measure (ℂ × ℂ)} {ι : Type*} (s : Finset ι) (f : ι → ι → ℂ × ℂ → ℝ)
    (hf : ∀ k j, Integrable (f k j) μ) :
    ∑ k ∈ s, ∑ j ∈ s, ∫ q, f k j q ∂μ = ∫ q, ∑ k ∈ s, ∑ j ∈ s, f k j q ∂μ := by
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hf k j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => hf k j]

theorem sum_pouTest_apply (φ : TestOn upperHalfPlaneOpens) (n : ℕ) (z : ℂ) :
    ∑ k ∈ pIdx φ n, pouTest φ n k z = φ z := by
  have hM : testRad φ * 2 ^ n ≤ (scaleIdx (testRad φ) n : ℝ) := Nat.le_ceil _
  rw [← testOn_sum_apply, sum_pouTest (M := scaleIdx (testRad φ) n) (tsupport_subset_testRad φ) hM]

open scoped Classical in
/-- **The variance defect, regrouped.** For a continuous driver with `w 0 = 0`, a test `φ`, the pieces at scale `n`
and their pocket indicators `e k ↔ (tsupport ψ_k is a pocket at N and nonempty)`:
`∑_{k,j} (G_{τₖ ∨ τⱼ} − G_N)(ψₖ, ψⱼ) − 2 ∑ₖ e_k ∬ φ ψₖ V_N + Q_{U_N}(∑ₖ e_k ψₖ)` is the pathwise variance defect. -/
theorem pathwise_defect_eq (hw : Continuous w) (hw0 : w 0 = 0) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ)
    (e : ℤ × ℤ → Prop)
    (he : ∀ k, e k ↔ IsPocketLabel w (tsupport (pouTest φ n k)) N ∧ (tsupport (pouTest φ n k)).Nonempty) :
    (∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
        (zeroGFFTestCov (actDom (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ))
          (pouTest φ n k) (pouTest φ n j) -
          zeroGFFTestCov (actDom (Ito.rpath w) ((N : ℝ≥0) : ℝ)) (pouTest φ n k) (pouTest φ n j))) -
      2 * ∑ k ∈ pIdx φ n, (if e k then ∫ a, ∫ b, φ a * pouTest φ n k b * VT (Ito.rpath w) N a b else 0) +
      WangWu.retainedGreenEnergy w N (fun z => ∑ k ∈ pIdx φ n, (if e k then (1 : ℝ) else 0) * pouTest φ n k z) =
    ∫ q, φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2 -
        (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 +
        pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2) ∂((volume : Measure ℂ).prod volume) := by
  have hW := continuous_rpath_of hw
  have hW0 : Ito.rpath w 0 = 0 := by simp [Ito.rpath, hw0]
  set c : ℤ × ℤ → ℝ := fun k => if e k then (1 : ℝ) else 0 with hc
  -- the pocket part of `φ`, as a test
  set φP : TestOn upperHalfPlaneOpens := ∑ k ∈ pIdx φ n, c k • pouTest φ n k with hφP
  have hφPa : ∀ z, φP z = φ z * pocW w φ N n z := by
    intro z
    rw [hφP, testOn_sum_apply, pocW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hck : (if IsPocketLabel w (tsupport (pouTest φ n k)) N ∧ (tsupport (pouTest φ n k)).Nonempty
        then (1 : ℝ) else 0) = c k := by
      simp only [hc]
      by_cases hk : e k
      · simp only [hk, (he k).1 hk, and_self, ↓reduceIte]
      · have hk' : ¬ (IsPocketLabel w (tsupport (pouTest φ n k)) N ∧ (tsupport (pouTest φ n k)).Nonempty) :=
          fun h' => hk ((he k).2 h')
        simp only [hk, hk', ↓reduceIte]
    rw [hck]
    show c k * pouTest φ n k z = φ z * (c k * pouSq n k z)
    rw [pouTest_apply]; ring
  have hfP : (fun z => ∑ k ∈ pIdx φ n, c k * pouTest φ n k z) = (φP : ℂ → ℝ) := by
    funext z; rw [hφP, testOn_sum_apply]; rfl
  have iG : ∀ (t : ℝ), 0 ≤ t → ∀ k j, Integrable (fun q : ℂ × ℂ => pouTest φ n k q.1 * pouTest φ n j q.2 *
      aGreen (Ito.rpath w) t q.1 q.2) ((volume : Measure ℂ).prod volume) :=
    fun t ht k j => integrable_test_aGreen hW hW0 ht (pouTest φ n k) (pouTest φ n j)
  -- the first sum
  have hpt : ∀ q : ℂ × ℂ, ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
      (pouTest φ n k q.1 * pouTest φ n j q.2 *
          aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) q.1 q.2 -
        pouTest φ n k q.1 * pouTest φ n j q.2 * aGreen (Ito.rpath w) ((N : ℝ≥0) : ℝ) q.1 q.2) =
      φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2) := by
    intro q
    simp only [Finset.sum_sub_distrib]
    rw [sum_sum_mul_mul, sum_pouTest_apply, sum_pouTest_apply, frzKer, mul_sub, Finset.mul_sum,
      NNReal.coe_natCast]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pouTest_apply]
    ring
  set F : ℤ × ℤ → ℤ × ℤ → ℂ × ℂ → ℝ := fun k j q => pouTest φ n k q.1 * pouTest φ n j q.2 *
      aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) q.1 q.2 -
    pouTest φ n k q.1 * pouTest φ n j q.2 * aGreen (Ito.rpath w) ((N : ℝ≥0) : ℝ) q.1 q.2 with hF
  have hFi : ∀ k j, Integrable (F k j) ((volume : Measure ℂ).prod volume) := fun k j =>
    (iG _ (NNReal.coe_nonneg _) k j).sub (iG _ (NNReal.coe_nonneg _) k j)
  have hT1 : (∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
        (zeroGFFTestCov (actDom (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ))
          (pouTest φ n k) (pouTest φ n j) -
          zeroGFFTestCov (actDom (Ito.rpath w) ((N : ℝ≥0) : ℝ)) (pouTest φ n k) (pouTest φ n j))) =
      ∫ q, φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2)
        ∂((volume : Measure ℂ).prod volume) := by
    have e1 : ∀ k j, zeroGFFTestCov (actDom (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ))
          (pouTest φ n k) (pouTest φ n j) -
        zeroGFFTestCov (actDom (Ito.rpath w) ((N : ℝ≥0) : ℝ)) (pouTest φ n k) (pouTest φ n j) =
        ∫ q, F k j q ∂((volume : Measure ℂ).prod volume) := by
      intro k j
      rw [integral_prod_test_aGreen hw hw0 (NNReal.coe_nonneg _),
        integral_prod_test_aGreen hw hw0 (NNReal.coe_nonneg _), ← integral_sub (iG _ (NNReal.coe_nonneg _) k j)
          (iG _ (NNReal.coe_nonneg _) k j)]
    calc _ = ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n, ∫ q, F k j q ∂((volume : Measure ℂ).prod volume) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => e1 k j
      _ = ∫ q, ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n, F k j q ∂((volume : Measure ℂ).prod volume) :=
          sum_sum_integral _ F hFi
      _ = _ := integral_congr_ae (Eventually.of_forall hpt)
  have iA : Integrable (fun q : ℂ × ℂ => φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 -
      aGreen (Ito.rpath w) N q.1 q.2)) ((volume : Measure ℂ).prod volume) := by
    refine (integrable_finsetSum (pIdx φ n) fun k _ => integrable_finsetSum (pIdx φ n) fun j _ =>
      hFi k j).congr (Eventually.of_forall fun q => ?_)
    simp only []
    exact hpt q
  -- the pocket covariance
  have hT3 : ∑ k ∈ pIdx φ n, (if e k then ∫ a, ∫ b, φ a * pouTest φ n k b * VT (Ito.rpath w) N a b else 0) =
      ∫ q, φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) := by
    have e1 : ∀ k, (if e k then ∫ a, ∫ b, φ a * pouTest φ n k b * VT (Ito.rpath w) N a b else 0) =
        ∫ q, (fun q : ℂ × ℂ => c k * (φ q.1 * pouTest φ n k q.2 * VT (Ito.rpath w) N q.1 q.2)) q
          ∂((volume : Measure ℂ).prod volume) := by
      intro k
      rw [integral_const_mul, ← integral_prod_test_VT_nat hw hw0]
      simp only [hc]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun k _ => e1 k, ← integral_finsetSum _ fun k _ =>
      (integrable_test_VT_nat hw hw0 N φ (pouTest φ n k)).const_mul (c k)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    show ∑ k ∈ pIdx φ n, c k * (φ q.1 * pouTest φ n k q.2 * VT (Ito.rpath w) N q.1 q.2) =
      φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2
    rw [← congrFun hfP q.2, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hT3' : ∫ q, φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) =
      ∫ q, φP q.1 * φ q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) := by
    rw [← integral_prod_swap]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [show VT (Ito.rpath w) N q.2 q.1 = VT (Ito.rpath w) N q.1 q.2 by unfold VT; rw [VTe_comm]]
    ring
  -- the pocket energy
  have hT4 : WangWu.retainedGreenEnergy w N (fun z => ∑ k ∈ pIdx φ n, c k * pouTest φ n k z) =
      ∫ q, φP q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) := by
    rw [hfP, WangWu.retainedGreenEnergy, ← integral_prod_test_VT_nat hw hw0 N φP φP]
    refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae
      (Eventually.of_forall fun b => ?_))
    simp only [WangWu.retainedGreen, NNReal.coe_natCast]
    ring
  have iB := integrable_test_VT_nat hw hw0 N φ φP
  have iC := integrable_test_VT_nat hw hw0 N φP φ
  have iD := integrable_test_VT_nat hw hw0 N φP φP
  have h2 : (2 : ℝ) * ∫ q, φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) =
      ∫ q, φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) +
        ∫ q, φP q.1 * φ q.2 * VT (Ito.rpath w) N q.1 q.2 ∂((volume : Measure ℂ).prod volume) := by
    rw [← hT3']; ring
  have iBC : Integrable (fun q : ℂ × ℂ => φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 +
      φP q.1 * φ q.2 * VT (Ito.rpath w) N q.1 q.2) ((volume : Measure ℂ).prod volume) := iB.add iC
  have iABC : Integrable (fun q : ℂ × ℂ => φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 -
      aGreen (Ito.rpath w) N q.1 q.2) - (φ q.1 * φP q.2 * VT (Ito.rpath w) N q.1 q.2 +
      φP q.1 * φ q.2 * VT (Ito.rpath w) N q.1 q.2)) ((volume : Measure ℂ).prod volume) := iA.sub iBC
  rw [hT1, hT3, hT4, h2, ← integral_add iB iC, ← integral_sub iA iBC, ← integral_add iABC iD]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [hφPa]
  ring

end Pathwise

/-! ### The exhaustion -/

section Exhaust

universe v'

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v'} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The pairing with a test is square integrable. -/
theorem memLp_pairing (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (ψ : TestOn upperHalfPlaneOpens) : MemLp (fun ω => h ω ψ) 2 P := by
  have e : (fun ω => h ω ψ) = fun ω => centredField h u₀ ω ψ + ∫ z, u₀ z * ψ z := by
    funext ω; rw [centredField_apply h hu₀.1 ω ψ]; ring
  rw [e]
  exact (memLp_centredField hC hu₀ ψ).add (memLp_const _)

/-- `E[G (g − E[g | m]) 1_E] = 0` for `G`, `E` of `m`. -/
theorem integral_mul_indicator_sub_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {E : Set Ω}
    (hE : MeasurableSet[m] E) {G g : Ω → ℝ} (hG : MemLp G 2 P) (hGm : StronglyMeasurable[m] G)
    (hg : MemLp g 2 P) : ∫ ω, G ω * E.indicator (fun ω => g ω - (P[g | m]) ω) ω ∂P = 0 := by
  have hEm : MeasurableSet[mΩ] E := hm E hE
  have hG' : MemLp (E.indicator G) 2 P := hG.indicator hEm
  have hG'm : StronglyMeasurable[m] (E.indicator G) := hGm.indicator hE
  have e1 := integral_condExp_mul_eq hm hg hG' hG'm
  have i1 : Integrable (fun ω => g ω * E.indicator G ω) P := hg.integrable_mul hG'
  have i2 : Integrable (fun ω => (P[g | m]) ω * E.indicator G ω) P := (hg.condExp one_le_two).integrable_mul hG'
  rw [show (fun ω => G ω * E.indicator (fun ω => g ω - (P[g | m]) ω) ω) =
      fun ω => g ω * E.indicator G ω - (P[g | m]) ω * E.indicator G ω by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω]; ring
    · simp only [indicator_of_notMem hω]; ring, integral_sub i1 i2, e1, sub_self]

open scoped Classical in
/-- **The covariance exhaustion** ((HGV11)–(HGV12)): for a coupling with infinite lifetime and a continuous trace,
`N ≥ 1` and a test `φ`, the germ conditional mean `N_N(φ)` is the limit in `L²` of the frozen piece means plus the
pocket fluctuations: `E[(N_N(φ) − A_n − Y_{S,n})²] → 0`. -/
theorem tendsto_integral_sq_exhaust (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0)) {AN : Ω → Set ℂ}
    (hAN : Measurable[mΩ, hittingSigma] AN)
    (hANK : ∀ᵐ ω ∂P, AN ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((N : ℝ≥0) : ℝ)) (φ : TestOn upperHalfPlaneOpens) :
    Tendsto (fun n : ℕ => ∫ ω, ((P[fun ω' => centredField h u₀ ω' φ |
        histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
      ∑ k ∈ pIdx φ n, ((P[fun ω' => h ω' (pouTest φ n k) |
        (isStoppingTime_pieceT hC hζ hX φ N n k).measurableSpace]) ω - ∫ z, u₀ z * pouTest φ n k z) -
      ∑ k ∈ pIdx φ n, {ω | histPoc N (tsupport (pouTest φ n k))
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => h ω (pouTest φ n k) - (P[fun ω' => h ω' (pouTest φ n k) | hN.measurableSpace]) ω) ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hN' : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ) := hN
  have hNle : hN.measurableSpace ≤ mΩ := hN.measurableSpace_le
  have hh0m := measurable_centredField hC.2.1 u₀
  have hΓle : histGerm hN.measurableSpace AN (centredField h u₀) ≤ mΩ :=
    histGerm_le hN.measurableSpace_le hAN hh0m
  have hNΓ : hN.measurableSpace ≤ histGerm hN.measurableSpace AN (centredField h u₀) := le_histGerm _ _
  have hgood := ae_isGoodPath hC.1 hζ
  -- the pathwise defect along the coupling
  set D : ℕ → Ω → ℝ := fun n ω => ∫ q, φ q.1 * φ q.2 * (frzKer (fun t => W t ω) φ N n q.1 q.2 -
      aGreen (Ito.rpath fun t => W t ω) N q.1 q.2 -
      (pocW (fun t => W t ω) φ N n q.1 + pocW (fun t => W t ω) φ N n q.2) *
        VT (Ito.rpath fun t => W t ω) N q.1 q.2 +
      pocW (fun t => W t ω) φ N n q.1 * pocW (fun t => W t ω) φ N n q.2 * VT (Ito.rpath fun t => W t ω) N q.1 q.2)
        ∂((volume : Measure ℂ).prod volume) with hD
  -- the identity at each scale
  have key : ∀ n, ∃ R : Ω → ℝ, Integrable R P ∧ R =ᵐ[P] D n ∧
      ∫ ω, ((P[fun ω' => centredField h u₀ ω' φ | histGerm hN.measurableSpace AN (centredField h u₀)]) ω -
        ∑ k ∈ pIdx φ n, ((P[fun ω' => h ω' (pouTest φ n k) |
          (isStoppingTime_pieceT hC hζ hX φ N n k).measurableSpace]) ω - ∫ z, u₀ z * pouTest φ n k z) -
        ∑ k ∈ pIdx φ n, {ω | histPoc N (tsupport (pouTest φ n k))
            (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun ω => h ω (pouTest φ n k) - (P[fun ω' => h ω' (pouTest φ n k) | hN.measurableSpace]) ω) ω) ^ 2 ∂P =
        ∫ ω, R ω ∂P := by
    intro n
    have hτ := fun k => isStoppingTime_pieceT hC hζ hX φ N n k
    have hτN : ∀ k ω, pieceT W VL VR ζ φ N n k ω ≤ N := fun k ω => pieceT_le φ N n k ω
    have hact := fun k => ae_disjoint_pieceT hC hζ φ N n k
    have hM : testRad φ * 2 ^ n ≤ (scaleIdx (testRad φ) n : ℝ) := Nat.le_ceil _
    have hφsum : ∑ k ∈ pIdx φ n, pouTest φ n k = φ :=
      sum_pouTest (M := scaleIdx (testRad φ) n) (tsupport_subset_testRad φ) hM
    -- (a) the frozen means
    have ha := integral_sq_germ_sub_sum_eq hC hκ hu₀ hX hζ hN hAN hANK (pIdx φ n) (fun k => pouTest φ n k)
      (τ := fun k => pieceT W VL VR ζ φ N n k) hτ hτN hact
    simp only [hφsum] at ha
    -- notation
    set E : ℤ × ℤ → Set Ω := fun k => {ω | histPoc N (tsupport (pouTest φ n k))
      (stopHistory (natStop N) (killedHistory W VL VR ζ ω))} with hEdef
    have hEm : ∀ k, MeasurableSet[hN.measurableSpace] (E k) := fun k => measurableSet_pocketEvent hX hN' _
    set X : Ω → ℝ := fun ω => centredField h u₀ ω φ with hXdef
    have hX2 : MemLp X 2 P := memLp_centredField hC hu₀ φ
    set A : Ω → ℝ := fun ω => ∑ k ∈ pIdx φ n, ((P[fun ω' => h ω' (pouTest φ n k) |
      (hτ k).measurableSpace]) ω - ∫ z, u₀ z * pouTest φ n k z) with hAdef
    have hA2 : MemLp A 2 P := memLp_finsetSum _ fun k _ =>
      ((memLp_pairing hC hu₀ (pouTest φ n k)).condExp one_le_two).sub (memLp_const (∫ z, u₀ z * pouTest φ n k z))
    have hAm : StronglyMeasurable[hN.measurableSpace] A := by
      refine Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_
      exact (stronglyMeasurable_condExp.mono ((hτ k).measurableSpace_mono hN
        fun ω => WithTop.coe_le_coe.2 (hτN k ω))).sub stronglyMeasurable_const
    set y : ℤ × ℤ → Ω → ℝ := fun k => (E k).indicator (fun ω => h ω (pouTest φ n k) -
      (P[fun ω' => h ω' (pouTest φ n k) | hN.measurableSpace]) ω) with hydef
    have hy2 : ∀ k, MemLp (y k) 2 P := fun k =>
      ((memLp_pairing hC hu₀ _).sub ((memLp_pairing hC hu₀ _).condExp one_le_two)).indicator (hNle _ (hEm k))
    set YS : Ω → ℝ := fun ω => ∑ k ∈ pIdx φ n, y k ω with hYSdef
    have hYS2 : MemLp YS 2 P := memLp_finsetSum _ fun k _ => hy2 k
    set N0 := P[X | histGerm hN.measurableSpace AN (centredField h u₀)] with hN0
    have hN02 : MemLp N0 2 P := hX2.condExp one_le_two
    -- (b) the cross term
    set T3 : ℤ × ℤ → Ω → ℝ := fun k => (E k).indicator (fun ω => ∫ a, ∫ b, φ a * pouTest φ n k b *
      VT (Ito.rpath fun t => W t ω) N a b) with hT3def
    have h3 := fun k => integral_mul_pocket_eq hC hκ hu₀ hX hζ hN1 hN' φ (pouTest φ n k)
    have hAy : ∀ k, ∫ ω, A ω * y k ω ∂P = 0 := fun k =>
      integral_mul_indicator_sub_condExp hNle (hEm k) hA2 hAm (memLp_pairing hC hu₀ _)
    -- the germ mean against the pocket fluctuations
    set YS' : Ω → ℝ := fun ω => ∑ k ∈ pIdx φ n, (E k).indicator (fun ω =>
      (P[fun ω' => centredField h u₀ ω' (pouTest φ n k) | histGerm hN.measurableSpace AN (centredField h u₀)]) ω +
        (∫ z, u₀ z * pouTest φ n k z) - (P[fun ω' => h ω' (pouTest φ n k) | hN.measurableSpace]) ω) ω
      with hYS'def
    have hYSeq : YS =ᵐ[P] YS' := by
      have hg := fun k => ae_eq_germMean_of_pocket hC hκ hu₀ hX hζ hN hAN hANK (pouTest φ n k)
      filter_upwards [ae_all_iff.2 hg] with ω hω
      simp only [hYSdef, hYS'def, hydef]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : ω ∈ E k
      · rw [indicator_of_mem hk, indicator_of_mem hk, ← hω k hk, centredField_apply h hu₀.1]
        ring
      · rw [indicator_of_notMem hk, indicator_of_notMem hk]
    have hYS'm : StronglyMeasurable[histGerm hN.measurableSpace AN (centredField h u₀)] YS' := by
      refine Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_
      refine StronglyMeasurable.indicator ?_ (hNΓ _ (hEm k))
      exact StronglyMeasurable.sub (StronglyMeasurable.add (stronglyMeasurable_condExp (μ := P)
        (f := fun ω' => centredField h u₀ ω' (pouTest φ n k)))
        (stronglyMeasurable_const (b := ∫ z, u₀ z * pouTest φ n k z)))
        ((stronglyMeasurable_condExp (μ := P) (f := fun ω' => h ω' (pouTest φ n k))).mono hNΓ)
    have hYS'2 : MemLp YS' 2 P := hYS2.ae_eq hYSeq
    have hb1 : ∫ ω, N0 ω * YS ω ∂P = ∫ ω, X ω * YS ω ∂P := by
      have e1 : ∫ ω, N0 ω * YS ω ∂P = ∫ ω, N0 ω * YS' ω ∂P :=
        integral_congr_ae (by filter_upwards [hYSeq] with ω hω; rw [hω])
      have e2 : ∫ ω, X ω * YS ω ∂P = ∫ ω, X ω * YS' ω ∂P :=
        integral_congr_ae (by filter_upwards [hYSeq] with ω hω; rw [hω])
      rw [e1, e2]
      exact integral_condExp_mul_eq hΓle hX2 hYS'2 hYS'm
    have hb2 : ∫ ω, X ω * YS ω ∂P = ∑ k ∈ pIdx φ n, ∫ ω, T3 k ω ∂P := by
      have e : (fun ω => X ω * YS ω) = fun ω => ∑ k ∈ pIdx φ n, X ω * y k ω := by
        funext ω; simp only [hYSdef, Finset.mul_sum]
      rw [e, integral_finsetSum _ fun k _ =>
        (show Integrable (fun ω => X ω * y k ω) P from hX2.integrable_mul (hy2 k))]
      exact Finset.sum_congr rfl fun k _ => (h3 k).2
    have hb : ∫ ω, (N0 ω - A ω) * YS ω ∂P = ∑ k ∈ pIdx φ n, ∫ ω, T3 k ω ∂P := by
      have hAYS : ∫ ω, A ω * YS ω ∂P = 0 := by
        have e : (fun ω => A ω * YS ω) = fun ω => ∑ k ∈ pIdx φ n, A ω * y k ω := by
          funext ω; simp only [hYSdef, Finset.mul_sum]
        rw [e, integral_finsetSum _ fun k _ =>
          (show Integrable (fun ω => A ω * y k ω) P from hA2.integrable_mul (hy2 k))]
        exact Finset.sum_eq_zero fun k _ => hAy k
      have e : (fun ω => (N0 ω - A ω) * YS ω) = fun ω => N0 ω * YS ω - A ω * YS ω := by funext ω; ring
      rw [e, integral_sub (show Integrable (fun ω => N0 ω * YS ω) P from hN02.integrable_mul hYS2)
        (show Integrable (fun ω => A ω * YS ω) P from hA2.integrable_mul hYS2), hAYS, sub_zero, hb1, hb2]
    -- (c) the pocket variance
    have hc := integral_sq_pocketSum_eq hC hκ hζ hX hN' (pIdx φ n) (fun k => pouTest φ n k)
    set T4 : Ω → ℝ := fun ω => WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ pIdx φ n,
      (E k).indicator (fun _ => (1 : ℝ)) ω * pouTest φ n k z) with hT4def
    have hT4i : Integrable T4 P := hc.1
    have hYS2int : ∫ ω, YS ω ^ 2 ∂P = ∫ ω, T4 ω ∂P := hc.2
    -- (d) the frozen covariances
    have hpair := fun k j => integral_mul_germ_sub_eq hC hκ hu₀ hX hζ hN hAN hANK (hτ k) (hτ j) (hτN k) (hτN j)
      (pouTest φ n k) (pouTest φ n j) (hact k) (hact j)
    set T1 : Ω → ℝ := fun ω => ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
      (covAt W (max (pieceT W VL VR ζ φ N n k ω) (pieceT W VL VR ζ φ N n j ω)) (pouTest φ n k) (pouTest φ n j) ω -
        covAt W N (pouTest φ n k) (pouTest φ n j) ω) with hT1def
    have hT1i : Integrable T1 P := integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (hpair k j).1.sub (hpair k j).2.1
    set G : ℤ × ℤ → ℤ × ℤ → Ω → ℝ := fun k j ω =>
      covAt W (max (pieceT W VL VR ζ φ N n k ω) (pieceT W VL VR ζ φ N n j ω)) (pouTest φ n k) (pouTest φ n j) ω -
        covAt W N (pouTest φ n k) (pouTest φ n j) ω with hGdef
    have hGi : ∀ k j, Integrable (G k j) P := fun k j => (hpair k j).1.sub (hpair k j).2.1
    have hT1int : ∫ ω, T1 ω ∂P = ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
        (∫ ω, covAt W (max (pieceT W VL VR ζ φ N n k ω) (pieceT W VL VR ζ φ N n j ω)) (pouTest φ n k)
          (pouTest φ n j) ω ∂P - ∫ ω, covAt W N (pouTest φ n k) (pouTest φ n j) ω ∂P) := by
      show ∫ ω, ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n, G k j ω ∂P = _
      rw [integral_finsetSum _ (f := fun k ω => ∑ j ∈ pIdx φ n, G k j ω)
        fun k _ => integrable_finsetSum _ fun j _ => hGi k j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ (f := fun j ω => G k j ω) fun j _ => hGi k j]
      exact Finset.sum_congr rfl fun j _ => integral_sub (hpair k j).1 (hpair k j).2.1
    have hT3i : ∀ k, Integrable (T3 k) P := fun k => (h3 k).1
    set R : Ω → ℝ := fun ω => T1 ω - 2 * ∑ k ∈ pIdx φ n, T3 k ω + T4 ω with hRdef
    have hRi : Integrable R P :=
      (hT1i.sub ((integrable_finsetSum _ fun k _ => hT3i k).const_mul 2)).add hT4i
    refine ⟨R, hRi, ?_, ?_⟩
    · -- the pathwise identity
      filter_upwards [hgood] with ω hg
      have he : ∀ k, (ω ∈ E k) ↔ IsPocketLabel (fun t => W t ω) (tsupport (pouTest φ n k)) N ∧
          (tsupport (pouTest φ n k)).Nonempty := by
        intro k
        by_cases hne : (tsupport (pouTest φ n k)).Nonempty
        · rw [and_iff_left hne]
          exact histPoc_iff hg N (pouTest φ n k).tsupport_subset hne
        · rw [Set.not_nonempty_iff_eq_empty] at hne
          simp only [hEdef, mem_ofPred_eq, histPoc, hne, Set.empty_disjoint, not_true_eq_false, and_false,
            false_iff, not_and]
          intro _ h'
          exact (Set.not_nonempty_empty) h'
      have hpd := pathwise_defect_eq hg.continuous hg.2.1 φ N n (fun k => ω ∈ E k) he
      simp only [hRdef, hT1def, hT3def, hT4def, pieceT_eq hg, Set.indicator_apply]
      exact hpd
    · -- the expansion
      have hNA2 : MemLp (fun ω => N0 ω - A ω) 2 P := hN02.sub hA2
      have hha : ∫ ω, (N0 ω - A ω) ^ 2 ∂P = ∫ ω, T1 ω ∂P := by
        rw [hT1int]
        exact ha
      have e : ∀ ω, (N0 ω - A ω - YS ω) ^ 2 =
          (N0 ω - A ω) ^ 2 - 2 * ((N0 ω - A ω) * YS ω) + YS ω ^ 2 := fun ω => by ring
      have i1 : Integrable (fun ω => (N0 ω - A ω) ^ 2) P := hNA2.integrable_sq
      have i2 : Integrable (fun ω => 2 * ((N0 ω - A ω) * YS ω)) P := (hNA2.integrable_mul hYS2).const_mul 2
      have i3 : Integrable (fun ω => YS ω ^ 2) P := hYS2.integrable_sq
      have i12 : Integrable (fun ω => (N0 ω - A ω) ^ 2 - 2 * ((N0 ω - A ω) * YS ω)) P := i1.sub i2
      have j1 : Integrable (fun ω => 2 * ∑ k ∈ pIdx φ n, T3 k ω) P :=
        (integrable_finsetSum _ fun k _ => hT3i k).const_mul 2
      have j2 : Integrable (fun ω => T1 ω - 2 * ∑ k ∈ pIdx φ n, T3 k ω) P := hT1i.sub j1
      show ∫ ω, (N0 ω - A ω - YS ω) ^ 2 ∂P = ∫ ω, R ω ∂P
      rw [integral_congr_ae (Eventually.of_forall e), integral_add i12 i3, integral_sub i1 i2,
        integral_const_mul, hha, hb, hYS2int, hRdef]
      simp only
      rw [integral_add j2 hT4i, integral_sub hT1i j1, integral_const_mul,
        integral_finsetSum _ fun k _ => hT3i k]
  choose R hRi hRD hRint using key
  have hlim : Tendsto (fun n => ∫ ω, D n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun _ => exhaustBound φ)
      (fun n => (hRi n).aestronglyMeasurable.congr (hRD n)) (integrable_const _)
      (fun n => by
        filter_upwards [hgood] with ω hg
        rw [Real.norm_eq_abs]
        exact abs_exhaust_le hg.continuous hg.2.1 φ N n)
      (by
        filter_upwards [hgood, htr] with ω hg hη
        obtain ⟨η, hη⟩ := hη
        rw [hg.1] at hη
        exact tendsto_exhaust hg.continuous hg.2.1 hη φ N)
    rwa [integral_zero] at this
  refine hlim.congr fun n => ?_
  rw [hRint n, integral_congr_ae (hRD n)]

end Exhaust

end Aux50Ge8

end InteractingSLE
