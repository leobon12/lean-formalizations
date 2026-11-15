/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Joint
import InteractingSLE.Spec.Sec7.LocalExtA3Green
import InteractingSLE.Spec.Sec7.LocalExtA3Gauss

/-!
# The local comparison of Aux. lemma 55: the conditional Cameron–Martin shift (proof)

Packet PROVE-LOCEXT-A3, item 3. Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L206, p. 250):
"Conditional Cameron–Martin shifting changes the mean to `C_{K_t} − P_t f` and leaves this covariance unchanged."

**`srcJointKernelStatement`** proves the named statement `SrcJointKernelStatement κ` (`LocalExtA2Joint`) for `κ > 0`:
for a driving stop `τ ≤ S` and a test `φ`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`E[Z e^{i h(φ)} | 𝓖_τ] = N_τ · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v) φ − ½ E_τ(φ))`.

Route.
1. *Joint conditional law.* For real `a, b`, the frozen kernel at the test `aφ + b v_{n_k}` (its support avoids `K_τ` on
   the event and along good paths) gives `E[e^{i(a h(φ) + b h(v_{n_k}))} | 𝓖_τ]`; its parameters converge along each good
   path (`tendsto_params_of_isGoodPath`: the means by `tendsto_integral_couplingMean_vApprox_of_isGoodPath`, the energies
   by the quadratic expansion `greenCross_combo` and `tendsto_greenCross`), and `h(v_{n_k}) → (h, v)` almost surely. So
   on the event `(h(φ), (h, v))` is conditionally Gaussian with means `(∫ 𝔥_τ φ, (𝔥_τ, v))` and covariances
   `(E_τ(φ), E_τ(φ, v), E_τ(v))` (`ae_condExp_cexp_of_tendsto_on`).
2. *Complex tilt.* `ae_condExp_tilt_of_joint` gives `E[e^{−(h, v)} e^{i h(φ)} | 𝓖_τ] = e^{−(𝔥_τ, v) + E_τ(v)/2} ·
   exp(i(∫ 𝔥_τ φ − E_τ(φ, v)) − E_τ(φ)/2)`.
3. *Identification.* `E_τ(φ, v) = ∫ φ · G_{ℍ∖K_τ} v` (`integral_sub_greenPot_mul_eq`), and the energy identity
   `E_τ(v) = ‖f‖²_∇ − ∫₀^τ A²` turns the scalar factor into `N_τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H Hbar fwdMap fwdHull greenH logDerivFwd chiC)
open LQGMetric (TestOn DistOn)

/-! ### Green tests and continuity off the hull -/

section Tests

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {W : ℝ → ℝ} {t T : ℝ}

theorem IsGreenTest.mono {g ψ : ℂ → ℝ} (hg : IsGreenTest W t g) (hψm : Measurable ψ)
    (hle : ∀ z, |ψ z| ≤ |g z|) : IsGreenTest W t ψ := by
  obtain ⟨C, hC⟩ := hg.bdd
  obtain ⟨K, hK, hKH, hKs⟩ := hg.compact
  have hne : ∀ z, ψ z ≠ 0 → g z ≠ 0 := fun z hz h0 => hz (abs_nonpos_iff.1 (by simpa [h0] using hle z))
  exact ⟨hψm, ⟨C, fun z => (hle z).trans (hC z)⟩, ⟨K, hK, hKH, fun z hz => hKs z (hne z hz)⟩,
    fun z hz => hg.alive z (hne z hz)⟩

theorem isGreenTest_vSrc (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (ht : t ∈ Icc 0 T) : IsGreenTest W t (vSrc κ xL xR ρL ρR r) := by
  obtain ⟨C, -, hC⟩ := exists_abs_vSrc_le (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
  refine ⟨measurable_vSrc hF hr, ⟨C, hC⟩, ⟨closedBall 0 (7 * r) ∩ Hbar,
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im),
    inter_subset_right, fun z hz => ?_⟩, fun z hz => srcSet_subset h ht (mem_srcSet_of_vSrc_ne_zero hF hr hz).1⟩
  obtain ⟨hzS, -, hz7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hz
  exact ⟨by rw [mem_closedBall, dist_zero_right]; exact hz7, show (0 : ℝ) ≤ z.im from le_of_lt hzS.1⟩

theorem isGreenTest_vApprox (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (ht : t ∈ Icc 0 T) (n : ℕ) : IsGreenTest W t (vApprox κ xL xR ρL ρR r n) :=
  (isGreenTest_vSrc h hF hr ht).mono (measurable_vApprox hF hr n) (abs_vApprox_le n)

/-- The coupling mean is continuous off the hull (continuous driver). -/
theorem continuousOn_couplingMean_alive (hW : Continuous W) (ht : 0 ≤ t) {u : ℂ → ℝ} (hu : ContinuousOn u H) :
    ContinuousOn (couplingMean κ W t u) (H \ fwdHull W t) := by
  have h1 : ContinuousOn (fwdMap W t) (H \ fwdHull W t) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn
  have h2 : ContinuousOn (fun z => u (fwdMap W t z)) (H \ fwdHull W t) :=
    hu.comp h1 fun z hz => Ito.im_fwdMap_pos hW ht hz ⟨ht, le_rfl⟩
  have h3 : ContinuousOn (fun z => (logDerivFwd W t z).im) (H \ fwdHull W t) := fun z hz =>
    (Complex.continuous_im.continuousAt.comp (continuousAt_logDerivFwd hW ht hz)).continuousWithinAt
  exact h2.sub (continuousOn_const.mul h3)

end Tests

/-! ### Along a good path, through the stop -/

section Path

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- Along a good path at a time `t ≤ S`: a continuous driver in the local regime through `t` with the same `f_t`, hull
and coupling means at `t`. -/
theorem exists_clamp_of_le_localStopPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    ∃ (Wc : ℝ → ℝ) (T : ℝ), IsLocalRegime Wc r T ∧ (t : ℝ) ≤ T ∧ fwdMap Wc t = fwdMap (Ito.rpath w) t ∧
      fwdHull Wc t = fwdHull (Ito.rpath w) t ∧ ∀ u, couplingMean κ Wc t u = couplingMean κ (Ito.rpath w) t u := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have htT₂ : (t : ℝ) < T₂ := by exact_mod_cast lt_of_le_of_lt htT hTT₂
  exact ⟨Ito.clampDrv (Ito.rpath w) T₂, T, hreg, by exact_mod_cast htT,
    funext fun z => Ito.fwdMap_clampDrv_of_le htT₂.le,
    fwdHull_eq_of_eqOn t.coe_nonneg htT₂ fun s hs => Ito.clampDrv_eqOn (W := Ito.rpath w) hs,
    fun u => couplingMean_clampDrv_of_le κ _ t.coe_nonneg htT₂.le u⟩

theorem greenCross_congr {W W' : ℝ → ℝ} {t : ℝ} (h : fwdMap W t = fwdMap W' t) (φ ψ : ℂ → ℝ) :
    greenCross W t φ ψ = greenCross W' t φ ψ := by
  unfold greenCross; rw [h]

theorem greenPot_congr {W W' : ℝ → ℝ} {t : ℝ} (h : fwdMap W t = fwdMap W' t) (y : ℂ) :
    greenPot κ xL xR ρL ρR r W t y = greenPot κ xL xR ρL ρR r W' t y := by
  unfold greenPot; rw [h]

/-- **The parameters of `aφ + b v_{n_k}` converge along a good path** at `t ≤ S`, for a test `φ` avoiding `K_t`:
the means to `a ∫ 𝔥_t φ + b (𝔥_t, v)`, the energies to `a² E_t(φ) + 2ab E_t(φ, v) + b² E_t(v)`. -/
theorem tendsto_params_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) {u : ℂ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (a c : ℝ) :
    Tendsto (fun k => ∫ z, couplingMean κ (Ito.rpath w) t u z * (a • φ + c • srcTest κ ρL ρR hF hr k) z) atTop
        (𝓝 (a * (∫ z, couplingMean κ (Ito.rpath w) t u z * φ z) +
          c * ∫ z, couplingMean κ (Ito.rpath w) t u z * vSrc κ xL xR ρL ρR r z)) ∧
      Tendsto (fun k => loewnerGreenEnergy (Ito.rpath w) t (a • φ + c • srcTest κ ρL ρR hF hr k)) atTop
        (𝓝 (a ^ 2 * loewnerGreenEnergy (Ito.rpath w) t φ +
          2 * a * c * greenCross (Ito.rpath w) t φ (vSrc κ xL xR ρL ρR r) +
          c ^ 2 * loewnerGreenEnergy (Ito.rpath w) t (vSrc κ xL xR ρL ρR r))) := by
  obtain ⟨Wc, T, hreg, htT, hfwd, hhull, hmean⟩ := exists_clamp_of_le_localStopPath hp hterm hF hr hseed ht
  have hcont : Continuous Wc := hreg.cont
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have htI : (t : ℝ) ∈ Icc 0 T := ⟨ht0, htT⟩
  have hφc : Disjoint (tsupport φ) (fwdHull Wc t) := by rw [hhull]; exact hφ
  have hφG : IsGreenTest Wc t φ := isGreenTest_of_testOn φ hφc
  have hvG : IsGreenTest Wc t (vSrc κ xL xR ρL ρR r) := isGreenTest_vSrc hreg hF hr htI
  have hnG : ∀ n, IsGreenTest Wc t (vApprox κ xL xR ρL ρR r n) := isGreenTest_vApprox hreg hF hr htI
  have hcm : ContinuousOn (couplingMean κ (Ito.rpath w) t u) (H \ fwdHull (Ito.rpath w) t) := by
    rw [← hmean, ← hhull]
    exact continuousOn_couplingMean_alive hcont ht0 (continuousOn_of_isBoundedHarmonicExtension hu)
  have hφH : tsupport φ ⊆ H \ fwdHull (Ito.rpath w) t := Coupling.tsupport_subset_diff_fwdHull φ hφ
  have hiφ : Integrable fun z => couplingMean κ (Ito.rpath w) t u z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcm φ hφH
  have hdisj : ∀ k, Disjoint (tsupport (srcTest κ ρL ρR hF hr k)) (fwdHull (Ito.rpath w) t) := fun k =>
    disjoint_tsupport_vApprox_fwdHull hp hterm hF hr hseed ht _
  have hik : ∀ k, Integrable fun z => couplingMean κ (Ito.rpath w) t u z * srcTest κ ρL ρR hF hr k z := fun k =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcm _
      (Coupling.tsupport_subset_diff_fwdHull _ (hdisj k))
  constructor
  · have e : ∀ k, (∫ z, couplingMean κ (Ito.rpath w) t u z * (a • φ + c • srcTest κ ρL ρR hF hr k) z) =
        a * (∫ z, couplingMean κ (Ito.rpath w) t u z * φ z) +
          c * ∫ z, couplingMean κ (Ito.rpath w) t u z * vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k) z :=
      fun k => by
        have e1 : (fun z => couplingMean κ (Ito.rpath w) t u z * (a • φ + c • srcTest κ ρL ρR hF hr k) z) =
            fun z => a * (couplingMean κ (Ito.rpath w) t u z * φ z) +
              c * (couplingMean κ (Ito.rpath w) t u z * srcTest κ ρL ρR hF hr k z) := by
          funext z
          show couplingMean κ (Ito.rpath w) t u z * (a * φ z + c * srcTest κ ρL ρR hF hr k z) = _
          ring
        rw [e1, integral_add (hiφ.const_mul a) ((hik k).const_mul c), integral_const_mul, integral_const_mul]
        rfl
    simp_rw [e]
    exact tendsto_const_nhds.add ((tendsto_integral_couplingMean_vApprox_of_isGoodPath hp hterm hF hr hseed ht hu
      (tendsto_pairSeq hF hr)).const_mul c)
  · have e : ∀ k, loewnerGreenEnergy (Ito.rpath w) t (a • φ + c • srcTest κ ρL ρR hF hr k) =
        a ^ 2 * greenCross Wc t φ φ + 2 * a * c * greenCross Wc t φ
          (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k)) +
          c ^ 2 * greenCross Wc t (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k))
            (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k)) := fun k => by
      rw [loewnerGreenEnergy_eq_greenCross, ← greenCross_congr hfwd]
      exact greenCross_combo hcont ht0 hφG (hnG _) a c
    simp_rw [e]
    have h1 : Tendsto (fun k => greenCross Wc t φ (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k))) atTop
        (𝓝 (greenCross Wc t φ (vSrc κ xL xR ρL ρR r))) :=
      tendsto_greenCross hcont ht0 hφG hvG (fun k => hnG _) hvG (fun k z => abs_vApprox_le _ z)
        fun z => (tendsto_vApprox z).comp (tendsto_pairSeq hF hr)
    have h2 : Tendsto (fun k => greenCross Wc t (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k))
        (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k))) atTop
        (𝓝 (greenCross Wc t (vSrc κ xL xR ρL ρR r) (vSrc κ xL xR ρL ρR r))) := by
      simp_rw [← loewnerGreenEnergy_eq_greenCross]
      exact tendsto_loewnerGreenEnergy_vApprox hreg hF hr htI (tendsto_pairSeq hF hr)
    rw [loewnerGreenEnergy_eq_greenCross, loewnerGreenEnergy_eq_greenCross, ← greenCross_congr hfwd,
      ← greenCross_congr hfwd, ← greenCross_congr hfwd]
    exact (tendsto_const_nhds.add (h1.const_mul _)).add (h2.const_mul _)

/-- **`∫ (𝔥_t − G_{ℍ∖K_t} v) φ = ∫ 𝔥_t φ − E_t(φ, v)`** along a good path at `t ≤ S`, for a test `φ` avoiding `K_t`. -/
theorem integral_sub_greenPot_mul_eq (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) {u : ℂ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hu : IsBoundedHarmonicExtension g S u) :
    ∫ z, (couplingMean κ (Ito.rpath w) t u z - greenPot κ xL xR ρL ρR r (Ito.rpath w) t z) * φ z =
      (∫ z, couplingMean κ (Ito.rpath w) t u z * φ z) -
        greenCross (Ito.rpath w) t φ (vSrc κ xL xR ρL ρR r) := by
  obtain ⟨Wc, T, hreg, htT, hfwd, hhull, hmean⟩ := exists_clamp_of_le_localStopPath hp hterm hF hr hseed ht
  have hcont : Continuous Wc := hreg.cont
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hφc : Disjoint (tsupport φ) (fwdHull Wc t) := by rw [hhull]; exact hφ
  have hφG : IsGreenTest Wc t φ := isGreenTest_of_testOn φ hφc
  have hvG : IsGreenTest Wc t (vSrc κ xL xR ρL ρR r) := isGreenTest_vSrc hreg hF hr ⟨ht0, htT⟩
  have hcm : ContinuousOn (couplingMean κ (Ito.rpath w) t u) (H \ fwdHull (Ito.rpath w) t) := by
    rw [← hmean, ← hhull]
    exact continuousOn_couplingMean_alive hcont ht0 (continuousOn_of_isBoundedHarmonicExtension hu)
  have hiφ : Integrable fun z => couplingMean κ (Ito.rpath w) t u z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcm φ (Coupling.tsupport_subset_diff_fwdHull φ hφ)
  have hpot : ∀ y, greenPot κ xL xR ρL ρR r (Ito.rpath w) t y * φ y =
      ∫ z, crossKer Wc t φ (vSrc κ xL xR ρL ρR r) (y, z) := fun y => by
    rw [← greenPot_congr (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (r := r) hfwd, greenPot,
      mul_comm, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show φ y * (greenH (fwdMap Wc t y) (fwdMap Wc t z) * vSrc κ xL xR ρL ρR r z) =
      crossKer Wc t φ (vSrc κ xL xR ρL ρR r) (y, z)
    rw [← crossKer_eq hφG.alive hvG.alive y z]
    ring
  have hiG : Integrable fun y => greenPot κ xL xR ρL ρR r (Ito.rpath w) t y * φ y := by
    simp_rw [hpot]
    exact (integrable_crossKer hcont ht0 hφG hvG).integral_prod_left
  have e : (fun z => (couplingMean κ (Ito.rpath w) t u z - greenPot κ xL xR ρL ρR r (Ito.rpath w) t z) * φ z) =
      fun z => couplingMean κ (Ito.rpath w) t u z * φ z - greenPot κ xL xR ρL ρR r (Ito.rpath w) t z * φ z := by
    funext z; ring
  rw [e, integral_sub hiφ hiG]
  congr 1
  rw [greenCross_eq_integral_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show greenPot κ xL xR ρL ρR r (Ito.rpath w) t y * φ y = _
  rw [mul_comm]
  rfl

end Path

/-! ### The conditional Cameron–Martin shift -/

section Main

variable {κ : ℝ}

/-- `e^{−(h, v)}` is integrable (`E Z = 1`). -/
theorem integrable_exp_neg_srcPair {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {r : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    Integrable (fun ω => Real.exp (-srcPair κ ρL ρR hF hr (h ω))) P := by
  have hZ : Integrable (fun ω => srcDensity κ ρL ρR hF hr (h ω)) P := by
    have h1 := lintegral_srcDensity hκ hC hF hr hseed
    have := integrable_toReal_of_lintegral_ne_top
      (f := fun ω => ENNReal.ofReal (srcDensity κ ρL ρR hF hr (h ω))) (μ := P)
      ((ENNReal.measurable_ofReal.comp ((measurable_srcDensity hF hr).comp hC.2.1)).aemeasurable)
      (by rw [h1]; exact ENNReal.one_ne_top)
    refine this.congr (ae_of_all _ fun ω => ?_)
    exact ENNReal.toReal_ofReal (srcDensity_pos hF hr _).le
  refine (hZ.mul_const (Real.exp (srcNorm κ xL xR ρL ρR r / 2 - srcCentre κ xL xR ρL ρR r))).congr
    (ae_of_all _ fun ω => ?_)
  simp only [srcDensity]
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The conditional Cameron–Martin shift before the local stop** (Aux. lemma 55, p. 250; the named statement
`SrcJointKernelStatement`, proved for `κ > 0`): for a driving stop `τ ≤ S` and a test `φ`, almost surely on
`{supp φ ∩ K_τ = ∅}`, `E[Z e^{i h(φ)} | 𝓖_τ] = N_τ · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v) φ − ½ E_τ(φ))`. -/
theorem srcJointKernelStatement (hκ : 0 < κ) : SrcJointKernelStatement.{u} κ := by
  intro nL nR xL xR ρL ρR r hF hr hseed Ω mΩ P 𝓕 W VL VR B ζ h hC hX τ hτ hτS φ
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  have hhm := hC.2.1
  have hgood := ae_isGoodPath hC.1 hκ
  have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hgood, hτS] with ω hg hτω
    exact lt_of_le_of_lt hτω (localStopPath_lt hg.1 hF hr hseed hg.2)
  obtain ⟨hX', hker⟩ := hC.2.2.2
  obtain ⟨-, hK⟩ := hker τ hτ hτζ
  have hK' := hK (fun ω => bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
      (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
    fun ω => isBoundedHarmonicExtension_bheAt κ ρL ρR _ _
  have hYg := hC.2.2.1 (bheAt κ ρL ρR xL xR) (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR)
  obtain ⟨C0, hC0⟩ := (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR).2.1
  have hconv := ae_tendsto_srcPair (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
    (continuousOn_of_isBoundedHarmonicExtension (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR)) hC0 hYg
  have hY₁ : Measurable fun ω => h ω φ :=
    (measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp hhm)
  have hY₂ : Measurable fun ω => srcPair κ ρL ρR hF hr (h ω) := (measurable_srcPair hF hr).comp hhm
  have hint := integrable_exp_neg_srcPair hκ hC hF hr hseed
  -- 1. the joint conditional law of `(h(φ), (h, v))` on the event
  have hjoint : ∀ a c : ℝ, ∀ᵐ ω ∂P, ω ∈ {ω | Disjoint (tsupport φ)
      (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} →
      (P[fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + c * srcPair κ ρL ρR hF hr (h ω') : ℝ) : ℂ)) |
        hτ.measurableSpace]) ω =
        cfVal (a * (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
              (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) z * φ z) +
            c * srcMeanAt κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω)
          (a ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ +
            2 * a * c * greenCross (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ
              (vSrc κ xL xR ρL ρR r) +
            c ^ 2 * srcEnergyAt κ xL xR ρL ρR r W ((τ ω).untopD 0) ω) := by
    intro a c
    refine ae_condExp_cexp_of_tendsto_on (m := hτ.measurableSpace)
      (Y := fun k ω => h ω (a • φ + c • srcTest κ ρL ρR hF hr k))
      (a := fun k ω => ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) z * (a • φ + c • srcTest κ ρL ρR hF hr k) z)
      (q := fun k ω => loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (a • φ + c • srcTest κ ρL ρR hF hr k))
      (fun k => ((measurable_pi_apply _).comp ((LQGMetric.measurable_distEval _).comp hhm)).aemeasurable)
      (fun k => ?_) ?_ ?_
    · filter_upwards [hK' (a • φ + c • srcTest κ ρL ρR hF hr k), hgood, hτS] with ω h1 hg hτω hD
      refine h1 (Disjoint.mono_left (tsupport_add _ _) (Disjoint.union_left ?_ ?_))
      · exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ => a) φ) hD
      · exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ => c) (srcTest κ ρL ρR hF hr k))
          (disjoint_tsupport_vApprox_fwdHull hg.1 hg.2 hF hr hseed (coe_untopD_le_localStopPath hτω) _)
    · filter_upwards [hconv] with ω hω
      have e : ∀ k, h ω (a • φ + c • srcTest κ ρL ρR hF hr k) =
          a * h ω φ + c * h ω (srcTest κ ρL ρR hF hr k) := fun k => by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp_rw [e]
      exact tendsto_const_nhds.add (hω.const_mul c)
    · filter_upwards [hgood, hτS] with ω hg hτω hD
      exact tendsto_params_of_isGoodPath hg.1 hg.2 hF hr hseed (coe_untopD_le_localStopPath hτω) φ hD
        (isBoundedHarmonicExtension_bheAt κ ρL ρR _ _) a c
  -- 2. the complex tilt
  have key := ae_condExp_tilt_of_joint (m := hτ.measurableSpace) hτ.measurableSpace_le hY₁ hY₂ hint hjoint
  -- 3. identification
  set k : ℝ := Real.exp (srcCentre κ xL xR ρL ρR r - srcNorm κ xL xR ρL ρR r / 2) with hk
  have hfun : (fun ω' => ((srcDensity κ ρL ρR hF hr (h ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      fun ω' => (k : ℂ) • (((Real.exp (-srcPair κ ρL ρR hF hr (h ω')) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (h ω' φ : ℂ))) := by
    funext ω'
    rw [smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, srcDensity]
    congr 3
    ring
  have hsm : P[fun ω' => (k : ℂ) • (((Real.exp (-srcPair κ ρL ρR hF hr (h ω')) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (h ω' φ : ℂ))) | hτ.measurableSpace] =ᵐ[P]
      fun ω => (k : ℂ) • (P[fun ω' => ((Real.exp (-srcPair κ ρL ρR hF hr (h ω')) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace]) ω :=
    condExp_smul (μ := P) (k : ℂ) (fun ω' => ((Real.exp (-srcPair κ ρL ρR hF hr (h ω')) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (h ω' φ : ℂ))) hτ.measurableSpace
  rw [hfun]
  filter_upwards [key, hsm, hgood, hτS] with ω h1 h2 hg hτω hD
  have hD' : Disjoint (tsupport φ) (fwdHull (Ito.rpath fun t => W t ω) ((τ ω).untopD 0 : ℝ≥0)) := hD
  have e1 : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) z -
        greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) z) * φ z) =
      (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) z * φ z) -
        greenCross (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ (vSrc κ xL xR ρL ρR r) :=
    integral_sub_greenPot_mul_eq hg.1 hg.2 hF hr hseed (coe_untopD_le_localStopPath hτω) φ hD'
      (isBoundedHarmonicExtension_bheAt κ ρL ρR _ _)
  have e2 : srcEnergyAt κ xL xR ρL ρR r W ((τ ω).untopD 0) ω = srcNorm κ xL xR ρL ρR r -
      ∫ u in (0 : ℝ)..((τ ω).untopD 0 : ℝ≥0), srcDrift κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) u ^ 2 :=
    loewnerGreenEnergy_vSrc_eq_of_isGoodPath hg.1 hg.2 hF hr hseed (coe_untopD_le_localStopPath hτω)
  rw [h2, h1 hD, smul_eq_mul, e1, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, e2, srcMart]
  congr 3
  ring

end Main

end LocalExt

end InteractingSLE
