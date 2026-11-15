/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Joint
import InteractingSLE.Spec.Sec7.LocalExtIPair

/-!
# The source of a random word along a good path

Packet PROVE-LOCEXT-K (Theorem 1.2's restart coupling). PROVE-LOCEXT-I made the GFF pairing with the source measurable
in the force word (`srcPairW`, approximations `srcTestW x k = v_{n_k(x)}`, `LocalExtIPair`). The path lemmas of
PROVE-LOCEXT-A2/A3 (`LocalExtA2Cond`, `LocalExtA3Joint`) are stated along the deterministic fast subsequence `srcTest`.
This file restates them for the approximations `srcTestW x k` of an admissible word `x`, along every integrated path of
that word with an admissible seed, at every time `t` before the local stop:

* `coe_srcTestW`: for an admissible word, `srcTestW x k = v_{n_k(x)}` as functions;
* `disjoint_tsupport_srcTestW_fwdHull`: their supports avoid the hull `K_t`;
* **`tendsto_params_srcTestW`**: the parameters of `a φ + c v_{n_k(x)}` converge: the means to
  `a ∫ 𝔥_t φ + c (𝔥_t, v_x)`, the energies to `a² E_t(φ) + 2ac E_t(φ, v_x) + c² E_t(v_x)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H Hbar fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)

section PathW

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {x : (Fin nL → ℝ) × (Fin nR → ℝ)}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- For an admissible word the approximations of the source are the `v_{n_k(x)}` of A2. -/
theorem coe_srcTestW (hx : IsAdmWord r x) (k : ℕ) :
    (⇑(srcTestW κ ρL ρR r x k) : ℂ → ℝ) = vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k) :=
  funext fun z => by rw [srcTestW_apply, vApproxW_of_adm κ ρL ρR r hx]

theorem tendsto_pairSeqW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    Tendsto (pairSeqW κ ρL ρR r x) atTop atTop :=
  (strictMono_pairSeqW κ ρL ρR r x).tendsto_atTop

/-- The supports of the approximations of an admissible word avoid the hull at every `t ≤ S` along a good path. -/
theorem disjoint_tsupport_srcTestW_fwdHull (hp : IsIntegratedSLEPath κ x.1 x.2 ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hx : IsAdmWord r x)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 x.1 x.2) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (k : ℕ) :
    Disjoint (tsupport (srcTestW κ ρL ρR r x k)) (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  rw [coe_srcTestW hx k]
  exact disjoint_tsupport_vApprox_fwdHull hp hterm hx.1 hx.2 hseed ht _

/-- **The parameters of `a φ + c v_{n_k(x)}` converge along a good path** at `t ≤ S`, for a test `φ` avoiding `K_t`
(the random-word form of `tendsto_params_of_isGoodPath`). -/
theorem tendsto_params_srcTestW (hp : IsIntegratedSLEPath κ x.1 x.2 ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hx : IsAdmWord r x)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 x.1 x.2) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) {u : ℂ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (a c : ℝ) :
    Tendsto (fun k => ∫ z, couplingMean κ (Ito.rpath w) t u z * (a • φ + c • srcTestW κ ρL ρR r x k) z) atTop
        (𝓝 (a * (∫ z, couplingMean κ (Ito.rpath w) t u z * φ z) +
          c * ∫ z, couplingMean κ (Ito.rpath w) t u z * vSrc κ x.1 x.2 ρL ρR r z)) ∧
      Tendsto (fun k => loewnerGreenEnergy (Ito.rpath w) t (a • φ + c • srcTestW κ ρL ρR r x k)) atTop
        (𝓝 (a ^ 2 * loewnerGreenEnergy (Ito.rpath w) t φ +
          2 * a * c * greenCross (Ito.rpath w) t φ (vSrc κ x.1 x.2 ρL ρR r) +
          c ^ 2 * loewnerGreenEnergy (Ito.rpath w) t (vSrc κ x.1 x.2 ρL ρR r))) := by
  obtain ⟨Wc, T, hreg, htT, hfwd, hhull, hmean⟩ := exists_clamp_of_le_localStopPath hp hterm hx.1 hx.2 hseed ht
  have hcont : Continuous Wc := hreg.cont
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have htI : (t : ℝ) ∈ Icc 0 T := ⟨ht0, htT⟩
  have hφc : Disjoint (tsupport φ) (fwdHull Wc t) := by rw [hhull]; exact hφ
  have hφG : IsGreenTest Wc t φ := isGreenTest_of_testOn φ hφc
  have hvG : IsGreenTest Wc t (vSrc κ x.1 x.2 ρL ρR r) := isGreenTest_vSrc hreg hx.1 hx.2 htI
  have hnG : ∀ n, IsGreenTest Wc t (vApprox κ x.1 x.2 ρL ρR r n) := isGreenTest_vApprox hreg hx.1 hx.2 htI
  have hcm : ContinuousOn (couplingMean κ (Ito.rpath w) t u) (H \ fwdHull (Ito.rpath w) t) := by
    rw [← hmean, ← hhull]
    exact continuousOn_couplingMean_alive hcont ht0 (continuousOn_of_isBoundedHarmonicExtension hu)
  have hφH : tsupport φ ⊆ H \ fwdHull (Ito.rpath w) t := Coupling.tsupport_subset_diff_fwdHull φ hφ
  have hiφ : Integrable fun z => couplingMean κ (Ito.rpath w) t u z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcm φ hφH
  have hdisj : ∀ k, Disjoint (tsupport (srcTestW κ ρL ρR r x k)) (fwdHull (Ito.rpath w) t) := fun k =>
    disjoint_tsupport_srcTestW_fwdHull hp hterm hx hseed ht k
  have hik : ∀ k, Integrable fun z => couplingMean κ (Ito.rpath w) t u z * srcTestW κ ρL ρR r x k z := fun k =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcm _
      (Coupling.tsupport_subset_diff_fwdHull _ (hdisj k))
  have hn := tendsto_pairSeqW (κ := κ) (ρL := ρL) (ρR := ρR) (r := r) x
  constructor
  · have e : ∀ k, (∫ z, couplingMean κ (Ito.rpath w) t u z * (a • φ + c • srcTestW κ ρL ρR r x k) z) =
        a * (∫ z, couplingMean κ (Ito.rpath w) t u z * φ z) +
          c * ∫ z, couplingMean κ (Ito.rpath w) t u z * vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k) z :=
      fun k => by
        have e1 : (fun z => couplingMean κ (Ito.rpath w) t u z * (a • φ + c • srcTestW κ ρL ρR r x k) z) =
            fun z => a * (couplingMean κ (Ito.rpath w) t u z * φ z) +
              c * (couplingMean κ (Ito.rpath w) t u z * srcTestW κ ρL ρR r x k z) := by
          funext z
          show couplingMean κ (Ito.rpath w) t u z * (a * φ z + c * srcTestW κ ρL ρR r x k z) = _
          ring
        rw [e1, integral_add (hiφ.const_mul a) ((hik k).const_mul c), integral_const_mul, integral_const_mul,
          coe_srcTestW hx k]
    simp_rw [e]
    exact tendsto_const_nhds.add ((tendsto_integral_couplingMean_vApprox_of_isGoodPath hp hterm hx.1 hx.2 hseed ht
      hu hn).const_mul c)
  · have e : ∀ k, loewnerGreenEnergy (Ito.rpath w) t (a • φ + c • srcTestW κ ρL ρR r x k) =
        a ^ 2 * greenCross Wc t φ φ + 2 * a * c * greenCross Wc t φ
          (vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k)) +
          c ^ 2 * greenCross Wc t (vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k))
            (vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k)) := fun k => by
      have hc : (a • ⇑φ + c • ⇑(srcTestW κ ρL ρR r x k) : ℂ → ℝ) =
          fun z => a * φ z + c * vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k) z := by
        funext z
        show a * φ z + c * srcTestW κ ρL ρR r x k z = _
        rw [coe_srcTestW hx k]
      rw [hc, loewnerGreenEnergy_eq_greenCross, ← greenCross_congr hfwd]
      exact greenCross_combo hcont ht0 hφG (hnG _) a c
    simp_rw [e]
    have h1 : Tendsto (fun k => greenCross Wc t φ (vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k))) atTop
        (𝓝 (greenCross Wc t φ (vSrc κ x.1 x.2 ρL ρR r))) :=
      tendsto_greenCross hcont ht0 hφG hvG (fun k => hnG _) hvG (fun k z => abs_vApprox_le _ z)
        fun z => (tendsto_vApprox z).comp hn
    have h2 : Tendsto (fun k => greenCross Wc t (vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k))
        (vApprox κ x.1 x.2 ρL ρR r (pairSeqW κ ρL ρR r x k))) atTop
        (𝓝 (greenCross Wc t (vSrc κ x.1 x.2 ρL ρR r) (vSrc κ x.1 x.2 ρL ρR r))) := by
      simp_rw [← loewnerGreenEnergy_eq_greenCross]
      exact tendsto_loewnerGreenEnergy_vApprox hreg hx.1 hx.2 htI hn
    rw [loewnerGreenEnergy_eq_greenCross, loewnerGreenEnergy_eq_greenCross, ← greenCross_congr hfwd,
      ← greenCross_congr hfwd, ← greenCross_congr hfwd]
    exact (tendsto_const_nhds.add (h1.const_mul _)).add (h2.const_mul _)

end PathW

end LocalExt

end InteractingSLE
