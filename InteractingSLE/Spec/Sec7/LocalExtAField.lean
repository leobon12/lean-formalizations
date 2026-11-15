/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAPath
import QuantumZipper.Proofs.GFF.Admissible

/-!
# The local comparison of Aux. lemma 55: test-function approximations of the source

Packet PROVE-LOCEXT-A, step 2 (the GFF pairing with the source). Source: Aux. lemma 55, proof
(`source/spec/p241-288.md` L146–L161, pp. 247–248): "Its pairing with the GFF is defined by approximating it by
smooth tests supported in `ℍ` outside the same neighborhood of `F`. Green-energy convergence justifies this
approximation: on a bounded set the half-plane Green kernel is dominated by a constant plus an integrable logarithmic
diagonal singularity. Dominated convergence gives `G_ℍ(v_n − v, v_n − v) → 0`."

* `cutIm n`: a smooth cutoff in `Im z`, `0` for `Im z ≤ 1/(n+1)`, `1` for `Im z ≥ 2/(n+1)`;
* `vApprox n = cutIm n · v`: a test function on `ℍ` (`vApproxTest n : TestOn upperHalfPlaneOpens`), supported in
  `{6r ≤ |z| ≤ 7r, Im z ≥ 1/(n+1)}`, with `vApprox n → v` pointwise and `|vApprox n| ≤ |v|`;
* `integrable_abs_mul_greenH`: `|v(y)| |v(z)| G_ℍ(y, z)` is integrable on `ℂ × ℂ` (QuantumZipper's admissible
  measures);
* `tendsto_greenEnergy_vApprox_sub`: **Green-energy convergence**,
  `∬ (v_n − v_m)(y) G_ℍ(y, z) (v_n − v_m)(z) → 0` as `n, m → ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H Hbar greenH)

/-! ### A smooth cutoff in the height -/

/-- `0` for `Im z ≤ 1/(n+1)`, `1` for `Im z ≥ 2/(n+1)`. -/
def cutIm (n : ℕ) (z : ℂ) : ℝ := Real.smoothTransition (((n : ℝ) + 1) * z.im - 1)

theorem contDiff_cutIm (n : ℕ) {k : ℕ∞} : ContDiff ℝ k (cutIm n) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul Complex.imCLM.contDiff).sub contDiff_const)

theorem cutIm_eq_zero {n : ℕ} {z : ℂ} (hz : z.im ≤ 1 / ((n : ℝ) + 1)) : cutIm n z = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hn] at hz
  linarith

theorem cutIm_nonneg (n : ℕ) (z : ℂ) : 0 ≤ cutIm n z := Real.smoothTransition.nonneg _

theorem cutIm_le_one (n : ℕ) (z : ℂ) : cutIm n z ≤ 1 := Real.smoothTransition.le_one _

theorem tendsto_cutIm {z : ℂ} (hz : 0 < z.im) : Tendsto (fun n => cutIm n z) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / z.im)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (Real.smoothTransition.one_of_one_le ?_).symm
  have h1 : 2 / z.im < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ hz] at h1
  linarith

/-! ### The approximating test functions -/

section Approx

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

theorem contDiff_vDens (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vDens κ xL xR ρL ρR r) := by
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fCut κ xL xR ρL ρR r) := contDiff_fCut hF hr
  have h1 : ∀ v : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ (fCut κ xL xR ρL ρR r) y v) :=
    fun v => (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have h2 : ∀ v w : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ (fun y => fderiv ℝ (fCut κ xL xR ρL ρR r) y v) z w) := fun v w =>
    ((h1 v).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hΔ : Δ (fCut κ xL xR ρL ρR r) = fun z => fderiv ℝ (fun y => fderiv ℝ (fCut κ xL xR ρL ρR r) y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ (fCut κ xL xR ρL ρR r) y Complex.I) z Complex.I :=
    funext (QuantumZipper.K3.laplacian_eq_fderiv_fderiv (hφ.of_le (by simp)))
  have hv : vDens κ xL xR ρL ρR r = fun z => -(2 * Real.pi)⁻¹ * Δ (fCut κ xL xR ρL ρR r) z := rfl
  rw [hv, hΔ]
  exact contDiff_const.mul ((h2 1 1).add (h2 Complex.I Complex.I))

variable (κ xL xR ρL ρR r) in
/-- `v_n = cutIm n · v`. -/
def vApprox (n : ℕ) (z : ℂ) : ℝ := cutIm n z * vDens κ xL xR ρL ρR r z

theorem vApprox_eq_zero_of_not (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) {z : ℂ}
    (hz : ¬ (1 / ((n : ℝ) + 1) < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r)) : vApprox κ xL xR ρL ρR r n z = 0 := by
  by_cases him : 1 / ((n : ℝ) + 1) < z.im
  · have hpos : 0 < z.im := lt_of_le_of_lt (by positivity) him
    have hS : vSrc κ xL xR ρL ρR r z = 0 := vSrc_eq_zero_of_not hF hr fun h => hz ⟨him, h.2⟩
    rw [vSrc, Set.indicator_of_mem (show z ∈ H from hpos)] at hS
    rw [vApprox, hS, mul_zero]
  · rw [vApprox, cutIm_eq_zero (not_lt.1 him), zero_mul]

theorem abs_vApprox_le (n : ℕ) (z : ℂ) :
    |vApprox κ xL xR ρL ρR r n z| ≤ |vSrc κ xL xR ρL ρR r z| := by
  by_cases hz : 0 < z.im
  · rw [vApprox, vSrc, Set.indicator_of_mem (show z ∈ H from hz), abs_mul,
      abs_of_nonneg (cutIm_nonneg n z)]
    exact mul_le_of_le_one_left (abs_nonneg _) (cutIm_le_one n z)
  · rw [vApprox, cutIm_eq_zero (le_trans (not_lt.1 hz) (by positivity)), zero_mul, abs_zero]
    exact abs_nonneg _

theorem tendsto_vApprox (z : ℂ) :
    Tendsto (fun n => vApprox κ xL xR ρL ρR r n z) atTop (𝓝 (vSrc κ xL xR ρL ρR r z)) := by
  by_cases hz : 0 < z.im
  · rw [vSrc, Set.indicator_of_mem (show z ∈ H from hz)]
    simpa [vApprox] using (tendsto_cutIm hz).mul_const (vDens κ xL xR ρL ρR r z)
  · rw [vSrc, Set.indicator_of_notMem (show z ∉ H from hz)]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [vApprox, cutIm_eq_zero (le_trans (not_lt.1 hz) (by positivity)), zero_mul]

theorem tsupport_vApprox_subset (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    tsupport (vApprox κ xL xR ρL ρR r n) ⊆ {z : ℂ | 1 / ((n : ℝ) + 1) ≤ z.im ∧ ‖z‖ ≤ 7 * r} := by
  refine closure_minimal (fun z hz => ?_)
    ((isClosed_le continuous_const Complex.continuous_im).inter (isClosed_le continuous_norm continuous_const))
  by_contra hn
  refine hz (vApprox_eq_zero_of_not hF hr n fun h => hn ⟨h.1.le, h.2.2⟩)

/-- **`v_n` is a test function on `ℍ`.** -/
def vApproxTest (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    LQGMetric.TestOn upperHalfPlaneOpens where
  toFun := vApprox κ xL xR ρL ρR r n
  contDiff' := (contDiff_cutIm n).mul (contDiff_vDens hF hr)
  hasCompactSupport' := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (7 * r)) fun z hz => by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact vApprox_eq_zero_of_not hF hr n fun h => by linarith [h.2.2]
  tsupport_subset' := fun z hz => by
    have h := (tsupport_vApprox_subset hF hr n hz).1
    change 0 < z.im
    exact lt_of_lt_of_le (by positivity) h

@[simp] theorem vApproxTest_apply (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) (z : ℂ) :
    vApproxTest (κ := κ) (ρL := ρL) (ρR := ρR) hF hr n z = vApprox κ xL xR ρL ρR r n z := rfl

/-! ### Green-energy convergence -/

/-- The half-plane Green energy `∬ φ(y) G_ℍ(y, z) ψ(z)` (the covariance of the zero-boundary GFF on `ℍ`). -/
def greenEnergy (φ ψ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 * greenH p.1 p.2 ∂((volume : Measure ℂ).prod volume)

/-- `|v(y)| |v(z)| G_ℍ(y, z)` is integrable on `ℂ × ℂ` (QuantumZipper's admissible measures). -/
theorem integrable_abs_mul_greenH (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Integrable (fun p : ℂ × ℂ => |vSrc κ xL xR ρL ρR r p.1| * |vSrc κ xL xR ρL ρR r p.2| * greenH p.1 p.2)
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨Cv, hCv0, hCv⟩ := exists_abs_vSrc_le (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |vSrc κ xL xR ρL ρR r z| with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (measurable_vSrc hF hr).abs
  have hK : IsCompact (closedBall (0 : ℂ) (7 * r) ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hadm : QuantumZipper.IsAdmissibleH (volume.withDensity g) := by
    refine QuantumZipper.isAdmissibleH_withDensity hgm (M := ENNReal.ofReal Cv) ENNReal.ofReal_lt_top
      (fun z => ENNReal.ofReal_le_ofReal (hCv z)) hK inter_subset_right fun z hz => ?_
    by_contra hne
    have hv : vSrc κ xL xR ρL ρR r z ≠ 0 := fun h0 => hne (by simp [hg, h0])
    obtain ⟨hzS, -, hz7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hv
    exact hz ⟨by rw [mem_closedBall, dist_zero_right]; exact hz7, le_of_lt hzS.1⟩
  have hI := QuantumZipper.integrable_greenH_prod hadm hadm
  have hgg : Measurable fun p : ℂ × ℂ => g p.1 * g p.2 := (hgm.comp measurable_fst).mul (hgm.comp measurable_snd)
  have hprod : (volume.withDensity g).prod (volume.withDensity g) =
      ((volume : Measure ℂ).prod volume).withDensity (fun p : ℂ × ℂ => g p.1 * g p.2) := prod_withDensity hgm hgm
  rw [hprod] at hI
  have hI2 := (integrable_withDensity_iff hgg
    (ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).1 hI
  refine hI2.congr (ae_of_all _ fun p => ?_)
  show greenH p.1 p.2 * (g p.1 * g p.2).toReal =
    |vSrc κ xL xR ρL ρR r p.1| * |vSrc κ xL xR ρL ρR r p.2| * greenH p.1 p.2
  rw [ENNReal.toReal_mul, hg, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

/-- **Green-energy convergence of the approximations** (p. 248: "Dominated convergence gives
`G_ℍ(v_n − v, v_n − v) → 0`"), in the Cauchy form used for the `L²` limit of the field pairings. -/
theorem tendsto_greenEnergy_vApprox_sub (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Tendsto (fun p : ℕ × ℕ =>
        greenEnergy (fun z => vApprox κ xL xR ρL ρR r p.1 z - vApprox κ xL xR ρL ρR r p.2 z)
          (fun z => vApprox κ xL xR ρL ρR r p.1 z - vApprox κ xL xR ρL ρR r p.2 z))
      (atTop ×ˢ atTop) (𝓝 0) := by
  have hdom := (integrable_abs_mul_greenH (κ := κ) (ρL := ρL) (ρR := ρR) hF hr).abs.const_mul 4
  have hmeasA : ∀ n, Measurable (vApprox κ xL xR ρL ρR r n) := fun n =>
    ((contDiff_cutIm n (k := 0)).continuous.mul (contDiff_vDens hF hr).continuous).measurable
  have hmeasF : ∀ p : ℕ × ℕ, Measurable fun q : ℂ × ℂ =>
      (vApprox κ xL xR ρL ρR r p.1 q.1 - vApprox κ xL xR ρL ρR r p.2 q.1) *
        (vApprox κ xL xR ρL ρR r p.1 q.2 - vApprox κ xL xR ρL ρR r p.2 q.2) * greenH q.1 q.2 := fun p => by
    have hA : Measurable fun q : ℂ × ℂ =>
        vApprox κ xL xR ρL ρR r p.1 q.1 - vApprox κ xL xR ρL ρR r p.2 q.1 :=
      ((hmeasA p.1).comp measurable_fst).sub ((hmeasA p.2).comp measurable_fst)
    have hB : Measurable fun q : ℂ × ℂ =>
        vApprox κ xL xR ρL ρR r p.1 q.2 - vApprox κ xL xR ρL ρR r p.2 q.2 :=
      ((hmeasA p.1).comp measurable_snd).sub ((hmeasA p.2).comp measurable_snd)
    exact (hA.mul hB).mul QuantumZipper.measurable_greenH
  have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℂ).prod volume)
    (l := atTop ×ˢ atTop)
    (F := fun (p : ℕ × ℕ) (q : ℂ × ℂ) => (vApprox κ xL xR ρL ρR r p.1 q.1 - vApprox κ xL xR ρL ρR r p.2 q.1) *
      (vApprox κ xL xR ρL ρR r p.1 q.2 - vApprox κ xL xR ρL ρR r p.2 q.2) * greenH q.1 q.2)
    (f := fun _ => 0) _
    (Eventually.of_forall fun p => (hmeasF p).aestronglyMeasurable)
    (Eventually.of_forall fun p => ae_of_all _ fun q => ?_) hdom (ae_of_all _ fun q => ?_)
  · simpa [greenEnergy] using key
  · simp only [Real.norm_eq_abs, abs_mul]
    have a1 := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) p.1 q.1
    have a2 := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) p.2 q.1
    have a3 := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) p.1 q.2
    have a4 := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) p.2 q.2
    have h1 : |vApprox κ xL xR ρL ρR r p.1 q.1 - vApprox κ xL xR ρL ρR r p.2 q.1| ≤
        2 * |vSrc κ xL xR ρL ρR r q.1| := (abs_sub _ _).trans (by linarith)
    have h2 : |vApprox κ xL xR ρL ρR r p.1 q.2 - vApprox κ xL xR ρL ρR r p.2 q.2| ≤
        2 * |vSrc κ xL xR ρL ρR r q.2| := (abs_sub _ _).trans (by linarith)
    calc |vApprox κ xL xR ρL ρR r p.1 q.1 - vApprox κ xL xR ρL ρR r p.2 q.1| *
          |vApprox κ xL xR ρL ρR r p.1 q.2 - vApprox κ xL xR ρL ρR r p.2 q.2| * |greenH q.1 q.2|
        ≤ (2 * |vSrc κ xL xR ρL ρR r q.1|) * (2 * |vSrc κ xL xR ρL ρR r q.2|) * |greenH q.1 q.2| := by
          gcongr
      _ = 4 * (|(|vSrc κ xL xR ρL ρR r q.1|)| * |(|vSrc κ xL xR ρL ρR r q.2|)| * |greenH q.1 q.2|) := by
          rw [abs_abs, abs_abs]; ring
  · have h1 : Tendsto (fun p : ℕ × ℕ => vApprox κ xL xR ρL ρR r p.1 q.1 - vApprox κ xL xR ρL ρR r p.2 q.1)
        (atTop ×ˢ atTop) (𝓝 0) := by
      have t1 := tendsto_vApprox (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) q.1
      have := (t1.comp tendsto_fst).sub (t1.comp tendsto_snd)
      simpa using this
    have h2 : Tendsto (fun p : ℕ × ℕ => vApprox κ xL xR ρL ρR r p.1 q.2 - vApprox κ xL xR ρL ρR r p.2 q.2)
        (atTop ×ˢ atTop) (𝓝 0) := by
      have t2 := tendsto_vApprox (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) q.2
      have := (t2.comp tendsto_fst).sub (t2.comp tendsto_snd)
      simpa using this
    simpa using (h1.mul h2).mul_const (greenH q.1 q.2)

end Approx

end LocalExt

end InteractingSLE
