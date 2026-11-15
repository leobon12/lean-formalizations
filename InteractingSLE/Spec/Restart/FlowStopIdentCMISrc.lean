/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Pair

/-!
# The Cameron–Martin source of a cutoff field and its GFF pairing

Packet PROVE-L1-CMI (Lemma G3's proof, supplement §7.3, `source/spec/p481-528.md` L290–L320, pp. 492–493: "the
weighted comparison field is `h + f`, with `f = v` on `U` […] by Cameron–Martin"). The explicit density of the
comparison is `exp(−(h, v))`, `v = (2π)⁻¹ Δ f` the source of the cutoff `f`. Its support meets `ℝ`, so `(h, v)`
is defined by approximating `v` by test functions supported in `ℍ`. This file does this for **every** cutoff
(PROVE-LOCEXT-A2 did it for Aux. lemma 55's specific source `LocalExt.vSrc`; the proofs below are copies of
`LocalExt.vApprox`, `LocalExt.srcPair` and their lemmas with the source abstracted):

* `CMCut`: a smooth, compactly supported, odd (`f(z̄) = −f(z)`) real function `f`; `CMCut.neg`;
* `CMCut.src F = −1_ℍ · greenDensity f = 1_ℍ (2π)⁻¹ Δ f`: the source of the tilt (`−G_ℍ(F.src) = f` on `ℍ` is
  `CMCut.integral_greenH_mul_src`, in `FlowStopIdentCMIShift`);
* `CMCut.approx F n = cutIm n · (−greenDensity f)` and `CMCut.test F n : TestOn ℍ`: the approximating test
  functions, `|F.approx n| ≤ |F.src|`, `F.approx n → F.src` pointwise;
* `CMCut.tendsto_greenEnergy_approx_sub`: Green-energy convergence;
* `CMCut.seq F`: a deterministic fast subsequence; `CMCut.testSeq F k = F.test (F.seq k)`;
* **`CMCut.pair F : DistOn ℍ → ℝ`**, a Borel function of the field (`CMCut.measurable_pair`), and
  **`CMCut.ae_tendsto_pair`**: for every field whose centred pairings form a zero-boundary GFF process on `ℍ` around a
  bounded function continuous on `ℍ`, `h(F.testSeq k) → F.pair h` almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar greenH)
open LQGMetric (TestOn DistOn)
open LocalExt (cutIm greenEnergy)

/-- **A cutoff field**: a smooth, compactly supported, odd real function on `ℂ`. -/
structure CMCut where
  /-- the function -/
  f : ℂ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f
  compact : HasCompactSupport f
  odd : ∀ z, f (conj z) = -f z

namespace CMCut

variable (F : CMCut)

/-- The negated cutoff. -/
def neg : CMCut where
  f := fun z => -F.f z
  smooth := F.smooth.neg
  compact := F.compact.neg
  odd := fun z => by rw [F.odd z]

@[simp] theorem neg_f (z : ℂ) : F.neg.f z = -F.f z := rfl

/-- The density `greenDensity f = −(2π)⁻¹ Δ f` is smooth (copy of `LocalExt.contDiff_vDens`). -/
theorem contDiff_greenDensity : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (QuantumZipper.K3.greenDensity F.f) := by
  have hφ := F.smooth
  have h1 : ∀ v : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ F.f y v) :=
    fun v => (hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have h2 : ∀ v w : ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ (fun y => fderiv ℝ F.f y v) z w) := fun v w =>
    ((h1 v).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hΔ : Δ F.f = fun z => fderiv ℝ (fun y => fderiv ℝ F.f y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ F.f y Complex.I) z Complex.I :=
    funext (QuantumZipper.K3.laplacian_eq_fderiv_fderiv (hφ.of_le (by simp)))
  have hv : QuantumZipper.K3.greenDensity F.f = fun z => -(2 * Real.pi)⁻¹ * Δ F.f z := rfl
  rw [hv, hΔ]
  exact contDiff_const.mul ((h2 1 1).add (h2 Complex.I Complex.I))

theorem continuous_greenDensity : Continuous (QuantumZipper.K3.greenDensity F.f) :=
  F.contDiff_greenDensity.continuous

theorem hasCompactSupport_greenDensity : HasCompactSupport (QuantumZipper.K3.greenDensity F.f) :=
  QuantumZipper.K3.hasCompactSupport_greenDensity F.compact

theorem greenDensity_neg (z : ℂ) :
    QuantumZipper.K3.greenDensity F.neg.f z = -QuantumZipper.K3.greenDensity F.f z := by
  have e : F.neg.f = fun y => -F.f y := rfl
  simp only [QuantumZipper.K3.greenDensity, e, LocalExt.laplacian_neg_apply]
  ring

/-! ### The source -/

/-- **The source of the tilt** `v = −1_ℍ · greenDensity f = 1_ℍ (2π)⁻¹ Δ f`. -/
def src (z : ℂ) : ℝ := -H.indicator (QuantumZipper.K3.greenDensity F.f) z

theorem src_of_mem {z : ℂ} (hz : z ∈ H) : F.src z = -QuantumZipper.K3.greenDensity F.f z := by
  rw [src, Set.indicator_of_mem hz]

theorem src_of_notMem {z : ℂ} (hz : z ∉ H) : F.src z = 0 := by
  rw [src, Set.indicator_of_notMem hz, neg_zero]

theorem src_neg (z : ℂ) : F.neg.src z = -F.src z := by
  by_cases hz : z ∈ H
  · rw [src_of_mem _ hz, src_of_mem _ hz, greenDensity_neg]
  · rw [src_of_notMem _ hz, src_of_notMem _ hz, neg_zero]

theorem measurable_src : Measurable F.src :=
  (F.continuous_greenDensity.measurable.indicator
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet).neg

theorem exists_abs_src_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |F.src z| ≤ C := by
  obtain ⟨C, hC⟩ := F.hasCompactSupport_greenDensity.exists_bound_of_continuous F.continuous_greenDensity
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ H
  · rw [src_of_mem _ hz, abs_neg, ← Real.norm_eq_abs]; exact (hC z).trans (le_max_left _ _)
  · rw [src_of_notMem _ hz, abs_zero]; exact le_max_right _ _

theorem src_eq_zero_of_notMem_tsupport {z : ℂ} (hz : z ∉ tsupport (QuantumZipper.K3.greenDensity F.f)) :
    F.src z = 0 := by
  by_cases hzH : z ∈ H
  · rw [src_of_mem _ hzH, image_eq_zero_of_notMem_tsupport hz, neg_zero]
  · exact src_of_notMem _ hzH

/-- The points where the source is nonzero lie in `ℍ` and in the support of `f`. -/
theorem mem_of_src_ne_zero {z : ℂ} (hz : F.src z ≠ 0) :
    z ∈ H ∧ z ∈ tsupport (QuantumZipper.K3.greenDensity F.f) := by
  by_cases hzH : z ∈ H
  · refine ⟨hzH, subset_tsupport _ fun h0 => hz ?_⟩
    rw [src_of_mem _ hzH, h0, neg_zero]
  · exact absurd (src_of_notMem _ hzH) hz

theorem integrable_src : Integrable F.src :=
  ((F.continuous_greenDensity.integrable_of_hasCompactSupport F.hasCompactSupport_greenDensity).indicator
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet).neg

/-! ### The approximating test functions -/

/-- The approximation `cutIm n · (−greenDensity f)` of the source. -/
def approx (n : ℕ) (z : ℂ) : ℝ := cutIm n z * -QuantumZipper.K3.greenDensity F.f z

theorem contDiff_approx (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.approx n) :=
  (LocalExt.contDiff_cutIm n).mul F.contDiff_greenDensity.neg

theorem approx_eq_zero_of_im_le {n : ℕ} {z : ℂ} (hz : z.im ≤ 1 / ((n : ℝ) + 1)) : F.approx n z = 0 := by
  rw [approx, LocalExt.cutIm_eq_zero hz, zero_mul]

theorem abs_approx_le (n : ℕ) (z : ℂ) : |F.approx n z| ≤ |F.src z| := by
  by_cases hz : 0 < z.im
  · rw [approx, src_of_mem _ (show z ∈ H from hz), abs_mul, abs_of_nonneg (LocalExt.cutIm_nonneg n z)]
    exact mul_le_of_le_one_left (abs_nonneg _) (LocalExt.cutIm_le_one n z)
  · rw [F.approx_eq_zero_of_im_le (le_trans (not_lt.1 hz) (by positivity)), abs_zero]
    exact abs_nonneg _

theorem tendsto_approx (z : ℂ) : Tendsto (fun n => F.approx n z) atTop (𝓝 (F.src z)) := by
  by_cases hz : 0 < z.im
  · rw [src_of_mem _ (show z ∈ H from hz)]
    simpa [approx] using (LocalExt.tendsto_cutIm hz).mul_const (-QuantumZipper.K3.greenDensity F.f z)
  · rw [src_of_notMem _ (show z ∉ H from hz)]
    exact tendsto_const_nhds.congr fun n => (F.approx_eq_zero_of_im_le
      (le_trans (not_lt.1 hz) (by positivity))).symm

theorem tsupport_approx_subset (n : ℕ) :
    tsupport (F.approx n) ⊆ {z : ℂ | 1 / ((n : ℝ) + 1) ≤ z.im} ∩ tsupport (QuantumZipper.K3.greenDensity F.f) := by
  refine closure_minimal (fun z hz => ⟨?_, subset_tsupport _ fun h0 => hz ?_⟩)
    ((isClosed_le continuous_const Complex.continuous_im).inter (isClosed_tsupport _))
  · by_contra hn
    exact hz (F.approx_eq_zero_of_im_le (not_le.1 hn).le)
  · rw [approx, h0, neg_zero, mul_zero]

/-- **The approximations are test functions on `ℍ`.** -/
def test (n : ℕ) : TestOn upperHalfPlaneOpens where
  toFun := F.approx n
  contDiff' := F.contDiff_approx n
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact F.hasCompactSupport_greenDensity
    ((subset_tsupport _).trans fun z hz => (F.tsupport_approx_subset n hz).2)
  tsupport_subset' := fun z hz => by
    have h := (F.tsupport_approx_subset n hz).1
    change 0 < z.im
    exact lt_of_lt_of_le (by positivity) h

theorem test_apply (n : ℕ) (z : ℂ) : F.test n z = F.approx n z := rfl

/-! ### Green-energy convergence -/

/-- `|v(y)| |v(z)| G_ℍ(y, z)` is integrable on `ℂ × ℂ` (copy of `LocalExt.integrable_abs_mul_greenH`). -/
theorem integrable_abs_mul_greenH :
    Integrable (fun p : ℂ × ℂ => |F.src p.1| * |F.src p.2| * greenH p.1 p.2)
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨Cv, -, hCv⟩ := F.exists_abs_src_le
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |F.src z| with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp F.measurable_src.abs
  have hK : IsCompact (tsupport (QuantumZipper.K3.greenDensity F.f) ∩ Hbar) :=
    F.hasCompactSupport_greenDensity.isCompact.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hadm : QuantumZipper.IsAdmissibleH (volume.withDensity g) := by
    refine QuantumZipper.isAdmissibleH_withDensity hgm (M := ENNReal.ofReal Cv) ENNReal.ofReal_lt_top
      (fun z => ENNReal.ofReal_le_ofReal (hCv z)) hK inter_subset_right fun z hz => ?_
    by_contra hne
    have hv : F.src z ≠ 0 := fun h0 => hne (by simp [hg, h0])
    obtain ⟨hzH, hzt⟩ := F.mem_of_src_ne_zero hv
    exact hz ⟨hzt, show (0 : ℝ) ≤ z.im from le_of_lt hzH⟩
  have hI := QuantumZipper.integrable_greenH_prod hadm hadm
  have hgg : Measurable fun p : ℂ × ℂ => g p.1 * g p.2 := (hgm.comp measurable_fst).mul (hgm.comp measurable_snd)
  have hprod : (volume.withDensity g).prod (volume.withDensity g) =
      ((volume : Measure ℂ).prod volume).withDensity (fun p : ℂ × ℂ => g p.1 * g p.2) := prod_withDensity hgm hgm
  rw [hprod] at hI
  have hI2 := (integrable_withDensity_iff hgg
    (ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).1 hI
  refine hI2.congr (ae_of_all _ fun p => ?_)
  show greenH p.1 p.2 * (g p.1 * g p.2).toReal = |F.src p.1| * |F.src p.2| * greenH p.1 p.2
  rw [ENNReal.toReal_mul, hg, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

/-- **Green-energy convergence of the approximations** (copy of `LocalExt.tendsto_greenEnergy_vApprox_sub`). -/
theorem tendsto_greenEnergy_approx_sub :
    Tendsto (fun p : ℕ × ℕ => greenEnergy (fun z => F.approx p.1 z - F.approx p.2 z)
      (fun z => F.approx p.1 z - F.approx p.2 z)) (atTop ×ˢ atTop) (𝓝 0) := by
  have hdom := F.integrable_abs_mul_greenH.abs.const_mul 4
  have hmeasA : ∀ n, Measurable (F.approx n) := fun n => (F.contDiff_approx n).continuous.measurable
  have hmeasF : ∀ p : ℕ × ℕ, Measurable fun q : ℂ × ℂ =>
      (F.approx p.1 q.1 - F.approx p.2 q.1) * (F.approx p.1 q.2 - F.approx p.2 q.2) * greenH q.1 q.2 :=
    fun p => ((((hmeasA p.1).comp measurable_fst).sub ((hmeasA p.2).comp measurable_fst)).mul
      (((hmeasA p.1).comp measurable_snd).sub ((hmeasA p.2).comp measurable_snd))).mul
        QuantumZipper.measurable_greenH
  have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℂ).prod volume)
    (l := atTop ×ˢ atTop)
    (F := fun (p : ℕ × ℕ) (q : ℂ × ℂ) => (F.approx p.1 q.1 - F.approx p.2 q.1) *
      (F.approx p.1 q.2 - F.approx p.2 q.2) * greenH q.1 q.2)
    (f := fun _ => 0) _
    (Eventually.of_forall fun p => (hmeasF p).aestronglyMeasurable)
    (Eventually.of_forall fun p => ae_of_all _ fun q => ?_) hdom (ae_of_all _ fun q => ?_)
  · simpa [greenEnergy] using key
  · simp only [Real.norm_eq_abs, abs_mul]
    have a1 := F.abs_approx_le p.1 q.1
    have a2 := F.abs_approx_le p.2 q.1
    have a3 := F.abs_approx_le p.1 q.2
    have a4 := F.abs_approx_le p.2 q.2
    have h1 : |F.approx p.1 q.1 - F.approx p.2 q.1| ≤ 2 * |F.src q.1| := (abs_sub _ _).trans (by linarith)
    have h2 : |F.approx p.1 q.2 - F.approx p.2 q.2| ≤ 2 * |F.src q.2| := (abs_sub _ _).trans (by linarith)
    calc |F.approx p.1 q.1 - F.approx p.2 q.1| * |F.approx p.1 q.2 - F.approx p.2 q.2| * |greenH q.1 q.2|
        ≤ (2 * |F.src q.1|) * (2 * |F.src q.2|) * |greenH q.1 q.2| := by gcongr
      _ = 4 * (|(|F.src q.1|)| * |(|F.src q.2|)| * |greenH q.1 q.2|) := by rw [abs_abs, abs_abs]; ring
  · have h1 : Tendsto (fun p : ℕ × ℕ => F.approx p.1 q.1 - F.approx p.2 q.1) (atTop ×ˢ atTop) (𝓝 0) := by
      have t1 := F.tendsto_approx q.1
      simpa using (t1.comp tendsto_fst).sub (t1.comp tendsto_snd)
    have h2 : Tendsto (fun p : ℕ × ℕ => F.approx p.1 q.2 - F.approx p.2 q.2) (atTop ×ˢ atTop) (𝓝 0) := by
      have t2 := F.tendsto_approx q.2
      simpa using (t2.comp tendsto_fst).sub (t2.comp tendsto_snd)
    simpa using (h1.mul h2).mul_const (greenH q.1 q.2)

/-! ### A deterministic fast subsequence -/

theorem eventually_greenEnergy_approx_sub_lt {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N in atTop, ∀ n m : ℕ, N ≤ n → N ≤ m →
    greenEnergy (fun z => F.approx n z - F.approx m z) (fun z => F.approx n z - F.approx m z) < ε := by
  have h := (tendsto_order.1 F.tendsto_greenEnergy_approx_sub).2 ε hε
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self'] at h
  obtain ⟨a, ha⟩ := h
  filter_upwards [eventually_ge_atTop a] with N hN n m hn hm
  exact ha n (hN.trans hn) m (hN.trans hm)

theorem exists_seq : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k n m : ℕ, φ k ≤ n → φ k ≤ m →
    greenEnergy (fun z => F.approx n z - F.approx m z) (fun z => F.approx n z - F.approx m z) <
      (1 / 16 : ℝ) ^ k :=
  extraction_forall_of_eventually fun k => F.eventually_greenEnergy_approx_sub_lt (by positivity)

/-- **The fast subsequence `n_k`**: `G_ℍ(v_n − v_m, v_n − v_m) < 16^{-k}` for `n, m ≥ n_k`. -/
def seq : ℕ → ℕ := Classical.choose F.exists_seq

theorem strictMono_seq : StrictMono F.seq := (Classical.choose_spec F.exists_seq).1

theorem greenEnergy_seq_lt {k n m : ℕ} (hn : F.seq k ≤ n) (hm : F.seq k ≤ m) :
    greenEnergy (fun z => F.approx n z - F.approx m z) (fun z => F.approx n z - F.approx m z) <
      (1 / 16 : ℝ) ^ k :=
  (Classical.choose_spec F.exists_seq).2 k n m hn hm

theorem tendsto_seq : Tendsto F.seq atTop atTop := F.strictMono_seq.tendsto_atTop

/-- The approximating test function `v_{n_k}`. -/
def testSeq (k : ℕ) : TestOn upperHalfPlaneOpens := F.test (F.seq k)

theorem testSeq_apply (k : ℕ) (z : ℂ) : F.testSeq k z = F.approx (F.seq k) z := rfl

theorem abs_testSeq_le (k : ℕ) (z : ℂ) : |F.testSeq k z| ≤ |F.src z| := F.abs_approx_le _ z

theorem tendsto_testSeq (z : ℂ) : Tendsto (fun k => F.testSeq k z) atTop (𝓝 (F.src z)) :=
  (F.tendsto_approx z).comp F.tendsto_seq

theorem tsupport_testSeq_subset (k : ℕ) :
    tsupport (F.testSeq k) ⊆ tsupport (QuantumZipper.K3.greenDensity F.f) :=
  fun _ hz => (F.tsupport_approx_subset _ hz).2

/-! ### The pairing as a Borel function of the field -/

/-- **The GFF pairing with the source**, a Borel function of the field: `T ↦ lim_k T(v_{n_k})`. -/
def pair (T : DistOn upperHalfPlaneOpens) : ℝ := limUnder atTop fun k => T (F.testSeq k)

theorem measurable_pair : Measurable F.pair := by
  have h : ∀ k, StronglyMeasurable fun T : DistOn upperHalfPlaneOpens => T (F.testSeq k) :=
    fun k => ((measurable_pi_apply (F.testSeq k)).comp
      (LQGMetric.measurable_distEval upperHalfPlaneOpens)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder h).measurable

/-! ### Almost sure convergence of the approximate pairings -/

section Conv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- The means `∫ u₀ v_{n_k}` converge to `∫ u₀ v` (copy of `LocalExt.tendsto_integral_mul_srcTest`). -/
theorem tendsto_integral_mul_testSeq (hu₀ : ContinuousOn u₀ H) {C : ℝ} (hC : ∀ z ∈ H, |u₀ z| ≤ C) :
    Tendsto (fun k => ∫ z, u₀ z * F.testSeq k z) atTop (𝓝 (∫ z, u₀ z * F.src z)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => C * |F.src z|)
    (fun k => (LocalExt.integrable_mul_testOn hu₀ (F.testSeq k)).aestronglyMeasurable)
    (F.integrable_src.abs.const_mul C) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : z ∈ H
    · exact mul_le_mul (hC z hz) (F.abs_testSeq_le k z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))
    · have h1 := F.abs_testSeq_le k z
      rw [F.src_of_notMem hz, abs_zero] at h1
      rw [abs_nonpos_iff.1 h1, F.src_of_notMem hz, abs_zero, mul_zero, mul_zero]
  · exact tendsto_const_nhds.mul (F.tendsto_testSeq z)

/-- The `L²` distance of two centred approximate pairings (copy of `LocalExt.integral_sq_sub_srcTest`). -/
theorem integral_sq_sub_testSeq [IsProbabilityMeasure P] (hu₀ : ContinuousOn u₀ H)
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) (n m : ℕ) :
    ∫ ω, ((h ω (F.testSeq n) - ∫ z, u₀ z * F.testSeq n z) -
        (h ω (F.testSeq m) - ∫ z, u₀ z * F.testSeq m z)) ^ 2 ∂P =
      greenEnergy (fun z => F.approx (F.seq n) z - F.approx (F.seq m) z)
        (fun z => F.approx (F.seq n) z - F.approx (F.seq m) z) := by
  set ψ := F.testSeq n - F.testSeq m with hψ
  have e : ∀ ω, (h ω (F.testSeq n) - ∫ z, u₀ z * F.testSeq n z) -
      (h ω (F.testSeq m) - ∫ z, u₀ z * F.testSeq m z) = h ω ψ - ∫ z, u₀ z * ψ z := fun ω => by
    have hi : ∫ z, u₀ z * ψ z = (∫ z, u₀ z * F.testSeq n z) - ∫ z, u₀ z * F.testSeq m z := by
      rw [← integral_sub (LocalExt.integrable_mul_testOn hu₀ _) (LocalExt.integrable_mul_testOn hu₀ _)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hψ]
      change u₀ z * (F.testSeq n z - F.testSeq m z) = _
      ring
    rw [hi, hψ, map_sub]
    ring
  simp_rw [e]
  rw [LocalExt.integral_sq_zbProcess hY ψ]
  rfl

/-- **The approximate pairings converge almost surely** to the Borel pairing `pair` (copy of
`LocalExt.ae_tendsto_srcPair`), for every field whose centred pairings form a zero-boundary GFF process on `ℍ` around a
bounded function `u₀` continuous on `ℍ`. -/
theorem ae_tendsto_pair [IsProbabilityMeasure P] (hu₀ : ContinuousOn u₀ H) {C : ℝ} (hC : ∀ z ∈ H, |u₀ z| ≤ C)
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) :
    ∀ᵐ ω ∂P, Tendsto (fun k => h ω (F.testSeq k)) atTop (𝓝 (F.pair (h ω))) := by
  set g : ℕ → Ω → ℝ := fun k ω => h ω (F.testSeq k) - ∫ z, u₀ z * F.testSeq k z with hg
  have hB : ∑' i : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ i) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (g n - g m) 2 P < ENNReal.ofReal ((1 / 4 : ℝ) ^ N) := by
    intro N n m hn hm
    have hL2 : MemLp (g n - g m) 2 P :=
      (LocalExt.memLp_zbProcess hY _ ENNReal.ofNat_ne_top).sub
        (LocalExt.memLp_zbProcess hY _ ENNReal.ofNat_ne_top)
    rw [Girsanov.eLpNorm_two_eq_sqrt hL2]
    have hI : ∫ ω, (g n - g m) ω ^ 2 ∂P < (1 / 16 : ℝ) ^ N := by
      simp only [hg, Pi.sub_apply]
      rw [F.integral_sq_sub_testSeq hu₀ hY n m]
      exact F.greenEnergy_seq_lt (F.strictMono_seq.monotone hn) (F.strictMono_seq.monotone hm)
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    rw [show (1 / 4 : ℝ) ^ N = Real.sqrt ((1 / 16 : ℝ) ^ N) by
      rw [show (1 / 16 : ℝ) ^ N = ((1 / 4 : ℝ) ^ N) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (integral_nonneg fun ω => sq_nonneg _) hI
  have hae := Lp.ae_tendsto_of_cauchy_eLpNorm (f := g) (p := 2)
    (fun n => (hY.measurable _).aestronglyMeasurable) one_le_two hB hcau
  have hmean := F.tendsto_integral_mul_testSeq hu₀ hC
  filter_upwards [hae] with ω ⟨l, hl⟩
  have hconv : Tendsto (fun k => h ω (F.testSeq k)) atTop (𝓝 (l + ∫ z, u₀ z * F.src z)) :=
    (hl.add hmean).congr fun k => by simp only [hg]; ring
  rw [pair, hconv.limUnder_eq]
  exact hconv

end Conv

end CMCut

end FlowStopIdentCMI

end Restart

end InteractingSLE
