/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMICut
import InteractingSLE.Spec.Restart.FlowStopIdentCMContactTilt
import InteractingSLE.Spec.Sec7.Lemma71Joint
import InteractingSLE.GFF.LocalSets.Projection

/-!
# The explicit Cameron–Martin shift: the law of the shifted field

Packet PROVE-L1-CMI (Lemma G3's proof, supplement §7.3, pp. 492–493: "the weighted comparison field is `h + f`").
Let `H₀` be a GFF with data `b`, `q` the bounded harmonic extension of `bR − b`, `F` a cutoff field (`CMCut`), and
`s_k` test functions with `|s_k| ≤ |v|`, `s_k → v` pointwise for the source `v = F.src = 1_ℍ (2π)⁻¹ Δ F.f`, and
`H₀(s_k) → Λ` almost surely. Under `Q* = k e^{−Λ} · Q₀` (a probability measure) the field
`H₀ + T`, `T = (q − F.f)` as a distribution, is a GFF with data `bR` (`isGFFWithBoundaryData_shift`).

Proof: the tilt of the time-`0` kernel (`FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel` with the trivial
σ-algebra, the zero driver and the empty hull) gives the characteristic function of every pairing of `H₀ + T` under
`Q*`, with mean `∫ u₀ φ − G_ℍ(φ, v) + T(φ) = ∫ u₀ φ + ∫ F.f φ + ∫ (q − F.f) φ = ∫ (u₀ + q) φ` (Green inversion,
`integral_greenH_mul_src`) and variance `E₀(φ)`; and linear random distributions with the same one-dimensional
characteristic functions as a GFF are GFFs (`LocalExt.isZBGFFProcess_of_integral_cexp_eq`).

* `CMCut.isGreenTest_src`, `CMCut.integral_greenH_mul_src`, `CMCut.greenCross_zero_src`;
* `integral_cexp_of_isGFFWithBoundaryData`: the characteristic function of a pairing of a GFF;
* `integrable_exp_neg_of_isGFF`: `e^{−Λ}` is integrable (Fatou);
* **`isGFFWithBoundaryData_shift`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar greenH fwdMap fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace CMCut

variable (F : CMCut)

/-- **The source is a Green test** at every time whose hull avoids the support of `Δ F.f`. -/
theorem isGreenTest_src {W : ℝ → ℝ} {t : ℝ}
    (hd : Disjoint (tsupport (QuantumZipper.K3.greenDensity F.f)) (fwdHull W t)) : IsGreenTest W t F.src := by
  obtain ⟨C, -, hC⟩ := F.exists_abs_src_le
  refine ⟨F.measurable_src, ⟨C, hC⟩, ⟨tsupport (QuantumZipper.K3.greenDensity F.f) ∩ Hbar,
    F.hasCompactSupport_greenDensity.isCompact.inter_right (isClosed_le continuous_const Complex.continuous_im),
    inter_subset_right, fun z hz => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨hzH, hzt⟩ := F.mem_of_src_ne_zero hz
    exact ⟨hzt, show (0 : ℝ) ≤ z.im from le_of_lt hzH⟩
  · obtain ⟨hzH, hzt⟩ := F.mem_of_src_ne_zero hz
    exact ⟨hzH, fun hK => Set.disjoint_left.1 hd hzt hK⟩

/-- **Green inversion**: `G_ℍ(v) = −F.f` (`GB7a.integral_greenH_mul_indicator_greenDensity`). -/
theorem integral_greenH_mul_src (w : ℂ) : ∫ z, greenH w z * F.src z = -F.f w := by
  have h := GB7a.integral_greenH_mul_indicator_greenDensity (F.smooth.of_le (by simp)) F.compact F.odd w
  rw [← h, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [src]
  ring

/-- **The cross Green energy of a test with the source at time `0`** (zero driver): `−∫ φ F.f`. -/
theorem greenCross_zero_src (φ : TestOn upperHalfPlaneOpens) :
    greenCross (fun _ => 0) 0 φ F.src = -∫ z, φ z * F.f z := by
  have hfix : ∀ y : ℂ, y ∈ H → fwdMap (fun _ => (0 : ℝ)) 0 y = y := fun y hy => by
    have hy0 : y ≠ ((fun _ => (0 : ℝ)) 0 : ℂ) := by
      intro h0
      have hyH' : (0 : ℝ) < y.im := hy
      rw [h0] at hyH'
      simp at hyH'
    rw [QuantumZipper.B5.fwdMap_zero_time (fun _ => (0 : ℝ)) hy0, Complex.ofReal_zero, sub_zero]
  unfold greenCross
  rw [← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : φ y = 0
  · simp only [hy, zero_mul, integral_zero, neg_zero]
  have hyH : y ∈ H := φ.tsupport_subset (subset_tsupport _ hy)
  have e : (fun z => φ y * greenH (fwdMap (fun _ => (0 : ℝ)) 0 y) (fwdMap (fun _ => (0 : ℝ)) 0 z) * F.src z) =
      fun z => φ y * (greenH y z * F.src z) := by
    funext z
    by_cases hz : F.src z = 0
    · simp only [hz, mul_zero]
    · rw [hfix y hyH, hfix z (F.mem_of_src_ne_zero hz).1]; ring
  simp only at e ⊢
  rw [e, integral_const_mul, F.integral_greenH_mul_src y]
  ring

end CMCut

/-! ### The law of the shifted field -/

section Law

variable {S : Type*} [MeasurableSpace S] {Q₀ : Measure S} [IsProbabilityMeasure Q₀]
  {H₀ : S → DistOn upperHalfPlaneOpens} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}

/-- **The characteristic function of a pairing of a GFF with data `b`.** -/
theorem integral_cexp_of_isGFF (hH : IsGFFWithBoundaryData Q₀ H₀ b J) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b J u₀) (ψ : TestOn upperHalfPlaneOpens) :
    ∫ x, Complex.exp (Complex.I * (H₀ x ψ : ℂ)) ∂Q₀ =
      cfVal (∫ z, u₀ z * ψ z) (loewnerGreenEnergy (fun _ => 0) 0 ψ) := by
  have hmap := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess (hH.2 u₀ hu₀) ψ
  have hm : Measurable fun x => H₀ x ψ := (LQGMetric.measurable_distOn_apply ψ).comp hH.1
  have hcov : 0 ≤ QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens ψ ψ :=
    LocalSets.zeroGFFTestCov_self_nonneg upperHalfPlaneOpens.isOpen subset_rfl ψ
  rw [Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
  have hF : Continuous fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)) := by fun_prop
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable, hmap]
  have hc := charFun_gaussianReal (μ := ∫ z, u₀ z * ψ z)
    (v := (QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens ψ ψ).toNNReal) 1
  rw [charFun_apply_real] at hc
  simp only [Complex.ofReal_one, one_mul, one_pow, mul_one, Real.coe_toNNReal _ hcov] at hc
  rw [cfVal]
  have e : (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ))) = fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I) :=
    funext fun y => by rw [mul_comm]
  rw [e, hc]
  congr 1
  push_cast
  ring

/-- **The explicit Cameron–Martin shift turns a GFF with data `b` into a GFF with data `bR`.** Let `q` be a bounded
harmonic extension of `bR − b`, `F` a cutoff field, `s_k` test functions with `|s_k| ≤ |v|` and `s_k → v` (the source
`v = F.src`), `H₀(s_k) → Λ` almost surely, `e^{−Λ}` integrable and `Q* = k e^{−Λ} · Q₀` a probability measure. Then
under `Q*` the field `H₀ + (q − F.f)` is a GFF with data `bR`. -/
theorem isGFFWithBoundaryData_shift (hb : IsPiecewiseConstantBoundaryData b J) (F : CMCut) {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q)
    (hH : IsGFFWithBoundaryData Q₀ H₀ b J) {s : ℕ → TestOn upperHalfPlaneOpens}
    (hsle : ∀ n z, |s n z| ≤ |F.src z|) (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)))
    {Λ : S → ℝ} (hΛm : Measurable Λ) (hΛ : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x)))
    (hint : Integrable (fun x => Real.exp (-Λ x)) Q₀) {k : ℝ} (hk : 0 < k)
    (hprob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))) :
    IsGFFWithBoundaryData (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))
      (fun x => H₀ x + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) bR Ĵ := by
  classical
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)) with hQ
  set T : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens fun z => q z - F.f z with hT
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hu₀c : ContinuousOn u₀ H := fun z hz => ((hu₀.1 z hz).1.continuousAt).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hu₀.2.1
  have hqc : ContinuousOn q H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
  have hTc : ContinuousOn (fun z => q z - F.f z) H := hqc.sub F.smooth.continuous.continuousOn
  have hTφ : ∀ φ : TestOn upperHalfPlaneOpens, T φ = ∫ z, φ z * (q z - F.f z) := fun φ => by
    rw [hT, SupercriticalConformalCovariance.GM24.smoothDist_apply hTc]
  -- the zero driver at time `0`
  have hK0 : fwdHull (fun _ : ℝ => (0 : ℝ)) 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const
  have hdis : ∀ ψ : ℂ → ℝ, Disjoint (tsupport ψ) (fwdHull (fun _ : ℝ => (0 : ℝ)) 0) := fun ψ => by
    rw [hK0]; exact disjoint_empty _
  have hgS : IsGreenTest (fun _ => 0) 0 F.src := F.isGreenTest_src (by rw [hK0]; exact disjoint_empty _)
  have hgs : ∀ n, IsGreenTest (fun _ => 0) 0 (s n) := fun n => LocalExt.isGreenTest_of_testOn (s n) (hdis _)
  have hcont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) := continuousOn_const
  -- the kernel at time `0` under `Q₀`
  have hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q₀,
      Disjoint (tsupport ψ) (fwdHull ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : S => (0 : ℝ)) ω)) →
      Q₀[fun ω' => Complex.exp (Complex.I * (H₀ ω' ψ : ℂ)) | ⊥] ω =
        cfVal (∫ z, (fun _ : S => u₀) ω z * ψ z) (loewnerGreenEnergy ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω)
          ((fun _ : S => (0 : ℝ)) ω) ψ) := fun ψ => by
    refine ae_of_all _ fun ω _ => ?_
    rw [condExp_bot]
    exact integral_cexp_of_isGFF hH hu₀ ψ
  have hpath : ∀ᵐ ω ∂Q₀, 0 ≤ (fun _ : S => (0 : ℝ)) ω ∧ ∃ t₂, (fun _ : S => (0 : ℝ)) ω < t₂ ∧
      ContinuousOn ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω) (Icc 0 t₂) :=
    ae_of_all _ fun _ => ⟨le_rfl, 1, one_pos, hcont⟩
  have hMint : ∀ᵐ ω ∂Q₀, ∀ ψ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport ψ) (fwdHull ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : S => (0 : ℝ)) ω)) →
      Integrable fun z => (fun _ : S => u₀) ω z * ψ z :=
    ae_of_all _ fun _ ψ _ => LocalExt.integrable_mul_testOn hu₀c ψ
  have hsd : ∀ᵐ ω ∂Q₀, ∀ n, Disjoint (tsupport (s n))
      (fwdHull ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : S => (0 : ℝ)) ω)) :=
    ae_of_all _ fun _ n => hdis _
  have hμ₂ : ∀ᵐ ω ∂Q₀, Tendsto (fun n => ∫ z, (fun _ : S => u₀) ω z * s n z) atTop
      (𝓝 ((fun _ : S => ∫ z, u₀ z * F.src z) ω)) := by
    refine ae_of_all _ fun _ => ?_
    refine tendsto_integral_of_dominated_convergence (fun z => C₀ * |F.src z|)
      (fun n => (LocalExt.integrable_mul_testOn hu₀c (s n)).aestronglyMeasurable)
      (F.integrable_src.abs.const_mul C₀) (fun n => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      by_cases hz : z ∈ H
      · exact mul_le_mul (hC₀ z hz) (hsle n z) (abs_nonneg _) ((abs_nonneg _).trans (hC₀ z hz))
      · have h1 := hsle n z
        rw [F.src_of_notMem hz, abs_zero] at h1
        rw [abs_nonpos_iff.1 h1, F.src_of_notMem hz, abs_zero, mul_zero, mul_zero]
    · exact tendsto_const_nhds.mul (hslim z)
  have hgc := fun φ : TestOn upperHalfPlaneOpens => FlowStopIdentCM.tendsto_greenCross_of_dominated le_rfl
    one_pos hcont (LocalExt.isGreenTest_of_testOn φ (hdis _)) hgS hgs hgS hsle hslim
  have hs₂₂ : ∀ᵐ ω ∂Q₀, Tendsto (fun n => loewnerGreenEnergy ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω)
      ((fun _ : S => (0 : ℝ)) ω) (s n)) atTop
      (𝓝 ((fun _ : S => loewnerGreenEnergy (fun _ : ℝ => (0 : ℝ)) 0 F.src) ω)) :=
    ae_of_all _ fun _ => (hgc (s 0)).2
  -- the tilt at time `0`
  have hcf : ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ x, Complex.exp (Complex.I * ((H₀ x + T) φ : ℂ)) ∂Q =
        cfVal (∫ z, (u₀ z + q z) * φ z) (loewnerGreenEnergy (fun _ => 0) 0 φ) := fun φ => by
    have hs₁₂ : ∀ᵐ ω ∂Q₀, Disjoint (tsupport φ)
        (fwdHull ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : S => (0 : ℝ)) ω)) →
        Tendsto (fun n => greenCross ((fun _ : S => fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : S => (0 : ℝ)) ω) φ (s n))
          atTop (𝓝 ((fun _ : S => greenCross (fun _ : ℝ => (0 : ℝ)) 0 φ F.src) ω)) :=
      ae_of_all _ fun _ _ => (hgc φ).1
    have h := FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel bot_le hH.1 hker hpath hMint hΛm hΛ hint
      hsd hμ₂ hs₂₂ hk T φ hs₁₂
    obtain ⟨ω, hω⟩ := h.exists
    have hω' := hω (hdis _)
    rw [condExp_bot] at hω'
    beta_reduce at hω'
    rw [hω', F.greenCross_zero_src φ, hTφ φ]
    congr 1
    have i1 := LocalExt.integrable_mul_testOn hu₀c φ
    have i2 : Integrable fun z => φ z * F.f z :=
      (φ.continuous.mul F.smooth.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
    have i3 : Integrable fun z => φ z * (q z - F.f z) := by
      have := LocalExt.integrable_mul_testOn hTc φ
      exact this.congr (ae_of_all _ fun z => mul_comm _ _)
    have i12 : Integrable fun z => u₀ z * φ z + φ z * F.f z := i1.add i2
    rw [sub_neg_eq_add, ← integral_add i1 i2, ← integral_add i12 i3]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  have hXm : Measurable fun x => H₀ x + T :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hH.1).add_const (T φ)
  refine ⟨hXm, fun û hû => ?_⟩
  -- `û = u₀ + q` on `ℍ`
  have hsum := isBoundedHarmonicExtension_sub (b := fun x => -b x) hq
    (show IsBoundedHarmonicExtension (fun x => -b x) J (fun z => -u₀ z) from
      ⟨hu₀.1.neg, ⟨C₀, fun z hz => by rw [abs_neg]; exact hC₀ z hz⟩, fun x hx => (hu₀.2.2 x hx).neg⟩)
  have hsum' : IsBoundedHarmonicExtension bR (((J ∪ Ĵ : Finset ℝ) : Set ℝ) ∪ (J : Set ℝ))
      (fun z => u₀ z + q z) := by
    refine ⟨hu₀.1.add hq.1, ?_, fun x hx => ?_⟩
    · obtain ⟨Cq, hCq⟩ := hq.2.1
      exact ⟨C₀ + Cq, fun z hz => (abs_add_le _ _).trans (add_le_add (hC₀ z hz) (hCq z hz))⟩
    · have := (hu₀.2.2 x fun h => hx (Or.inr h)).add (hq.2.2 x fun h => hx (Or.inl h))
      simpa using this
  have heq := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension
    (((J ∪ Ĵ).finite_toSet).union J.finite_toSet) hsum'
    (isBoundedHarmonicExtension_mono' hû (fun x hx => Or.inl (by simp [hx])))
  clear hsum
  have hûc : ContinuousOn û H := fun z hz => ((hû.1 z hz).1.continuousAt).continuousWithinAt
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, û z * φ z = ∫ z, (u₀ z + q z) * φ z := fun φ => by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · simp only
      rw [heq (φ.tsupport_subset hz)]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have href := Coupling.isZBGFFProcess_fieldLaw0 hûc
  have hrefP : IsProbabilityMeasure (Coupling.fieldLaw0 û) := href.gaussian.isProbabilityMeasure
  have e₁ : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, û z * φ z = smoothDist upperHalfPlaneOpens û φ := fun φ => by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hûc]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eP : (fun φ ω => (H₀ ω + T) φ - ∫ z, û z * φ z) = fun φ ω =>
      (H₀ ω + T) φ - smoothDist upperHalfPlaneOpens û φ := by
    funext φ ω; rw [e₁ φ]
  have eR : (fun φ (x : DistOn upperHalfPlaneOpens) => x φ - ∫ z, û z * φ z) = fun φ x =>
      x φ - smoothDist upperHalfPlaneOpens û φ := by
    funext φ x; rw [e₁ φ]
  rw [eR] at href
  show LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => (H₀ ω + T) φ - ∫ z, û z * φ z) Q
  rw [eP]
  refine LocalExt.isZBGFFProcess_of_integral_cexp_eq (X := fun x => H₀ x + T) hXm _ (X' := fun x => x) _ href
    fun φ => ?_
  rw [← e₁ φ]
  set c : ℝ := ∫ z, û z * φ z
  have hsplit : ∀ y : ℝ, Complex.exp (Complex.I * ((y - c : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * (c : ℂ))) * Complex.exp (Complex.I * (y : ℂ)) := fun y => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [hsplit]
  rw [integral_const_mul, integral_const_mul, hcf φ, Coupling.integral_cexp_fieldLaw0 hûc φ, ← hmean φ,
    Sec7.Lemma71J.loewnerGreenEnergy_const_zero, cfVal]
  congr 2
  push_cast
  ring

/-- **The density `e^{−Λ}` is integrable** (Fatou): `E[e^{−H₀(s_n)}] = e^{−μ_n + v_n/2}` with `|μ_n| ≤ C ∫ |v|`
and `v_n = G_ℍ(s_n, s_n) ≤ ∬ |v| |v| |G_ℍ|`. -/
theorem integrable_exp_neg_of_isGFF (hb : IsPiecewiseConstantBoundaryData b J)
    (hH : IsGFFWithBoundaryData Q₀ H₀ b J) (F : CMCut) {s : ℕ → TestOn upperHalfPlaneOpens}
    (hsle : ∀ n z, |s n z| ≤ |F.src z|) {Λ : S → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) :
    Integrable (fun x => Real.exp (-Λ x)) Q₀ := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hu₀c : ContinuousOn u₀ H := fun z hz => ((hu₀.1 z hz).1.continuousAt).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hu₀.2.1
  set A : ℝ := |C₀| * ∫ z, |F.src z| with hA
  set B : ℝ := ∫ p : ℂ × ℂ, |(|F.src p.1| * |F.src p.2| * greenH p.1 p.2)| ∂((volume : Measure ℂ).prod volume)
    with hB
  have hY := hH.2 u₀ hu₀
  have hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (Real.exp (-H₀ x (s n))) ∂Q₀ ≤ ENNReal.ofReal (Real.exp (A + B / 2)) := by
    intro n
    have hm : Measurable fun x => H₀ x (s n) := (LQGMetric.measurable_distOn_apply (s n)).comp hH.1
    have hmap := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess hY (s n)
    set μn : ℝ := ∫ z, u₀ z * s n z with hμn
    set vn : ℝ := QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens (s n) (s n) with hvn
    have hvn0 : 0 ≤ vn := LocalSets.zeroGFFTestCov_self_nonneg upperHalfPlaneOpens.isOpen subset_rfl (s n)
    have hlaw : HasLaw (fun x => H₀ x (s n)) (gaussianReal μn vn.toNNReal) Q₀ := ⟨hm.aemeasurable, hmap⟩
    have hint : Integrable (fun x => Real.exp (-H₀ x (s n))) Q₀ := by
      have h1 := integrable_exp_mul_gaussianReal (μ := μn) (v := vn.toNNReal) (-1)
      have h2 : Integrable (fun y : ℝ => Real.exp (-1 * y)) (Q₀.map fun x => H₀ x (s n)) := by rwa [hmap]
      have h3 := h2.comp_measurable hm
      refine h3.congr (ae_of_all _ fun x => ?_)
      simp
    have hmgf := mgf_gaussianReal hlaw (-1)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ x, Real.exp (-H₀ x (s n)) ∂Q₀ = mgf (fun x => H₀ x (s n)) Q₀ (-1) := by
      simp only [mgf]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp
    rw [e, hmgf, Real.coe_toNNReal _ hvn0]
    refine Real.exp_le_exp.2 ?_
    -- the mean
    have hμ : -μn ≤ A := by
      have h1 : |μn| ≤ ∫ z, |C₀| * |F.src z| := by
        rw [hμn]
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _)
          (F.integrable_src.abs.const_mul _) (ae_of_all _ fun z => ?_))
        show |u₀ z * s n z| ≤ |C₀| * |F.src z|
        rw [abs_mul]
        by_cases hz : z ∈ H
        · exact mul_le_mul ((hC₀ z hz).trans (le_abs_self _)) (hsle n z) (abs_nonneg _) (abs_nonneg _)
        · have h0 := hsle n z
          rw [F.src_of_notMem hz, abs_zero] at h0
          rw [abs_nonpos_iff.1 h0, abs_zero, mul_zero]
          exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [integral_const_mul] at h1
      linarith [neg_le_abs μn]
    -- the variance
    have hv : vn ≤ B := by
      have hvg : vn = LocalExt.greenEnergy (s n) (s n) := by
        rw [hvn, LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl GFF.isConformalOnto_id_H]
        rfl
      rw [hvg]
      have hI := F.integrable_abs_mul_greenH.abs
      have hdom : ∀ p : ℂ × ℂ, |s n p.1 * s n p.2 * greenH p.1 p.2| ≤
          |(|F.src p.1| * |F.src p.2| * greenH p.1 p.2)| := fun p => by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_abs, abs_abs]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hsle n p.1) (hsle n p.2) (abs_nonneg _)
          (abs_nonneg _)) (abs_nonneg _)
      have hmeas : Measurable fun p : ℂ × ℂ => s n p.1 * s n p.2 * greenH p.1 p.2 :=
        (((s n).continuous.measurable.comp measurable_fst).mul ((s n).continuous.measurable.comp measurable_snd)).mul
          QuantumZipper.measurable_greenH
      have hI2 : Integrable (fun p : ℂ × ℂ => |s n p.1 * s n p.2 * greenH p.1 p.2|)
          ((volume : Measure ℂ).prod volume) :=
        Integrable.mono' hI hmeas.abs.aestronglyMeasurable (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_abs]; exact hdom p)
      calc LocalExt.greenEnergy (s n) (s n) ≤ |LocalExt.greenEnergy (s n) (s n)| := le_abs_self _
        _ ≤ ∫ p : ℂ × ℂ, |s n p.1 * s n p.2 * greenH p.1 p.2| ∂((volume : Measure ℂ).prod volume) :=
          abs_integral_le_integral_abs
        _ ≤ B := integral_mono_of_nonneg (ae_of_all _ fun p => abs_nonneg _) hI (ae_of_all _ hdom)
    nlinarith
  -- Fatou
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal (Real.exp (-H₀ x (s n))) := fun n =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((LQGMetric.measurable_distOn_apply (s n)).comp hH.1).neg)
  have hlim : (fun x => ENNReal.ofReal (Real.exp (-Λ x))) =ᵐ[Q₀]
      fun x => liminf (fun n => ENNReal.ofReal (Real.exp (-H₀ x (s n)))) atTop := by
    filter_upwards [hΛ] with x hx
    have h := ((ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).tendsto _).comp hx
    exact h.liminf_eq.symm
  have hfat := lintegral_liminf_le hmeas (μ := Q₀) (u := atTop)
  have hle : ∫⁻ x, ENNReal.ofReal (Real.exp (-Λ x)) ∂Q₀ ≤ ENNReal.ofReal (Real.exp (A + B / 2)) := by
    rw [lintegral_congr_ae hlim]
    exact hfat.trans (Filter.liminf_le_of_le ⟨0, Eventually.of_forall fun n => bot_le⟩
      fun c hc => (hc.exists).elim fun n hn => hn.trans (hbound n))
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (-Λ x)) ∂Q₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have h := integrable_toReal_of_lintegral_ne_top
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hΛm.neg)).aemeasurable hfin
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.exp_pos _).le

end Law

end FlowStopIdentCMI

end Restart

end InteractingSLE
