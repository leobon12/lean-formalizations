/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovHull

/-!
# The restart fibre's Cameron–Martin tilt at one stop, in both directions

Packet PROVE-AUX61-ACT (Theorem 1.2's Prop 5.1 (E1), the per-fibre kernel). Astra's follow-up 4 §1.3
(`source/external/AstraIG1/ig1_followup4_audited.txt` L232–L246, ruling R71): weighting the fibre's law by the
Cameron–Martin density of the cutoff `−Fq` turns the actual mean `meanF κ u q Fq` (Aux. lemma 61 relative to the
reference word) into the reference word's mean, and conversely. PROVE-AUX61-R2's
`RefFibre.TiltData.isCouplingCharFun_tilt` does the forward direction at every stop at once, from the kernel at every
stop. Here both directions are proved **at one σ-algebra and one random time**, from the kernel there only, so that a
kernel known at countably many stops can be moved to the reference side, extended there by the landed dyadic
argument, and moved back (`Aux61ActDyadic`):

* `exists_tiltΛ`: a field whose centred pairings form a zero-boundary GFF process, with a mean bounded on the support of
  a cutoff's source, has an almost-sure pairing limit `Λ` with the source and `e^{−Λ}` is integrable (the construction
  of PROVE-AUX61-R2's `RefFibre.tiltData`, for any such field);
* **`ae_condExp_tilt_fwd`**: the actual kernel at `(m, t)` gives, under `k e^{−Λ} · P`, the reference kernel of the
  shifted field `h + (Fq − q)` at `(m, t)`;
* **`ae_condExp_tilt_rev`**: conversely, the reference kernel of the shifted field at `(m, t)` under `k e^{−Λ} · P`
  (a probability measure) gives the actual kernel of `h` at `(m, t)` under `P` (the inverse density is again a
  Cameron–Martin density, of the cutoff `+Fq`, for the shifted field).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Act

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Win (meanF IsCutoffOn)

universe u

/-! ### The pairing limit with a cutoff's source -/

section Lambda

variable {S : Type*} [MeasurableSpace S] {P : Measure S} [IsProbabilityMeasure P]
  {field : S → DistOn upperHalfPlaneOpens}

/-- **The pairing limit of a Gaussian field with a cutoff's source** (the construction of PROVE-AUX61-R2's
`RefFibre.tiltData` for any field whose centred pairings form a zero-boundary GFF process): if `m0` is continuous on
`ℍ` and bounded on the support of `F.src`, the pairings `h(F.testSeq n)` converge almost surely to a measurable `Λ`,
and `e^{−Λ}` is integrable. -/
theorem exists_tiltΛ (hfm : Measurable field) {m0 : ℂ → ℝ} (hm0 : ContinuousOn m0 H)
    (hG : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => field ω φ - ∫ z, m0 z * φ z) P)
    (F : CMCut) {C : ℝ} (hC : ∀ z, F.src z ≠ 0 → |m0 z| ≤ C) :
    ∃ Λ : S → ℝ, Measurable Λ ∧ (∀ᵐ ω ∂P, Tendsto (fun n => field ω (F.testSeq n)) atTop (𝓝 (Λ ω))) ∧
      Integrable (fun ω => Real.exp (-Λ ω)) P := by
  set centred : S → DistOn upperHalfPlaneOpens := fun ω => field ω + -smoothDist upperHalfPlaneOpens m0 with hcdef
  have hcm : Measurable centred := (Coupling.measurable_add_distOnConst _).comp hfm
  have hcapp : ∀ ω φ, centred ω φ = field ω φ - ∫ z, m0 z * φ z := fun ω φ => by
    have e : smoothDist upperHalfPlaneOpens m0 φ = ∫ z, m0 z * φ z := by
      rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hm0]
      exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
    change field ω φ + -smoothDist upperHalfPlaneOpens m0 φ = _
    rw [e, ← sub_eq_add_neg]
  set Λ : S → ℝ := fun ω => F.pair (centred ω) + ∫ z, m0 z * F.src z with hΛdef
  have hΛm : Measurable Λ := (F.measurable_pair.comp hcm).add_const _
  have hlimm : Tendsto (fun n => ∫ z, m0 z * F.testSeq n z) atTop (𝓝 (∫ z, m0 z * F.src z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => C * |F.src z|)
      (fun n => (LocalExt.integrable_mul_testOn hm0 (F.testSeq n)).aestronglyMeasurable)
      (F.integrable_src.abs.const_mul C) (fun n => ae_of_all _ fun z => ?_)
      (ae_of_all _ fun z => (F.tendsto_testSeq z).const_mul _)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : F.src z = 0
    · have h0 := F.abs_testSeq_le n z
      rw [hz, abs_zero] at h0
      rw [abs_nonpos_iff.1 h0, hz, abs_zero, mul_zero, mul_zero]
    · exact mul_le_mul (hC z hz) (F.abs_testSeq_le n z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))
  have hY' : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => centred ω φ - ∫ z, (fun _ : ℂ => (0 : ℝ)) z * φ z) P := by
    have e : (fun φ ω => centred ω φ - ∫ z, (fun _ : ℂ => (0 : ℝ)) z * φ z) =
        fun φ ω => field ω φ - ∫ z, m0 z * φ z := by
      funext φ ω
      rw [hcapp]
      simp
    rw [e]; exact hG
  have hpair := F.ae_tendsto_pair (h := centred) (u₀ := fun _ => 0) continuousOn_const
    (C := 0) (fun _ _ => by simp) hY'
  have hΛ : ∀ᵐ ω ∂P, Tendsto (fun n => field ω (F.testSeq n)) atTop (𝓝 (Λ ω)) := by
    filter_upwards [hpair] with ω hω
    have e : ∀ n, field ω (F.testSeq n) = centred ω (F.testSeq n) + ∫ z, m0 z * F.testSeq n z := fun n => by
      rw [hcapp]; ring
    simp_rw [e]
    exact hω.add hlimm
  exact ⟨Λ, hΛm, hΛ, Aux61R2.integrable_exp_neg_of_isZBGFFProcess hfm hG F hC F.abs_testSeq_le hΛm hΛ⟩

end Lambda

/-! ### The forward tilt at one stop -/

section Tilt

variable {S : Type*} {m : MeasurableSpace S} [mS : MeasurableSpace S] {P : Measure S} [IsProbabilityMeasure P]
  {κ : ℝ} {field : S → DistOn upperHalfPlaneOpens}
  {q : ℂ → ℝ} {O₀ : Set ℝ} {Fq : CMCut} {Nq : Set ℂ} {Cq : ℝ} {buffer : Set ℂ}
  {W : ℝ≥0 → S → ℝ} {t : S → ℝ≥0} {u : S → ℂ → ℝ}

/-- The shifted field `h + (Fq − q)`. -/
def shiftField (field : S → DistOn upperHalfPlaneOpens) (q : ℂ → ℝ) (Fq : CMCut) :
    S → DistOn upperHalfPlaneOpens :=
  fun ω => field ω + smoothDist upperHalfPlaneOpens (fun z => Fq.f z - q z)

omit m [IsProbabilityMeasure P] in
theorem measurable_shiftField (hfm : Measurable field) : Measurable (shiftField field q Fq) :=
  (Coupling.measurable_add_distOnConst _).comp hfm

/-- **The forward tilt at one stop** (the proof of `Aux61R2.RefFibre.TiltData.isCouplingCharFun_tilt` at one
σ-algebra `m` and one random time `t`): if the actual kernel `meanF κ u q Fq` holds at `(m, t)` and the hulls up to `t`
lie in a buffer on which `Fq = q` is harmonic, then under `k e^{−Λ} · P` (`Λ` the pairing limit with the source of
`−Fq`) the shifted field `h + (Fq − q)` has the reference kernel `couplingMean κ · t u` at `(m, t)`. -/
theorem ae_condExp_tilt_fwd (hm : m ≤ mS) (hfm : Measurable field) (hq : ContinuousOn q H)
    (hcut : IsCutoffOn Fq q Nq O₀) (hqb : ∀ z, Fq.src z ≠ 0 → |q z| ≤ Cq) (hbo : IsOpen buffer)
    (hb0 : (0 : ℂ) ∈ buffer) (hbN : buffer ⊆ Nq) (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hKb : ∀ᵐ ω ∂P, closure (fwdHull (Ito.rpath (W · ω)) (t ω)) ⊆ buffer)
    (hu : ∀ ω, InnerProductSpace.HarmonicOnNhd (u ω) H) (hub : ∀ ω, ∃ C : ℝ, ∀ z ∈ H, |u ω z| ≤ C)
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, meanF κ (u ω) q Fq (Ito.rpath (W · ω)) (t ω) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) ψ))
    {Λ : S → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun n => field ω (Fq.neg.testSeq n)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P) {k : ℝ} (hk : 0 < k) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))),
      Disjoint (tsupport φ) (fwdHull (Ito.rpath (W · ω)) (t ω)) →
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
          Complex.exp (Complex.I * (shiftField field q Fq ω' φ : ℂ)) | m] ω =
        cfVal (∫ z, couplingMean κ (Ito.rpath (W · ω)) (t ω) (u ω) z * φ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) φ) := by
  set Wd : S → ℝ → ℝ := fun ω => Ito.rpath (W · ω) with hWd
  set F : CMCut := Fq.neg with hFdef
  have hWdc : ∀ ω, Continuous (Wd ω) := fun ω => (hWc ω).comp continuous_real_toNNReal
  have hΔq : ∀ z ∈ buffer, QuantumZipper.K3.greenDensity Fq.f z = 0 := fun z hz => hcut.harmonic z (hbN hz)
  have hΔ : ∀ z ∈ buffer, QuantumZipper.K3.greenDensity F.f z = 0 := fun z hz => by
    rw [hFdef, CMCut.greenDensity_neg, hΔq z hz, neg_zero]
  have hFq' : IsCutoffOn Fq (fun z => Fq.f z) buffer univ :=
    ⟨hbo, fun _ _ _ => trivial, fun _ _ _ => rfl, hΔq⟩
  have hF' : IsCutoffOn F (fun z => F.f z) buffer univ :=
    ⟨hbo, fun _ _ _ => trivial, fun _ _ _ => rfl, hΔ⟩
  have hqb' : ∀ z, F.src z ≠ 0 → |q z| ≤ Cq := fun z hz => hqb z fun h0 => hz (by
    rw [hFdef, CMCut.src_neg, h0, neg_zero])
  set s : ℕ → TestOn upperHalfPlaneOpens := F.testSeq with hs
  have hsle : ∀ n z, |s n z| ≤ |F.src z| := F.abs_testSeq_le
  have hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)) := F.tendsto_testSeq
  have hMint : ∀ᵐ ω ∂P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => meanF κ (u ω) q Fq (Wd ω) (t ω) z * ψ z := by
    filter_upwards [hKb] with ω hK ψ hψ
    exact Aux61Win.integrable_meanF_mul (hu ω) hq (hWc ω) (hFq'.isGreenTest_src hK) ψ hψ
  have hsd : ∀ᵐ ω ∂P, ∀ n, Disjoint (tsupport (s n)) (fwdHull (Wd ω) (t ω)) := by
    filter_upwards [hKb] with ω hK n
    exact Aux61Win.disjoint_tsupport_of_abs_le_src hF' (hsle n) fun z hz => hK (subset_closure hz)
  have hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ z, meanF κ (u ω) q Fq (Wd ω) (t ω) z * s n z) atTop
      (𝓝 ((∫ z, couplingMean κ (Wd ω) (t ω) (u ω) z * F.src z) - greenCross (Wd ω) (t ω) F.src Fq.src +
        ∫ z, (q z - Fq.f z) * F.src z)) := by
    filter_upwards [hKb] with ω hK
    obtain ⟨Cu, hCu⟩ := hub ω
    exact Aux61Win.tendsto_integral_meanF_mul (hu ω) hCu hq hbo hb0 hΔq hΔ hqb' (hWc ω) (hW0 ω) hK hsle hslim
  have hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun n => loewnerGreenEnergy (Wd ω) (t ω) (s n)) atTop
      (𝓝 (loewnerGreenEnergy (Wd ω) (t ω) F.src)) := by
    filter_upwards [hKb] with ω hK
    exact Aux61Win.tendsto_energy_of_abs_le_src hF' (hWdc ω) (NNReal.coe_nonneg _) hK hsle hslim
  have hs₁₂ : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun n => greenCross (Wd ω) (t ω) φ (s n)) atTop (𝓝 (greenCross (Wd ω) (t ω) φ F.src)) := by
    filter_upwards [hKb, hsd] with ω hK hd hφ
    have hG := hF'.isGreenTest_src hK
    exact LocalExt.tendsto_greenCross (hWdc ω) (NNReal.coe_nonneg _) (LocalExt.isGreenTest_of_testOn φ hφ) hG
      (fun n => LocalExt.isGreenTest_of_testOn (s n) (hd n)) hG hsle hslim
  have hpath : ∀ᵐ ω ∂P, 0 ≤ (t ω : ℝ) ∧ ∃ t₂, (t ω : ℝ) < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂) :=
    ae_of_all _ fun ω => ⟨NNReal.coe_nonneg _, t ω + 1, by linarith, (hWdc ω).continuousOn⟩
  set Sh : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens (fun z => Fq.f z - q z) with hSh
  have htilt := Restart.FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel hm hfm hker hpath hMint hΛm hΛ hint
    hsd hμ₂ hs₂₂ hk Sh φ hs₁₂
  have hc : ContinuousOn (fun z => Fq.f z - q z) H := Fq.smooth.continuous.continuousOn.sub hq
  have hShφ : Sh φ = -∫ z, (q z - Fq.f z) * φ z := by
    rw [hSh, SupercriticalConformalCovariance.GM24.smoothDist_apply hc φ, ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only; ring)
  have hQP : (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))) ≪ P :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [htilt, hQP.ae_le hKb] with ω h1 hK hφ
  have hφ' : Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) := hφ
  change (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
    Complex.exp (Complex.I * ((field ω' + Sh) φ : ℂ)) | m] ω = _
  rw [h1 hφ', hShφ, Aux61Win.integral_meanF_eq (hu ω) hq (hWc ω) (hFq'.isGreenTest_src hK) φ hφ',
    hFdef, show (Fq.neg.src : ℂ → ℝ) = fun z => -Fq.src z from funext Fq.src_neg,
    Aux61R2.RefFibre.greenCross_neg_right]
  simp only [cfVal]
  congr 4
  change ((∫ z, couplingMean κ (Ito.rpath fun x => W x ω) (t ω : ℝ) (u ω) z * φ z) -
      greenCross (Ito.rpath fun x => W x ω) (t ω : ℝ) φ Fq.src + ∫ z, (q z - Fq.f z) * φ z) -
      -greenCross (Ito.rpath fun x => W x ω) (t ω : ℝ) φ Fq.src + -(∫ z, (q z - Fq.f z) * φ z) =
    ∫ z, couplingMean κ (Ito.rpath fun x => W x ω) (t ω : ℝ) (u ω) z * φ z
  ring

/-! ### The reverse tilt at one stop -/

/-- The zero cutoff. -/
def zeroCut : CMCut where
  f := fun _ => 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  odd := fun _ => by simp

theorem greenDensity_zeroCut (z : ℂ) : QuantumZipper.K3.greenDensity zeroCut.f z = 0 := by
  rw [QuantumZipper.K3.greenDensity]
  simp [zeroCut]

theorem zeroCut_src (z : ℂ) : zeroCut.src z = 0 := by
  have h : H.indicator (QuantumZipper.K3.greenDensity zeroCut.f) = fun _ => 0 := by
    funext y
    by_cases hy : y ∈ H
    · rw [indicator_of_mem hy, greenDensity_zeroCut]
    · rw [indicator_of_notMem hy]
  change -H.indicator (QuantumZipper.K3.greenDensity zeroCut.f) z = 0
  rw [h, neg_zero]

/-- With the zero cutoff and `q = 0`, the explicit mean is the coupling mean. -/
theorem meanF_zeroCut (κ : ℝ) (u : ℂ → ℝ) (w : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    meanF κ u (fun _ => 0) zeroCut w t z = couplingMean κ w t u z := by
  have h : H.indicator (QuantumZipper.K3.greenDensity zeroCut.f) = fun _ => 0 := by
    funext y
    by_cases hy : y ∈ H
    · rw [indicator_of_mem hy, greenDensity_zeroCut]
    · rw [indicator_of_notMem hy]
  simp only [meanF, h, GB7a.greenPot, mul_zero, integral_zero, add_zero]
  change couplingMean κ w t u z + ((0 : ℝ) - 0) = couplingMean κ w t u z
  rw [sub_self, add_zero]

theorem greenCross_zeroCut (w : ℝ → ℝ) (t : ℝ) (φ : ℂ → ℝ) : greenCross w t φ zeroCut.src = 0 := by
  simp only [greenCross, zeroCut_src, mul_zero, integral_zero]

/-- **The reverse tilt at one stop**: if, under the probability measure `Q = k e^{−Λ} · P` (`Λ` the pairing limit of
`h` with the source of `−Fq`), the shifted field `h + (Fq − q)` has the reference kernel `couplingMean κ · t u` at
`(m, t)`, then `h` has the actual kernel `meanF κ u q Fq` at `(m, t)` under `P`. The inverse density
`(k e^{−Λ})⁻¹ = k' e^{−Λ'}` is the Cameron–Martin density of the cutoff `+Fq` for the shifted field (`Λ' = −Λ + c`,
the pairing limit of `h + (Fq − q)` with the source of `+Fq`), so the forward tilt lemma applies under `Q`. -/
theorem ae_condExp_tilt_rev (hm : m ≤ mS) (hfm : Measurable field) (hq : ContinuousOn q H)
    (hcut : IsCutoffOn Fq q Nq O₀) (hqb : ∀ z, Fq.src z ≠ 0 → |q z| ≤ Cq) (hbo : IsOpen buffer)
    (hb0 : (0 : ℂ) ∈ buffer) (hbN : buffer ⊆ Nq) (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hKb : ∀ᵐ ω ∂P, closure (fwdHull (Ito.rpath (W · ω)) (t ω)) ⊆ buffer)
    (hu : ∀ ω, InnerProductSpace.HarmonicOnNhd (u ω) H) (hub : ∀ ω, ∃ C : ℝ, ∀ z ∈ H, |u ω z| ≤ C)
    {Λ : S → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun n => field ω (Fq.neg.testSeq n)) atTop (𝓝 (Λ ω))) {k : ℝ} (hk : 0 < k)
    [IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))]
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))),
        Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) (t ω)) →
        (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
            Complex.exp (Complex.I * (shiftField field q Fq ω' ψ : ℂ)) | m] ω =
          cfVal (∫ z, couplingMean κ (Ito.rpath (W · ω)) (t ω) (u ω) z * ψ z)
            (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) ψ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Ito.rpath (W · ω)) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (field ω' φ : ℂ)) | m] ω =
        cfVal (∫ z, meanF κ (u ω) q Fq (Ito.rpath (W · ω)) (t ω) z * φ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) φ) := by
  set Q := P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)) with hQdef
  set Wd : S → ℝ → ℝ := fun ω => Ito.rpath (W · ω) with hWd
  have hWdc : ∀ ω, Continuous (Wd ω) := fun ω => (hWc ω).comp continuous_real_toNNReal
  have hΔq : ∀ z ∈ buffer, QuantumZipper.K3.greenDensity Fq.f z = 0 := fun z hz => hcut.harmonic z (hbN hz)
  have hFq' : IsCutoffOn Fq (fun z => Fq.f z) buffer univ :=
    ⟨hbo, fun _ _ _ => trivial, fun _ _ _ => rfl, hΔq⟩
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hKbQ : ∀ᵐ ω ∂Q, closure (fwdHull (Wd ω) (t ω)) ⊆ buffer := hQP.ae_le hKb
  -- the test sequence of the source of `+Fq`
  set s : ℕ → TestOn upperHalfPlaneOpens := fun n => -Fq.neg.testSeq n with hs
  have hsapp : ∀ n z, s n z = -Fq.neg.testSeq n z := fun n z => rfl
  have hsle : ∀ n z, |s n z| ≤ |Fq.src z| := fun n z => by
    have h := Fq.neg.abs_testSeq_le n z
    rw [CMCut.src_neg, abs_neg] at h
    rwa [hsapp, abs_neg]
  have hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (Fq.src z)) := fun z => by
    have h := (Fq.neg.tendsto_testSeq z).neg
    rw [CMCut.src_neg, neg_neg] at h
    simpa only [hsapp] using h
  -- the constant `c = ∫ (Fq − q) Fq.src`
  obtain ⟨B, hB⟩ := Fq.smooth.continuous.bounded_above_of_compact_support Fq.compact
  set c : ℝ := ∫ z, (Fq.f z - q z) * Fq.src z with hcdef
  have hcont : ContinuousOn (fun z => Fq.f z - q z) H := Fq.smooth.continuous.continuousOn.sub hq
  have hclim : Tendsto (fun n => ∫ z, (Fq.f z - q z) * s n z) atTop (𝓝 c) := by
    refine tendsto_integral_of_dominated_convergence (fun z => (B + Cq) * |Fq.src z|)
      (fun n => (LocalExt.integrable_mul_testOn hcont (s n)).aestronglyMeasurable)
      (Fq.integrable_src.abs.const_mul _) (fun n => ae_of_all _ fun z => ?_)
      (ae_of_all _ fun z => (hslim z).const_mul _)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : Fq.src z = 0
    · have h0 := hsle n z
      rw [hz, abs_zero] at h0
      rw [abs_nonpos_iff.1 h0, hz, abs_zero, mul_zero, mul_zero]
    · have h1 : |Fq.f z - q z| ≤ B + Cq := by
        have hb := hB z
        rw [Real.norm_eq_abs] at hb
        exact (abs_sub _ _).trans (add_le_add hb (hqb z hz))
      exact mul_le_mul h1 (hsle n z) (abs_nonneg _) ((abs_nonneg _).trans h1)
  -- the reversed pairing limit
  set Λ' : S → ℝ := fun ω => -Λ ω + c with hΛ'def
  have hΛ'm : Measurable Λ' := hΛm.neg.add_const _
  have hsmooth : ∀ ψ : TestOn upperHalfPlaneOpens,
      smoothDist upperHalfPlaneOpens (fun z => Fq.f z - q z) ψ = ∫ z, (Fq.f z - q z) * ψ z := fun ψ => by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hcont]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have hΛ' : ∀ᵐ ω ∂Q, Tendsto (fun n => shiftField field q Fq ω (s n)) atTop (𝓝 (Λ' ω)) := by
    refine hQP.ae_le ?_
    filter_upwards [hΛ] with ω hω
    have e : ∀ n, shiftField field q Fq ω (s n) =
        -field ω (Fq.neg.testSeq n) + ∫ z, (Fq.f z - q z) * s n z := fun n => by
      change field ω (s n) + smoothDist upperHalfPlaneOpens (fun z => Fq.f z - q z) (s n) = _
      rw [hsmooth, hs, map_neg]
    simp_rw [e]
    exact hω.neg.add hclim
  -- integrability of the reversed density under `Q`
  have hgm : Measurable fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp hΛm.neg))
  have hint' : Integrable (fun ω => Real.exp (-Λ' ω)) Q := by
    rw [hQdef, integrable_withDensity_iff hgm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine (integrable_const (k * Real.exp (-c))).congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [ENNReal.toReal_ofReal (mul_nonneg hk.le (Real.exp_pos _).le), hΛ'def]
    simp only
    rw [show -(-Λ ω + c) = Λ ω + -c by ring, Real.exp_add, Real.exp_neg (Λ ω)]
    field_simp
  -- the inputs of the tilt under `Q`
  have hpath : ∀ᵐ ω ∂Q, 0 ≤ (t ω : ℝ) ∧ ∃ t₂, (t ω : ℝ) < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂) :=
    ae_of_all _ fun ω => ⟨NNReal.coe_nonneg _, t ω + 1, by linarith, (hWdc ω).continuousOn⟩
  have hMint : ∀ᵐ ω ∂Q, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => couplingMean κ (Wd ω) (t ω) (u ω) z * ψ z :=
    ae_of_all _ fun ω ψ hψ => LocalExt.integrable_couplingMean_mul (κ := κ) (hWdc ω).continuousOn (hu ω) hψ
  have hsd : ∀ᵐ ω ∂Q, ∀ n, Disjoint (tsupport (s n)) (fwdHull (Wd ω) (t ω)) := by
    filter_upwards [hKbQ] with ω hK n
    exact Aux61Win.disjoint_tsupport_of_abs_le_src hFq' (hsle n) fun z hz => hK (subset_closure hz)
  have hμ₂ : ∀ᵐ ω ∂Q, Tendsto (fun n => ∫ z, couplingMean κ (Wd ω) (t ω) (u ω) z * s n z) atTop
      (𝓝 (∫ z, couplingMean κ (Wd ω) (t ω) (u ω) z * Fq.src z)) := by
    filter_upwards [hKbQ] with ω hK
    obtain ⟨Cu, hCu⟩ := hub ω
    have h := Aux61Win.tendsto_integral_meanF_mul (κ := κ) (hu ω) hCu (q := fun _ => 0) continuousOn_const
      (Fq := zeroCut) (F := Fq) hbo hb0 (fun z _ => greenDensity_zeroCut z) hΔq (Cq := 0)
      (fun _ _ => by simp) (hWc ω) (hW0 ω) hK hsle hslim
    simp only [meanF_zeroCut, greenCross_zeroCut, sub_zero] at h
    have e : ∫ z, (0 - zeroCut.f z) * Fq.src z = 0 := by
      simp only [zeroCut, sub_self, zero_mul, integral_zero]
    rwa [e, add_zero] at h
  have hs₂₂ : ∀ᵐ ω ∂Q, Tendsto (fun n => loewnerGreenEnergy (Wd ω) (t ω) (s n)) atTop
      (𝓝 (loewnerGreenEnergy (Wd ω) (t ω) Fq.src)) := by
    filter_upwards [hKbQ] with ω hK
    exact Aux61Win.tendsto_energy_of_abs_le_src hFq' (hWdc ω) (NNReal.coe_nonneg _) hK hsle hslim
  have hs₁₂ : ∀ᵐ ω ∂Q, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun n => greenCross (Wd ω) (t ω) φ (s n)) atTop (𝓝 (greenCross (Wd ω) (t ω) φ Fq.src)) := by
    filter_upwards [hKbQ, hsd] with ω hK hd hφ
    have hG := hFq'.isGreenTest_src hK
    exact LocalExt.tendsto_greenCross (hWdc ω) (NNReal.coe_nonneg _) (LocalExt.isGreenTest_of_testOn φ hφ) hG
      (fun n => LocalExt.isGreenTest_of_testOn (s n) (hd n)) hG hsle hslim
  set k' : ℝ := k⁻¹ * Real.exp c with hk'def
  have hk' : 0 < k' := mul_pos (inv_pos.2 hk) (Real.exp_pos _)
  set T : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens (fun z => q z - Fq.f z) with hT
  have htilt := Restart.FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel (P := Q) hm
    (measurable_shiftField hfm) hker hpath hMint hΛ'm hΛ' hint' hsd hμ₂ hs₂₂ hk' T φ hs₁₂
  -- the reversed tilt of `Q` is `P`
  have hPeq : (Q.withDensity fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω))) = P := by
    have hg'm : Measurable fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp hΛ'm.neg))
    rw [hQdef, ← withDensity_mul P hgm hg'm]
    have e : ((fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))) *
        fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω))) = 1 := by
      funext ω
      simp only [Pi.mul_apply, Pi.one_apply]
      rw [← ENNReal.ofReal_mul (mul_nonneg hk.le (Real.exp_pos _).le), hk'def, hΛ'def]
      simp only
      rw [show -(-Λ ω + c) = Λ ω + -c by ring, Real.exp_add, Real.exp_neg c]
      have h1 : k * Real.exp (-Λ ω) * (k⁻¹ * Real.exp c * (Real.exp (Λ ω) * (Real.exp c)⁻¹)) =
          (k * k⁻¹) * (Real.exp (-Λ ω) * Real.exp (Λ ω)) * (Real.exp c * (Real.exp c)⁻¹) := by ring
      rw [h1, mul_inv_cancel₀ hk.ne', mul_inv_cancel₀ (Real.exp_pos c).ne', ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, one_mul, mul_one, ENNReal.ofReal_one]
    rw [e, withDensity_one]
  rw [hPeq] at htilt
  -- identify the field and the mean
  have hT : ∀ ψ : TestOn upperHalfPlaneOpens, T ψ = ∫ z, (q z - Fq.f z) * ψ z := fun ψ => by
    rw [hT, SupercriticalConformalCovariance.GM24.smoothDist_apply (hq.sub Fq.smooth.continuous.continuousOn)]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have hfield : ∀ ω', (shiftField field q Fq ω' + T) φ = field ω' φ := fun ω' => by
    change field ω' φ + smoothDist upperHalfPlaneOpens (fun z => Fq.f z - q z) φ + T φ = field ω' φ
    rw [hsmooth, hT, add_assoc, ← integral_add (LocalExt.integrable_mul_testOn hcont φ)
      (LocalExt.integrable_mul_testOn (u₀ := fun z => q z - Fq.f z)
        (hq.sub Fq.smooth.continuous.continuousOn) φ)]
    have e : ∫ z, ((Fq.f z - q z) * φ z + (q z - Fq.f z) * φ z) = 0 := by
      rw [← integral_zero ℂ ℝ]
      exact integral_congr_ae (ae_of_all _ fun z => by simp only; ring)
    rw [e, add_zero]
  filter_upwards [htilt, hKb] with ω h1 hK hφ
  have hφ' : Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) := hφ
  have e1 : (fun ω' => Complex.exp (Complex.I * (field ω' φ : ℂ))) =
      fun ω' => Complex.exp (Complex.I * ((shiftField field q Fq ω' + T) φ : ℂ)) := by
    funext ω'; rw [hfield]
  rw [e1, h1 hφ', Aux61Win.integral_meanF_eq (hu ω) hq (hWc ω) (hFq'.isGreenTest_src hK) φ hφ', hT]

end Tilt

end InteractingSLE.Sec5.Aux61Act
