/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WinMean
import InteractingSLE.Spec.Restart.FlowStopIdentCMContactTilt

/-!
# Aux. lemma 62 for a general actual mean: the tilted kernel at one stop is the reference kernel (piece R3)

Packet PROVE-AUX61-WIN. Specification Aux. lemma 62 (`source/spec/p241-288.md` L467–L500, pp. 262–263: "Start with the
given coupling and weight by the full Cameron–Martin density for adding `f`. Conditional on any additional retained
pre-contact range `A`, the Gaussian mean becomes `M_A + P_{ℍ∖A} f` […] Applying (PC1) to the actual and the reference
canonical means, and using `f = v` on the range and in its buffer, shows that the weighted mean agrees […] with
`M̂_A`"); Astra's follow-up 4 L236–L262 (ruling R71).

The actual coupling here is **general**: at a stop `t` of the restarted path the conditional characteristic functional
of the field given the retained σ-algebra `m` is Gaussian with an arbitrary pointwise mean `M` (`hker`), and `M`
satisfies (PC1) with the old-mean difference `q` (`hPC1`, the output of Aux. lemma 61, piece R2). The reference is
any mean `M̂` satisfying (PC1) with `q̂` (for a finite word: `Aux61Win.isPC1_couplingMean_ref`). The comparison cutoff
`F` equals `v = q̂ − q` near the hull. Weighting by `k e^{−Λ}` (`Λ = lim h(s_n)`, `s_n → F.src`) and adding the
deterministic shift `T = (v − F.f)` (a distribution, zero near the hull) gives the reference kernel:

* **`ae_condExp_tilt_eq_ref`**: under `Q = k e^{−Λ} · P`, almost surely on `{φ off K_t}`,
  `E_Q[e^{i (h + T)(φ)} | m] = cfVal(∫ M̂_t φ, E_t(φ))`.

This is the landed general-mean tilt (`Restart.FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel`, which takes an
arbitrary mean family) followed by the deterministic identity `Aux61Win.integral_mean_shift_eq`; the cross-energy limit
is identified by dominated convergence (`LocalExt.tendsto_greenCross`). The analytic side conditions of the tilt
(integrability of `M` against tests, the limits `μ₂`, `s₂₂` and of the field pairing `Λ`, integrability of `e^{−Λ}`)
are hypotheses: they are properties of the actual fibre, supplied where it is constructed.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61Win

open QuantumZipper (H Hbar fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The tests dominated by a cutoff's source avoid every hull inside the cutoff's harmonic region. -/
theorem disjoint_tsupport_of_abs_le_src {F : CMCut} {q : ℂ → ℝ} {N : Set ℂ} {O₀ : Set ℝ} (hF : IsCutoffOn F q N O₀)
    {s : ℂ → ℝ} (hs : ∀ z, |s z| ≤ |F.src z|) {K : Set ℂ} (hKN : K ⊆ N) : Disjoint (tsupport s) K := by
  have hsub : tsupport s ⊆ tsupport (QuantumZipper.K3.greenDensity F.f) := by
    refine closure_mono fun z hz => ?_
    intro h0
    apply hz
    have h1 : F.src z = 0 := by
      by_cases hzH : z ∈ H
      · rw [CMCut.src_of_mem _ hzH, h0, neg_zero]
      · exact CMCut.src_of_notMem _ hzH
    have h2 := hs z
    rw [h1, abs_zero] at h2
    exact abs_nonpos_iff.1 h2
  refine Set.disjoint_of_subset_left hsub (Set.disjoint_left.2 fun z hz hzK => ?_)
  have hloc : ∀ᶠ y in 𝓝 z, QuantumZipper.K3.greenDensity F.f y = 0 :=
    Filter.eventually_of_mem (hF.isOpen.mem_nhds (hKN hzK)) hF.harmonic
  exact (notMem_tsupport_iff_eventuallyEq.2 hloc) hz

/-- **The general-mean Cameron–Martin tilt at one stop gives the reference kernel** (Aux. lemma 62's kernel step,
piece R3). See the module docstring. -/
theorem ae_condExp_tilt_eq_ref {S : Type*} {m mS : MeasurableSpace S} {P : Measure S} [IsProbabilityMeasure P]
    (hm : m ≤ mS) {h : S → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {κ : ℝ} {u₀ q qR : ℂ → ℝ} {O₀ : Set ℝ} (hq : ContinuousOn q H) (hqR : ContinuousOn qR H)
    {Wd : S → ℝ → ℝ} {t : S → ℝ} {M MR : S → ℂ → ℝ}
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, M ω z * ψ z) (loewnerGreenEnergy (Wd ω) (t ω) ψ))
    (hpath : ∀ᵐ ω ∂P, Continuous (Wd ω) ∧ 0 ≤ t ω)
    (hMint : ∀ᵐ ω ∂P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => M ω z * ψ z)
    (hPC1 : ∀ᵐ ω ∂P, IsPC1 κ u₀ (Wd ω) (t ω) q O₀ (M ω))
    (hPC1R : ∀ᵐ ω ∂P, IsPC1 κ u₀ (Wd ω) (t ω) qR O₀ (MR ω))
    {Fq : CMCut} {Nq : Set ℂ} (hFq : IsCutoffOn Fq q Nq O₀) (h0q : (0 : ℂ) ∈ Nq)
    {F : CMCut} {N : Set ℂ} (hF : IsCutoffOn F (fun z => qR z - q z) N O₀) (h0N : (0 : ℂ) ∈ N)
    (hKN : ∀ᵐ ω ∂P, closure (fwdHull (Wd ω) (t ω)) ⊆ Nq ∩ N)
    {s : ℕ → TestOn upperHalfPlaneOpens} (hsle : ∀ n z, |s n z| ≤ |F.src z|)
    (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)))
    {Λ : S → ℝ} (hΛm : Measurable Λ) (hΛ : ∀ᵐ ω ∂P, Tendsto (fun n => h ω (s n)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P) {μ₂ s₂₂ : S → ℝ}
    (hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ z, M ω z * s n z) atTop (𝓝 (μ₂ ω)))
    (hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun n => loewnerGreenEnergy (Wd ω) (t ω) (s n)) atTop (𝓝 (s₂₂ ω)))
    {k : ℝ} (hk : 0 < k) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))),
      Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
          Complex.exp (Complex.I * ((h ω' + smoothDist upperHalfPlaneOpens
            (fun z => (qR z - q z) - F.f z)) φ : ℂ)) | m] ω =
        cfVal (∫ z, MR ω z * φ z) (loewnerGreenEnergy (Wd ω) (t ω) φ) := by
  set Q := P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)) with hQ
  set T : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens (fun z => (qR z - q z) - F.f z) with hT
  -- the tests stay off the hull, and the cross energies converge to the source's
  have hsd : ∀ᵐ ω ∂P, ∀ n, Disjoint (tsupport (s n)) (fwdHull (Wd ω) (t ω)) := by
    filter_upwards [hKN] with ω hK n
    exact disjoint_tsupport_of_abs_le_src hF (hsle n) fun z hz => (hK (subset_closure hz)).2
  have hsrcG : ∀ᵐ ω ∂P, IsGreenTest (Wd ω) (t ω) F.src := by
    filter_upwards [hKN] with ω hK
    exact hF.isGreenTest_src fun z hz => (hK hz).2
  have hs₁₂ : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun n => greenCross (Wd ω) (t ω) φ (s n)) atTop (𝓝 (greenCross (Wd ω) (t ω) φ F.src)) := by
    filter_upwards [hpath, hsd, hsrcG] with ω hp hd hG hφ
    exact LocalExt.tendsto_greenCross hp.1 hp.2 (LocalExt.isGreenTest_of_testOn φ hφ) hG
      (fun n => LocalExt.isGreenTest_of_testOn (s n) (hd n)) hG hsle hslim
  have hpath' : ∀ᵐ ω ∂P, 0 ≤ t ω ∧ ∃ t₂, t ω < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂) := by
    filter_upwards [hpath] with ω hp
    exact ⟨hp.2, t ω + 1, by linarith, hp.1.continuousOn⟩
  have htilt := Restart.FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel hm hhm hker hpath' hMint hΛm hΛ hint
    hsd hμ₂ hs₂₂ hk T φ hs₁₂
  -- the mean identity, pathwise
  have hc : ContinuousOn (fun z => (qR z - q z) - F.f z) H := (hqR.sub hq).sub F.smooth.continuous.continuousOn
  have hTφ : T φ = ∫ z, ((qR z - q z) - F.f z) * φ z := by
    rw [hT, SupercriticalConformalCovariance.GM24.smoothDist_apply hc φ]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  filter_upwards [htilt, hQP.ae_le hpath, hQP.ae_le hPC1, hQP.ae_le hPC1R, hQP.ae_le hKN] with ω h1 hp hA hR hK hφ
  rw [h1 hφ, hTφ]
  congr 1
  exact integral_mean_shift_eq hp.1 hp.2 hq hqR hA hR hFq h0q (fun z hz => (hK hz).1) hF h0N
    (fun z hz => (hK hz).2) φ hφ

end InteractingSLE.Sec5.Aux61Win
