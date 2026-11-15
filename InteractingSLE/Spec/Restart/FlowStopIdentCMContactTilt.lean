/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Joint
import InteractingSLE.Spec.Sec7.LocalExtCKernel
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The conditional Cameron–Martin tilt of a hull kernel by an abstract source (ruling R60)

Packet PROVE-G3SRC, the analytic core of the restricted (L1) (`FlowLineStopIdentCMIntervalStatement`). Source: Lemma
G3's proof (supplement p. 493: "Use the one full Cameron–Martin density for adding `f` to the conditional field. Apply
Aux. lemmas 61–63 […] always using this same density"), Aux. lemma 55's proof (`source/spec/p241-288.md` L196–L206,
p. 250: "Conditional Cameron–Martin shifting changes the mean to `C_{K_t} − P_t f` and leaves this covariance
unchanged").

PROVE-LOCEXT-A3 proved the conditional Cameron–Martin shift for the seed-ball source of Aux. lemma 55
(`LocalExt.srcJointKernelStatement`); its proof only uses the source through three convergence statements along the
approximating tests. This file states the computation for an **abstract source**, at any σ-algebra `m` for which the
field has the hull kernel (`E[e^{i h(ψ)} | m] = cfVal(∫ M ψ, E_t(ψ))` on `{supp ψ ∩ K_t = ∅}`, the form of the frozen
optional hull clause at a driving stop):

* `loewnerGreenEnergy_combo`: the quadratic expansion of the Loewner Green energy for a driver continuous on `[0, t₂]`,
  `t < t₂` (the clamped driver of `Ito.clampDrv` and `LocalExt.greenCross_combo`);
* **`ae_condExp_tilt_of_kernel`**: with test functions `s_k` avoiding the hull and `h(s_k) → Λ` almost surely, the
  joint conditional law of `(h(φ), Λ)` is Gaussian and
  `E[e^{−Λ} e^{i h(φ)} | m] = e^{−μ₂ + s₂₂/2} · cfVal(∫ M φ − s₁₂, E_t(φ))` on `{supp φ ∩ K_t = ∅}`, where `μ₂`, `s₂₂`,
  `s₁₂` are the limits of `∫ M s_k`, `E_t(s_k)`, `E_t(φ, s_k)`;
* **`ae_condExp_withDensity_of_kernel`**: Bayes' formula — under `Q = c e^{−Λ} · P` the field has the hull kernel with
  the mean shifted by `−s₁₂` (the Green potential of the source in `ℍ ∖ K_t`) and the same variance;
* `ae_condExp_withDensity_add_of_kernel`: the same for the field shifted by a deterministic distribution `T`.

These are the conditional kernel half of the Cameron–Martin identification (b) of `planning/handoffs/PROVE-L1G.md`
§4.1; the identification of the shifted mean with the reference word's coupling mean is a separate, deterministic step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCM

open LocalExt
open QuantumZipper (H Hbar fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)

/-! ### The quadratic expansion of the Loewner Green energy -/

/-- **The quadratic expansion of the Loewner Green energy** of `a φ + c ψ` for tests avoiding the hull, for a driver
continuous on `[0, t₂]` with `t < t₂` (the clamped driver `Ito.clampDrv W t₂` has the same maps and hull at `t`). -/
theorem loewnerGreenEnergy_combo {W : ℝ → ℝ} {t t₂ : ℝ} (ht : 0 ≤ t) (htt₂ : t < t₂)
    (hW : ContinuousOn W (Icc 0 t₂)) {φ ψ : TestOn upperHalfPlaneOpens}
    (hφ : Disjoint (tsupport φ) (fwdHull W t)) (hψ : Disjoint (tsupport ψ) (fwdHull W t)) (a c : ℝ) :
    loewnerGreenEnergy W t (a • φ + c • ψ) =
      a ^ 2 * loewnerGreenEnergy W t φ + 2 * a * c * greenCross W t φ ψ + c ^ 2 * loewnerGreenEnergy W t ψ := by
  set Wc : ℝ → ℝ := Ito.clampDrv W t₂ with hWc
  have hc : Continuous Wc := Ito.continuous_clampDrv (ht.trans htt₂.le) hW
  have hfwd : fwdMap Wc t = fwdMap W t := funext fun _ => Ito.fwdMap_clampDrv_of_le htt₂.le
  have hhull : fwdHull Wc t = fwdHull W t :=
    InteractingSLE.fwdHull_eq_of_eqOn ht htt₂ fun r hr => Ito.clampDrv_eqOn hr
  have hφG : IsGreenTest Wc t φ := isGreenTest_of_testOn φ (by rw [hhull]; exact hφ)
  have hψG : IsGreenTest Wc t ψ := isGreenTest_of_testOn ψ (by rw [hhull]; exact hψ)
  have e := greenCross_combo hc ht hφG hψG a c
  rw [loewnerGreenEnergy_eq_greenCross, loewnerGreenEnergy_eq_greenCross, loewnerGreenEnergy_eq_greenCross,
    ← greenCross_congr hfwd, ← greenCross_congr hfwd, ← greenCross_congr hfwd, ← greenCross_congr hfwd]
  exact e

/-! ### Convergence of the Loewner cross energies along dominated approximations -/

/-- `IsGreenTest` sees the driver only through the hull at `t`. -/
theorem isGreenTest_of_fwdHull_eq {W W' : ℝ → ℝ} {t : ℝ} {φ : ℂ → ℝ} (h : IsGreenTest W t φ)
    (hK : fwdHull W t = fwdHull W' t) : IsGreenTest W' t φ :=
  ⟨h.measurable, h.bdd, h.compact, fun z hz => hK ▸ h.alive z hz⟩

/-- **The diagonal Loewner cross energy converges along dominated approximations** (dominated convergence on the
product, with the bound `|g(y)| |g(z)| G_ℍ(y, z)`). -/
theorem tendsto_greenCross_diag {W : ℝ → ℝ} {t : ℝ} (hW : Continuous W) (ht : 0 ≤ t) {ψs : ℕ → ℂ → ℝ}
    {g ψ : ℂ → ℝ} (hg : IsGreenTest W t g) (hψs : ∀ k, IsGreenTest W t (ψs k)) (hψ : IsGreenTest W t ψ)
    (hle : ∀ k z, |ψs k z| ≤ |g z|) (hlim : ∀ z, Tendsto (fun k => ψs k z) atTop (𝓝 (ψ z))) :
    Tendsto (fun k => greenCross W t (ψs k) (ψs k)) atTop (𝓝 (greenCross W t ψ ψ)) := by
  simp_rw [greenCross_eq_integral_crossKer hW ht (hψs _) (hψs _), greenCross_eq_integral_crossKer hW ht hψ hψ]
  have hb : ∀ p : ℂ × ℂ, p.1 ≠ p.2 → 0 ≤ |g p.1| * |g p.2| * greenH p.1 p.2 := fun p hp => by
    by_cases h1 : g p.1 = 0
    · rw [h1, abs_zero, zero_mul, zero_mul]
    by_cases h2 : g p.2 = 0
    · rw [h2, abs_zero, mul_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (QuantumZipper.greenH_nonneg
      (show (0 : ℝ) ≤ p.1.im from le_of_lt (hg.alive _ h1).1)
      (show (0 : ℝ) ≤ p.2.im from le_of_lt (hg.alive _ h2).1) hp)
  refine tendsto_integral_of_dominated_convergence (fun p => |g p.1| * |g p.2| * greenH p.1 p.2)
    (fun k => (measurable_crossKer hW ht (hψs k).measurable (hψs k).measurable).aestronglyMeasurable)
    (integrable_abs_mul_abs_mul_greenH hg hg) (fun k => ae_ne_prod.mono fun p hp => ?_) (ae_of_all _ fun p => ?_)
  · rw [Real.norm_eq_abs]
    refine (abs_crossKer_le hW ht (hψs k) (hψs k) hp).trans ?_
    by_cases h1 : ψs k p.1 = 0
    · rw [h1, abs_zero, zero_mul, zero_mul]; exact hb p hp
    by_cases h2 : ψs k p.2 = 0
    · rw [h2, abs_zero, mul_zero, zero_mul]; exact hb p hp
    have hg1 : g p.1 ≠ 0 := fun h0 => h1 (abs_nonpos_iff.1 ((hle k p.1).trans (by rw [h0, abs_zero])))
    have hg2 : g p.2 ≠ 0 := fun h0 => h2 (abs_nonpos_iff.1 ((hle k p.2).trans (by rw [h0, abs_zero])))
    have hG := QuantumZipper.greenH_nonneg (show (0 : ℝ) ≤ p.1.im from le_of_lt (hg.alive _ hg1).1)
      (show (0 : ℝ) ≤ p.2.im from le_of_lt (hg.alive _ hg2).1) hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hle k p.1) (hle k p.2) (abs_nonneg _) (abs_nonneg _)) hG
  · simp only [crossKer]
    exact ((hlim p.1).mul tendsto_const_nhds).mul (hlim p.2)

/-- **The tilt's energy hypotheses from a dominated approximation of the source**, for a driver continuous on
`[0, t₂]`, `t < t₂`: if `ψ_k → ψ` pointwise with `|ψ_k| ≤ |g|` (all Green tests at `t`), then `E_t(φ, ψ_k) → E_t(φ, ψ)`
and `E_t(ψ_k) → E_t(ψ)`. -/
theorem tendsto_greenCross_of_dominated {W : ℝ → ℝ} {t t₂ : ℝ} (ht : 0 ≤ t) (htt₂ : t < t₂)
    (hW : ContinuousOn W (Icc 0 t₂)) {φ g ψ : ℂ → ℝ} {ψs : ℕ → ℂ → ℝ} (hφ : IsGreenTest W t φ)
    (hg : IsGreenTest W t g) (hψs : ∀ k, IsGreenTest W t (ψs k)) (hψ : IsGreenTest W t ψ)
    (hle : ∀ k z, |ψs k z| ≤ |g z|) (hlim : ∀ z, Tendsto (fun k => ψs k z) atTop (𝓝 (ψ z))) :
    Tendsto (fun k => greenCross W t φ (ψs k)) atTop (𝓝 (greenCross W t φ ψ)) ∧
      Tendsto (fun k => loewnerGreenEnergy W t (ψs k)) atTop (𝓝 (loewnerGreenEnergy W t ψ)) := by
  set Wc : ℝ → ℝ := Ito.clampDrv W t₂ with hWc
  have hc : Continuous Wc := Ito.continuous_clampDrv (ht.trans htt₂.le) hW
  have hfwd : fwdMap Wc t = fwdMap W t := funext fun _ => Ito.fwdMap_clampDrv_of_le htt₂.le
  have hhull : fwdHull W t = fwdHull Wc t :=
    (InteractingSLE.fwdHull_eq_of_eqOn ht htt₂ fun r hr => Ito.clampDrv_eqOn hr).symm
  refine ⟨?_, ?_⟩
  · simp_rw [← greenCross_congr hfwd]
    exact tendsto_greenCross hc ht (isGreenTest_of_fwdHull_eq hφ hhull) (isGreenTest_of_fwdHull_eq hg hhull)
      (fun k => isGreenTest_of_fwdHull_eq (hψs k) hhull) (isGreenTest_of_fwdHull_eq hψ hhull) hle hlim
  · simp_rw [loewnerGreenEnergy_eq_greenCross, ← greenCross_congr hfwd]
    exact tendsto_greenCross_diag hc ht (isGreenTest_of_fwdHull_eq hg hhull)
      (fun k => isGreenTest_of_fwdHull_eq (hψs k) hhull) (isGreenTest_of_fwdHull_eq hψ hhull) hle hlim

/-! ### The conditional tilt -/

section Tilt

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The conditional Cameron–Martin tilt of a hull kernel by an abstract source.** Let the field `h` have, given
`m`, the hull kernel with driver `Wd ω` (continuous on `[0, t₂]` for some `t₂ > t ω`), time `t ω` and mean `M ω`. Let
`s_k` be test functions avoiding the hull with `h(s_k) → Λ` almost surely, `e^{−Λ}` integrable, and with
`∫ M s_k → μ₂`, `E_t(s_k) → s₂₂` and (on the event) `E_t(φ, s_k) → s₁₂`. Then, almost surely on
`{supp φ ∩ K_t = ∅}`, `E[e^{−Λ} e^{i h(φ)} | m] = e^{−μ₂ + s₂₂/2} · cfVal(∫ M φ − s₁₂, E_t(φ))`. -/
theorem ae_condExp_tilt_of_kernel [IsProbabilityMeasure P] (hm : m ≤ mΩ) {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) {Wd : Ω → ℝ → ℝ} {t : Ω → ℝ} {M : Ω → ℂ → ℝ}
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, M ω z * ψ z) (loewnerGreenEnergy (Wd ω) (t ω) ψ))
    (hpath : ∀ᵐ ω ∂P, 0 ≤ t ω ∧ ∃ t₂, t ω < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂))
    (hMint : ∀ᵐ ω ∂P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => M ω z * ψ z)
    {s : ℕ → TestOn upperHalfPlaneOpens} {Λ : Ω → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (s k)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P)
    (hsd : ∀ᵐ ω ∂P, ∀ k, Disjoint (tsupport (s k)) (fwdHull (Wd ω) (t ω))) {μ₂ s₂₂ : Ω → ℝ}
    (hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, M ω z * s k z) atTop (𝓝 (μ₂ ω)))
    (hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun k => loewnerGreenEnergy (Wd ω) (t ω) (s k)) atTop (𝓝 (s₂₂ ω)))
    (φ : TestOn upperHalfPlaneOpens) {s₁₂ : Ω → ℝ}
    (hs₁₂ : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun k => greenCross (Wd ω) (t ω) φ (s k)) atTop (𝓝 (s₁₂ ω))) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) | m] ω =
        ((Real.exp (-μ₂ ω + s₂₂ ω / 2) : ℝ) : ℂ) *
          cfVal ((∫ z, M ω z * φ z) - s₁₂ ω) (loewnerGreenEnergy (Wd ω) (t ω) φ) := by
  set D : Set Ω := {ω | Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω))} with hD
  have hY₁ : Measurable fun ω => h ω φ :=
    (measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp hhm)
  have hjoint : ∀ a c : ℝ, ∀ᵐ ω ∂P, ω ∈ D →
      P[fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + c * Λ ω' : ℝ) : ℂ)) | m] ω =
        cfVal (a * (∫ z, M ω z * φ z) + c * μ₂ ω)
          (a ^ 2 * loewnerGreenEnergy (Wd ω) (t ω) φ + 2 * a * c * s₁₂ ω + c ^ 2 * s₂₂ ω) := by
    intro a c
    refine ae_condExp_cexp_of_tendsto_on (m := m) (P := P)
      (Y := fun k ω => h ω (a • φ + c • s k)) (Y' := fun ω => a * h ω φ + c * Λ ω)
      (a := fun k ω => ∫ z, M ω z * (a • φ + c • s k) z)
      (q := fun k ω => loewnerGreenEnergy (Wd ω) (t ω) (a • φ + c • s k))
      (fun k => ((measurable_pi_apply _).comp ((LQGMetric.measurable_distEval _).comp hhm)).aemeasurable)
      (fun k => ?_) ?_ ?_
    · filter_upwards [hker (a • φ + c • s k), hsd] with ω h1 hs hDω
      refine h1 (Disjoint.mono_left (tsupport_add _ _) (Disjoint.union_left ?_ ?_))
      · exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ => a) φ) hDω
      · exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ => c) (s k)) (hs k)
    · filter_upwards [hΛ] with ω hω
      have e : ∀ k, h ω (a • φ + c • s k) = a * h ω φ + c * h ω (s k) := fun k => by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp_rw [e]
      exact tendsto_const_nhds.add (hω.const_mul c)
    · filter_upwards [hpath, hMint, hsd, hμ₂, hs₂₂, hs₁₂] with ω hp hi hs h2 h22 h12 hDω
      obtain ⟨ht0, t₂, htt₂, hc⟩ := hp
      refine ⟨?_, ?_⟩
      · have e : ∀ k, (∫ z, M ω z * (a • φ + c • s k) z) =
            a * (∫ z, M ω z * φ z) + c * ∫ z, M ω z * s k z := fun k => by
          have e1 : (fun z => M ω z * (a • φ + c • s k) z) =
              fun z => a * (M ω z * φ z) + c * (M ω z * s k z) := by
            funext z
            show M ω z * (a * φ z + c * s k z) = _
            ring
          rw [e1, integral_add ((hi φ hDω).const_mul a) ((hi (s k) (hs k)).const_mul c), integral_const_mul,
            integral_const_mul]
        simp_rw [e]
        exact tendsto_const_nhds.add (h2.const_mul c)
      · have e : ∀ k, loewnerGreenEnergy (Wd ω) (t ω) (a • φ + c • s k) =
            a ^ 2 * loewnerGreenEnergy (Wd ω) (t ω) φ + 2 * a * c * greenCross (Wd ω) (t ω) φ (s k) +
              c ^ 2 * loewnerGreenEnergy (Wd ω) (t ω) (s k) := fun k =>
          loewnerGreenEnergy_combo ht0 htt₂ hc hDω (hs k) a c
        simp_rw [e]
        exact (tendsto_const_nhds.add ((h12 hDω).const_mul _)).add (h22.const_mul _)
  exact ae_condExp_tilt_of_joint (m := m) (P := P) (μ₁ := fun ω => ∫ z, M ω z * φ z) (μ₂ := μ₂)
    (s₁₁ := fun ω => loewnerGreenEnergy (Wd ω) (t ω) φ) (s₁₂ := s₁₂) (s₂₂ := s₂₂) hm hY₁ hΛm hint hjoint

/-- The Loewner cross energy against the zero function vanishes. -/
theorem greenCross_zero_left (W : ℝ → ℝ) (t : ℝ) (ψ : ℂ → ℝ) : greenCross W t 0 ψ = 0 := by
  simp only [greenCross, Pi.zero_apply, zero_mul, integral_zero]

/-- **The conditional mean of the tilt** (`ae_condExp_tilt_of_kernel` at the test `0`):
`E[e^{−Λ} | m] = e^{−μ₂ + s₂₂/2}` almost surely, as real conditional expectations. -/
theorem condExp_exp_neg_ae_eq_of_kernel [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {Wd : Ω → ℝ → ℝ} {t : Ω → ℝ} {M : Ω → ℂ → ℝ}
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, M ω z * ψ z) (loewnerGreenEnergy (Wd ω) (t ω) ψ))
    (hpath : ∀ᵐ ω ∂P, 0 ≤ t ω ∧ ∃ t₂, t ω < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂))
    (hMint : ∀ᵐ ω ∂P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => M ω z * ψ z)
    {s : ℕ → TestOn upperHalfPlaneOpens} {Λ : Ω → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (s k)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P)
    (hsd : ∀ᵐ ω ∂P, ∀ k, Disjoint (tsupport (s k)) (fwdHull (Wd ω) (t ω))) {μ₂ s₂₂ : Ω → ℝ}
    (hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, M ω z * s k z) atTop (𝓝 (μ₂ ω)))
    (hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun k => loewnerGreenEnergy (Wd ω) (t ω) (s k)) atTop (𝓝 (s₂₂ ω))) :
    P[fun ω => Real.exp (-Λ ω) | m] =ᵐ[P] fun ω => Real.exp (-μ₂ ω + s₂₂ ω / 2) := by
  have h0 := ae_condExp_tilt_of_kernel hm hhm hker hpath hMint hΛm hΛ hint hsd hμ₂ hs₂₂ 0 (s₁₂ := fun _ => 0)
    (ae_of_all _ fun ω _ => by
      simp only [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, greenCross_zero_left]
      exact tendsto_const_nhds)
  have hc : P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) | m] =ᵐ[P]
      fun ω => ((Real.exp (-μ₂ ω + s₂₂ ω / 2) : ℝ) : ℂ) := by
    filter_upwards [h0] with ω hω
    have hd : Disjoint (tsupport ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) (fwdHull (Wd ω) (t ω)) := by
      rw [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, tsupport_zero]
      exact Set.empty_disjoint _
    have e := hω hd
    have e1 : (fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' 0 : ℂ))) =
        fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) := by
      funext ω'
      rw [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [e1] at e
    rw [e]
    have e2 : (∫ z, M ω z * ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) z) = 0 := by
      simp only [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, Pi.zero_apply, mul_zero,
        integral_zero]
    have e3 : loewnerGreenEnergy (Wd ω) (t ω) ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 := by
      simp only [loewnerGreenEnergy, show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl,
        Pi.zero_apply, zero_mul, integral_zero]
    rw [e2, e3, cfVal]
    simp
  have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := m) hint
  filter_upwards [hcomm, hc] with ω h1 h2
  have h3 : ((P[fun ω => Real.exp (-Λ ω) | m] ω : ℝ) : ℂ) = ((Real.exp (-μ₂ ω + s₂₂ ω / 2) : ℝ) : ℂ) := by
    rw [← h2]
    exact h1
  exact_mod_cast h3

/-- **Bayes' form of the conditional Cameron–Martin tilt.** In the setting of `ae_condExp_tilt_of_kernel`, under
`Q = k e^{−Λ} · P` (`k > 0` a constant), almost surely on `{supp φ ∩ K_t = ∅}` the field has the hull kernel with the
mean shifted by `−s₁₂` and the same variance: `E_Q[e^{i h(φ)} | m] = cfVal(∫ M φ − s₁₂, E_t(φ))`. -/
theorem ae_condExp_withDensity_of_kernel [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {Wd : Ω → ℝ → ℝ} {t : Ω → ℝ} {M : Ω → ℂ → ℝ}
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, M ω z * ψ z) (loewnerGreenEnergy (Wd ω) (t ω) ψ))
    (hpath : ∀ᵐ ω ∂P, 0 ≤ t ω ∧ ∃ t₂, t ω < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂))
    (hMint : ∀ᵐ ω ∂P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => M ω z * ψ z)
    {s : ℕ → TestOn upperHalfPlaneOpens} {Λ : Ω → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (s k)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P)
    (hsd : ∀ᵐ ω ∂P, ∀ k, Disjoint (tsupport (s k)) (fwdHull (Wd ω) (t ω))) {μ₂ s₂₂ : Ω → ℝ}
    (hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, M ω z * s k z) atTop (𝓝 (μ₂ ω)))
    (hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun k => loewnerGreenEnergy (Wd ω) (t ω) (s k)) atTop (𝓝 (s₂₂ ω)))
    {k : ℝ} (hk : 0 < k) (φ : TestOn upperHalfPlaneOpens) {s₁₂ : Ω → ℝ}
    (hs₁₂ : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun k => greenCross (Wd ω) (t ω) φ (s k)) atTop (𝓝 (s₁₂ ω))) :
    ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))),
      Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
          Complex.exp (Complex.I * (h ω' φ : ℂ)) | m] ω =
        cfVal ((∫ z, M ω z * φ z) - s₁₂ ω) (loewnerGreenEnergy (Wd ω) (t ω) φ) := by
  set Z : Ω → ℝ := fun ω => k * Real.exp (-Λ ω) with hZdef
  set Q := P.withDensity fun ω => ENNReal.ofReal (Z ω) with hQ
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hZm : Measurable Z := measurable_const.mul (Real.measurable_exp.comp hΛm.neg)
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => (mul_pos hk (Real.exp_pos _)).le
  have hZi : Integrable Z P := hint.const_mul k
  -- the conditional mean of the density
  have hE := condExp_exp_neg_ae_eq_of_kernel hm hhm hker hpath hMint hΛm hΛ hint hsd hμ₂ hs₂₂
  have hZE : P[Z | m] =ᵐ[P] fun ω => k * Real.exp (-μ₂ ω + s₂₂ ω / 2) := by
    have e := condExp_smul (μ := P) (m := m) k (fun ω => Real.exp (-Λ ω))
    filter_upwards [e, hE] with ω h1 h2
    have hZf : Z = k • fun ω => Real.exp (-Λ ω) := rfl
    rw [hZf, h1, Pi.smul_apply, smul_eq_mul, h2]
  set N : Ω → ℝ := fun ω => if 0 < P[Z | m] ω then P[Z | m] ω else 1 with hNdef
  have hNm : StronglyMeasurable[m] N := by
    have hs : MeasurableSet[m] {ω | 0 < P[Z | m] ω} :=
      measurableSet_lt (measurable_const) stronglyMeasurable_condExp.measurable
    exact StronglyMeasurable.ite hs stronglyMeasurable_condExp stronglyMeasurable_const
  have hNpos : ∀ ω, 0 < N ω := fun ω => by
    simp only [hNdef]
    split_ifs with hpos
    · exact hpos
    · exact one_pos
  have hNE : N =ᵐ[P] fun ω => k * Real.exp (-μ₂ ω + s₂₂ ω / 2) := by
    filter_upwards [hZE] with ω hω
    simp only [hNdef, hω, mul_pos hk (Real.exp_pos _), ↓reduceIte]
  have hZN : P[Z | m] =ᵐ[P] N := hZE.trans hNE.symm
  -- Bayes
  set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hXdef
  have hXm : AEStronglyMeasurable X P :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp hhm))))).aestronglyMeasurable
  have hXb : ∀ ω, ‖X ω‖ ≤ 1 := fun ω => by
    show ‖Complex.exp (Complex.I * (h ω φ : ℂ))‖ ≤ 1
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hB := condExp_withDensity_ae_eq (P := P) (m := m) hm hZm hZ0 hZi hNm hNpos hZN hXm hXb
  -- the numerator
  have hT := ae_condExp_tilt_of_kernel hm hhm hker hpath hMint hΛm hΛ hint hsd hμ₂ hs₂₂ φ hs₁₂
  have hsm : P[fun ω => Z ω • X ω | m] =ᵐ[P]
      fun ω => (k : ℂ) • P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω' | m] ω := by
    have e := condExp_smul (μ := P) (m := m) (k : ℂ) (fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω')
    have hf : (fun ω => Z ω • X ω) = (k : ℂ) • fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω' := by
      funext ω
      simp only [hZdef, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [hf]
    filter_upwards [e] with ω hω
    rw [hω, Pi.smul_apply]
  filter_upwards [hB, hQP.ae_le hsm, hQP.ae_le hT, hQP.ae_le hNE] with ω e1 e2 e3 e4 hD
  rw [e1, e2, e3 hD, e4]
  simp only [smul_eq_mul, Complex.real_smul]
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk.ne'
  have he0 : ((Real.exp (-μ₂ ω + s₂₂ ω / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [Complex.ofReal_inv, Complex.ofReal_mul]
  field_simp

/-- `cfVal` absorbs a phase: `e^{i b} cfVal(a, q) = cfVal(a + b, q)`. -/
theorem cexp_mul_cfVal (a b q : ℝ) : Complex.exp (Complex.I * (b : ℂ)) * cfVal a q = cfVal (a + b) q := by
  simp only [cfVal, ← Complex.exp_add, Complex.ofReal_add]
  congr 1
  ring

/-- **The tilted kernel for a deterministically shifted field**: under `Q = k e^{−Λ} · P`, the field `h + T` (`T` a
deterministic distribution) has, almost surely on `{supp φ ∩ K_t = ∅}`, the hull kernel with mean
`∫ M φ − s₁₂ + T(φ)`. -/
theorem ae_condExp_withDensity_add_of_kernel [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {Wd : Ω → ℝ → ℝ} {t : Ω → ℝ} {M : Ω → ℂ → ℝ}
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, M ω z * ψ z) (loewnerGreenEnergy (Wd ω) (t ω) ψ))
    (hpath : ∀ᵐ ω ∂P, 0 ≤ t ω ∧ ∃ t₂, t ω < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂))
    (hMint : ∀ᵐ ω ∂P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => M ω z * ψ z)
    {s : ℕ → TestOn upperHalfPlaneOpens} {Λ : Ω → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (s k)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P)
    (hsd : ∀ᵐ ω ∂P, ∀ k, Disjoint (tsupport (s k)) (fwdHull (Wd ω) (t ω))) {μ₂ s₂₂ : Ω → ℝ}
    (hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, M ω z * s k z) atTop (𝓝 (μ₂ ω)))
    (hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun k => loewnerGreenEnergy (Wd ω) (t ω) (s k)) atTop (𝓝 (s₂₂ ω)))
    {k : ℝ} (hk : 0 < k) (T : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) {s₁₂ : Ω → ℝ}
    (hs₁₂ : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun k => greenCross (Wd ω) (t ω) φ (s k)) atTop (𝓝 (s₁₂ ω))) :
    ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))),
      Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
          Complex.exp (Complex.I * ((h ω' + T) φ : ℂ)) | m] ω =
        cfVal ((∫ z, M ω z * φ z) - s₁₂ ω + T φ) (loewnerGreenEnergy (Wd ω) (t ω) φ) := by
  set Q := P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)) with hQ
  have hB := ae_condExp_withDensity_of_kernel hm hhm hker hpath hMint hΛm hΛ hint hsd hμ₂ hs₂₂ hk φ hs₁₂
  have hf : (fun ω' => Complex.exp (Complex.I * ((h ω' + T) φ : ℂ))) =
      Complex.exp (Complex.I * (T φ : ℂ)) • fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext ω'
    have ha : (h ω' + T) φ = h ω' φ + T φ := rfl
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, ha, Complex.ofReal_add]
    congr 1
    ring
  have e := condExp_smul (μ := Q) (m := m) (Complex.exp (Complex.I * (T φ : ℂ)))
    (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)))
  rw [hf]
  filter_upwards [e, hB] with ω h1 h2 hD
  rw [h1, Pi.smul_apply, smul_eq_mul, h2 hD, cexp_mul_cfVal]

end Tilt

/-! ### At a driving stop of an optional hull coupling -/

section Coupling

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- A finite stop before `z`, read as a real time. -/
theorem coe_untopD_lt {τ : WithTop ℝ≥0} {z : ℝ≥0∞} (h : (τ : ℝ≥0∞) < z) :
    ((τ.untopD 0 : ℝ≥0) : ℝ≥0∞) < z := by
  induction τ using WithTop.recTopCoe with
  | top => exact absurd h (not_lt.2 le_top)
  | coe a => exact h

/-- Along a path continuous before `ζ`, a time `t < ζ` has room: the driver is continuous on `[0, t₂]` for some
`t₂ > t`. -/
theorem exists_continuousOn_Icc_of_lt {w : ℝ≥0 → ℝ} {z : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < z})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < z) : ∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ContinuousOn (fun s : ℝ => w s.toNNReal) (Icc 0 t₂) := by
  obtain ⟨t₂, htt₂, ht₂z⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  exact ⟨t₂, by exact_mod_cast htt₂, Ito.continuousOn_rpath hw ht₂z⟩

/-- **The conditional Cameron–Martin tilt at a driving stop of an optional hull coupling.** Let `τ < ζ` be a stopping
time of the driving filtration, `u` bounded harmonic extensions of the data at `τ`, and `s_k`, `Λ`, `μ₂`, `s₂₂`, `s₁₂` a
source as in `ae_condExp_tilt_of_kernel` (for the coupling mean at `τ`). Under `Q = k e^{−Λ} · P`, for a deterministic
distribution `T`, almost surely on `{supp φ ∩ K_τ = ∅}`:
`E_Q[e^{i (h + T)(φ)} | 𝓕_τ] = cfVal(∫ 𝔥_τ φ − s₁₂ + T(φ), E_τ(φ))`. The kernel hypothesis is the frozen optional hull
clause, the continuity of the driver before `ζ` comes from the evolution, and the integrability of the coupling mean
against tests avoiding the hull from `LocalExt.integrable_couplingMean_mul`. -/
theorem ae_condExp_withDensity_add_of_coupling [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    {s : ℕ → TestOn upperHalfPlaneOpens} {Λ : Ω → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (s k)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P)
    (hsd : ∀ᵐ ω ∂P, ∀ k, Disjoint (tsupport (s k))
      (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) {μ₂ s₂₂ : Ω → ℝ}
    (hμ₂ : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
      (u ω) z * s k z) atTop (𝓝 (μ₂ ω)))
    (hs₂₂ : ∀ᵐ ω ∂P, Tendsto (fun k => loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
      ((τ ω).untopD 0 : ℝ≥0) (s k)) atTop (𝓝 (s₂₂ ω)))
    {k : ℝ} (hk : 0 < k) (T : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) {s₁₂ : Ω → ℝ}
    (hs₁₂ : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      Tendsto (fun k => greenCross (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ (s k)) atTop
        (𝓝 (s₁₂ ω))) :
    ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))),
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[fun ω' =>
          Complex.exp (Complex.I * ((h ω' + T) φ : ℂ)) | hτ.measurableSpace] ω =
        cfVal ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) -
            s₁₂ ω + T φ)
          (loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ) := by
  obtain ⟨_hX', hker⟩ := hC.2.2.2
  obtain ⟨-, hK⟩ := hker τ hτ hτζ
  have hpathC : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hC.1.2.2.2.2] with ω hp
    exact hp.2.2.2.1
  refine ae_condExp_withDensity_add_of_kernel (m := hτ.measurableSpace) (P := P) hτ.measurableSpace_le hC.2.1
    (Wd := fun ω => fun s : ℝ => W s.toNNReal ω) (t := fun ω => (((τ ω).untopD 0 : ℝ≥0) : ℝ))
    (M := fun ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω))
    (fun ψ => hK u hu ψ) ?_ ?_ hΛm hΛ hint hsd hμ₂ hs₂₂ hk T φ hs₁₂
  · filter_upwards [hpathC, hτζ] with ω hw hτω
    have hτω' := coe_untopD_lt hτω
    exact ⟨NNReal.coe_nonneg _, exists_continuousOn_Icc_of_lt hw hτω'⟩
  · filter_upwards [hpathC, hτζ] with ω hw hτω ψ hψ
    have hτω' := coe_untopD_lt hτω
    exact integrable_couplingMean_mul (κ := κ) (Ito.continuousOn_rpath hw hτω') (hu ω).1 hψ

end Coupling

end FlowStopIdentCM

end Restart

end InteractingSLE
