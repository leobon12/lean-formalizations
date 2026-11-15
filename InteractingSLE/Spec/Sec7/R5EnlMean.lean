/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlKernel

/-!
# Means of retained kernels whose records agree on an event

Packet PROVE-R5-ENLARGED. Aux. 35's proof (`source/spec/p193-240.md` L28, p. 194): "On `{q < T}`, one has `q* = q`
and `T_q = T`. The stopped information at `T` already contains the prefix at `q` and its germ; on this event the
retained stopped information and the marked harmonic mean for `A_{T_q}` are exactly those for `A_T`. This is an
equality of the restricted stopped sigma-algebras, not a claim that conditioning on the event preserves a Gaussian
law."

Here: if the field is `M₁ + GFF_{U₁}` given `𝒢₁` and `M₂ + GFF_{U₂}` given `𝒢₂`, the two σ-algebras have the same
trace on an event `E ∈ 𝒢₁` and `U₁ = U₂` on `E`, then `M₁ = M₂` on `E` (as whole distributions, almost surely). The
two records need not be nested. Also: a version of a local-set mean agrees with the mean of any retained kernel at a
larger record that is measurable for the germ σ-algebra.

## Main results

* `condExp_exp_eq_of_isCondZeroBoundaryGFF` — the conditional characteristic function `e^{iM} e^{−σ²/2}`;
* `ae_apply_eq_of_isCondZeroBoundaryGFF_of_trace` (per test function) and
  **`ae_eq_of_isCondZeroBoundaryGFF_of_trace`** (whole distributions);
* `ae_eq_of_isLocalSetMean_of_retained` — a local-set mean equals a germ-measurable retained mean.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets PocketStopSide

section Mean

variable {Ω : Type*} {𝒢 𝒢₁ 𝒢₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The conditional characteristic function of a retained kernel**: given `𝒢`, `h = M + GFF_U` gives
`E[e^{i h(φ)} | 𝒢] = e^{i M(φ)} e^{−σ²_U(φ)/2}`. -/
theorem condExp_exp_eq_of_isCondZeroBoundaryGFF [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hM : Measurable[𝒢] M)
    {U : Ω → Set ℂ} (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => h ω - M ω) (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (M ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ) := by
  set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (M ω φ : ℂ)) with hYdef
  set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((h ω - M ω) φ : ℂ)) with hXdef
  have hsplit : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) = Y * X := by
    funext ω
    simp only [hYdef, hXdef, Pi.mul_apply, ← Complex.exp_add]
    congr 1
    have e : (h ω - M ω) φ = h ω φ - M ω φ := rfl
    rw [e]
    push_cast
    ring
  have hMφ : Measurable[𝒢] fun ω => M ω φ := (LQGMetric.measurable_distOn_apply φ).comp hM
  have hYm : StronglyMeasurable[𝒢] Y := (@GFF.measurable_exp_I_mul Ω 𝒢 _ hMφ).stronglyMeasurable
  have hXm : Measurable X := GFF.measurable_exp_I_mul
    ((LQGMetric.measurable_distOn_apply φ).comp (measurable_sub_of_le h𝒢 hh hM))
  have hXi : Integrable X P := GFF.integrable_exp_I_mul
    ((LQGMetric.measurable_distOn_apply φ).comp (measurable_sub_of_le h𝒢 hh hM))
  have hYXi : Integrable (Y * X) P := by
    rw [← hsplit]
    exact GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh)
  have hpull : P[Y * X | 𝒢] =ᵐ[P] Y * P[X | 𝒢] :=
    condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hYm.aestronglyMeasurable hYXi hXi
  rw [hsplit]
  filter_upwards [hpull, hc φ] with ω e1 e2
  rw [e1, Pi.mul_apply, e2]

/-- **Means of two retained kernels agree where their records and domains agree** (one test function). The records
`𝒢₁`, `𝒢₂` need not be nested: only their traces on `E ∈ 𝒢₁` are compared. -/
theorem ae_apply_eq_of_isCondZeroBoundaryGFF_of_trace [IsFiniteMeasure P] (hm₁ : 𝒢₁ ≤ mΩ) (hm₂ : 𝒢₂ ≤ mΩ)
    {E : Set Ω} (hE : MeasurableSet[𝒢₁] E)
    (htrace : ∀ t, MeasurableSet[𝒢₁] (E ∩ t) ↔ MeasurableSet[𝒢₂] (E ∩ t))
    {h M₁ M₂ : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hM₁ : Measurable[𝒢₁] M₁)
    (hM₂ : Measurable[𝒢₂] M₂) {U₁ U₂ : Ω → Set ℂ}
    (hc₁ : IsCondZeroBoundaryGFF P 𝒢₁ U₁ fun ω => h ω - M₁ ω)
    (hc₂ : IsCondZeroBoundaryGFF P 𝒢₂ U₂ fun ω => h ω - M₂ ω)
    (hU : ∀ᵐ ω ∂P, ω ∈ E → U₁ ω = U₂ ω) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ E → M₁ ω φ = M₂ ω φ := by
  have hEm : MeasurableSet E := hm₁ _ hE
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ E →
      Real.cos (((n : ℝ) + 1)⁻¹ * (M₁ ω φ - M₂ ω φ)) = 1 := by
    intro n
    set c : ℝ := ((n : ℝ) + 1)⁻¹
    have e1 := condExp_exp_eq_of_isCondZeroBoundaryGFF hm₁ hh hM₁ hc₁ (c • φ)
    have e2 := condExp_exp_eq_of_isCondZeroBoundaryGFF hm₂ hh hM₂ hc₂ (c • φ)
    have e12 : P[fun ω => Complex.exp (Complex.I * (h ω (c • φ) : ℂ)) | 𝒢₁] =ᵐ[P.restrict E]
        P[fun ω => Complex.exp (Complex.I * (h ω (c • φ) : ℂ)) | 𝒢₂] :=
      condExp_ae_eq_restrict_of_measurableSpace_eq_on hm₁ hm₂ hE htrace
    filter_upwards [e1, e2, (ae_restrict_iff' hEm).1 e12, hU] with ω h1 h2 h12 hUω hω
    have key := h1.symm.trans ((h12 hω).trans h2)
    rw [hUω hω] at key
    have hne : ((Real.exp (-(1 / 2) * zeroGFFTestCov (U₂ ω) (c • φ) (c • φ)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have key' := mul_right_cancel₀ hne key
    have hlin₁ : M₁ ω (c • φ) = c * M₁ ω φ := by rw [map_smul, smul_eq_mul]
    have hlin₂ : M₂ ω (c • φ) = c * M₂ ω φ := by rw [map_smul, smul_eq_mul]
    rw [hlin₁, hlin₂] at key'
    have hone : Complex.exp (((c * (M₁ ω φ - M₂ ω φ) : ℝ) : ℂ) * Complex.I) = 1 := by
      have e : (((c * (M₁ ω φ - M₂ ω φ) : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((c * M₁ ω φ : ℝ) : ℂ) - Complex.I * ((c * M₂ ω φ : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e, Complex.exp_sub, key', div_self (Complex.exp_ne_zero _)]
    have := Complex.exp_ofReal_mul_I_re (c * (M₁ ω φ - M₂ ω φ))
    rw [hone, Complex.one_re] at this
    exact this.symm
  filter_upwards [ae_all_iff.2 hn] with ω hω hωE
  have := eq_zero_of_forall_cos_eq_one fun n => hω n hωE
  linarith

/-- **Means of two retained kernels agree where their records and domains agree**, as whole distributions on one
probability-one event. -/
theorem ae_eq_of_isCondZeroBoundaryGFF_of_trace [IsFiniteMeasure P] (hm₁ : 𝒢₁ ≤ mΩ) (hm₂ : 𝒢₂ ≤ mΩ)
    {E : Set Ω} (hE : MeasurableSet[𝒢₁] E)
    (htrace : ∀ t, MeasurableSet[𝒢₁] (E ∩ t) ↔ MeasurableSet[𝒢₂] (E ∩ t))
    {h M₁ M₂ : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hM₁ : Measurable[𝒢₁] M₁)
    (hM₂ : Measurable[𝒢₂] M₂) {U₁ U₂ : Ω → Set ℂ}
    (hc₁ : IsCondZeroBoundaryGFF P 𝒢₁ U₁ fun ω => h ω - M₁ ω)
    (hc₂ : IsCondZeroBoundaryGFF P 𝒢₂ U₂ fun ω => h ω - M₂ ω)
    (hU : ∀ᵐ ω ∂P, ω ∈ E → U₁ ω = U₂ ω) :
    ∀ᵐ ω ∂P, ω ∈ E → M₁ ω = M₂ ω := by
  have hj := fun j : ℕ × ℕ => ae_apply_eq_of_isCondZeroBoundaryGFF_of_trace hm₁ hm₂ hE htrace hh hM₁ hM₂
    hc₁ hc₂ hU (LQGMetric.distGen upperHalfPlaneOpens j)
  filter_upwards [ae_all_iff.2 hj] with ω hω hωE
  exact LQGMetric.injective_distOn_pairings upperHalfPlaneOpens (funext fun j => hω j hωE)

/-- **Two retained kernels on nested records with a common domain have the same mean** (whole distributions):
`𝒢₁ ≤ 𝒢₂`, `M₁` measurable for `𝒢₁`. -/
theorem ae_eq_of_isCondZeroBoundaryGFF_of_le [IsProbabilityMeasure P] (h12 : 𝒢₁ ≤ 𝒢₂) (hm₂ : 𝒢₂ ≤ mΩ)
    {h M₁ M₂ : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hM₁ : Measurable[𝒢₁] M₁)
    (hM₂ : Measurable[𝒢₂] M₂) {U : Ω → Set ℂ}
    (hc₁ : IsCondZeroBoundaryGFF P 𝒢₁ U fun ω => h ω - M₁ ω)
    (hc₂ : IsCondZeroBoundaryGFF P 𝒢₂ U fun ω => h ω - M₂ ω) : M₁ =ᵐ[P] M₂ := by
  have hj := fun j : ℕ × ℕ => ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) h12 hm₂ hh hM₁ hM₂ hc₁ hc₂
    (LQGMetric.distGen upperHalfPlaneOpens j) MeasurableSet.univ
    (fun _ => Eventually.of_forall fun _ _ => rfl)
  filter_upwards [ae_all_iff.2 hj] with ω hω
  exact LQGMetric.injective_distOn_pairings upperHalfPlaneOpens (funext fun j => hω j (mem_univ ω))

/-- **A version of a local-set mean is the mean of every retained kernel at a larger record** (whole distributions),
when the retained mean is measurable for the germ σ-algebra of the set. -/
theorem ae_eq_of_isLocalSetMean_of_retained [IsProbabilityMeasure P] {A : Ω → Set ℂ}
    {h g g' : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hg : IsLocalSetMean A h P g)
    (hle : germSigma A h ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) (hg' : Measurable[germSigma A h] g')
    (hc : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) fun ω => h ω - g' ω) : g =ᵐ[P] g' :=
  ae_eq_of_isCondZeroBoundaryGFF_of_le hle h𝒢 hh hg.1 (hg'.mono hle le_rfl) hg.2.2 hc

end Mean

end InteractingSLE.Sec7.R5Enl
