/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Path
import InteractingSLE.Spec.Coupling.MartMeansCond

/-!
# Conditional-mean form of the frozen kernel: localized means, active tests, the active factor

Packet PROVE-WHOLEFIELD9 (follow-up note C.1 and C.4, `source/external/AstraIG1/ig1_followup_proofs.txt`
L1451–1704; PROVE-WHOLEFIELD8 handoff §5, "run C.4 in conditional-mean form").

For `κ ≠ 4` the explicit mean `𝔥_t(z) = u_t(f_t z) − χ arg f_t'(z)` is unbounded near the trace, so the `κ = 4` kernel
value of PROVE-WHOLEFIELD7 (a bounded frozen mean) is not available. The kernel identities are therefore written with
the **conditional mean** itself:

  `E[e^{ic(h,ψ)} | 𝓕_σ] = exp(i c E[(h,ψ) | 𝓕_σ] − ½ c² Q_{U_σ}(ψ))`   (`WangWu.gaussCF`)

with the retained Green energy `Q_{U_t}` (κ-free, `WholeField9Path`).

* `ae_condExp_eq_of_condCharFun_on`: if, on an event `E`, `E[e^{icX} | 𝒢] = e^{icm − c² v/2}` for every real `c`, then
  `E[X | 𝒢] = m` almost surely on `E` (the localized form of `MartMeans.condExp_ae_eq_of_condCharFun`);
* `integrable_pairing`: the pairings of the coupling field are integrable;
* `actMean`: the active mean pairing `∫ 𝔥_σ ψ` (canonical harmonic extension);
* **`ae_condExp_exp_smul_eq_of_active`**, **`ae_condExp_pairing_eq_actMean`**,
  **`ae_condExp_exp_eq_gaussCF_of_active`**: the frozen kernel of Theorem 1.1 for a test avoiding `K_σ`, in explicit
  form for every multiple `cψ`, its conditional mean, and the conditional-mean form;
* **`ae_condExp_exp_add_eq_of_active'`**: the active factor (C.4, "a final tower calculation adds the independent
  active kernel") for every `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets

/-! ### Conditional characteristic function on an event ⇒ conditional mean on the event -/

section CharFun

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The conditional mean from the conditional characteristic function, on an event.** If `X` is integrable and,
almost surely on `E`, `E[e^{icX} | 𝒢] = e^{icm − c² v/2}` for every real `c` (one null set per `c`), then
`E[X | 𝒢] = m` almost surely on `E`. Neither `E`, `m` nor `v` is assumed measurable. -/
theorem ae_condExp_eq_of_condCharFun_on [IsFiniteMeasure P] {X m v : Ω → ℝ} (hX : Integrable X P) {E : Set Ω}
    (hc : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ E → P[fun ω => cexp (I * ((c * X ω : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * ((c * m ω : ℝ) : ℂ) - (((1 / 2) * (c ^ 2 * v ω) : ℝ) : ℂ))) :
    ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝒢] ω = m ω := by
  -- imaginary parts
  have hsin : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ E → P[fun ω => Real.sin (c * X ω) | 𝒢] ω =
      Real.exp (-((1 / 2) * (c ^ 2 * v ω))) * Real.sin (c * m ω) := by
    intro c
    have hmeas : AEStronglyMeasurable (fun ω => cexp (I * ((c * X ω : ℝ) : ℂ))) P :=
      (by fun_prop : Continuous fun x : ℝ => cexp (I * ((c * x : ℝ) : ℂ))).comp_aestronglyMeasurable
        hX.aestronglyMeasurable
    have hint : Integrable (fun ω => cexp (I * ((c * X ω : ℝ) : ℂ))) P := by
      refine Integrable.of_bound hmeas 1 (Eventually.of_forall fun ω => ?_)
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
    have h1 := Complex.imCLM.comp_condExp_comm (m := 𝒢) hint
    have e : (Complex.imCLM : ℂ →L[ℝ] ℝ) ∘ (fun ω => cexp (I * ((c * X ω : ℝ) : ℂ))) =
        fun ω => Real.sin (c * X ω) := by
      funext ω
      simp only [Function.comp, Complex.imCLM_apply]
      rw [mul_comm, Complex.exp_ofReal_mul_I_im]
    rw [e] at h1
    filter_upwards [h1, hc c] with ω h1ω hcω hωE
    rw [← h1ω]
    simp only [Function.comp, Complex.imCLM_apply, hcω hωE, Complex.exp_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring_nf
  -- the difference quotients
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hcdef
  set f : ℕ → Ω → ℝ := fun n ω => (c n)⁻¹ * Real.sin (c n * X ω) with hfdef
  have hfm : ∀ n, AEStronglyMeasurable (f n) P := fun n =>
    (by fun_prop : Continuous fun x : ℝ => (c n)⁻¹ * Real.sin (c n * x)).comp_aestronglyMeasurable
      hX.aestronglyMeasurable
  have hfb : ∀ n ω, ‖f n ω‖ ≤ |X ω| := fun n ω => by
    rw [Real.norm_eq_abs]; exact Coupling.MartMeans.abs_inv_mul_sin_le n (X ω)
  have hfi : ∀ n, Integrable (f n) P := fun n =>
    Integrable.mono' hX.abs (hfm n) (Eventually.of_forall (hfb n))
  have hfcond : ∀ n, ∀ᵐ ω ∂P, ω ∈ E → P[f n | 𝒢] ω =
      (c n)⁻¹ * (Real.exp (-((1 / 2) * (c n ^ 2 * v ω))) * Real.sin (c n * m ω)) := by
    intro n
    have h := condExp_smul (μ := P) ((c n)⁻¹) (fun ω => Real.sin (c n * X ω)) 𝒢
    filter_upwards [h, hsin (c n)] with ω h1 h2 hωE
    have e : f n = (c n)⁻¹ • fun ω => Real.sin (c n * X ω) := by
      funext ω; simp [hfdef, smul_eq_mul]
    rw [e, h1, Pi.smul_apply, h2 hωE, smul_eq_mul]
  have hL1 : Tendsto (fun n => eLpNorm (f n - X) 1 P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_norm_of_dominated_convergence (μ := P) (F := f) (f := X)
      (bound := fun ω => |X ω|) hfm hX.abs.2 (fun n => Eventually.of_forall (hfb n))
      (Eventually.of_forall fun ω => Coupling.MartMeans.tendsto_inv_mul_sin (X ω))
    refine h.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun ω => ?_
    rw [ofReal_norm, Pi.sub_apply]
  have hL1c : Tendsto (fun n => eLpNorm (P[f n | 𝒢] - P[X | 𝒢]) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun _ => bot_le)
      fun n => ?_
    calc eLpNorm (P[f n | 𝒢] - P[X | 𝒢]) 1 P = eLpNorm (P[f n - X | 𝒢]) 1 P :=
          eLpNorm_congr_ae (condExp_sub (hfi n) hX 𝒢).symm
      _ ≤ eLpNorm (f n - X) 1 P := eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hmeas : TendstoInMeasure P (fun n => P[f n | 𝒢]) atTop (P[X | 𝒢]) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun _ => integrable_condExp.aestronglyMeasurable) integrable_condExp.aestronglyMeasurable hL1c
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.2 hfcond] with ω h1 h2 hωE
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun n => Real.exp (-((1 / 2) * (c n ^ 2 * v ω)))) atTop (𝓝 1) := by
    have h := ((by fun_prop : Continuous fun x : ℝ => Real.exp (-((1 / 2) * (x ^ 2 * v ω)))).tendsto
      0).comp hc0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, neg_zero,
      Real.exp_zero] at h
    exact h
  have hlim : Tendsto (fun n => (c n)⁻¹ * (Real.exp (-((1 / 2) * (c n ^ 2 * v ω))) *
      Real.sin (c n * m ω))) atTop (𝓝 (m ω)) := by
    have h := he.mul (Coupling.MartMeans.tendsto_inv_mul_sin (m ω))
    rw [one_mul] at h
    exact h.congr fun n => by ring
  exact tendsto_nhds_unique (h1.congr fun i => h2 (ns i) hωE) (hlim.comp hns.tendsto_atTop)

end CharFun

/-! ### The active kernel in conditional-mean form -/

section Active

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The active mean pairing `∫ 𝔥_t ψ` at the path of `ω` (with the canonical bounded harmonic extension of the time-`t`
boundary data). -/
def actMean (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ψ : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) t
    (bheAt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω)) z * ψ z

/-- The pairings of the coupling field are integrable (a zero-boundary GFF plus a bounded mean). -/
theorem integrable_pairing (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (ψ : TestOn upperHalfPlaneOpens) : Integrable (fun ω => h ω ψ) P := by
  obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hi : Integrable (fun ω => centredField h u₀ ω ψ) P :=
    (hh0.process.gaussian.hasGaussianLaw_eval ψ).memLp_two.integrable one_le_two
  have e : (fun ω => h ω ψ) = fun ω => centredField h u₀ ω ψ + ∫ z, u₀ z * ψ z := by
    funext ω; rw [centredField_apply h hu₀.1 ω ψ]; ring
  rw [e]
  exact hi.add (integrable_const _)

theorem testOn_smul_apply (c : ℝ) (ψ : TestOn upperHalfPlaneOpens) (z : ℂ) : (c • ψ) z = c * ψ z := by
  rfl

omit [IsProbabilityMeasure P] in
/-- **The frozen kernel of an active test, for every multiple** (Theorem 1.1's conditional law, in the retained Green
energy): for a driving stop `σ < ζ`, almost surely on `{supp ψ ∩ K_σ = ∅}`,
`E[e^{ic(h,ψ)} | 𝓕_σ] = exp(i c ∫ 𝔥_σ ψ − ½ c² Q_{U_σ}(ψ))`. -/
theorem ae_condExp_exp_smul_eq_of_active (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) (c : ℝ) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => cexp (I * ((c * h ω' ψ : ℝ) : ℂ)) | hσ.measurableSpace]) ω =
        cexp (I * ((c * actMean κ ρL ρR W VL VR (σ ω) ψ ω : ℝ) : ℂ) -
          (((1 / 2) * (c ^ 2 * WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ) : ℝ) : ℂ)) := by
  have hker := (hC.2.2.2.choose_spec _ hσ (hσζ.mono fun ω hω => hω)).2
    (fun ω => bheAt κ ρL ρR (W (σ ω) ω) (fun i => VL i (σ ω) ω) (fun i => VR i (σ ω) ω))
    (fun ω => bheAt_spec κ ρL ρR _ _ _) (c • ψ)
  have efun : (fun ω' => cexp (I * ((c * h ω' ψ : ℝ) : ℂ))) =
      fun ω' => cexp (I * (h ω' (c • ψ) : ℂ)) := by
    funext ω'; rw [map_smul, smul_eq_mul]
  filter_upwards [hker, hC.1.2.2.2.2, hσζ] with ω h1 hP hlt hdisj
  simp only [WithTop.untopD_coe] at h1
  have hdisj' : Disjoint (tsupport ⇑(c • ψ)) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) :=
    hdisj.mono_left (tsupport_smul_subset_right (fun _ => c) ψ)
  rw [efun]
  rw [show (P[fun ω' => cexp (I * (h ω' (c • ψ) : ℂ)) | hσ.measurableSpace]) ω =
    condExp hσ.measurableSpace P (fun ω' => cexp (I * (h ω' (c • ψ) : ℂ))) ω from rfl, h1 hdisj']
  have hm : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (σ ω)
      (bheAt κ ρL ρR (W (σ ω) ω) (fun i => VL i (σ ω) ω) (fun i => VR i (σ ω) ω)) z * (c • ψ) z) =
      c * actMean κ ρL ρR W VL VR (σ ω) ψ ω := by
    rw [actMean, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [testOn_smul_apply]
    ring
  have hq : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (σ ω) ⇑(c • ψ) =
      c ^ 2 * WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ := by
    have e : (⇑(c • ψ) : ℂ → ℝ) = c • ⇑ψ := funext fun z => testOn_smul_apply c ψ z
    rw [e, loewnerGreenEnergy_smul,
      retainedGreenEnergy_eq_loewnerGreenEnergy_of_path hP.2.2.2.1 hP.1 hlt ψ.tsupport_subset hdisj]
    rfl
  rw [hm, hq]

omit [IsProbabilityMeasure P] in
/-- **The conditional mean of an active test is the active mean pairing**: almost surely on
`{supp ψ ∩ K_σ = ∅}`, `E[(h,ψ) | 𝓕_σ] = ∫ 𝔥_σ ψ`. -/
theorem ae_condExp_pairing_eq_actMean [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => h ω' ψ | hσ.measurableSpace]) ω = actMean κ ρL ρR W VL VR (σ ω) ψ ω :=
  ae_condExp_eq_of_condCharFun_on (integrable_pairing hC ψ)
    (E := {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω))})
    (v := fun ω => WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ)
    fun c => ae_condExp_exp_smul_eq_of_active hC hX hσ hσζ ψ c

/-- **The active kernel in conditional-mean form.** -/
theorem ae_condExp_exp_eq_gaussCF_of_active (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) (c : ℝ) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => cexp (I * ((c * h ω' ψ : ℝ) : ℂ)) | hσ.measurableSpace]) ω =
        WangWu.gaussCF (c * (P[fun ω' => h ω' ψ | hσ.measurableSpace]) ω)
          (c ^ 2 * WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ) := by
  filter_upwards [ae_condExp_exp_smul_eq_of_active hC hX hσ hσζ ψ c,
    ae_condExp_pairing_eq_actMean hC hX hσ hσζ ψ] with ω h1 h2 hd
  rw [h1 hd, h2 hd, WangWu.gaussCF]

end Active

/-! ### The active factor for every `κ > 0` -/

section ActiveFactor

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The active kernel given the germ**, for every `κ > 0`: for a driving stop `σ < ζ`, a hull version `A` of `K_σ`
and a test `ψ`, almost surely on `{supp ψ ∩ A = ∅}`,
`E[e^{i(h,ψ)} | Γ(𝓕_σ, A)] = exp(i ∫ 𝔥_σ ψ − ½ Q_{U_σ}(ψ))`. -/
theorem ae_condExp_exp_histGerm_eq_gaussCF (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω : ℝ)) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (A ω) →
      (P[fun ω' => cexp (I * (h ω' ψ : ℂ)) | histGerm hσ.measurableSpace A (centredField h u₀)]) ω =
        WangWu.gaussCF (actMean κ ρL ρR W VL VR (σ ω) ψ ω)
          (WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ) := by
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hσζ
  have hAK' : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
      (((σ ω : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ) := hAK.mono fun ω hω => by rw [hω, WithTop.untopD_coe]
  obtain ⟨-, k2⟩ := ae_condExp_histGerm_hull_eq hC hκ hu₀ hX hσ hσζ' hA hAK'
    (u := fun ω => bheAt κ ρL ρR (W (σ ω) ω) (fun i => VL i (σ ω) ω) (fun i => VR i (σ ω) ω))
    (fun ω => by simp only [WithTop.untopD_coe]; exact bheAt_spec κ ρL ρR _ _ _) ψ
  set c : ℂ := cexp (I * ((∫ z, u₀ z * ψ z : ℝ) : ℂ)) with hc
  have hsplit : (fun ω' => cexp (I * (h ω' ψ : ℂ))) =
      c • fun ω' => cexp (I * (centredField h u₀ ω' ψ : ℂ)) := by
    funext ω'
    rw [Pi.smul_apply, centredField_apply h hu₀.1 ω' ψ, smul_eq_mul, hc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hce := condExp_smul (μ := P) c (fun ω' => cexp (I * (centredField h u₀ ω' ψ : ℂ)))
    (histGerm hσ.measurableSpace A (centredField h u₀))
  filter_upwards [k2, hce, hC.1.2.2.2.2, hσζ, hAK] with ω h2 h3 hP hlt hAω hdisj
  rw [hsplit, h3, Pi.smul_apply, smul_eq_mul]
  simp only [WithTop.untopD_coe] at h2
  rw [h2 hdisj]
  have hdisj' : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := hAω ▸ hdisj
  have e3 : zeroGFFTestCov (H \ A ω) ψ ψ = WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ := by
    rw [hAω, ← loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hP.2.2.2.1 hP.1 hlt ψ hdisj',
      retainedGreenEnergy_eq_loewnerGreenEnergy_of_path hP.2.2.2.1 hP.1 hlt ψ.tsupport_subset hdisj']
    rfl
  rw [e3, hc, WangWu.gaussCF, actMean, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [IsProbabilityMeasure P] in
/-- The active kernel at `c = 1` in the plain form. -/
theorem ae_condExp_exp_eq_gaussCF_actMean (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => cexp (I * (h ω' ψ : ℂ)) | hσ.measurableSpace]) ω =
        WangWu.gaussCF (actMean κ ρL ρR W VL VR (σ ω) ψ ω) (WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ) := by
  have e : (fun ω' => cexp (I * (h ω' ψ : ℂ))) = fun ω' => cexp (I * (((1 : ℝ) * h ω' ψ : ℝ) : ℂ)) := by
    funext ω'; rw [one_mul]
  filter_upwards [ae_condExp_exp_smul_eq_of_active hC hX hσ hσζ ψ 1] with ω hω hd
  rw [e, hω hd, WangWu.gaussCF, one_mul, one_pow, one_mul]

/-- **The active factor** (C.4: "A final tower calculation adds the independent active kernel"), for every `κ > 0`.
For a driving stop `σ < ζ`, an active test `ψA` and a test `ψP` inside the hull: almost surely,
`E[e^{i(h, ψA + ψP)} | 𝓕_σ] = exp(i ∫ 𝔥_σ ψA − ½ Q_{U_σ}(ψA)) · E[e^{i(h, ψP)} | 𝓕_σ]`. -/
theorem ae_condExp_exp_add_eq_of_active' (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψA ψP : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, IsActiveLabel (W · ω) (tsupport ψA) (σ ω) →
      tsupport ψP ⊆ fwdHull (Ito.rpath (W · ω)) (σ ω) →
      (P[fun ω' => cexp (I * (h ω' (ψA + ψP) : ℂ)) | hσ.measurableSpace]) ω =
        WangWu.gaussCF (actMean κ ρL ρR W VL VR (σ ω) ψA ω) (WangWu.retainedGreenEnergy (W · ω) (σ ω) ψA) *
          (P[fun ω' => cexp (I * (h ω' ψP : ℂ)) | hσ.measurableSpace]) ω := by
  have hh := hC.2.1
  obtain ⟨A, hAm, hAK, hA𝓕⟩ := exists_hullVersion hC hκ hX hσ hσζ
  obtain ⟨σ₀, hσ₀⟩ := exists_isAnnouncingSeq_driving hC.1 hκ hX (not_threshold_seed_of_ae_lt hC.1 hσζ)
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hσζ
  obtain ⟨G, hGm, hGiff⟩ := exists_measurableSet_ae_iff_disjoint hC.1 hX hσ₀ hσ hσζ'
    ψA.hasCompactSupport.isCompact ψA.tsupport_subset
  obtain ⟨F, hFm, hFsub, hFmem⟩ := exists_pocketEvent hA𝓕 ψP.tsupport_subset
  set c : ℝ := ∫ z, u₀ z * ψP z with hc
  have hY : StronglyMeasurable[histGerm hσ.measurableSpace A (centredField h u₀)]
      (F.indicator fun ω => cexp (I * (h ω ψP : ℂ))) := by
    have e : (F.indicator fun ω => cexp (I * (h ω ψP : ℂ))) =
        F.indicator fun ω => (fun x : ℝ => cexp (I * ((x + c : ℝ) : ℂ)))
          (centredField h u₀ ω ψP) := by
      congr 1; funext ω
      simp only [centredField_apply h hu₀.1 ω ψP, hc, sub_add_cancel]
    rw [e]
    exact stronglyMeasurable_indicator_histGerm hFm hFsub
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_id.add_const c))))
  have hYb : ∀ ω, ‖(F.indicator fun ω => cexp (I * (h ω ψP : ℂ))) ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ F
    · rw [indicator_of_mem hω]; exact norm_exp_I_mul_pairing ψP ω
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  set X : Ω → ℂ := fun ω => cexp (I * (h ω ψA : ℂ)) with hXdef
  set g : Ω → ℂ := WangWu.truncOne (P[X | hσ.measurableSpace]) with hgdef
  have hg : StronglyMeasurable[hσ.measurableSpace] g :=
    WangWu.stronglyMeasurable_truncOne stronglyMeasurable_condExp
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := WangWu.norm_truncOne_le _
  have hXb' : ∀ᵐ ω ∂P, ‖(P[X | hσ.measurableSpace]) ω‖ ≤ 1 :=
    ae_bdd_norm_condExp_of_ae_bdd_norm (Eventually.of_forall fun ω => norm_exp_I_mul_pairing ψA ω)
  have hgerm := ae_condExp_exp_histGerm_eq_gaussCF hC hκ hu₀ hX hσ hσζ hAm hAK ψA
  have hact := ae_condExp_exp_eq_gaussCF_actMean hC hX hσ hσζ ψA
  have hXg : ∀ᵐ ω ∂P, ω ∈ F ∩ G →
      (P[X | histGerm hσ.measurableSpace A (centredField h u₀)]) ω = g ω := by
    filter_upwards [hgerm, hact, hXb', hGiff, hAK] with ω h1 h2 h3 h4 h5 hω
    simp only [WithTop.untopD_coe] at h4
    have hd : Disjoint (tsupport ψA) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := h4.1 hω.2
    have hdA : Disjoint (tsupport ψA) (A ω) := by rw [h5]; exact hd
    rw [h1 hdA, hgdef, WangWu.truncOne, ite_eq_left h3, h2 hd]
  have hmul := ae_condExp_mul_eq_on (P := P) (le_histGerm A (centredField h u₀))
    (histGerm_le hσ.measurableSpace_le hAm (measurable_centredField hh u₀)) (hFm.inter hGm) hY hYb
    (aestronglyMeasurable_exp_pairing hh ψA) (fun ω => norm_exp_I_mul_pairing ψA ω) hg hgb hXg
  have hZi : ∀ ψ : TestOn upperHalfPlaneOpens, Integrable (fun ω => cexp (I * (h ω ψ : ℂ))) P :=
    fun ψ => Integrable.of_bound (aestronglyMeasurable_exp_pairing hh ψ) 1
      (Eventually.of_forall fun ω => norm_exp_I_mul_pairing ψ ω)
  have hind1 := condExp_indicator (μ := P) (hZi (ψA + ψP)) hFm
  have hind2 := condExp_indicator (μ := P) (hZi ψP) hFm
  have hYX : (F.indicator fun ω => cexp (I * (h ω ψP : ℂ))) * X =
      F.indicator fun ω => cexp (I * (h ω (ψA + ψP) : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ F
    · simp only [Pi.mul_apply, indicator_of_mem hω, hXdef, map_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    · simp only [Pi.mul_apply, indicator_of_notMem hω, zero_mul]
  filter_upwards [hmul, hind1, hind2, hXg, hact, hXb', hGiff, hAK] with ω hm1 hi1 hi2 hxg ha hb hgi hak hA hPK
  simp only [WithTop.untopD_coe] at hgi
  have hd : Disjoint (tsupport ψA) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) := hA
  have hωG : ω ∈ G := hgi.2 hd
  have hωF : ω ∈ F := hFmem ω (by rw [hak]; exact hPK)
  rw [hYX] at hm1
  have e1 := hm1 ⟨hωF, hωG⟩
  rw [hi1, indicator_of_mem hωF, hi2, indicator_of_mem hωF] at e1
  rw [e1, hgdef, WangWu.truncOne, ite_eq_left hb, ha hd]

end ActiveFactor

end WholeField

end InteractingSLE
