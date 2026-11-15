/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Conditional characteristic functions give conditional means; martingales of stopped means

Packet PROVE-CPL-MART (the forward step "coupling specification ⇒ coupling means are local martingales",
`planning/handoffs/PROVE-LEMMA71.md` item 3: "conditional characteristic function ⇒ conditional mean,
integrability, …, localization"). This file is the abstract, process-free layer.

* `condExp_ae_eq_of_condCharFun`: if `E[e^{icX} | 𝒢] = e^{icm − c² v/2}` for every real `c`, with `X` integrable and
  `m`, `v` arbitrary (no measurability is assumed), then `E[X | 𝒢] = m` almost surely. Proof: the imaginary parts give
  `E[sin(cX) | 𝒢] = e^{−c²v/2} sin(cm)`; as `c = 1/(n+1) → 0`, `sin(cX)/c → X` in `L¹` (dominated by `|X|`), hence
  `E[sin(cX)/c | 𝒢] → E[X | 𝒢]` in `L¹` and almost surely along a subsequence, while
  `e^{−c²v/2} sin(cm)/c → m` pointwise.
* `martingale_of_ae_eq_condExp_min_const`: an adapted process `M` with `M_t = E[X | 𝓖_{ρ∧t}]` almost surely, for
  one stopping time `ρ` and one integrable `X`, is a martingale (split an event `A ∈ 𝓖_s` along `{s < ρ}`, where
  `A ∩ {s < ρ} ∈ 𝓖_{ρ∧s}`, and `{ρ ≤ s}`, where `ρ∧t = ρ = ρ∧s`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

namespace MartMeans

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ### Elementary limits -/

/-- `sin(c x)/c → x` along `c = 1/(n+1)`. -/
theorem tendsto_inv_mul_sin (x : ℝ) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))⁻¹ * Real.sin (1 / ((n : ℝ) + 1) * x)) atTop (𝓝 x) := by
  have hd : HasDerivAt (fun c : ℝ => Real.sin (c * x)) x 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const x).sin
    simpa using this
  have hs := hd.tendsto_slope_zero
  have hc : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => mem_compl_singleton_iff.2 (ne_of_gt (by positivity))⟩
  have := hs.comp hc
  refine this.congr fun n => ?_
  simp [Function.comp, smul_eq_mul]

/-- `|sin(c x)/c| ≤ |x|` for `c = 1/(n+1)`. -/
theorem abs_inv_mul_sin_le (n : ℕ) (x : ℝ) :
    |(1 / ((n : ℝ) + 1))⁻¹ * Real.sin (1 / ((n : ℝ) + 1) * x)| ≤ |x| := by
  have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hc, inv_mul_le_iff₀ hc]
  refine (Real.abs_sin_le_abs).trans ?_
  rw [abs_mul, abs_of_pos hc]

/-! ### Conditional characteristic function ⇒ conditional mean -/

/-- **The conditional mean from the conditional characteristic function.** If `X` is integrable and
`E[e^{icX} | 𝒢] = e^{icm − c² v/2}` almost surely for every real `c`, then `E[X | 𝒢] = m` almost surely. Neither `m`
nor `v` is assumed measurable. -/
theorem condExp_ae_eq_of_condCharFun [IsFiniteMeasure P] {X m v : Ω → ℝ} (hX : Integrable X P)
    (hc : ∀ c : ℝ, P[fun ω => cexp (I * ((c * X ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((c * m ω : ℝ) : ℂ) - (((1 / 2) * (c ^ 2 * v ω) : ℝ) : ℂ))) :
    P[X | 𝒢] =ᵐ[P] m := by
  -- imaginary parts
  have hsin : ∀ c : ℝ, P[fun ω => Real.sin (c * X ω) | 𝒢] =ᵐ[P]
      fun ω => Real.exp (-((1 / 2) * (c ^ 2 * v ω))) * Real.sin (c * m ω) := by
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
    filter_upwards [h1, hc c] with ω h1ω hcω
    rw [← h1ω]
    simp only [Function.comp, Complex.imCLM_apply, hcω, Complex.exp_im, Complex.sub_re,
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
    rw [Real.norm_eq_abs]; exact abs_inv_mul_sin_le n (X ω)
  have hfi : ∀ n, Integrable (f n) P := fun n =>
    Integrable.mono' hX.abs (hfm n) (Eventually.of_forall (hfb n))
  have hfcond : ∀ n, P[f n | 𝒢] =ᵐ[P]
      fun ω => (c n)⁻¹ * (Real.exp (-((1 / 2) * (c n ^ 2 * v ω))) * Real.sin (c n * m ω)) := by
    intro n
    have h := condExp_smul (μ := P) ((c n)⁻¹) (fun ω => Real.sin (c n * X ω)) 𝒢
    filter_upwards [h, hsin (c n)] with ω h1 h2
    have e : f n = (c n)⁻¹ • fun ω => Real.sin (c n * X ω) := by
      funext ω; simp [hfdef, smul_eq_mul]
    rw [e, h1, Pi.smul_apply, h2, smul_eq_mul]
  -- `L¹` convergence of the quotients and of their conditional expectations
  have hL1 : Tendsto (fun n => eLpNorm (f n - X) 1 P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_norm_of_dominated_convergence (μ := P) (F := f) (f := X)
      (bound := fun ω => |X ω|) hfm hX.abs.2 (fun n => Eventually.of_forall (hfb n))
      (Eventually.of_forall fun ω => tendsto_inv_mul_sin (X ω))
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
  filter_upwards [hae, ae_all_iff.2 hfcond] with ω h1 h2
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun n => Real.exp (-((1 / 2) * (c n ^ 2 * v ω)))) atTop (𝓝 1) := by
    have h := ((by fun_prop : Continuous fun x : ℝ => Real.exp (-((1 / 2) * (x ^ 2 * v ω)))).tendsto
      0).comp hc0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, neg_zero,
      Real.exp_zero] at h
    exact h
  have hlim : Tendsto (fun n => (c n)⁻¹ * (Real.exp (-((1 / 2) * (c n ^ 2 * v ω))) *
      Real.sin (c n * m ω))) atTop (𝓝 (m ω)) := by
    have h := he.mul (tendsto_inv_mul_sin (m ω))
    rw [one_mul] at h
    exact h.congr fun n => by ring
  exact tendsto_nhds_unique (h1.congr fun i => h2 (ns i)) (hlim.comp hns.tendsto_atTop)

/-! ### Martingales of conditional means at stopped times -/

section Stopped

variable {𝓖 : Filtration ℝ≥0 mΩ}

/-- For `A ∈ 𝓖_s`, the event `A ∩ {s < ρ}` belongs to the stopped σ-algebra of `ρ ∧ s`. -/
theorem measurableSet_inter_lt_min_const {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ) {s : ℝ≥0}
    {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    MeasurableSet[(hρ.min_const s).measurableSpace] (A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}) := by
  have hgt : MeasurableSet[𝓖 s] {ω | (s : WithTop ℝ≥0) < ρ ω} := by
    have h := (hρ s).compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  refine ((hρ.min_const s).measurableSet _).2
    ⟨le_iSup (fun u => 𝓖 u) s _ (hA.inter hgt), fun i => ?_⟩
  by_cases hsi : s ≤ i
  · have e : A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω} ∩ {ω | min (ρ ω) (s : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)}
        = A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω} :=
      inter_eq_left.2 fun ω _ => (min_le_right _ _).trans (WithTop.coe_le_coe.2 hsi)
    rw [e]
    exact 𝓖.mono hsi _ (hA.inter hgt)
  · have e : A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω} ∩ {ω | min (ρ ω) (s : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)}
        = ∅ := by
      refine eq_empty_of_forall_notMem fun ω hω => hsi ?_
      have h2 : min (ρ ω) (s : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0) := hω.2
      rw [min_eq_right hω.1.2.le] at h2
      exact WithTop.coe_le_coe.1 h2
    rw [e]
    exact @MeasurableSet.empty _ (𝓖 i)

/-- **A process of conditional means at `ρ ∧ t` is a martingale.** If `M` is adapted and, for one stopping time `ρ`
and one integrable `X`, `M_t = E[X | 𝓖_{ρ∧t}]` almost surely for every `t`, then `M` is a martingale. -/
theorem martingale_of_ae_eq_condExp_min_const [IsFiniteMeasure P] {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime 𝓖 ρ) {X : Ω → ℝ} (hX : Integrable X P) {M : ℝ≥0 → Ω → ℝ}
    (hMa : StronglyAdapted 𝓖 M) (hM : ∀ t, M t =ᵐ[P] P[X | (hρ.min_const t).measurableSpace]) :
    Martingale M 𝓖 P := by
  refine ⟨hMa, fun s t hst => ?_⟩
  have hMi : ∀ u, Integrable (M u) P := fun u => integrable_condExp.congr (hM u).symm
  have hle : ∀ u : ℝ≥0, (hρ.min_const u).measurableSpace ≤ mΩ := fun u =>
    (hρ.min_const u).measurableSpace_le_of_le fun ω => min_le_right _ _
  have hρle : ∀ u : ℝ≥0, MeasurableSet {ω | ρ ω ≤ (u : WithTop ℝ≥0)} := fun u => 𝓖.le u _ (hρ u)
  have hgtm : MeasurableSet {ω | (s : WithTop ℝ≥0) < ρ ω} := by
    have h := (hρle s).compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) (hMi t)
    (fun A _ _ => (hMi s).integrableOn) (fun A hA _ => ?_) (hMa s).aestronglyMeasurable).symm
  have hAm : MeasurableSet A := 𝓖.le s _ hA
  rw [← integral_inter_add_sdiff hgtm (hMi s).integrableOn,
    ← integral_inter_add_sdiff hgtm (hMi t).integrableOn]
  congr 1
  · -- on `{s < ρ}`: both are `∫ X` over an event of `𝓖_{ρ∧s} ⊆ 𝓖_{ρ∧t}`
    have hA1 := measurableSet_inter_lt_min_const hρ hA
    have hA1' : MeasurableSet[(hρ.min_const t).measurableSpace] (A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}) :=
      IsStoppingTime.measurableSpace_mono _ _ (fun ω => min_le_min_left _ (WithTop.coe_le_coe.2 hst))
        _ hA1
    rw [setIntegral_congr_ae (hAm.inter hgtm) (Eventually.of_forall fun ω _ => rfl)]
    calc ∫ ω in A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}, M s ω ∂P
        = ∫ ω in A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}, (P[X | (hρ.min_const s).measurableSpace]) ω ∂P :=
          setIntegral_congr_ae (hAm.inter hgtm) ((hM s).mono fun ω h _ => h)
      _ = ∫ ω in A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}, X ω ∂P := setIntegral_condExp (hle s) hX hA1
      _ = ∫ ω in A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}, (P[X | (hρ.min_const t).measurableSpace]) ω ∂P :=
          (setIntegral_condExp (hle t) hX hA1').symm
      _ = ∫ ω in A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}, M t ω ∂P :=
          setIntegral_congr_ae (hAm.inter hgtm) ((hM t).mono fun ω h _ => h.symm)
  · -- on `{ρ ≤ s}`: `ρ ∧ s = ρ = ρ ∧ t`
    have h1 := condExp_min_stopping_time_ae_eq_restrict_le_const (μ := P) (f := X) hρ s
    have h2 := condExp_min_stopping_time_ae_eq_restrict_le_const (μ := P) (f := X) hρ t
    rw [EventuallyEq, ae_restrict_iff' (hρle s)] at h1
    rw [EventuallyEq, ae_restrict_iff' (hρle t)] at h2
    refine setIntegral_congr_ae (hAm.diff hgtm) ?_
    filter_upwards [h1, h2, hM s, hM t] with ω e1 e2 e3 e4 hω
    have hρs : ρ ω ≤ (s : WithTop ℝ≥0) := by
      have := hω.2
      simp only [mem_ofPred_eq, not_lt] at this
      exact this
    rw [e3, e4, e1 hρs, e2 (hρs.trans (WithTop.coe_le_coe.2 hst))]

end Stopped

end MartMeans

end Coupling

end InteractingSLE
