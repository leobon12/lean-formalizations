/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Atomless laws and the probability integral transform

Packet PROVE-FLOWEXIST3 (AUD-3c N1, `Exist.CanonicalBrownianStatement`), deterministic measure theory.

* **`measure_singleton_eq_zero_of_norm_charFun_le`**: a finite measure on `ℝ` whose characteristic function has
  Gaussian decay `‖ν̂(s)‖ ≤ C e^{−c s²}` (`c > 0`) has no atoms. Proof (Gaussian smoothing): for `δ > 0`,
  `e^{−y²/(4δ)} = K_δ⁻¹ ∫ e^{iys} e^{−δ s²} ds` with `‖K_δ‖ = (Real.pi/δ)^{1/2}` (`fourierIntegral_gaussian`), so by Fubini
  `ν{a} ≤ ∫ e^{−(x−a)²/(4δ)} dν(x) ≤ (δ/Real.pi)^{1/2} ∫ e^{−δ s²} ‖ν̂(s)‖ ds ≤ C (δ/c)^{1/2} → 0`.
* **`measure_cdf_le_eq`** (probability integral transform): for an atomless probability measure `ν` on `ℝ` and
  `0 ≤ u ≤ 1`, `ν{y | F(y) ≤ u} = u`, `F = cdf ν`.
* **`measure_prod_cdf_condKernel`**: for a finite measure `ρ` on `α × ℝ` (`α` standard Borel) and a measurable set `A`
  of first coordinates on which the conditional kernel is atomless almost everywhere,
  `ρ{(x, y) | x ∈ A, F_x(y) ≤ u} = ρ.fst A · u`, `F_x = cdf (ρ.condKernel x)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace InteractingSLE

namespace Exist

/-! ### Gaussian decay of the characteristic function excludes atoms -/

section Atom

/-- The Gaussian Fourier identity in the form used for smoothing: for `δ > 0` and real `y`,
`∫ e^{iys} e^{−δ s²} ds = (Real.pi/δ)^{1/2} e^{−y²/(4δ)}`. -/
theorem integral_cexp_mul_gaussian {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    ∫ s : ℝ, cexp (I * y * s) * cexp (-(δ : ℂ) * s ^ 2) =
      ((Real.pi / δ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((Real.exp (-(y ^ 2 / (4 * δ))) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (δ : ℂ)) (by simpa using hδ) (y : ℂ)
  rw [h]
  congr 1
  · push_cast; ring_nf
  · rw [Complex.ofReal_exp]; congr 1; push_cast; ring

theorem norm_cpow_half {r : ℝ} (hr : 0 < r) : ‖((r : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ = r ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  norm_num

/-- **Gaussian decay of the characteristic function excludes atoms.** -/
theorem measure_singleton_eq_zero_of_norm_charFun_le {ν : Measure ℝ} [IsFiniteMeasure ν] {C c : ℝ}
    (hc : 0 < c) (h : ∀ s, ‖charFun ν s‖ ≤ C * Real.exp (-(c * s ^ 2))) (a : ℝ) : ν {a} = 0 := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (h 0)
    have he := Real.exp_pos (-(c * (0 : ℝ) ^ 2))
    exact nonneg_of_mul_nonneg_left this he
  -- the bound at scale `δ`
  have key : ∀ δ : ℝ, 0 < δ → ν.real {a} ≤ C * Real.sqrt (Real.pi / c) / (Real.pi / δ) ^ (1 / 2 : ℝ) := by
    intro δ hδ
    set K : ℂ := ((Real.pi / δ : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hK
    have hKn : ‖K‖ = (Real.pi / δ) ^ (1 / 2 : ℝ) := norm_cpow_half (by positivity)
    have hKpos : 0 < ‖K‖ := by rw [hKn]; positivity
    set g : ℝ → ℝ := fun x => Real.exp (-((x - a) ^ 2 / (4 * δ))) with hg
    have hgc : Continuous g := by fun_prop
    have hgint : Integrable g ν := by
      refine Integrable.of_bound hgc.aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ (x - a) ^ 2 / (4 * δ) := by positivity
      linarith
    -- the atom is below the smoothed mass
    have h1 : ν.real {a} ≤ ∫ x, g x ∂ν := by
      have hle : ({a} : Set ℝ).indicator (fun _ => (1 : ℝ)) ≤ g := by
        intro x
        by_cases hx : x = a
        · subst hx; simp [hg]
        · simp only [indicator_of_notMem (show x ∉ ({a} : Set ℝ) from hx)]
          exact (Real.exp_pos _).le
      calc ν.real {a} = ∫ x, ({a} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ∂ν := by
            rw [integral_indicator (measurableSet_singleton a), setIntegral_const, smul_eq_mul,
              mul_one]
        _ ≤ ∫ x, g x ∂ν := integral_mono ((integrable_const 1).indicator (measurableSet_singleton a))
            hgint hle
    -- Fubini
    set F : ℝ × ℝ → ℂ := fun p => cexp (I * (p.1 - a : ℝ) * p.2) * cexp (-(δ : ℂ) * p.2 ^ 2) with hF
    have hFm : Measurable F := by fun_prop
    have hFn : ∀ p : ℝ × ℝ, ‖F p‖ = Real.exp (-(δ * p.2 ^ 2)) := by
      intro p
      simp only [hF, norm_mul, Complex.norm_exp]
      have e1 : (I * ((p.1 - a : ℝ) : ℂ) * (p.2 : ℂ)).re = 0 := by simp
      have e2 : (-(δ : ℂ) * (p.2 : ℂ) ^ 2).re = -(δ * p.2 ^ 2) := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
      rw [e1, e2, Real.exp_zero, one_mul]
    have hgauss : Integrable (fun s : ℝ => Real.exp (-(δ * s ^ 2))) := by
      simpa [neg_mul] using integrable_exp_neg_mul_sq hδ
    have hFint : Integrable F (ν.prod volume) := by
      refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
      · refine hgauss.congr' (hFm.comp measurable_prodMk_left).aestronglyMeasurable
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (hFn (x, s)).symm
      · simp_rw [hFn]
        exact integrable_const _
    have hswap := integral_integral_swap (f := fun x s => F (x, s)) hFint
    -- inner integral in `s`: the Gaussian
    have hin1 : ∀ x : ℝ, ∫ s, F (x, s) = K * (g x : ℂ) := fun x => by
      simp only [hF]
      rw [integral_cexp_mul_gaussian hδ (x - a)]
    -- inner integral in `x`: the characteristic function
    have hin2 : ∀ s : ℝ, ∫ x, F (x, s) ∂ν =
        cexp (-(I * a * s)) * cexp (-(δ : ℂ) * s ^ 2) * charFun ν s := fun s => by
      rw [charFun_apply_real, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hF]
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast; ring
    have hlhs : ∫ x, ∫ s, F (x, s) ∂volume ∂ν = K * ((∫ x, g x ∂ν : ℝ) : ℂ) := by
      simp_rw [hin1]
      rw [integral_const_mul, integral_complex_ofReal]
    have hbound : ‖∫ s, ∫ x, F (x, s) ∂ν ∂volume‖ ≤ C * Real.sqrt (Real.pi / c) := by
      simp_rw [hin2]
      have hdom : ∀ s : ℝ, ‖cexp (-(I * a * s)) * cexp (-(δ : ℂ) * s ^ 2) * charFun ν s‖ ≤
          C * Real.exp (-(c * s ^ 2)) := by
        intro s
        rw [norm_mul, norm_mul]
        have e1 : ‖cexp (-(I * a * s))‖ = 1 := by
          rw [Complex.norm_exp]; simp
        have e2 : ‖cexp (-(δ : ℂ) * s ^ 2)‖ = Real.exp (-(δ * s ^ 2)) := by
          have := hFn (a, s)
          simp only [hF, sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
            one_mul] at this
          exact this
        rw [e1, e2, one_mul]
        have he : Real.exp (-(δ * s ^ 2)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; have : 0 ≤ δ * s ^ 2 := by positivity
          linarith
        calc Real.exp (-(δ * s ^ 2)) * ‖charFun ν s‖ ≤ 1 * ‖charFun ν s‖ :=
              mul_le_mul_of_nonneg_right he (norm_nonneg _)
          _ = ‖charFun ν s‖ := one_mul _
          _ ≤ C * Real.exp (-(c * s ^ 2)) := h s
      calc ‖∫ s : ℝ, cexp (-(I * a * s)) * cexp (-(δ : ℂ) * s ^ 2) * charFun ν s‖
          ≤ ∫ s, C * Real.exp (-(c * s ^ 2)) :=
            norm_integral_le_of_norm_le ((by simpa [neg_mul] using integrable_exp_neg_mul_sq hc :
              Integrable fun s : ℝ => Real.exp (-(c * s ^ 2))).const_mul C) (Eventually.of_forall hdom)
        _ = C * Real.sqrt (Real.pi / c) := by
            rw [integral_const_mul]
            congr 1
            have := integral_gaussian c
            simpa [neg_mul] using this
    rw [← hswap, hlhs, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hbound
    have hgnn : 0 ≤ ∫ x, g x ∂ν := integral_nonneg fun x => (Real.exp_pos _).le
    rw [abs_of_nonneg hgnn] at hbound
    rw [hKn] at hbound hKpos
    rw [le_div_iff₀ hKpos]
    calc ν.real {a} * (Real.pi / δ) ^ (1 / 2 : ℝ) ≤ (∫ x, g x ∂ν) * (Real.pi / δ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hKpos.le
      _ = (Real.pi / δ) ^ (1 / 2 : ℝ) * ∫ x, g x ∂ν := mul_comm _ _
      _ ≤ C * Real.sqrt (Real.pi / c) := hbound
  -- let `δ → 0`
  have hlim : Tendsto (fun δ : ℝ => C * Real.sqrt (Real.pi / c) / (Real.pi / δ) ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have e : ∀ δ : ℝ, 0 < δ → C * Real.sqrt (Real.pi / c) / (Real.pi / δ) ^ (1 / 2 : ℝ) =
        C * Real.sqrt (Real.pi / c) * (δ / Real.pi) ^ (1 / 2 : ℝ) := by
      intro δ hδ
      rw [div_eq_mul_inv, ← Real.inv_rpow (by positivity), inv_div]
    have ht : Tendsto (fun δ : ℝ => C * Real.sqrt (Real.pi / c) * (δ / Real.pi) ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have hc0 : Continuous fun δ : ℝ => C * Real.sqrt (Real.pi / c) * (δ / Real.pi) ^ (1 / 2 : ℝ) := by
        refine continuous_const.mul ?_
        exact (continuous_id.div_const _).rpow_const fun _ => Or.inr (by norm_num)
      have := (hc0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (e δ hδ).symm
  have hle : ν.real {a} ≤ 0 :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
  have h0 : ν.real {a} = 0 := le_antisymm hle measureReal_nonneg
  rwa [measureReal_eq_zero_iff] at h0

end Atom

/-! ### The probability integral transform -/

section Transform

/-- The distribution function of an atomless probability measure is continuous. -/
theorem continuous_cdf_of_noAtom {ν : Measure ℝ} [IsProbabilityMeasure ν] (hna : ∀ a, ν {a} = 0) :
    Continuous (cdf ν) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, (cdf ν).rightLim_eq]
  have h := (cdf ν).measure_singleton a
  rw [measure_cdf, hna a, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h
  exact le_antisymm ((cdf ν).mono.leftLim_le le_rfl) h

/-- **Probability integral transform.** For an atomless probability measure `ν` on `ℝ` with distribution function
`F` and `0 ≤ u ≤ 1`, `ν{y | F(y) ≤ u} = u`. -/
theorem measure_cdf_le_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] (hna : ∀ a, ν {a} = 0) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ν {y | cdf ν y ≤ u} = ENNReal.ofReal u := by
  have hF := continuous_cdf_of_noAtom hna
  rcases hu1.lt_or_eq with hu1 | rfl
  · set S : Set ℝ := {y | cdf ν y ≤ u} with hS
    have hSc : IsClosed S := isClosed_le hF continuous_const
    -- bounded above, since `F → 1 > u`
    obtain ⟨M, hM⟩ := (eventually_atTop.1 ((tendsto_cdf_atTop (μ := ν)).eventually (lt_mem_nhds hu1)))
    have hbdd : BddAbove S := ⟨M, fun y hy => by
      by_contra hlt
      exact absurd hy (not_le.2 (hM y (le_of_lt (not_le.1 hlt))))⟩
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · -- then `u = 0`
      have hu : u = 0 := by
        by_contra hu
        have hpos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
        obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot (μ := ν)).eventually (gt_mem_nhds hpos)).exists
        have : y ∈ S := hy.le
        rw [hSe] at this
        exact this
      rw [hSe, hu, measure_empty, ENNReal.ofReal_zero]
    · set y₀ := sSup S with hy₀
      have hy₀S : y₀ ∈ S := hSc.csSup_mem hSne hbdd
      have hSeq : S = Iic y₀ := by
        ext y
        refine ⟨fun hy => le_csSup hbdd hy, fun hy => ?_⟩
        exact ((cdf ν).mono hy).trans hy₀S
      have hFy : cdf ν y₀ = u := by
        refine le_antisymm hy₀S (not_lt.1 fun hlt => ?_)
        have hev : ∀ᶠ y in 𝓝 y₀, cdf ν y < u := (hF.tendsto y₀).eventually (gt_mem_nhds hlt)
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
        have hyS : cdf ν (y₀ + ε / 2) < u :=
          hball (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
        have hy : y₀ < y₀ + ε / 2 := by linarith
        exact absurd (le_csSup hbdd hyS.le) (not_le.2 hy)
      rw [hSeq, ← ofReal_cdf, hFy]
  · have : {y | cdf ν y ≤ 1} = univ := eq_univ_of_forall fun y => cdf_le_one ν y
    rw [this, measure_univ, ENNReal.ofReal_one]

end Transform

/-! ### The kernel form -/

section Kernel

variable {α : Type*} [MeasurableSpace α]

/-- Joint measurability of the distribution function of a Markov kernel into `ℝ`. -/
theorem measurable_cdf_kernel (κ : Kernel α ℝ) [IsMarkovKernel κ] :
    Measurable fun p : α × ℝ => cdf (κ p.1) p.2 := by
  have h : Measurable fun p : α × ℝ => κ p.1 (Iic p.2) := by
    have := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ κ)
      (t := {q : (α × ℝ) × ℝ | q.2 ≤ q.1.2}) (measurableSet_le measurable_snd measurable_fst.snd)
    exact this
  have e : (fun p : α × ℝ => cdf (κ p.1) p.2) = fun p => (κ p.1 (Iic p.2)).toReal := by
    funext p; rw [cdf_eq_real]; rfl
  rw [e]
  exact h.ennreal_toReal

/-- **The conditional probability integral transform.** If `κ x` is atomless for `μ`-almost every `x ∈ A`, then
`(μ ⊗ κ){(x, y) | x ∈ A, F_x(y) ≤ u} = μ(A) u` (`F_x = cdf (κ x)`, `0 ≤ u ≤ 1`). -/
theorem compProd_cdf_le (μ : Measure α) [SFinite μ] (κ : Kernel α ℝ) [IsMarkovKernel κ] {A : Set α}
    (hA : MeasurableSet A) (hna : ∀ᵐ x ∂μ, x ∈ A → ∀ a, κ x {a} = 0) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    (μ ⊗ₘ κ) {p | p.1 ∈ A ∧ cdf (κ p.1) p.2 ≤ u} = μ A * ENNReal.ofReal u := by
  have hm : MeasurableSet {p : α × ℝ | p.1 ∈ A ∧ cdf (κ p.1) p.2 ≤ u} :=
    (measurable_fst hA).inter (measurableSet_le (measurable_cdf_kernel κ) measurable_const)
  rw [Measure.compProd_apply hm]
  have e : ∀ x, κ x (Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ A ∧ cdf (κ p.1) p.2 ≤ u}) =
      A.indicator (fun x => κ x {y | cdf (κ x) y ≤ u}) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      congr 1
      ext y
      simp [hx]
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' {p : α × ℝ | p.1 ∈ A ∧ cdf (κ p.1) p.2 ≤ u} = ∅ := by
        ext y; simp [hx]
      rw [this, measure_empty]
  simp_rw [e]
  rw [lintegral_indicator hA, mul_comm, ← setLIntegral_const]
  refine setLIntegral_congr_fun_ae hA ?_
  filter_upwards [hna] with x hx hxA
  exact measure_cdf_le_eq (hx hxA) hu0 hu1

end Kernel

end Exist

end InteractingSLE
