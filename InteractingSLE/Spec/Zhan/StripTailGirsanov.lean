/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailAdapt
import InteractingSLE.Spec.Sec7.ContinuityProb5Girsanov
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# Whole-tail Girsanov for the strip driver

Packet PROVE-ZHAN-A4. Astra, *Formalization proofs* L1559–L1566: "Start at deterministic integers `n`, and stop either
when a relevant gap falls below `1` or when `∫ₙᵗ e_s²/κ ds` reaches an integer `M`. Bounded-energy adapted Girsanov
gives equivalent measures on the entire stopped future … After a cutoff, extend the reference driver with a fresh
Brownian motion of constant drift `σ`. On each no-cutoff event the complete original tail is a constant-drift
reference tail under an equivalent measure."

Here the cutoffs are continuous, so no stopping time is needed: with a continuous adapted error `e`,

  `θ_t = ramp_n(t) · clamp(e_t) · ψ_M(A_t) / √κ`,   `A_t = ∫₀ᵗ (ramp_n · clamp(e))²`,

where `ramp_n` rises from `0` at `n` to `1` at `n + 1`, `clamp` cuts at `±1` and `ψ_M` falls from `1` at `M` to `0`
at `M + 1`. Then `θ` is bounded, continuous, adapted and has energy `∫₀^∞ θ² ≤ (M + 1)/κ` (through
`Φ(a) = ∫₀ᵃ ψ_M ≤ M + 1` and `d/dt Φ(A_t) = ψ_M(A_t) A'_t`), so PROVE-SEC7-C5's whole-tail Girsanov theorem
(`Girsanov.isFilteredBrownianReal_girsanovTail`) applies, and the restart at the constant time `n + 1`
(`Sec2.Restart.isFilteredBrownianReal_restart_cond`) gives a Brownian motion `β` under an equivalent measure. On the
no-cutoff event (`|e| ≤ 1` and `∫ₙᵘ e² ≤ M` after `n`), `√κ β_t = √κ (B_{n+1+t} − B_{n+1}) + ∫_{n+1}^{n+1+t} e`.

## Main results

* `Tail.thetaCut` and its properties (`abs_thetaCut_le`, `isStronglyProgressive_thetaCut`,
  `isRiemannRegular_thetaCut`, `quadInt_thetaCut_le`);
* **`Tail.exists_tail_reference`**: the equivalent measure and the reference Brownian motion of the tail.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Tail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The time ramp: `0` up to `n`, `1` from `n + 1` on. -/
def ramp (n : ℕ) (t : ℝ≥0) : ℝ := min (max ((t : ℝ) - n) 0) 1

/-- The clamp at `±1`. -/
def clamp1 (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- The energy cutoff: `1` up to `M`, `0` from `M + 1` on. -/
def psi (M : ℕ) (a : ℝ) : ℝ := min (max ((M : ℝ) + 1 - a) 0) 1

/-- The cut integrand `ramp_n(t) clamp(e_t)`. -/
def gCut (n : ℕ) (e : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := ramp n t * clamp1 (e t ω)

/-- Its running energy `A_t = ∫₀ᵗ gCut²`. -/
def aCut (n : ℕ) (e : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..(t : ℝ), gCut n e u.toNNReal ω ^ 2

/-- **The cut drift** `θ = gCut · ψ_M(A) / √κ`. -/
def thetaCut (κ : ℝ) (n M : ℕ) (e : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gCut n e t ω * psi M (aCut n e t ω) / Real.sqrt κ

theorem continuous_ramp (n : ℕ) : Continuous (ramp n) := by unfold ramp; fun_prop

theorem continuous_clamp1 : Continuous clamp1 := by unfold clamp1; fun_prop

theorem continuous_psi (M : ℕ) : Continuous (psi M) := by unfold psi; fun_prop

theorem ramp_nonneg (n : ℕ) (t : ℝ≥0) : 0 ≤ ramp n t := le_min (le_max_right _ _) zero_le_one

theorem ramp_le_one (n : ℕ) (t : ℝ≥0) : ramp n t ≤ 1 := min_le_right _ _

theorem abs_clamp1_le (x : ℝ) : |clamp1 x| ≤ 1 := by
  unfold clamp1; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem psi_nonneg (M : ℕ) (a : ℝ) : 0 ≤ psi M a := le_min (le_max_right _ _) zero_le_one

theorem psi_le_one (M : ℕ) (a : ℝ) : psi M a ≤ 1 := min_le_right _ _

theorem abs_gCut_le (n : ℕ) (e : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : |gCut n e t ω| ≤ 1 := by
  unfold gCut
  rw [abs_mul, abs_of_nonneg (ramp_nonneg n t)]
  exact (mul_le_mul (ramp_le_one n t) (abs_clamp1_le _) (abs_nonneg _) zero_le_one).trans (by norm_num)

variable {e : ℝ≥0 → Ω → ℝ}

theorem continuous_gCut (hec : ∀ ω, Continuous (e · ω)) (n : ℕ) (ω : Ω) :
    Continuous fun t => gCut n e t ω :=
  (continuous_ramp n).mul (continuous_clamp1.comp (hec ω))

theorem continuous_gCut_sq_real (hec : ∀ ω, Continuous (e · ω)) (n : ℕ) (ω : Ω) :
    Continuous fun u : ℝ => gCut n e u.toNNReal ω ^ 2 :=
  ((continuous_gCut hec n ω).comp continuous_real_toNNReal).pow 2

theorem continuous_aCut (hec : ∀ ω, Continuous (e · ω)) (n : ℕ) (ω : Ω) :
    Continuous fun t => aCut n e t ω :=
  (intervalIntegral.continuous_primitive (fun _ _ => (continuous_gCut_sq_real hec n ω).intervalIntegrable _ _)
    0).comp NNReal.continuous_coe

theorem continuous_thetaCut (hec : ∀ ω, Continuous (e · ω)) (κ : ℝ) (n M : ℕ) (ω : Ω) :
    Continuous fun t => thetaCut κ n M e t ω :=
  (((continuous_gCut hec n ω).mul ((continuous_psi M).comp (continuous_aCut hec n ω)))).div_const _

theorem abs_thetaCut_le (κ : ℝ) (n M : ℕ) (t : ℝ≥0) (ω : Ω) :
    |thetaCut κ n M e t ω| ≤ 1 / Real.sqrt κ := by
  unfold thetaCut
  rw [abs_div, abs_mul, abs_of_nonneg (psi_nonneg M _), abs_of_nonneg (Real.sqrt_nonneg κ)]
  gcongr
  exact (mul_le_mul (abs_gCut_le n e t ω) (psi_le_one M _) (psi_nonneg M _) zero_le_one).trans
    (by norm_num)

variable {𝓗 : Filtration ℝ≥0 mΩ}

theorem stronglyAdapted_gCut (he : ∀ t, Measurable[𝓗 t] (e t)) (n : ℕ) : StronglyAdapted 𝓗 (gCut n e) :=
  fun t => (measurable_const.mul (continuous_clamp1.measurable.comp (he t))).stronglyMeasurable

theorem isStronglyProgressive_gCut (he : ∀ t, Measurable[𝓗 t] (e t)) (hec : ∀ ω, Continuous (e · ω))
    (n : ℕ) : IsStronglyProgressive 𝓗 (gCut n e) :=
  (stronglyAdapted_gCut he n).isStronglyProgressive_of_continuous (continuous_gCut hec n)

theorem stronglyAdapted_thetaCut (he : ∀ t, Measurable[𝓗 t] (e t)) (hec : ∀ ω, Continuous (e · ω))
    (κ : ℝ) (n M : ℕ) : StronglyAdapted 𝓗 (thetaCut κ n M e) := fun t => by
  have hA : Measurable[𝓗 t] fun ω => aCut n e t ω :=
    (Girsanov.stronglyMeasurable_integral_comp (isStronglyProgressive_gCut he hec n)
      (g := fun x => x ^ 2) (by fun_prop) t).measurable
  exact ((((stronglyAdapted_gCut he n t).measurable).mul ((continuous_psi M).measurable.comp hA)).div_const
    _).stronglyMeasurable

theorem isStronglyProgressive_thetaCut (he : ∀ t, Measurable[𝓗 t] (e t)) (hec : ∀ ω, Continuous (e · ω))
    (κ : ℝ) (n M : ℕ) : IsStronglyProgressive 𝓗 (thetaCut κ n M e) :=
  (stronglyAdapted_thetaCut he hec κ n M).isStronglyProgressive_of_continuous (continuous_thetaCut hec κ n M)

theorem isRiemannRegular_thetaCut (P : Measure Ω) (hec : ∀ ω, Continuous (e · ω)) (κ : ℝ) (n M : ℕ) :
    Girsanov.IsRiemannRegular P (thetaCut κ n M e) :=
  ae_of_all _ fun ω => ae_of_all _ fun _ => (continuous_thetaCut hec κ n M ω).continuousWithinAt

/-- `Φ(a) = ∫₀ᵃ ψ_M ≤ M + 1` for `a ≥ 0`. -/
theorem integral_psi_le (M : ℕ) {a : ℝ} (ha : 0 ≤ a) : ∫ x in (0 : ℝ)..a, psi M x ≤ M + 1 := by
  have hle : ∀ b, 0 ≤ b → ∫ x in (0 : ℝ)..b, psi M x ≤ b := fun b hb => by
    have h := intervalIntegral.integral_mono_on (μ := volume) hb ((continuous_psi M).intervalIntegrable _ _)
      (intervalIntegrable_const (c := (1 : ℝ))) fun x _ => psi_le_one M x
    simpa using h
  rcases le_or_gt a (M + 1) with h1 | h1
  · exact (hle a ha).trans h1
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := (M : ℝ) + 1)
      (c := a) ((continuous_psi M).intervalIntegrable _ _) ((continuous_psi M).intervalIntegrable _ _)
    have hzero : ∫ x in ((M : ℝ) + 1)..a, psi M x = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => ?_)]
      · simp
      · rw [uIcc_of_le h1.le] at hx
        have : (M : ℝ) + 1 - x ≤ 0 := by linarith [hx.1]
        simp only [psi, max_eq_right this, min_eq_left zero_le_one]
    have := hle ((M : ℝ) + 1) (by positivity)
    linarith

/-- **The energy of the cut drift is at most `(M + 1)/κ`.** -/
theorem quadInt_thetaCut_le {κ : ℝ} (hκ : 0 < κ) (hec : ∀ ω, Continuous (e · ω)) (n M : ℕ) (t : ℝ≥0)
    (ω : Ω) : Girsanov.quadInt (thetaCut κ n M e) t ω ≤ (M + 1) / κ := by
  set f : ℝ → ℝ := fun u => gCut n e u.toNNReal ω ^ 2 with hf
  have hfc : Continuous f := continuous_gCut_sq_real hec n ω
  set A : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u, f x with hA
  set Φ : ℝ → ℝ := fun a => ∫ x in (0 : ℝ)..a, psi M x with hΦ
  have hAd : ∀ u, HasDerivAt A (f u) u := fun u => (hfc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun u => (hAd u).continuousAt
  have hΦd : ∀ a, HasDerivAt Φ (psi M a) a := fun a =>
    ((continuous_psi M).integral_hasStrictDerivAt 0 a).hasDerivAt
  have hcomp : ∀ u, HasDerivAt (fun u => Φ (A u)) (psi M (A u) * f u) u := fun u =>
    (hΦd (A u)).comp u (hAd u)
  have hint : ∫ u in (0 : ℝ)..t, psi M (A u) * f u = Φ (A t) - Φ (A 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hcomp u)
      ((((continuous_psi M).comp hAc).mul hfc).intervalIntegrable _ _)
  have hA0 : A 0 = 0 := intervalIntegral.integral_same
  have hΦ0 : Φ 0 = 0 := intervalIntegral.integral_same
  have hAt : 0 ≤ A t := intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun u _ => sq_nonneg _
  have hpt : ∀ u ∈ Icc (0 : ℝ) t, thetaCut κ n M e u.toNNReal ω ^ 2 ≤ psi M (A u) * f u / κ := by
    intro u hu
    have haC : aCut n e u.toNNReal ω = A u := by
      simp only [aCut, hA, Real.coe_toNNReal _ hu.1]
      rfl
    have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
    have hψ := psi_nonneg M (A u)
    have hψ1 := psi_le_one M (A u)
    simp only [thetaCut, haC, hf, div_pow, mul_pow, hsq]
    rw [div_le_div_iff_of_pos_right hκ]
    have : psi M (A u) ^ 2 ≤ psi M (A u) := by nlinarith
    nlinarith [sq_nonneg (gCut n e u.toNNReal ω)]
  unfold Girsanov.quadInt
  calc ∫ u in (0 : ℝ)..t, thetaCut κ n M e u.toNNReal ω ^ 2
      ≤ ∫ u in (0 : ℝ)..t, psi M (A u) * f u / κ :=
        intervalIntegral.integral_mono_on (NNReal.coe_nonneg t)
          ((((continuous_thetaCut hec κ n M ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _)
          (((((continuous_psi M).comp hAc).mul hfc).div_const κ).intervalIntegrable _ _) hpt
    _ = (Φ (A t) - Φ (A 0)) / κ := by rw [intervalIntegral.integral_div, hint]
    _ ≤ (M + 1) / κ := by
        rw [hA0, hΦ0, sub_zero]
        exact div_le_div_of_nonneg_right (integral_psi_le M hAt) hκ.le

/-- On the no-cutoff event, after `n + 1` the cut drift is `e/√κ`. -/
theorem thetaCut_eq_of_noCut {κ : ℝ} {n M : ℕ} {ω : Ω} (hec : ∀ ω, Continuous (e · ω))
    (hb : ∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1)
    (hen : ∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M)
    {u : ℝ} (hu : (n : ℝ) + 1 ≤ u) : thetaCut κ n M e u.toNNReal ω = e u.toNNReal ω / Real.sqrt κ := by
  have hu0 : 0 ≤ u := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcu : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal _ hu0
  have hnu : (n : ℝ≥0) ≤ u.toNNReal := by
    rw [← NNReal.coe_le_coe, hcu]; push_cast; linarith
  -- the ramp is `1`, the clamp is inactive
  have hramp1 : ∀ v : ℝ, (n : ℝ) + 1 ≤ v → ramp n v.toNNReal = 1 := fun v hv => by
    have hv0 : 0 ≤ v := by linarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [ramp, Real.coe_toNNReal _ hv0]
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  have hramp0 : ∀ v : ℝ, v ≤ n → ramp n v.toNNReal = 0 := fun v hv => by
    simp only [ramp]
    rw [max_eq_right (by
      rcases le_total v 0 with h | h
      · rw [Real.toNNReal_of_nonpos h]; simp
      · rw [Real.coe_toNNReal _ h]; linarith)]
    simp
  have hclamp : ∀ x : ℝ, |x| ≤ 1 → clamp1 x = x := fun x hx => by
    rw [abs_le] at hx
    simp only [clamp1, min_eq_right hx.2, max_eq_right hx.1]
  -- the running energy stays below `M`
  have haC : aCut n e u.toNNReal ω ≤ M := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := (n : ℝ))
      (c := u) ((continuous_gCut_sq_real hec n ω).intervalIntegrable _ _)
      ((continuous_gCut_sq_real hec n ω).intervalIntegrable _ _)
    have h0 : ∫ r in (0 : ℝ)..(n : ℝ), gCut n e r.toNNReal ω ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun r hr => ?_)]
      · simp
      · rw [uIcc_of_le (Nat.cast_nonneg n)] at hr
        simp only [gCut, hramp0 r hr.2, zero_mul]; ring
    have h1 : ∫ r in (n : ℝ)..u, gCut n e r.toNNReal ω ^ 2 ≤ ∫ r in (n : ℝ)..u, e r.toNNReal ω ^ 2 := by
      refine intervalIntegral.integral_mono_on (by linarith)
        ((continuous_gCut_sq_real hec n ω).intervalIntegrable _ _)
        ((((hec ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _) fun r hr => ?_
      have hr0 : 0 ≤ r := (Nat.cast_nonneg n).trans hr.1
      have hnr : (n : ℝ≥0) ≤ r.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; push_cast; exact hr.1
      simp only [gCut, hclamp _ (hb _ hnr), mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (ramp_nonneg _ _) (ramp_le_one _ _))
    have h2 := hen u.toNNReal hnu
    rw [hcu] at h2
    simp only [aCut, hcu]
    linarith
  have hpsi : psi M (aCut n e u.toNNReal ω) = 1 := by
    simp only [psi]
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  simp only [thetaCut, gCut, hramp1 u hu, one_mul, hclamp _ (hb _ hnu), hpsi, mul_one]

/-- **The reference Brownian motion of the tail** (whole-tail Girsanov, Astra L1559–L1566). For a Brownian
motion `B` of `𝓗` (every path continuous) and a continuous `𝓗`-adapted process `e`, and integers `n`, `M`, there
are a probability `Q` equivalent to `P` and a `Q`-Brownian motion `β` of some filtration such that, on the no-cutoff
event (`|e| ≤ 1` and `∫ₙᵘ e² ≤ M` after `n`), `√κ β_t = √κ (B_{n+1+t} − B_{n+1}) + ∫_{n+1}^{n+1+t} e`. -/
theorem exists_tail_reference {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓗 B P) (hBc : ∀ ω, Continuous (B · ω))
    (he : ∀ t, Measurable[𝓗 t] (e t)) (hec : ∀ ω, Continuous (e · ω)) (n M : ℕ) :
    ∃ (Q : Measure Ω) (𝓗' : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ), MathFin.IsEquivProbMeasure P Q ∧
      IsFilteredBrownianReal 𝓗' β Q ∧
      ∀ ω, (∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1) →
        (∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M) →
        ∀ t : ℝ≥0, Real.sqrt κ * β t ω =
          Real.sqrt κ * (B ((n : ℝ≥0) + 1 + t) ω - B ((n : ℝ≥0) + 1) ω) +
            ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω := by
  set θ := thetaCut κ n M e with hθdef
  have hθp := isStronglyProgressive_thetaCut he hec κ n M
  have hθb : ∀ t ω, |θ t ω| ≤ 1 / Real.sqrt κ := abs_thetaCut_le κ n M
  have hθr := isRiemannRegular_thetaCut P hec κ n M
  have hK : ∀ᵐ ω ∂P, ∀ t, Girsanov.quadInt θ t ω ≤ (M + 1) / κ :=
    ae_of_all _ fun ω t => quadInt_thetaCut_le hκ hec n M t ω
  obtain ⟨hQ, hβ⟩ := Girsanov.isFilteredBrownianReal_girsanovTail hB hθp hθb hθr hK
  have hβc : ∀ ω, Continuous (Girsanov.girsanovProcess B θ · ω) := fun ω =>
    (hBc ω).add (Girsanov.continuous_drift hθp hθb ω)
  have hT : IsStoppingTime 𝓗 fun _ : Ω => (((n : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_const 𝓗 _
  have := hQ.isProb
  have hR := Sec2.Restart.isFilteredBrownianReal_restart_cond hβ hβc hT (A := univ) MeasurableSet.univ
    (by simp)
  rw [ProbabilityTheory.cond_univ] at hR
  refine ⟨_, _, _, hQ, hR, fun ω hb hen t => ?_⟩
  simp only [QuantumZipper.StrongMarkov.smShift, Girsanov.girsanovProcess, Girsanov.drift]
  have hθc : Continuous fun u : ℝ => θ u.toNNReal ω :=
    (continuous_thetaCut hec κ n M ω).comp continuous_real_toNNReal
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume) (hθc.intervalIntegrable 0
    (((n : ℝ≥0) + 1 + t : ℝ≥0) : ℝ)) (hθc.intervalIntegrable 0 (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ))
  have hcongr : Real.sqrt κ * ∫ u in (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ)..(((n : ℝ≥0) + 1 + t : ℝ≥0) : ℝ),
      θ u.toNNReal ω = ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω := by
    rw [← intervalIntegral.integral_const_mul]
    push_cast
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (by linarith [NNReal.coe_nonneg t])] at hr
    simp only [hθdef]
    rw [thetaCut_eq_of_noCut hec hb hen hr.1]
    field_simp [(Real.sqrt_pos.2 hκ).ne']
  rw [← hcongr, ← hsub]
  ring

end Tail

end Zhan

end InteractingSLE
