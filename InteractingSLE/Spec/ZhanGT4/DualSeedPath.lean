/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldMart
import InteractingSLE.Spec.ZhanGT4.D9Const

/-!
# Zhan's A.1.6, the seeded field X: the per-path inputs from the integrated equations

Packet PROVE-ZHAN-GT4-A21. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L507, R38): "For a mark `p_m = x_j^±`, interpret `g_j(p_m)` as its integrated force
coordinate `V_j^m` … The seed inequalities in the coupling statement imply `V_j^m ≠ W_j` at every positive time before
lifetime"; "differentiating (D13)–(D15) by Itô and the force ODE".

The seeded force-point evolution supplies its coordinates only in **integrated** form (Definition 2.1:
`V_t = x + ∫₀ᵗ 2/(V − W)`, `W_t = √κ B_t + Σ ∫₀ᵗ ρ/(W − V)`), with integrable but possibly singular integrands at
time `0`. A20's seeded field asks for the force ODE, the rate of the other source's derivative factor and the rate of
the drift **after a positive time `ε`**, where the gaps are positive. Here:

* `hasDerivWithinAt_of_eq_integral`, `hasDerivWithinAt_of_eq_sum_integral`: the fundamental theorem of calculus on
  `[ε, T]` for an integral from `0` whose integrand is integrable on `[0, ε]` and continuous on `[ε, T]`;
* `hasDerivWithinAt_mark_of_integral`: **the force ODE** `V' = 2/(V − W)` on `[ε, T]` (inputs `hV`, `hV₀` of
  `isDriftLogField_seed`);
* `derivFactor`, `hasDerivWithinAt_derivFactor`: **`G⁰_t = g_t'(x_k) = exp(−∫₀ᵗ 2/(V⁰ − W)²)`** and its rate
  `−2G⁰/(V⁰ − W)²` (input `hG₀`);
* `SeedData.drift_eq`, `hasDerivWithinAt_drift_of_integral`: the force-point drift `−(κ/2)/(W − V⁰) + Σ κ r_m/(W −
  V^m)` is the rate of the integrated drift (input `hD`);
* `exists_seedScaleOK`: every family of constants admits a seeded scale `L` (`SeedScaleOK`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

/-! ### The fundamental theorem of calculus after a positive time -/

/-- FTC within `[b, c]`, integrating from `b` (real-valued). -/
theorem hasDerivWithinAt_integral_base_real {f : ℝ → ℝ} {b c t : ℝ} (hf : ContinuousOn f (Icc b c))
    (ht : t ∈ Icc b c) : HasDerivWithinAt (fun s => ∫ r in b..s, f r) (f t) (Icc b c) t := by
  have : Fact (t ∈ Icc b c) := ⟨ht⟩
  have hint : IntervalIntegrable f volume b t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hf.mono (Icc_subset_Icc_right ht.2)
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- **FTC after a positive time.** If `v u = x₀ + ∫₀ᵘ f` on `[ε, T]`, `f` is interval integrable on `[0, ε]` and
continuous on `[ε, T]`, then `v' = f` within `[ε, T]`. -/
theorem hasDerivWithinAt_of_eq_integral {f v : ℝ → ℝ} {x₀ ε T t : ℝ} (hint : IntervalIntegrable f volume 0 ε)
    (hf : ContinuousOn f (Icc ε T)) (hv : ∀ u ∈ Icc ε T, v u = x₀ + ∫ s in (0 : ℝ)..u, f s) (ht : t ∈ Icc ε T) :
    HasDerivWithinAt v (f t) (Icc ε T) t := by
  have heq : ∀ u ∈ Icc ε T, v u = (x₀ + ∫ s in (0 : ℝ)..ε, f s) + ∫ s in ε..u, f s := fun u hu => by
    have hint' : IntervalIntegrable f volume ε u := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hu.1]
      exact hf.mono (Icc_subset_Icc_right hu.2)
    rw [hv u hu, add_assoc, intervalIntegral.integral_add_adjacent_intervals hint hint']
  exact ((hasDerivWithinAt_integral_base_real hf ht).const_add _).congr heq (heq t ht)

/-- **FTC after a positive time, for a finite sum of integrals.** -/
theorem hasDerivWithinAt_of_eq_sum_integral {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {v : ℝ → ℝ}
    {x₀ ε T t : ℝ} (hint : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 ε)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Icc ε T))
    (hv : ∀ u ∈ Icc ε T, v u = x₀ + ∑ i ∈ s, ∫ r in (0 : ℝ)..u, f i r) (ht : t ∈ Icc ε T) :
    HasDerivWithinAt v (∑ i ∈ s, f i t) (Icc ε T) t := by
  have hsum : HasDerivWithinAt (fun u => ∑ i ∈ s, ∫ r in (0 : ℝ)..u, f i r) (∑ i ∈ s, f i t) (Icc ε T) t := by
    have := HasDerivWithinAt.fun_sum (u := s) (A := fun i u => ∫ r in (0 : ℝ)..u, f i r)
      (A' := fun i => f i t) (x := t) (s := Icc ε T) fun i hi =>
        hasDerivWithinAt_of_eq_integral (x₀ := 0) (hint i hi) (hf i hi) (fun u _ => (zero_add _).symm) ht
    exact this
  exact (hsum.const_add x₀).congr (fun u hu => hv u hu) (hv t ht)

/-! ### The force ODE and the derivative factor of the other source -/

/-- **The force ODE after a positive time**: a mark in integrated form `V u = x + ∫₀ᵘ 2/(V − W)`, with the
integrand integrable on `[0, ε]`, `V`, `W` continuous and `V ≠ W` on `[ε, T]`, satisfies `V' = 2/(V − W)` within
`[ε, T]`. -/
theorem hasDerivWithinAt_mark_of_integral {W V : ℝ → ℝ} {x ε T t : ℝ}
    (hint : IntervalIntegrable (fun s => 2 / (V s - W s)) volume 0 ε) (hWc : ContinuousOn W (Icc ε T))
    (hVc : ContinuousOn V (Icc ε T)) (hne : ∀ u ∈ Icc ε T, V u - W u ≠ 0)
    (hV : ∀ u ∈ Icc ε T, V u = x + ∫ s in (0 : ℝ)..u, 2 / (V s - W s)) (ht : t ∈ Icc ε T) :
    HasDerivWithinAt V (2 / (V t - W t)) (Icc ε T) t :=
  hasDerivWithinAt_of_eq_integral (f := fun s => 2 / (V s - W s)) hint
    (continuousOn_const.div (hVc.sub hWc) hne) hV ht

/-- **The derivative factor `G⁰_t = g_t'(x_k) = exp(−∫₀ᵗ 2/(V⁰ − W)²)`** of the other source. -/
def derivFactor (W V₀ : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (-∫ s in (0 : ℝ)..t, 2 / (V₀ s - W s) ^ 2)

theorem derivFactor_pos (W V₀ : ℝ → ℝ) (t : ℝ) : 0 < derivFactor W V₀ t := Real.exp_pos _

theorem derivFactor_zero (W V₀ : ℝ → ℝ) : derivFactor W V₀ 0 = 1 := by
  simp [derivFactor]

/-- **The rate of the derivative factor**: `∂_t G⁰ = −2G⁰/(V⁰ − W)²` within `[ε, T]`, when `V⁰ ≠ W` on `[0, T]` and
both are continuous there. -/
theorem hasDerivWithinAt_derivFactor {W V₀ : ℝ → ℝ} {ε T t : ℝ} (hε : 0 ≤ ε) (hWc : ContinuousOn W (Icc 0 T))
    (hVc : ContinuousOn V₀ (Icc 0 T)) (hne : ∀ u ∈ Icc (0 : ℝ) T, V₀ u - W u ≠ 0) (ht : t ∈ Icc ε T) :
    HasDerivWithinAt (derivFactor W V₀) (-2 * derivFactor W V₀ t / (V₀ t - W t) ^ 2) (Icc ε T) t := by
  have hcont : ContinuousOn (fun s => 2 / (V₀ s - W s) ^ 2) (Icc 0 T) :=
    continuousOn_const.div ((hVc.sub hWc).pow 2) fun u hu => pow_ne_zero 2 (hne u hu)
  have ht0 : t ∈ Icc 0 T := ⟨hε.trans ht.1, ht.2⟩
  have hI : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, 2 / (V₀ s - W s) ^ 2) (2 / (V₀ t - W t) ^ 2)
      (Icc 0 T) t := hasDerivWithinAt_integral_base_real hcont ht0
  have hE := (hI.neg.exp).mono (Icc_subset_Icc_left hε)
  have e : Real.exp (-∫ s in (0 : ℝ)..t, 2 / (V₀ s - W s) ^ 2) * -(2 / (V₀ t - W t) ^ 2) =
      -2 * derivFactor W V₀ t / (V₀ t - W t) ^ 2 := by
    unfold derivFactor; ring
  rw [← e]
  exact hE

/-! ### The drift -/

/-- The force-point drift of the seeded data in explicit form. -/
theorem SeedData.drift_eq {n : ℕ} (d : SeedData n) (t : ℝ) :
    d.drift t = -(d.κ / 2) / (d.W t - d.V₀ t) + ∑ m, d.κ * d.r m / (d.W t - d.V m t) :=
  kappa_mul_dualLogSpaceX_id d.r (d.W t) (d.V₀ t) (d.Vv t)

/-- **The rate of the integrated drift is the force-point drift** after a positive time: if the drift path is
`D u = ∫₀ᵘ (−(κ/2)/(W − V⁰)) + Σ_m ∫₀ᵘ κ r_m/(W − V^m)` on `[ε, T]` (the force terms of the integrated driving
equation), with integrands integrable on `[0, ε]` and the gaps nonzero on `[ε, T]`, then `D' = d.drift` within
`[ε, T]`. -/
theorem hasDerivWithinAt_drift_of_integral {n : ℕ} (d : SeedData n) {D : ℝ → ℝ} {ε T t : ℝ}
    (hWc : ContinuousOn d.W (Icc ε T)) (hV₀c : ContinuousOn d.V₀ (Icc ε T))
    (hVc : ∀ m, ContinuousOn (d.V m) (Icc ε T)) (hne₀ : ∀ u ∈ Icc ε T, d.W u - d.V₀ u ≠ 0)
    (hne : ∀ m, ∀ u ∈ Icc ε T, d.W u - d.V m u ≠ 0)
    (hint₀ : IntervalIntegrable (fun s => -(d.κ / 2) / (d.W s - d.V₀ s)) volume 0 ε)
    (hint : ∀ m, IntervalIntegrable (fun s => d.κ * d.r m / (d.W s - d.V m s)) volume 0 ε)
    (hD : ∀ u ∈ Icc ε T, D u = (∫ s in (0 : ℝ)..u, -(d.κ / 2) / (d.W s - d.V₀ s))
      + ∑ m, ∫ s in (0 : ℝ)..u, d.κ * d.r m / (d.W s - d.V m s)) (ht : t ∈ Icc ε T) :
    HasDerivWithinAt D (d.drift t) (Icc ε T) t := by
  have h0 := hasDerivWithinAt_of_eq_integral (x₀ := 0) (v := fun u => ∫ s in (0 : ℝ)..u, -(d.κ / 2) /
    (d.W s - d.V₀ s)) hint₀ (continuousOn_const.div (hWc.sub hV₀c) hne₀) (fun u _ => (zero_add _).symm) ht
  have h1 := hasDerivWithinAt_of_eq_sum_integral (x₀ := 0) Finset.univ
    (f := fun m s => d.κ * d.r m / (d.W s - d.V m s))
    (v := fun u => ∑ m, ∫ s in (0 : ℝ)..u, d.κ * d.r m / (d.W s - d.V m s)) (fun m _ => hint m)
    (fun m _ => continuousOn_const.div (hWc.sub (hVc m)) (hne m)) (fun u _ => (zero_add _).symm) ht
  rw [d.drift_eq]
  exact (h0.add h1).congr (fun u hu => hD u hu) (hD t ht)

/-! ### The seeded scale -/

/-- `ScaleOK` is antitone in `λ`. -/
theorem ScaleOK.mono_lam {r a₀ γ Γ lam lam' T L : ℝ} (h : ScaleOK r a₀ γ Γ lam' T L) (hl : lam ≤ lam') :
    ScaleOK r a₀ γ Γ lam T L :=
  { h with
    la := hl.trans h.la
    gl := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hl) zero_le_two)
      (sq_nonneg γ)).trans h.gl }

/-- **Every family of constants admits a seeded scale.** -/
theorem exists_seedScaleOK {r a₀ γ : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hγ : 0 < γ) (Γ lam T : ℝ) :
    ∃ L, SeedScaleOK r a₀ γ Γ lam T L := by
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha₀ hγ Γ (max lam 0 + Real.log 2) T
  refine ⟨L, hL.mono_lam ((le_max_left lam 0).trans (le_add_of_nonneg_right (Real.log_nonneg one_le_two))),
    ?_, ?_⟩
  · have h1 := hL.gl
    rw [Real.exp_add, Real.exp_log two_pos] at h1
    have h2 : Real.exp lam ≤ Real.exp (max lam 0) := Real.exp_le_exp.2 (le_max_left _ _)
    calc 4 * Real.exp lam / γ ^ 2 ≤ 4 * Real.exp (max lam 0) / γ ^ 2 := by gcongr
      _ = 2 * (Real.exp (max lam 0) * 2) / γ ^ 2 := by ring
      _ ≤ Real.exp L := h1
  · have h1 := hL.gl
    rw [Real.exp_add, Real.exp_log two_pos] at h1
    have h2 : 1 ≤ Real.exp (max lam 0) := Real.one_le_exp (le_max_right _ _)
    calc 4 / γ ^ 2 ≤ 4 * Real.exp (max lam 0) / γ ^ 2 :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right (by norm_num) h2) (sq_nonneg γ)
      _ = 2 * (Real.exp (max lam 0) * 2) / γ ^ 2 := by ring
      _ ≤ Real.exp L := h1

end InteractingSLE.ZhanGT4
